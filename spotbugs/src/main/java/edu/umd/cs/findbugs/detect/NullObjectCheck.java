/*
 * Contributions to SpotBugs
 * Copyright (C) 2019, Administrator
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package edu.umd.cs.findbugs.detect;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.ReturnInstruction;

import edu.umd.cs.findbugs.BugAnnotation;
import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.Detector;
import edu.umd.cs.findbugs.FieldAnnotation;
import edu.umd.cs.findbugs.LocalVariableAnnotation;
import edu.umd.cs.findbugs.SourceLineAnnotation;
import edu.umd.cs.findbugs.ba.CFG;
import edu.umd.cs.findbugs.ba.CFGBuilderException;
import edu.umd.cs.findbugs.ba.ClassContext;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.vna.ValueNumber;
import edu.umd.cs.findbugs.ba.vna.ValueNumberDataflow;
import edu.umd.cs.findbugs.ba.vna.ValueNumberFrame;
import edu.umd.cs.findbugs.ba.vna.ValueNumberSourceInfo;

/**
 * @since ?
 *
 */
public class NullObjectCheck implements Detector {

    private ClassContext classCtx;
    private final BugReporter bugReporter;

    public NullObjectCheck(BugReporter bugReporter) {
        this.bugReporter = bugReporter;
    }

    @Override
    public void visitClassContext(ClassContext classContext) {
        this.classCtx = classContext;

        Method[] methods = classContext.getJavaClass().getMethods();

        for (Method method : methods) {
            try {
                // Init method,skip
                String methodName = method.getName();
                if ("<init>".equals(methodName) || "<clinit>".equals(methodName)) {
                    continue;
                }

                analyseMethod(method);
            } catch (Exception e) {
                bugReporter.logError("Detector " + this.getClass().getName() + " caught exception", e);
            }
        }

    }

    private void analyseMethod(Method method) throws CFGBuilderException, DataflowAnalysisException {
        CFG cfg = classCtx.getCFG(method);
        Map<String, ObjectModel> objModels = new HashMap<>();
        if (null == cfg) {
            return;
        }

        Collection<Location> locations = cfg.orderedLocations();
        ValueNumberDataflow flow = classCtx.getValueNumberDataflow(method);
        ConstantPoolGen constPool = classCtx.getConstantPoolGen();

        for (Location location : locations) {
            InstructionHandle handle = location.getHandle();
            if (null == handle) {
                continue;
            }
            Instruction ins = handle.getInstruction();

            if (ins instanceof IFNONNULL || ins instanceof IFNULL) {
                ObjectModel objModel = getObjectModel(location, method, flow);
                if (null != objModel) {
                    objModels.put(objModel.getName(), objModel);
                }
            }

            if (ins instanceof InvokeInstruction) {
                int paramNum = ((InvokeInstruction) ins).getArgumentTypes(constPool).length;
                Map<String, String> objInfo = getObjName(flow, location, paramNum, method);
                if (null != objInfo) {
                    ObjectModel objModel = objModels.get(objInfo.get("name"));
                    String isField = objInfo.get("field");
                    if (objModel.getIndexInStack() == -1 && isField.equals("true")
                            || objModel.getIndexInStack() != -1 && isField.equals("false")) {
                        checkNullPoint(location, handle.getPosition(), objModel, method, constPool);
                    }
                }
            }

        }

    }

    /**
     * Get object model
     *
     * @param location
     *            location
     * @param method
     *            method
     * @param flow
     *            value number data flow
     * @return object model
     * @throws DataflowAnalysisException
     */
    private ObjectModel getObjectModel(Location location, Method method, ValueNumberDataflow flow)
            throws DataflowAnalysisException {
        InstructionHandle handle = location.getHandle();

        ValueNumberFrame frame = flow.getFactAtLocation(location);
        ValueNumber topValueNum = frame.getTopValue();

        InstructionHandle preHandle = handle.getPrev();
        if (null != preHandle) {
            Instruction preIns = preHandle.getInstruction();
            if (preIns instanceof GETFIELD) {
                FieldAnnotation field = ValueNumberSourceInfo.findFieldAnnotationFromValueNumber(method, location,
                        topValueNum, frame);
                if (null != field) {
                    ObjectModel objModel = new ObjectModel(field.getFieldName(), Integer.MAX_VALUE, handle, -1);
                    return objModel;
                }
            }

            if (preIns instanceof LoadInstruction) {
                int local = ((LoadInstruction) preIns).getIndex();
                LocalVariableTable localVariableTable = method.getLocalVariableTable();
                LocalVariable lv1 = localVariableTable.getLocalVariable(local, handle.getPosition());
                if (null != lv1) {
                    ObjectModel objModel = new ObjectModel(lv1.getName(), lv1.getStartPC() + lv1.getLength(), handle,
                            local);
                    return objModel;
                }
            }
        }
        return null;
    }

    private void checkNullPoint(Location accessLocation, int currentPc, ObjectModel objModel, Method method,
            ConstantPoolGen constPool) throws DataflowAnalysisException, CFGBuilderException {
        if (null == objModel) {
            return;
        }

        InstructionHandle ifHandle = objModel.getIfHandle();
        Instruction ifIns = ifHandle.getInstruction();
        int ifPc = ifHandle.getPosition();

        if (currentPc > objModel.getEndPc()) {
            return;
        }

        if (ifIns instanceof IFNONNULL) {
            InstructionHandle targetHandle = ((IFNONNULL) ifIns).getTarget();
            int targetPc = targetHandle.getPosition();

            if (currentPc > ifPc && currentPc < targetPc
                    && !hasReturn(ifHandle, accessLocation.getHandle(), objModel, constPool)) {
                fillWarningReport(accessLocation, method);
            }
        }

        if (ifIns instanceof IFNULL) {
            InstructionHandle targetHandle = ((IFNULL) ifIns).getTarget();
            int targetPc = targetHandle.getPosition();
            if (currentPc > targetPc && !hasReturn(targetHandle, accessLocation.getHandle(), objModel, constPool)) {
                fillWarningReport(accessLocation, method);
            }
        }
    }

    private boolean hasReturn(InstructionHandle startHandle, InstructionHandle endHandle, ObjectModel objModel,
            ConstantPoolGen constPool) {
        int endPc = endHandle.getPosition();
        int index = objModel.getIndexInStack();

        Instruction loopIns = startHandle.getInstruction();
        InstructionHandle loopHandle = startHandle;
        int loopPc = startHandle.getPosition();

        while (loopPc < endPc) {
            if (loopIns instanceof ReturnInstruction) {
                return true;
            }

            if (index != -1 && loopIns instanceof LoadInstruction) {
                int indexTmp = ((LoadInstruction) loopIns).getIndex();
                if (indexTmp == index) {
                    return true;
                }
            }

            if (index == -1 && loopIns instanceof PUTFIELD) {
                String filedName = ((PUTFIELD) loopIns).getFieldName(constPool);
                if (filedName.equals(objModel.getName())) {
                    return true;
                }
            }

            loopHandle = loopHandle.getNext();
            if (null == loopHandle) {
                break;
            }
            loopIns = loopHandle.getInstruction();
            loopPc = loopHandle.getPosition();
        }

        return false;

    }

    private Map<String, String> getObjName(ValueNumberDataflow flow, Location location, int paramNum, Method method)
            throws DataflowAnalysisException {
        Map<String, String> objInfoMap = new HashMap<>();
        ValueNumberFrame vnaFrame = flow.getFactAtLocation(location);
        int objStack = vnaFrame.getNumSlots() - paramNum - 1;

        if (objStack < vnaFrame.getNumLocals()) {
            return null;
        }
        ValueNumber valueNumber = vnaFrame.getValue(vnaFrame.getNumSlots() - paramNum - 1);
        FieldAnnotation fieldAnnotation = ValueNumberSourceInfo.findFieldAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame);

        if (null != fieldAnnotation) {
            objInfoMap.put("name", fieldAnnotation.getFieldName());
            objInfoMap.put("field", "true");
            return objInfoMap;
        }
        LocalVariableAnnotation localVariable = ValueNumberSourceInfo.findLocalAnnotationFromValueNumber(method,
                location, valueNumber, vnaFrame);
        if (null != localVariable) {
            objInfoMap.put("name", localVariable.getName());
            objInfoMap.put("field", "false");
            return objInfoMap;
        }

        return null;
    }

    /**
     * Fill the bug report
     *
     * @param location
     *            code location
     * @param classCtx
     *            class context
     * @param method
     *            method
     * @throws DataflowAnalysisException
     * @throws CFGBuilderException
     */
    private void fillWarningReport(Location location, Method method)
            throws DataflowAnalysisException, CFGBuilderException {
        if (null == location) {
            return;
        }
        InstructionHandle insHandle = location.getHandle();
        MethodGen methodGen = classCtx.getMethodGen(method);
        String sourceFile = classCtx.getJavaClass().getSourceFileName();
        ValueNumberDataflow valueNumDataFlow = classCtx.getValueNumberDataflow(method);

        ValueNumberFrame vnaFrame = valueNumDataFlow.getFactAtLocation(location);

        ValueNumber valueNumber = vnaFrame.getValue(vnaFrame.getNumLocals());

        BugAnnotation variableAnnotation = ValueNumberSourceInfo.findAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame, "VALUE_OF");

        SourceLineAnnotation sourceLineAnnotation = SourceLineAnnotation.fromVisitedInstruction(classCtx, methodGen,
                sourceFile, insHandle);

        BugInstance bug = new BugInstance(this, "SPEC_ACCESS_NULL_OBJECT", NORMAL_PRIORITY);
        bug.addClassAndMethod(classCtx.getJavaClass(), method);
        bug.addOptionalAnnotation(variableAnnotation);
        bug.addSourceLine(sourceLineAnnotation);
        bugReporter.reportBug(bug);

    }

    @Override
    public void report() {
        // TODO Auto-generated method stub

    }

    private static class ObjectModel {
        private String name;
        private int endPc;
        private InstructionHandle ifHandle;
        private int indexInStack;

        public ObjectModel(String name, int endPc, InstructionHandle ifHandle, int indexInStack) {
            this.name = name;
            this.endPc = endPc;
            this.ifHandle = ifHandle;
            this.indexInStack = indexInStack;
        }

        public String getName() {
            return name;
        }

        public void setName(String name) {
            this.name = name;
        }

        public int getEndPc() {
            return endPc;
        }

        public void setEndPc(int endPc) {
            this.endPc = endPc;
        }

        public InstructionHandle getIfHandle() {
            return ifHandle;
        }

        public void setIfHandle(InstructionHandle ifHandle) {
            this.ifHandle = ifHandle;
        }

        public int getIndexInStack() {
            return indexInStack;
        }

        public void setIndexInStack(int indexInStack) {
            this.indexInStack = indexInStack;
        }

    }

}
