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
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.StoreInstruction;

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

    /**
     * @param bugReporter
     */
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

    /**
     * @param method
     * @throws CFGBuilderException
     * @throws DataflowAnalysisException
     */
    private void analyseMethod(Method method) throws CFGBuilderException, DataflowAnalysisException {
        CFG cfg = classCtx.getCFG(method);
        // key is value number of the object, value is the object model
        Map<ValueNumber, ObjectModel> objNullCheckMap = new HashMap<>();
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

            // when encounter if(obj == null) or if(obj != null)
            if (ins instanceof IFNONNULL || ins instanceof IFNULL) {
                int targetPc = ((IfInstruction) ins).getTarget().getPosition();
                if (targetPc < handle.getPosition()) {
                    continue;
                }
                // Get the value number stack of ifinstruction
                ValueNumberFrame frameTmp = flow.getFactAtLocation(location);

                // the top value of stack must be the Object to be compared
                ValueNumber objValueNum = frameTmp.getTopValue();
                ObjectModel objModel = getObjectModel(location, method, constPool);
                if (null != objModel) {
                    objModel.setValueNumber(objValueNum);
                    objNullCheckMap.put(objModel.getValueNumber(), objModel);
                }
            }

            // when encounter invokeInstruction
            if (ins instanceof InvokeInstruction) {
                // if the objNullCheckMap is empty, do nothing
                if (objNullCheckMap.isEmpty()) {
                    continue;
                }
                int paramNum = ((InvokeInstruction) ins).getArgumentTypes(constPool).length;

                // get the access object
                ObjectModel accessObj = accessObjInfo(flow, location, paramNum, method);

                if (null != accessObj) {
                    // check the accessed object has been null checked
                    ObjectModel objModel = objNullCheckMap.get(accessObj.getValueNumber());
                    boolean res = checkNullPoint(location, handle.getPosition(), objModel, constPool);
                    if (!res) {
                        fillWarningReport(objModel.getName(), location, method);
                        // every object warn once time
                        objNullCheckMap.remove(accessObj.getValueNumber());
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
     * @param constPool
     *            constant pool
     * @return object model
     * @throws DataflowAnalysisException
     */
    private static ObjectModel getObjectModel(Location location, Method method, ConstantPoolGen constPool)
            throws DataflowAnalysisException {
        InstructionHandle handle = location.getHandle();
        InstructionHandle preHandle = handle.getPrev();

        if (null != preHandle) {
            Instruction preIns = preHandle.getInstruction();
            // the object is global field
            if (preIns instanceof GETFIELD) {
                String fieldName = ((GETFIELD) preIns).getFieldName(constPool);
                ObjectModel objModel = new ObjectModel(fieldName, Integer.MAX_VALUE, handle, -1);
                    return objModel;
            }

            // the object is local variable
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

    /**
     * Check the instruction has accessed the null object
     *
     * @param accessLocation
     *            location to be checked
     * @param currentPc
     *            current position
     * @param objModel
     *            object null checked model
     * @param constPool
     *            constant pool
     * @return boolean check result
     */
    private static boolean checkNullPoint(Location accessLocation, int currentPc, ObjectModel objModel,
            ConstantPoolGen constPool) {
        if (null == objModel) {
            return true;
        }

        InstructionHandle ifHandle = objModel.getIfHandle();
        Instruction ifIns = ifHandle.getInstruction();
        int ifPc = ifHandle.getPosition();

        // if the access instruction's position beyond the object's range, return true
        if (currentPc > objModel.getEndPc()) {
            return true;
        }

        if (ifIns instanceof IFNONNULL) {
            InstructionHandle targetHandle = ((IFNONNULL) ifIns).getTarget();
            int targetPc = targetHandle.getPosition();

            // if the access instruction is between the if branch, and there is no return and new instruction before,
            // return false
            /*
             * if(obj == null){ obj.toString(); }
             */
            if (currentPc > ifPc && currentPc < targetPc
                    && !hasReturnOrNew(ifHandle, accessLocation.getHandle(), objModel, constPool)) {
                return false;

            }
        }

        if (ifIns instanceof IFNULL) {
            InstructionHandle targetHandle = ((IFNULL) ifIns).getTarget();
            int targetPc = targetHandle.getPosition();

            // if the access instruction is beyond the else branch, and there is no return and new instruction before,
            // return false
            /*
             * if(obj != null) { ... } else { obj.toString(); }
             */
            if (currentPc > targetPc
                    && !hasReturnOrNew(targetHandle, accessLocation.getHandle(), objModel, constPool)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Check there is return or new instruction between start handle and end handle;
     *
     * @param startHandle
     *            start handle
     * @param endHandle
     *            end handle
     * @param objModel
     *            object null checked model
     * @param constPool
     *            constant pool
     * @return boolean result
     */
    private static boolean hasReturnOrNew(InstructionHandle startHandle, InstructionHandle endHandle,
            ObjectModel objModel,
            ConstantPoolGen constPool) {
        int endPc = endHandle.getPosition();
        int index = objModel.getIndexInStack();

        Instruction loopIns = startHandle.getInstruction();
        InstructionHandle loopHandle = startHandle;
        int loopPc = startHandle.getPosition();

        while (loopPc < endPc) {
            // when encounter return instruction, return true
            if (loopIns instanceof ReturnInstruction) {
                return true;
            }

            // when encounter throw exception, return true
            if (loopIns instanceof ATHROW) {
                return true;
            }

            // when encounter assign value to the local object, for example
            /**
             * if(obj = null){ obj = getString(); //obj = new Sting("test") }
             */
            if (index != -1 && loopIns instanceof StoreInstruction) {
                int indexTmp = ((StoreInstruction) loopIns).getIndex();
                if (indexTmp == index) {
                    return true;
                }
            }

            // when encounter assign value to the global object, for example
            /**
             * if(obj = null){ obj = getString(); //obj = new Sting("test") }
             */
            if (index == -1 && loopIns instanceof PUTFIELD) {
                String filedName = ((PUTFIELD) loopIns).getFieldName(constPool);
                if (filedName.equals(objModel.getName())) {
                    return true;
                }
            }

            // when encounter goto instruction, goto the target instruction
            if (loopIns instanceof GotoInstruction) {
                if (((GotoInstruction) loopIns).getTarget().getPosition() > loopPc) {
                    loopHandle = ((GotoInstruction) loopIns).getTarget();
                    loopIns = loopHandle.getInstruction();
                    loopPc = loopHandle.getPosition();
                    endPc = Integer.MAX_VALUE;
                    continue;
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

    /**
     * Get the access object from the invoke instruction, as name.toString(), name is the target object
     *
     * @param flow
     *            value number data flow of this metod
     * @param location
     *            location
     * @param paramNum
     *            the number of called method's parameter
     * @param method
     *            method to be analyzed
     * @return the access object
     * @throws DataflowAnalysisException
     */
    private static ObjectModel accessObjInfo(ValueNumberDataflow flow, Location location, int paramNum, Method method)
            throws DataflowAnalysisException {
        ValueNumberFrame vnaFrame = flow.getFactAtLocation(location);

        // get the index of the object in stack
        int objStack = vnaFrame.getNumSlots() - paramNum - 1;

        if (objStack < vnaFrame.getNumLocals()) {
            return null;
        }
        ValueNumber valueNumber = vnaFrame.getValue(objStack);
        FieldAnnotation fieldAnnotation = ValueNumberSourceInfo.findFieldAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame);

        if (null != fieldAnnotation) {
            ObjectModel obj = new ObjectModel(fieldAnnotation.getFieldName(), valueNumber);
            return obj;
        }

        LocalVariableAnnotation localVariable = ValueNumberSourceInfo.findLocalAnnotationFromValueNumber(method,
                location, valueNumber, vnaFrame);
        if (null != localVariable) {
            ObjectModel obj = new ObjectModel(localVariable.getName(), valueNumber);
            return obj;
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
    private void fillWarningReport(String objName, Location location, Method method)
            throws DataflowAnalysisException, CFGBuilderException {
        if (null == location) {
            return;
        }
        InstructionHandle insHandle = location.getHandle();
        MethodGen methodGen = classCtx.getMethodGen(method);
        String sourceFile = classCtx.getJavaClass().getSourceFileName();

        SourceLineAnnotation sourceLineAnnotation = SourceLineAnnotation.fromVisitedInstruction(classCtx, methodGen,
                sourceFile, insHandle);

        BugInstance bug = new BugInstance(this, "SPEC_ACCESS_NULL_OBJECT", NORMAL_PRIORITY);
        bug.addClassAndMethod(classCtx.getJavaClass(), method);
        bug.addString(objName);
        bug.addSourceLine(sourceLineAnnotation);
        bugReporter.reportBug(bug);

    }

    @Override
    public void report() {
        // TODO Auto-generated method stub

    }

    private static class ObjectModel {
        private final String name;
        private int endPc;
        private InstructionHandle ifHandle;
        private int indexInStack;
        private ValueNumber valueNumber;

        public ObjectModel(String name, ValueNumber valueNumber) {
            this.name = name;
            this.valueNumber = valueNumber;
        }

        public ObjectModel(String name, int endPc, InstructionHandle ifHandle, int indexInStack) {
            this.name = name;
            this.endPc = endPc;
            this.ifHandle = ifHandle;
            this.indexInStack = indexInStack;
        }

        public String getName() {
            return name;
        }

        public int getEndPc() {
            return endPc;
        }

        public InstructionHandle getIfHandle() {
            return ifHandle;
        }

        public int getIndexInStack() {
            return indexInStack;
        }

        public ValueNumber getValueNumber() {
            return valueNumber;
        }

        public void setValueNumber(ValueNumber valueNumber) {
            this.valueNumber = valueNumber;
        }

    }

}
