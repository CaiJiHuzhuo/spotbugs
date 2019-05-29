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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;

import edu.umd.cs.findbugs.BugAnnotation;
import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.Detector;
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
public class SelectorCloseDetector implements Detector {

    private final BugReporter bugReporter;
    private ClassContext classCtx;

    /**
     * @param bugReporter
     */
    public SelectorCloseDetector(BugReporter bugReporter) {
        this.bugReporter = bugReporter;

    }

    @Override
    public void visitClassContext(ClassContext classContext) {
        this.classCtx = classContext;

        Method[] methods = classContext.getJavaClass().getMethods();

        for (Method method : methods) {
            if (method.getCode() == null) {
                continue;
            }

            // Init method,skip
            String methodName = method.getName();
            if ("<init>".equals(methodName) || "<clinit>".equals(methodName)) {
                continue;
            }

            try {
                analyzeMethod(method);
            } catch (Exception e) {
                bugReporter.logError("Detector " + this.getClass().getName() + " caught exception", e);
            }

        }
    }

    private void analyzeMethod(Method method)
            throws CFGBuilderException, DataflowAnalysisException {
        CFG cfg = classCtx.getCFG(method);
        if (null == cfg) {
            return;
        }

        Collection<Location> locationList = cfg.orderedLocations();
        ConstantPoolGen constPool = classCtx.getConstantPoolGen();
        List<InstructionHandle> socketCloseList = new ArrayList<>();

        for (Location location : locationList) {
            InstructionHandle handle = location.getHandle();

            if (null == handle) {
                continue;
            }

            Instruction ins = handle.getInstruction();

            if (ins instanceof INVOKEVIRTUAL) {
                int constIndex = ((INVOKEVIRTUAL) ins).getIndex();
                String className = getClassOrMethodFromInstruction(true, constIndex, constPool);
                String methodName = getClassOrMethodFromInstruction(false, constIndex, constPool);

                // when encounter *Channel.close(), add this instruction into list
                if (className.endsWith("Channel") && methodName.equals("close")) {
                    socketCloseList.add(handle);
                }

                // when encounter Selector.close(), check the sockets were closed before
                if (className.endsWith("Selector") && methodName.equals("close")) {

                    // if the socketClose is empty, it means sockets were not closed
                    if (socketCloseList.isEmpty()) {
                        fillWarningReport(location, method);
                    } else {
                        // find a selector.close(), remove a socketChannel.close()
                        socketCloseList.remove(0);
                    }
                }
            }
        }

    }

    /**
     * Get class name or method name
     *
     * @param isClass
     *            true: get class name; false: get method name
     * @param constIndex
     *            index in constant pool
     * @param constPool
     *            constant pool
     * @return
     */
    private static String getClassOrMethodFromInstruction(boolean isClass, int constIndex, ConstantPoolGen constPool) {
        String res = null;
        ConstantCP constTmp = (ConstantCP) constPool.getConstant(constIndex);

        if (isClass) {
            ConstantClass classInfo = (ConstantClass) constPool.getConstant(constTmp.getClassIndex());
            res = ((ConstantUtf8) constPool.getConstant(classInfo.getNameIndex())).getBytes();
        } else {
            ConstantNameAndType cnat = (ConstantNameAndType) constPool.getConstant(constTmp.getNameAndTypeIndex());
            res = ((ConstantUtf8) constPool.getConstant(cnat.getNameIndex())).getBytes();
        }
        return res;
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

        BugInstance bug = new BugInstance(this, "SPEC_SELECTOR_CLOSE", NORMAL_PRIORITY);
        bug.addClassAndMethod(classCtx.getJavaClass(), method);
        bug.addOptionalAnnotation(variableAnnotation);
        bug.addSourceLine(sourceLineAnnotation);
        bugReporter.reportBug(bug);

    }

    @Override
    public void report() {

    }

}
