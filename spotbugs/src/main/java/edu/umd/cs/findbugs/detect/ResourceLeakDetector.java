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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.FieldOrMethod;
import org.apache.bcel.generic.INVOKEINTERFACE;
import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.Type;

import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.Detector;
import edu.umd.cs.findbugs.SourceLineAnnotation;
import edu.umd.cs.findbugs.ba.CFG;
import edu.umd.cs.findbugs.ba.CFGBuilderException;
import edu.umd.cs.findbugs.ba.ClassContext;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.Hierarchy;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.ObjectTypeFactory;
import edu.umd.cs.findbugs.ba.vna.ValueNumber;
import edu.umd.cs.findbugs.ba.vna.ValueNumberDataflow;
import edu.umd.cs.findbugs.ba.vna.ValueNumberFrame;

/**
 * @since ?
 *
 */
public class ResourceLeakDetector implements Detector {

    static final ObjectType[] streamBaseList = { ObjectTypeFactory.getInstance("java.io.InputStream"),
            ObjectTypeFactory.getInstance("java.io.OutputStream"),
            ObjectTypeFactory.getInstance("java.util.zip.ZipFile"), ObjectTypeFactory.getInstance("java.io.Reader"),
            ObjectTypeFactory.getInstance("java.io.Writer"), ObjectTypeFactory.getInstance("java.sql.Connection"),
            ObjectTypeFactory.getInstance("java.sql.Statement"), ObjectTypeFactory.getInstance("java.sql.ResultSet") };

    // private static Map<String, String> resourceMethodFilterMap = new HashMap<>();
    private static Map<String, String> usedMethodFilterMap = new HashMap<>();
    private ClassContext classCtx;
    private final BugReporter bugReporter;

    static {
        // resourceMethodFilterMap.put("org.apache.http.HttpEntity", "getContent");

        usedMethodFilterMap.put("org.apache.commons.configuration.XMLConfiguration", "load");
        usedMethodFilterMap.put("javax.ws.rs.core.Response", "ok");
        usedMethodFilterMap.put("java.util.Properties", "load");// 子类
        usedMethodFilterMap.put("javax.xml.bind.Unmarshaller", "unmarshal");// 接口
        usedMethodFilterMap.put("org.dom4j.io.SAXReader", "read");
        usedMethodFilterMap.put("javax.xml.parsers.DocumentBuilder", "parse");

    }

    /**
     * @param bugReporter
     */
    public ResourceLeakDetector(BugReporter bugReporter) {
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
                analyze(method);
            } catch (Exception e) {
                bugReporter.logError("Detector " + this.getClass().getName() + " caught exception", e);
            }

        }

    }

    private void analyze(Method method) throws CFGBuilderException, ClassNotFoundException, DataflowAnalysisException {
        CFG cfg = classCtx.getCFG(method);
        if (null == cfg) {
            return;
        }
        ConstantPoolGen constPoool = classCtx.getConstantPoolGen();

        Collection<Location> locations = cfg.orderedLocations();
        List<Location> locationList = new ArrayList<>(locations.size());
        locationList.addAll(locations);

        for (int i = 0; i < locationList.size(); i++) {
            Location location = locationList.get(i);

            InstructionHandle handle = location.getHandle();

            if (null == handle) {
                continue;
            }

            Instruction ins = handle.getInstruction();


            if (ins instanceof INVOKESPECIAL || ins instanceof INVOKESTATIC || ins instanceof INVOKEVIRTUAL
                    || ins instanceof INVOKEINTERFACE) {
                Type classType = ((FieldOrMethod) ins).getReferenceType(constPoool);
                String className = ((FieldOrMethod) ins).getClassName(constPoool);
                String methodName = ((InvokeInstruction) ins).getMethodName(constPoool);
                Type returnType = ((InvokeInstruction) ins).getReturnType(constPoool);
                Type[] argTypes = ((InvokeInstruction) ins).getArgumentTypes(constPoool);

                // when the method's name is <init> means it is constructor method
                if ("<init>".equals(methodName)) {
                    returnType = classType;
                }

                if (!(returnType instanceof ObjectType)) {
                    continue;
                }

                // String filterMethod = resourceMethodFilterMap.get(className);
                //
                // if (methodName.equals(filterMethod)) {
                // continue;
                // }

                if (isCreateResourceNoStore(handle, (ObjectType) returnType, methodName, argTypes)
                        && !isFilter(i, locationList, (ObjectType) returnType, constPoool, method)) {
                    fillBugReport(location, method);
                }
            }
        }

    }

    /**
     * Check the method is open a resource and doesn't store the resource
     *
     * @param handle
     *            instruction handle
     * @param type
     *            return type
     * @return boolean
     * @throws ClassNotFoundException
     */
    private boolean isCreateResourceNoStore(InstructionHandle handle, ObjectType type, String methodName,
            Type[] argTypes) throws ClassNotFoundException {
        // check the return is the resource type
        if (!isSubTypeOfList(type, streamBaseList)) {
            return false;
        }

        // get method, pass
        if (methodName.startsWith("get") && argTypes.length == 0) {
            return false;
        }

        InstructionHandle nextHandle = handle.getNext();

        if (null == nextHandle) {
            return false;
        }

        Instruction nextIns = nextHandle.getInstruction();

        /*
         * For example: code: InputStreamReader reader = null; reader = new InputStreamReader(inputStream); Instruction:
         * invokeSpecial *.io.InputStreamReader(InputStream) dup Astore (reader)
         */
        if (nextIns instanceof DUP) {
            InstructionHandle dNextHandle = nextHandle.getNext();
            if (null != dNextHandle && dNextHandle.getInstruction() instanceof StoreInstruction) {
                return false;
            }
        }

        // when the next instruction is storeinstruction, putfiled and returninstruction, it means the resource is
        // stored
        if (!(nextIns instanceof StoreInstruction) && !(nextIns instanceof PUTFIELD)
                && !(nextIns instanceof ReturnInstruction)) {
            return true;
        }

        return false;
    }

    /**
     * Check whether the type is the sub type of the types array
     *
     * @param objType
     *            type to be checked
     * @param objectTypes
     *            types array
     * @return boolean
     * @throws ClassNotFoundException
     */
    private boolean isSubTypeOfList(ObjectType objType, Type[] objectTypes) throws ClassNotFoundException {
        for (Type streamBase : objectTypes) {
            if (!(streamBase instanceof ObjectType)) {
                continue;
            }
            if (Hierarchy.isSubtype(objType, (ObjectType) streamBase)) {
                return true;
            }
        }

        return false;
    }


    /**
     * Check the resource is filtered
     *
     * @param index
     *            the index of the location
     * @param locationList
     *            location list
     * @param resourceType
     *            resource type
     * @param constPoool
     *            constant pool
     * @param method
     *            method
     * @return boolean
     * @throws DataflowAnalysisException
     * @throws CFGBuilderException
     * @throws ClassNotFoundException
     */
    private boolean isFilter(int index, List<Location> locationList, ObjectType resourceType,
            ConstantPoolGen constPoool, Method method)
            throws DataflowAnalysisException, CFGBuilderException, ClassNotFoundException {
        ValueNumberDataflow dataFlow = classCtx.getValueNumberDataflow(method);
        Location location = locationList.get(index);
        ValueNumber resourceValuNum = null;
        ValueNumberFrame frame = dataFlow.getFactAfterLocation(location);

        if (frame.getStackDepth() > 0) {
            // get the value number of resource in stack
            resourceValuNum = frame.getTopValue();
        } else {
            return false;
        }

        for (int i = index + 1; i < locationList.size(); i++) {
            Location locationTmp = locationList.get(i);
            InstructionHandle hanleTmp = locationTmp.getHandle();

            if (null == hanleTmp) {
                return false;
            }
            Instruction ins = hanleTmp.getInstruction();

            ValueNumberFrame frameTmp = dataFlow.getFactAtLocation(locationTmp);

            // when the resource is not in the stack, it means resource is used or stored
            if (frameTmp.getStackDepth() <= 0 || !isInStack(resourceValuNum, frameTmp)) {
                return false;
            }

            if (ins instanceof INVOKESPECIAL || ins instanceof INVOKESTATIC || ins instanceof INVOKEVIRTUAL
                    || ins instanceof INVOKEINTERFACE) {
                String methodName = ((InvokeInstruction) ins).getMethodName(constPoool);
                String className = ((FieldOrMethod) ins).getClassName(constPoool);
                Type[] paramTypes = ((InvokeInstruction) ins).getArgumentTypes(constPoool);

                // if call the close method, filter it
                if (methodName.equals("close")) {
                    return true;
                }

                // if call the ok method, filter it
                if (methodName.equals("ok")) {
                    return true;
                }

                // when the resource is added to a list, filter it
                if (className.endsWith("List") && methodName.equals("add")
                        && isSubTypeOfList(resourceType, paramTypes)) {
                    return true;
                }

                // when the resource is set to a variable, filter it
                if (methodName.startsWith("set") && isSubTypeOfList(resourceType, paramTypes)) {
                    return true;
                }

                // if it is not constructor method, and check the input resource type is the parameter of the
                // constructor method
                if ("<init>".equals(methodName) && isSubTypeOfList(resourceType, paramTypes)) {
                    return true;
                }

                // if the resource is used as parameter of the filterMap's method, filter it
                if (methodName.equals(usedMethodFilterMap.get(className))
                        && isSubTypeOfList(resourceType, paramTypes)) {
                    return true;
                }
            }
        }
        return false;

    }

    /**
     * Check the value number is in the stack
     *
     * @param valueNum
     *            value number to be checked
     * @param frame
     *            stack frame
     * @return boolean
     * @throws DataflowAnalysisException
     */
    private boolean isInStack(ValueNumber valueNum, ValueNumberFrame frame) throws DataflowAnalysisException {
        for (int i = 0; i < frame.getStackDepth(); i++) {
            ValueNumber tmp = frame.getStackValue(i);
            if (valueNum.equals(tmp)) {
                return true;
            }
        }

        return false;
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
    private void fillBugReport(Location location, Method method) throws DataflowAnalysisException, CFGBuilderException {
        if (null == location) {
            return;
        }

        InstructionHandle insHandle = location.getHandle();
        MethodGen methodGen = classCtx.getMethodGen(method);
        String sourceFile = classCtx.getJavaClass().getSourceFileName();

        SourceLineAnnotation sourceLineAnnotation = SourceLineAnnotation.fromVisitedInstruction(classCtx, methodGen,
                sourceFile, insHandle);

        BugInstance bug = new BugInstance(this, "SPEC_RESOURCE_LEAK", NORMAL_PRIORITY);
        bug.addClassAndMethod(methodGen, sourceFile);
        bug.addSourceLine(sourceLineAnnotation);
        bugReporter.reportBug(bug);
    }

    @Override
    public void report() {
        // TODO Auto-generated method stub

    }

}
