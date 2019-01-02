/*
 * Contributions to SpotBugs
 * Copyright (C) 2018, Administrator
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
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.INVOKEINTERFACE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;

import edu.umd.cs.findbugs.BugAccumulator;
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
public class MapTraversalWayCheck implements Detector {

    private static final String CLASS_MAP = "java/util/Map";

    private static final String CLASS_ITERATOR = "java/util/Iterator";

    private static final String CLASS_MAP_ENTRY = "java/util/Map\u0024Entry";

    private static final String MAP_KEYSET = "keySet";

    private static final String MAP_ENTRYSET = "entrySet";

    private static final String MAP_HASNEXT = "hasNext";

    private static final int NUM_KEYSET = 0;

    private static final int NUM_ENTRYSET = 1;

    private static final int NUM_VALUES = -1;

    private final List<Integer> mapEndList = new ArrayList<>();

    private final BugAccumulator bugAccumulator;

    /**
     * @param bugReporter
     */
    public MapTraversalWayCheck(BugReporter bugReporter) {
        this.bugAccumulator = new BugAccumulator(bugReporter);
    }

    @Override
    public void visitClassContext(ClassContext classContext) {
        Method[] methodList = classContext.getJavaClass().getMethods();
        for (Method method : methodList) {
            if (method.getCode() == null) {
                continue;
            }

            // Init method,skip
            String methodName = method.getName();
            if ("<init>".equals(methodName) || "<clinit>".equals(methodName)) {
                continue;
            }

            try {
                analyzeMethod(classContext, method);
            } catch (CFGBuilderException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (DataflowAnalysisException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        bugAccumulator.reportAccumulatedBugs();

    }

    /**
     * Analyze method
     *
     * @param classContext
     *            class context
     * @param method
     *            method to be analyzed
     * @throws CFGBuilderException
     * @throws DataflowAnalysisException
     */
    private void analyzeMethod(ClassContext classContext, Method method)
            throws CFGBuilderException, DataflowAnalysisException {
        CFG cfg = classContext.getCFG(method);
        if (null == cfg) {
            return;
        }

        ConstantPoolGen constPool = classContext.getConstantPoolGen();

        Collection<Location> locationCollection = cfg.orderedLocations();
        ArrayList<Location> locationList = new ArrayList<>();
        locationList.addAll(locationCollection);

        loopAnalyse(locationList, 0, -1, constPool, classContext, method);
    }

    /**
     * loop analyze the byte codes
     *
     * @param locationList
     *            codes location list
     * @param startIndex
     *            start index
     * @param constPool
     *            constant pool
     * @param classContext
     *            class context
     * @param method
     *            method to be analyzed
     * @return the end index in the instruction list
     * @throws DataflowAnalysisException
     * @throws CFGBuilderException
     */
    private int loopAnalyse(ArrayList<Location> locationList, int startIndex, int way, ConstantPoolGen constPool,
            ClassContext classContext, Method method) throws DataflowAnalysisException, CFGBuilderException {
        int currentStartIndex = startIndex;
        int currentEndIndex = locationList.size();
        int currentWay = way;

        Location currentLocation = locationList.get(startIndex);

        for (int i = startIndex + 1; i < locationList.size(); i++) {
            Location location = locationList.get(i);
            InstructionHandle insHandle = location.getHandle();
            if (null == insHandle) {
                continue;
            }

            Instruction ins = insHandle.getInstruction();

            if (ins instanceof INVOKEINTERFACE) {
                // check is the end of the map loop
                boolean end = checkMapLoopEnd(ins, constPool);
                if (!mapEndList.contains(Integer.valueOf(i)) && end) {
                    currentEndIndex = i;
                    mapEndList.add(Integer.valueOf(i));
                    break;
                }
                int constIndex = ((INVOKEINTERFACE) ins).getIndex();

                int tmp = checkIsMapTravsal(constIndex, constPool);

                if (NUM_VALUES != tmp) {
                    int nextStartIndex = i;
                    // when encounter the instruction of traversing map, find the end index of the loop
                    int endIndex = loopAnalyse(locationList, nextStartIndex, tmp, constPool, classContext, method);
                    i = endIndex + 1;
                }
            }
        }

        if (NUM_VALUES == currentWay) {
            return currentEndIndex;
        }

        boolean res = checkValid(currentWay, locationList, currentStartIndex, currentEndIndex, classContext, method,
                constPool);

        if (!res) {
            fillReport(currentLocation, classContext, method, constPool);
        }

        return currentEndIndex;
    }


    /**
     * Fill the bug report
     *
     * @param location
     *            code location
     * @param classContext
     *            class context
     * @param method
     *            method
     * @param constPool
     *            constant pool
     * @throws DataflowAnalysisException
     * @throws CFGBuilderException
     */
    private void fillReport(Location location, ClassContext classContext, Method method, ConstantPoolGen constPool)
            throws DataflowAnalysisException, CFGBuilderException {
        if (null == location) {
            return;
        }

        InstructionHandle insHandle = location.getHandle();
        MethodGen methodGen = classContext.getMethodGen(method);
        String sourceFile = classContext.getJavaClass().getSourceFileName();
        ValueNumberDataflow valueNumDataFlow = classContext.getValueNumberDataflow(method);

        ValueNumberFrame vnaFrame = valueNumDataFlow.getFactAtLocation(location);
        ValueNumber valueNumber = vnaFrame.getTopValue();

        BugAnnotation variableAnnotation = ValueNumberSourceInfo.findAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame, "VALUE_OF");

        SourceLineAnnotation sourceLineAnnotation = SourceLineAnnotation.fromVisitedInstruction(classContext, methodGen,
                sourceFile, insHandle);

        bugAccumulator.accumulateBug(new BugInstance(this, "DM_TRAVERSAL_MAP_INEFFICIENT_CHECK", NORMAL_PRIORITY)
                .addClassAndMethod(methodGen, sourceFile).addOptionalAnnotation(variableAnnotation),
                sourceLineAnnotation);
    }

    /**
     * Check the way of traversing Map
     *
     * @param constIndex
     *            the index in constant pool
     * @param constPool
     *            constant pool
     * @return way: -1: values or not map traversal; 0:keySet; 1: entrySet
     */
    private int checkIsMapTravsal(int constIndex, ConstantPoolGen constPool) {

        ConstantCP constTmp = (ConstantCP) constPool.getConstant(constIndex);

        ConstantClass classInfo = (ConstantClass) constPool.getConstant(constTmp.getClassIndex());
        String className = ((ConstantUtf8) constPool.getConstant(classInfo.getNameIndex())).getBytes();

        ConstantNameAndType cnat = (ConstantNameAndType) constPool.getConstant(constTmp.getNameAndTypeIndex());
        String methodName = ((ConstantUtf8) constPool.getConstant(cnat.getNameIndex())).getBytes();
        if (!CLASS_MAP.equals(className)) {
            return NUM_VALUES;
        }

        if (MAP_KEYSET.equals(methodName)) {
            return NUM_KEYSET;
        } else if (MAP_ENTRYSET.equals(methodName)) {
            return NUM_ENTRYSET;
        } else {
            return NUM_VALUES;
        }

    }

    /**
     * Check whether the way of traversing Map is valid
     *
     * @param way
     *            the way of traversing Map
     * @param locationList
     *            the code location list
     * @param startIndex
     *            start loop index
     * @param endIndex
     *            end loop index
     * @param classContext
     *            class context
     * @param method
     *            method
     * @param constPool
     *            constant pool
     * @return boolean true: valid; false: invalid
     * @throws CFGBuilderException
     * @throws DataflowAnalysisException
     */
    private boolean checkValid(int way, List<Location> locationList, int startIndex, int endIndex,
            ClassContext classContext, Method method, ConstantPoolGen constPool)
            throws DataflowAnalysisException, CFGBuilderException {
        boolean valid = true;
        int keyCount = 0;
        int valueCount = 0;

        Location startLocation = locationList.get(startIndex);

        String objName = getFieldName(1, startLocation, classContext, method);
        String entryName = null;
        if (null == objName) {
            return true;
        }

        for (int j = startIndex + 1; j < endIndex; j++) {
            Location location = locationList.get(j);
            InstructionHandle insHandleLoop = location.getHandle();

            if (null == insHandleLoop) {
                continue;
            }

            Instruction ins = insHandleLoop.getInstruction();
            if (!(ins instanceof INVOKEINTERFACE)) {
                continue;
            }


            int constIndex = ((INVOKEINTERFACE) ins).getIndex();
            ConstantCP constTmp = (ConstantCP) constPool.getConstant(constIndex);

            ConstantClass classInfo = (ConstantClass) constPool.getConstant(constTmp.getClassIndex());
            String className = ((ConstantUtf8) constPool.getConstant(classInfo.getNameIndex())).getBytes();

            ConstantNameAndType cnat = (ConstantNameAndType) constPool.getConstant(constTmp.getNameAndTypeIndex());
            String methodName = ((ConstantUtf8) constPool.getConstant(cnat.getNameIndex())).getBytes();

            if (!CLASS_MAP.equals(className) && !CLASS_MAP_ENTRY.equals(className)
                    && !CLASS_ITERATOR.equals(className)) {
                continue;
            }

            /* If the way is keyset, the method-‘Map.get(key)’ is called, invalid */
            if (NUM_KEYSET == way) {
                if (CLASS_MAP.equals(className) && "get".equals(methodName)) {
                    String fieldName = getFieldName(0, location, classContext, method);
                    if (objName.equals(fieldName)) {
                        return false;
                    }
                }
            } else if (NUM_ENTRYSET == way) {
                if (CLASS_ITERATOR.equals(className) && null == entryName) {
                    /*
                     * When the Iterator.next() is called, the following instruction must be 'checkcast' and 'astore' in
                     * entryset loop
                     */
                    Location loc = locationList.get(j + 2);
                    Instruction insTmp = loc.getHandle().getInstruction();
                    int index = -1;
                    if (insTmp instanceof ASTORE) {
                        // get the index of the entry in local variable table
                        index = ((ASTORE) insTmp).getIndex();
                    }
                    LocalVariable localVa = method.getLocalVariableTable().getLocalVariable(index,
                            loc.getHandle().getPosition() + 1);
                    entryName = localVa.getName();
                    continue;
                }

                /* If the way is entryset, the method-‘Entry.getKey() or Entry.getValue()’ is never called, invalid */
                if (CLASS_MAP_ENTRY.equals(className)) {
                    if ("getKey".equals(methodName)) {
                        String valueName = getFieldName(1, location, classContext, method);
                        if (null != entryName && entryName.equals(valueName)) {
                            keyCount++;
                        }
                    } else if ("getValue".equals(methodName)) {
                        String valueName = getFieldName(1, location, classContext, method);
                        if (null != entryName && entryName.equals(valueName)) {
                            valueCount++;
                        }
                    }
                }
            }
        }

        if (NUM_ENTRYSET == way) {
            // if getKey or getValue is never called and the count of calling number is not equal, invalid
            if ((0 == keyCount || 0 == valueCount) && (keyCount != valueCount)) {
                valid = false;
            }
        }

        return valid;
    }

    /**
     * Get the object name of operator of the instruction
     *
     * @param way
     *            whether has parameter,1: no parameter, 0: one parameter
     * @param location
     *            the location of instruction
     * @param classContext
     *            class context
     * @param method
     *            method
     * @return String object name
     * @throws DataflowAnalysisException
     * @throws CFGBuilderException
     */
    private String getFieldName(int way, Location location, ClassContext classContext, Method method)
            throws DataflowAnalysisException, CFGBuilderException {
        ValueNumberFrame vnaFrame = classContext.getValueNumberDataflow(method).getFactAtLocation(location);
        // If there is no parameter，the object is the top in stack
        ValueNumber valueNumber = vnaFrame.getTopValue();
        if (0 == way) {
            // If there is one parameter，the object is the second to last in stack
            valueNumber = vnaFrame.getValue(vnaFrame.getNumSlots() - 2);
        }

        // golable variable
        FieldAnnotation filedAnn = ValueNumberSourceInfo.findFieldAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame);

        if (null != filedAnn) {
            return filedAnn.getFieldName();
        }


        // local variable
        LocalVariableAnnotation localAnn = ValueNumberSourceInfo.findLocalAnnotationFromValueNumber(method, location,
                valueNumber, vnaFrame);
        if (null != localAnn) {
            return localAnn.getName();
        }

        return null;
    }


    /**
     * check whether the instruction is the end of the map loop
     *
     * @param ins
     *            instruction
     * @param constPool
     *            constant pool
     * @return boolean true: end
     */
    private boolean checkMapLoopEnd(Instruction ins, ConstantPoolGen constPool) {

            int constIndex = ((INVOKEINTERFACE) ins).getIndex();
            ConstantCP constTmp = (ConstantCP) constPool.getConstant(constIndex);

            ConstantClass classInfo = (ConstantClass) constPool.getConstant(constTmp.getClassIndex());
            String className = ((ConstantUtf8) constPool.getConstant(classInfo.getNameIndex())).getBytes();

            ConstantNameAndType cnat = (ConstantNameAndType) constPool.getConstant(constTmp.getNameAndTypeIndex());
            String methodName = ((ConstantUtf8) constPool.getConstant(cnat.getNameIndex())).getBytes();

            if (CLASS_ITERATOR.equals(className) && MAP_HASNEXT.equals(methodName)) {
                return true;
            }
        return false;
    }


    @Override
    public void report() {
        // TODO Auto-generated method stub

    }

}
