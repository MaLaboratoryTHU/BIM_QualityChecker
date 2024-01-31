package org.bimserver.ifcvalidator.extractor;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.*;

class BasicGraphPara {
	
	private static final String DOC_LOC = System.getProperty("user.dir")+ "\\docs\\paths\\";
	

    // Info of sorted paths
    List<Integer> topologicalSortedVerticesList = new ArrayList<> ();
    List<Integer> startVerticesList = new ArrayList<>();
    List<Integer> endVerticesList = new ArrayList<>();
    HashMap<Integer, ArrayList<Integer>> newToOriginMap = new HashMap<>();

    // Info of vertices
    HashMap<Integer, String> VerticesNumToNameMap = new HashMap<>();
    HashMap<String, Integer> VerticesNameToNumMap = new HashMap<>();
    HashMap<String, List<String>> subVerticesMap = new HashMap<>();
    HashMap<String, String> inverseVerticesMap = new HashMap<>();

    // Info of edges
    HashMap<Integer, ArrayList<Integer>> edgeSetMap = new HashMap<>();
    HashMap<Integer, HashMap<Integer, String>> edgeLabelMap = new HashMap<>();

    public BasicGraphPara(String elementInstanceString, String infoEntityString) {

        initVariablesFromFiles(elementInstanceString, infoEntityString);


        //System.out.println("topologicalSortedVerticesList:"+topologicalSortedVerticesList.toString());
        //System.out.println("startVerticesList:"+startVerticesList.toString());
        //System.out.println("endVerticesList:"+endVerticesList.toString());
        //System.out.println("newToOriginMap:"+newToOriginMap.toString());
        //System.out.println("VerticesNumToNameMap:"+VerticesNumToNameMap.toString());
        //System.out.println("VerticesNameToNumMap:"+VerticesNameToNumMap.toString());
        //System.out.println("edgeSetMap:"+edgeSetMap.toString());
        //System.out.println("edgeLabelMap:"+edgeLabelMap.toString());
        //System.out.println("subVerticesMap:"+ subVerticesMap.toString());
        //System.out.println("inverseVerticesMap:" + inverseVerticesMap.toString());
    }

    private void initVariablesFromFiles(String elementInstanceString, String infoEntityString) {

        String infoFileNameString = DOC_LOC + "0104-" + elementInstanceString + "-" +
                infoEntityString + ".txt";
        String subclassFileNameString = DOC_LOC + "subClass" + ".txt";
        String inverseFileNameString = DOC_LOC + "inverse" + ".txt";
        initVariablesFromInfoFile(infoFileNameString);
        initVariablesFromSubClassFile(subclassFileNameString);
        initVariablesFromInverseFile(inverseFileNameString);
    }

    private void initVariablesFromInfoFile(String infoFileNameString){
        try {
            // handle the file such as ifcElement-ifcColourRgb
            int step = 0;
            File filename = new File(infoFileNameString);
            InputStreamReader reader = new InputStreamReader(new FileInputStream(filename));
            BufferedReader br = new BufferedReader(reader);
            String line = "";
            while (line != null) {
                line = br.readLine();
                if(line != null) {
                    if(line.equals("") || line.equals("\n")) {
                        continue;
                    }
                    if(line.startsWith("topologically") || line.startsWith("start")
                            || line.startsWith("end") || line.startsWith("map")  || line.startsWith("edge") ) {
                        step ++;
                        continue;
                    }
                    // System.out.println(step + " *** " + line);
                    try {
                        switch (step) {
                            case 1 :
                            	initVerticesList(line, 1);
                            	break;
                            case 2 : 
                            	initVerticesList(line, 2);
                            	break;
                            case 3 : 
                            	initVerticesList(line, 3);
                            	break;
                            case 4 : 
                            	addElementIntoNewToOriginMap(line);
                            	break;

                            case 5 : 
                            	addElementIntoN2NMap(line);
                            	break;

                            case 6 : 
                            	addElementIntoEdgeSet(line);
                            	break;

                            case 7 : 
                            	addElementIntoEdgeLabel(line);
                            	break;

                            default : throw new IllegalArgumentException("Unexpected value: " + step);
                        }

                    }
                    catch (Exception e){
                        System.out.println("Error happens at " + line);
                    }
                }
            }
            supplementEdgeLabel();
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void initVariablesFromSubClassFile(String subclassFileNameString){
        try {
            // handle the file such as ifcElement-ifcColourRgb
            String line;
            File filename2 = new File(subclassFileNameString);
            InputStreamReader reader2 = new InputStreamReader(
                    new FileInputStream(filename2));
            BufferedReader br2 = new BufferedReader(reader2);
            line = "";
            while (line != null) {
                line = br2.readLine();
                if(line != null) {
                    if(line.equals("") || line.equals("\n") ) {
                        continue;
                    }

                    // System.out.println(step + " *** " + line);
                    try {
                        addElementIntoSubclassMap(line);
                    }
                    catch (Exception e){
                        System.out.println("Error happens at " + line);
                    }
                }
            }
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void initVariablesFromInverseFile(String inverseFileNameString){
        try {
            // handle the file such as ifcElement-ifcColourRgb
            String line;
            File filename2 = new File(inverseFileNameString);
            InputStreamReader reader2 = new InputStreamReader(
                    new FileInputStream(filename2));
            BufferedReader br2 = new BufferedReader(reader2);
            line = "";
            while (line != null) {
                line = br2.readLine();
                if(line != null) {
                    if(line.equals("") || line.equals("\n") ) {
                        continue;
                    }
                    // System.out.println(step + " *** " + line);
                    try {
                        addElementIntoInverseMap(line);
                    }
                    catch (Exception e){
                        System.out.println("Error happens at " + line);
                    }
                }
            }
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    /* add elements into necessary variables for generating SPARQL */
    // vListCase:(1:topologicalSortedVerticesList, 2:startVerticesList, 3:endVerticesList)
    private void initVerticesList(String vertices, int vListCase) {
        if (! vertices.contains(",")) return;
        int verticesNum;
        for (String vString: vertices.split(",")){
            try {
                if(vString.equals("")) continue;
                verticesNum = Integer.parseInt(vString);
                switch (vListCase) {
                    case 1 : 
                    	topologicalSortedVerticesList.add(verticesNum);
                    	break;
                    case 2 : 
                    	startVerticesList.add(verticesNum);
                    	break;
                    case 3 : 
                    	endVerticesList.add(verticesNum);
                    	break;
                    default : 
                    	throw new IllegalArgumentException("Unexpected value: " + vListCase);
                }

            }
            catch (Exception e){
                System.out.println("Error when parsing topological" +
                        " sorted vertices" + "The error info is: " + e.getMessage());
            }
        }
    }

    private void addElementIntoNewToOriginMap(String newToOriginString) {
        if (! newToOriginString.contains(":")) return;
        try {
            newToOriginString = newToOriginString.replaceAll("\\[", "")
                    .replaceAll("]", "").replaceAll(" ", "");

            String [] newAndOriginStrings = newToOriginString.split(":");
            int newVerticesNum = Integer.parseInt(newAndOriginStrings[0]);
            int originVerticesNum;
            ArrayList<Integer> originVerticesNumList = new ArrayList<>();
            for (String originVerticesString: newAndOriginStrings[1].split(",")){
                originVerticesNum = Integer.parseInt(originVerticesString);
                originVerticesNumList.add(originVerticesNum);
            }
            newToOriginMap.put(newVerticesNum, originVerticesNumList);
        }
        catch (Exception e){
            System.out.println("Error when adding element into new to origin map. "	+
                    "The error info is" + newToOriginString);
        }
    }

    // add elements into number2name map and name2num map
    private void addElementIntoN2NMap(String numToNameString) {
        if (! numToNameString.contains(":")) return;
        String [] numAndNameString = numToNameString.split(":", 2);
        try {
            int verticesNum = Integer.parseInt(numAndNameString[0]);
            VerticesNumToNameMap.put(verticesNum, numAndNameString[1]);
            VerticesNameToNumMap.put(numAndNameString[1], verticesNum);
        }
        catch (Exception e){
            System.out.println("Error when adding element into N TO N map."	+ "The error info is" + e.getMessage());
        }
    }

    private void addElementIntoEdgeSet(String edgeString) {

        if (! edgeString.contains(",")) return;

        String [] startAndEndString = edgeString.split(",");
        try {
            ArrayList<Integer> tempArrayList = new ArrayList<>();

            int startInt = Integer.parseInt(startAndEndString[0]);
            int endInt = Integer.parseInt(startAndEndString[1]);

            if(edgeSetMap.containsKey(startInt)) {
                tempArrayList = edgeSetMap.get(startInt);
            }
            tempArrayList.add(endInt);
            edgeSetMap.put(startInt, tempArrayList);
        }
        catch (Exception e){
            System.out.println("Error when adding element into edge set." + "The error info is: " + e.getMessage());
        }
    }

    private void addElementIntoEdgeLabel(String edgeLabelString) {

        if (! edgeLabelString.contains(",")) return;
        edgeLabelString = edgeLabelString.replaceAll("ifc:", "");
        String [] startAndEndAndLabelString = edgeLabelString.split(",");
        try {
            int startInt = Integer.parseInt(startAndEndAndLabelString[0]);
            int endInt = Integer.parseInt(startAndEndAndLabelString[1]);
            String labelString = startAndEndAndLabelString[2];

            HashMap<Integer, String> tempHashMap = new HashMap<>();
            if(edgeLabelMap.containsKey(startInt)) {
                tempHashMap = edgeLabelMap.get(startInt);
            }
            tempHashMap.put(endInt, labelString);
            edgeLabelMap.put(startInt, tempHashMap);

        }
        catch (Exception e){
            System.out.println("Error when adding element into edge label." + "The error info is" + e.getMessage());
        }
    }

    private void supplementEdgeLabel(){
        int tempStart, tempEnd;
        for(Integer start : edgeSetMap.keySet()){
            for(Integer end : edgeSetMap.get(start)){

                if(!newToOriginMap.containsKey(start)) tempStart=start;
                else {
                    tempStart=newToOriginMap.get(start).get(newToOriginMap.get(start).size()-1);
                }
                if(!newToOriginMap.containsKey(end)) tempEnd=end;
                else {
                    tempEnd=newToOriginMap.get(end).get(0);
                }

                if(edgeLabelMap.containsKey(start)){
                    if(!edgeLabelMap.get(start).containsKey(end)) {
                        edgeLabelMap.get(start).put(end, edgeLabelMap.get(tempStart).get(tempEnd));
                    }
                }
                else{
                    HashMap<Integer, String> tempMap = new HashMap<>();
                    tempMap.put(end, edgeLabelMap.get(tempStart).get(tempEnd));
                    edgeLabelMap.put(start, tempMap);
                }
            }
        }
    }

    private void addElementIntoSubclassMap(String subclass) {
        if (! subclass.contains("-")) return;
        //subclass=subclass.replaceAll("ifc:", "");
        try {

            String [] fatherAndSons = subclass.split("-");
            String father = fatherAndSons[0];

            ArrayList<String> SonsList = new ArrayList<>();
            Collections.addAll(SonsList, fatherAndSons[1].split(","));
            subVerticesMap.put(father, SonsList);
        }
        catch (Exception e){
            System.out.println("Error when adding element into new to origin map. "	+
                    "The error info is" + subVerticesMap);
        }

    }

    private void addElementIntoInverseMap(String inversePairString){
        inversePairString = inversePairString.replace(" ", "")
                .replace("'owl:inverseOf',", "")
                .replace("[", "").replace("]", "")
                .replace("'", "").replace("(","");
        List<String> inversePairList = Arrays.asList(inversePairString.split("\\),"));
        for(String predAndItsReverseString:inversePairList){
            String[] predAndInverseList = predAndItsReverseString.split(",");
            if(predAndInverseList.length==2)
                inverseVerticesMap.put(predAndInverseList[0], predAndInverseList[1]);
        }


    }
}
