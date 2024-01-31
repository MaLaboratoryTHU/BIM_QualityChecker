package org.bimserver.ifcvalidator.extractor;

import java.util.*;

import org.apache.jena.base.Sys;
import org.apache.jena.rdf.model.*;
import org.apache.jena.riot.*;
import org.apache.jena.query.*;


public class  InfoExtractorUtil{

    private final BasicGraphPara graphPara;
    private final Model instanceModel;
    private final String elementInstanceString;
    private final  String infoEntityString;
    private  final HashMap<String, String> prefixStringMap = new HashMap<String, String>(){{
        put("http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#", "ifc:");
        put("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
        put("https://w3id.org/list#", "list:");
        put("https://w3id.org/express#", "expr:");
        put("http://linkedbuildingdata.net/ifc/resources20170627_104702/", "inst:");
    }
    };

    public InfoExtractorUtil(String rdfPathName, String elementSchemaString,
                             String elementInstanceString, String infoEntityString){
        this.instanceModel = RDFDataMgr.loadModel(rdfPathName) ;
        this.graphPara = new BasicGraphPara(elementSchemaString, infoEntityString);

        this.elementInstanceString = elementInstanceString;
        this.infoEntityString = infoEntityString;

    }
    public InfoExtractorUtil(Model instanceModel, String elementSchemaString,
            String elementInstanceString, String infoEntityString){
		this.instanceModel = instanceModel ;
		this.graphPara = new BasicGraphPara(elementSchemaString, infoEntityString);
		
		this.elementInstanceString = elementInstanceString;
		this.infoEntityString = infoEntityString;
		
	}

    /* Dynamic Construct SPARQL and carry out query */
    // Element in evQueue is an edge-vertices pair (EV pair) representing by String connected with "+"
    // edge is in instance layer, while vertices in schema layer, e.g
    // "IfcWallStandardCase_6027+representation_IfcProduct"
    private List<String> dynamicQuery(Model instanceModel, String elementInstanceString, String infoEntityString) {
        List<String> queryResultList = new ArrayList<>();

        PriorityQueue<String> evQueue = initEVQueue(elementInstanceString);
        String completeInfoEntity = "ifc:" + infoEntityString;

        StringBuilder tempInfo = new StringBuilder();

        int effective_count = 1;

        while(! evQueue.isEmpty()) {
            tempInfo.delete(0, tempInfo.length());
            tempInfo.append("*****************\n");
            tempInfo.append("size of ev queue is ").append(evQueue.size()).append("\n");

            String evString = evQueue.poll();
            List<String> subAndPredStrings = Arrays.asList(evString.split("\\+"));
            tempInfo.append("polled sub and pred").append(subAndPredStrings).append("\n");

            String subString = subAndPredStrings.get(0);
            List<String> predStringList = subAndPredStrings.subList(1, subAndPredStrings.size());

            //get next ev pairs candidates
            ArrayList<String> nextEVPairStringList=getOutEdgeAndVerticesOfPred
                    (predStringList.get(predStringList.size()-1));
            tempInfo.append("next ev candidates").append(nextEVPairStringList).append("\n");

            //generate sparql query
            String currentQueryString = generateSparql(subString, predStringList);
            String currentQueryStringToPrint = generateSimpleSparql(subString, predStringList);

            // need to consider several query results
            List<String> queryResultStringList = carryOutQuery(instanceModel, currentQueryString); //new ArrayList<>();
            if(!queryResultStringList.isEmpty()) {
                tempInfo.append(queryResultStringList).append("\n");
                if(!queryResultStringList.get(0).contains("Propert")){
                    if (effective_count>0)  {

//                        System.out.println("-------------------iteration " + effective_count + "-------------------");
//                        System.out.println("predicate in P-Path " + predStringList.get(0));
//                        System.out.println("Generated SPAQRL query: \n " + currentQueryStringToPrint);
//                        System.out.println("query result:" + queryResultStringList);

                    }
                    effective_count++;
                }

            }
            else tempInfo.append("query result is null\n");

            for(String qr: queryResultStringList){
                // if the query result is target entity, add it into result list
                String qrComparedWithLabelAndInfo = qr;
                String qrGeneSparqlAndAsResult =qr;

                for(String prefix: prefixStringMap.keySet()){
                    if(qr.contains(prefix)) {
                        if(prefixStringMap.get(prefix).equals("inst:")) {
                            qrComparedWithLabelAndInfo = qr.replaceAll(prefix, "ifc:");
                        }
                        else {
                            qrComparedWithLabelAndInfo = qr.replaceAll(prefix, prefixStringMap.get(prefix));
                        }
                        qrGeneSparqlAndAsResult = qr.replaceAll(prefix, prefixStringMap.get(prefix));
                        break;
                    }
                }
                qrComparedWithLabelAndInfo = qrComparedWithLabelAndInfo.split("_")[0];
                //System.out.println(qrComparedWithLabelAndInfo);
                //System.out.println(qrGeneSparqlAndAsResult);

                // handle the case the info entity is found->add it into queryResultList
                if(qrComparedWithLabelAndInfo.equals(completeInfoEntity)) {
                    if(!queryResultList.contains(qrGeneSparqlAndAsResult))
                        queryResultList.add(qrGeneSparqlAndAsResult);
                        continue;
                }
                if(graphPara.subVerticesMap.containsKey(completeInfoEntity)) {
                    if(graphPara.subVerticesMap.get(completeInfoEntity).contains(qrComparedWithLabelAndInfo)){
                        if(!queryResultList.contains(qrGeneSparqlAndAsResult))
                            queryResultList.add(qrGeneSparqlAndAsResult);
                            continue;
                    }
                }

                // handle the edge and vertices pair in different cases
                for(String nextEVPairString : nextEVPairStringList){
                    String[] subPredicatesPair = nextEVPairString.split("\\+", 2);
                    // if the edge Label is superclass of query result, enqueue the edge-vertices pair into queue
                    if(qrComparedWithLabelAndInfo.equals(subPredicatesPair[0])) {
                        evQueue.add(qrGeneSparqlAndAsResult + "+" + subPredicatesPair[1]);
                    }
                    if(graphPara.subVerticesMap.containsKey(subPredicatesPair[0])) {
                        if(graphPara.subVerticesMap.get(subPredicatesPair[0]).contains(qrComparedWithLabelAndInfo)){
                            tempInfo.append(qrComparedWithLabelAndInfo).append(subPredicatesPair[0]);
                            evQueue.add(qrGeneSparqlAndAsResult + "+" + subPredicatesPair[1]);
                        }
                    }
                    // else do nothing
                }
            }

            tempInfo.append("*****************\n");
            //System.out.println(tempInfo);
        }
        return queryResultList;
    }

    /* Construct SPARQL query  */
    /*subString is the entity in instance schema, such as inst:IfcWallStandard*/
    private String generatePartSparql(String predString, int i) {
        StringBuilder partSparql = new StringBuilder();
        //handle the case of "ifc:relatedObjects_IfcRelDefines", caused by the difference between ifc 2x3 and ifc 4
        if(predString.startsWith("ifc:relatedObjects_IfcRelDefines"))
            predString = "ifc:relatedObjects_IfcRelDefines";
        // handle the case of "List:hasContents"
        if(predString.startsWith("list:hasContents"))  predString = predString.split("_")[0];
        // handle the case of "relatedObjects"
        /*
        if (predString.startsWith("ifc:related"))
           partSparql.append("{?variable_").append(i+1).append(" ").append(predString)
                    .append(" ").append("?variable_").append(i).append("}");
        else
        */

        if(graphPara.inverseVerticesMap.containsKey(predString)){
            partSparql.append("{");
            partSparql.append("{?variable_").append(i).append(" ")
                    .append(graphPara.inverseVerticesMap.get(predString))
                    .append(" ").append("?variable_").append(i + 1).append("} UNION ");
            partSparql.append("{?variable_").append(i+1).append(" ")
                    .append(graphPara.inverseVerticesMap.get(predString))
                    .append(" ").append("?variable_").append(i).append("} UNION ");
            partSparql.append("{?variable_").append(i+1).append(" ").append(predString)
                    .append(" ").append("?variable_").append(i).append("} UNION ");
        }
        else  if (predString.startsWith("ifc:related")){
            partSparql.append("{?variable_").append(i+1).append(" ").append(predString)
                    .append(" ").append("?variable_").append(i).append("} UNION ");
        }

        partSparql.append("{?variable_").append(i).append(" ").append(predString)
                .append(" ").append("?variable_").append(i + 1).append("}");

        if(graphPara.inverseVerticesMap.containsKey(predString)) partSparql.append("}");
        partSparql.append("\n");
        return partSparql.toString();
    }

    private String generatePartSparql(String subString, String predString) {
        StringBuilder partFirstSparql = new StringBuilder();
        //handle the case of "ifc:relatedObjects_IfcRelDefines", caused by the difference between ifc 2x3 and ifc 4
        if(predString.startsWith("ifc:relatedObjects_IfcRelDefines"))
            predString = "ifc:relatedObjects_IfcRelDefines";
        // handle the case of "List:hasContents"
        if(predString.startsWith("list:hasContents"))  predString = predString.split("_")[0];
        // handle the case of "ifc:relatedObjects"

        /*
        if (predString.startsWith("ifc:related"))
            partFirstSparql.append("{?variable_0 ").append(predString)
                    .append(" ").append(subString).append(" }");
        else
        */

        if(graphPara.inverseVerticesMap.containsKey(predString)){
            partFirstSparql.append("{");
            partFirstSparql.append("{").append(subString).append(" ")
                    .append(graphPara.inverseVerticesMap.get(predString))
                    .append(" ").append("?variable_0} UNION ");
            partFirstSparql.append("{?variable_0").append(" ")
                    .append(graphPara.inverseVerticesMap.get(predString))
                    .append(" ").append(subString).append(" } UNION ");
            partFirstSparql.append("{?variable_0 ").append(predString)
                    .append(" ").append(subString).append(" } UNION ");
        }
        else  if (predString.startsWith("ifc:related")){
            partFirstSparql.append("{?variable_0 ").append(predString)
                    .append(" ").append(subString).append(" } UNION ");
        }

        partFirstSparql.append("{").append(subString).append(" ").append(predString)
                .append(" ").append("?variable_0}");
        if(graphPara.inverseVerticesMap.containsKey(predString)) partFirstSparql.append("}");
        partFirstSparql.append("\n");
        return partFirstSparql.toString();
    }

    public String generateSparql(String subString, List<String> predStringList) {
        // prefix of namespaces
        String ifcOWLPrefix = "PREFIX ifc:<http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#>\n";
        String rdfPrefix = "PREFIX rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n";
        String listPrefix = "PREFIX list:<https://w3id.org/list#>\n";
        String expressPrefix = "PREFIX express: <https://w3id.org/express#>\n";
        String instPrefix = "PREFIX inst: <http://linkedbuildingdata.net/ifc/resources20170627_104702/>\n";
        StringBuilder queryString = new StringBuilder();
        queryString.append(ifcOWLPrefix).append(rdfPrefix).append(listPrefix).append(expressPrefix).append(instPrefix);
        int predLength = predStringList.size();

        queryString.append("SELECT ?variable_").append(predLength-1).append(" \nWHERE { \n");
        queryString.append(generatePartSparql(subString, predStringList.get(0)));

        if(predLength>1){
            for(int variableNum=1; variableNum<predLength; variableNum++){
                queryString.append(generatePartSparql(predStringList.get(variableNum), variableNum-1));
            }
        }
        queryString.append("}");

        return queryString.toString();
    }

    public String generateSimpleSparql(String subString, List<String> predStringList) {
        // prefix of namespaces
        StringBuilder queryString = new StringBuilder();
        int predLength = predStringList.size();

        queryString.append("SELECT ?variable_").append(predLength-1).append(" \nWHERE { \n");
        queryString.append(generatePartSparql(subString, predStringList.get(0)));

        if(predLength>1){
            for(int variableNum=1; variableNum<predLength; variableNum++){
                queryString.append(generatePartSparql(predStringList.get(variableNum), variableNum-1));
            }
        }
        queryString.append("}");

        return queryString.toString();
    }

    /* Carry out SPARQL query */
    private List<String> carryOutQuery(Model instanceModel, String queryString) {
        List<String> queryResultStringList = new ArrayList<>();
        //System.out.println(queryString);
        Query query = QueryFactory.create(queryString);

        QueryExecution qe = QueryExecutionFactory.create(query, instanceModel);
        ResultSet results = qe.execSelect();
        //ResultSetFormatter.out(System.out, results, query);

        while (results.hasNext()) {
            QuerySolution qs = results.next();
            String firstVarName = results.getResultVars().get(0);
            RDFNode rdfNode = qs.get(firstVarName);
            if (rdfNode != null) {
                //System.out.println(rdfNode.toString());;
                queryResultStringList.add(rdfNode.toString());
            }
        }
        return queryResultStringList;
    }

    // Get out edge(classes) and pointed vertices (object property)
    private ArrayList<String> getOutEdgeAndVerticesOfPred(String predString) {
        ArrayList<String> evStringList =  new ArrayList<>();
        int currVertices = graphPara.VerticesNameToNumMap.get(predString);

        // reverse edge label map to find out edges(string) and vertices(integer)
        // find the name of vertices of next vertices
        HashMap<Integer, String> tempMap;
        StringBuilder evString = new StringBuilder();

        if (graphPara.edgeLabelMap.containsKey(currVertices)){
            tempMap = graphPara.edgeLabelMap.get(currVertices);            
            for(Map.Entry<Integer, String> entry: tempMap.entrySet()){
                evString.delete(0, evString.length());
                evString.append("ifc:").append(entry.getValue());
                // if the next vertices is old vertices
                if(graphPara.VerticesNumToNameMap.containsKey(entry.getKey())){
                    evString.append("+").append(graphPara.VerticesNumToNameMap.get(entry.getKey()));
                }
                // if the next vertices is new vertices
                // get the origin vertices of the new vertices
                else{
                    ArrayList<Integer> nextPredStringList = graphPara.newToOriginMap.get(entry.getKey());
                    for(Integer predNum: nextPredStringList){
                        evString.append("+").append(graphPara.VerticesNumToNameMap.get(predNum));
                    }
                }
                evStringList.add(evString.toString());
            }
        }
        return evStringList;
    }

    // Generate initial edge and vertices queue
    // e.g [("IfcWallStandardCase_6027+representation_IfcProduct",
    // "IfcWallStandardCase_6027+relatedObjects_IfcRelDefinesByProperties")]
    private PriorityQueue<String> initEVQueue(String elementInstanceString){
        PriorityQueue<String> initEVQueue = new PriorityQueue<>();
        StringBuilder startEVString = new StringBuilder();
        for(Integer startVertices:graphPara.startVerticesList){
            startEVString.delete(0, startEVString.length());
            startEVString.append(elementInstanceString);
            if(!graphPara.newToOriginMap.containsKey(startVertices)){
                startEVString.append("+").append(graphPara.VerticesNumToNameMap.get(startVertices));
            }
            else {
                ArrayList<Integer> oldPredStringList = graphPara.newToOriginMap.get(startVertices);
                for(Integer predNum: oldPredStringList){
                    startEVString.append("+").append(graphPara.VerticesNumToNameMap.get(predNum));
                }
            }
            initEVQueue.add(startEVString.toString());
        }
        return initEVQueue;
    }

    public List<String> queryInfoForElement() {

        return dynamicQuery(this.instanceModel,this.elementInstanceString, this.infoEntityString);
    }


}
