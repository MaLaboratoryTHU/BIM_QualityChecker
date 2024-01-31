package org.bimserver.ifcvalidator.reasoner;

import org.bimserver.ifcvalidator.extractor.*;

import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import com.clarkparsia.pellet.rules.builtins.BuiltInRegistry;
import com.clarkparsia.pellet.rules.builtins.GeneralFunction;
import com.clarkparsia.pellet.rules.builtins.GeneralFunctionBuiltIn;
import com.google.common.collect.Multimap;
import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;

import de.derivo.sparqldlapi.Query;
import de.derivo.sparqldlapi.QueryArgument;
import de.derivo.sparqldlapi.QueryAtomGroup;
import de.derivo.sparqldlapi.QueryBinding;
import de.derivo.sparqldlapi.QueryEngine;
import de.derivo.sparqldlapi.QueryResult;
import de.derivo.sparqldlapi.Var;
import de.derivo.sparqldlapi.exceptions.QueryEngineException;
import de.derivo.sparqldlapi.exceptions.QueryParserException;

import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.checker.javari.qual.Mutable;
import org.checkerframework.checker.nullness.qual.KeyForBottom;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.dlsyntax.renderer.DLSyntaxObjectRenderer;
import org.semanticweb.owlapi.formats.PrefixDocumentFormat;
import org.semanticweb.owlapi.io.OWLObjectRenderer;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.search.EntitySearcher;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.swrlapi.core.SWRLRuleEngine;
import org.swrlapi.factory.SWRLAPIFactory;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.ReasonerFactory;

import org.apache.jena.rdf.model.*;
import org.apache.jena.riot.*;
import org.apache.jena.shared.JenaException;
import org.apache.jena.sys.JenaSystem;
import org.apache.jena.util.FileManager;
import org.apache.xmlbeans.impl.store.Path;
import org.apache.jena.ontology.OntModel;
import org.apache.jena.ontology.OntModelSpec;
import org.apache.jena.query.*;

import com.fasterxml.jackson.core.JsonGenerationException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;


@SuppressWarnings("deprecation")
public class BimQualityCheckOntology {
	
	// ontology settings
	private final String ONTO_LOC = System.getProperty("user.dir")+ "\\docs\\owl\\bimqualitychecker.owl";
	private final String ONTO_URL = "http://www.semanticweb.org/bimqualitychecker/v1.0";	
	
	//ifcowl prefix
	private final String IFCOWL_PREFIX = "PREFIX ifcowl:<http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#>";
	private final String RDF_PREFIX = "PREFIX rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#>";
	private final String LIST_PREFIX = "PREFIX list:<https://w3id.org/list#>";
	
	//mapping settings
	//{Wall=[IfcWall, IfcWallStandardCase], Material=[IfcMaterial]}
	private HashMap<String, List<String>> bimQualityCheckToIfcowl;
	//{IfcWall=[Wall], IfcMaterial=[Material], IfcWallStandardCase=[Wall]}
	private HashMap<String, List<String>> ifcowlTobimQualityCheck;	
	// {RelatingMaterial:IfcMaterial}
	private HashMap<String, String> featureObjectPropertyToIfcEntity; 
	//{ConnectTo=[IfcRelConnectsPort+IfcRelConnectsPort, IfcRelConnects]}
	private HashMap<String, List<String>> relationshipObjectPropertyToPredicateList;
	private HashMap<String, List<String>> modelUnitToRelatingFeatures;
	private HashMap<String, List<String>> modelUnitToRelationship;
	
	// members of ontology
	private OWLOntologyManager bimQulityCheckManager;
	private OWLOntology bimQulityCheckOntology;
	private OWLDataFactory bimQulityCheckDatafactory;
	private DefaultPrefixManager bimQulityCheckPrefixManager= new DefaultPrefixManager();;
	private OWLReasonerFactory reasonerFactory = PelletReasonerFactory.getInstance();//(OWLReasonerFactory)new ReasonerFactory();
	
	private OWLReasoner reasoner;
	private QueryEngine engine;
    
    public BimQualityCheckOntology(){
    	
    }
	
	@SuppressWarnings("deprecation")
	public BimQualityCheckOntology(String bimModelLoc) throws OWLOntologyCreationException{		 
		
		//reasonerFactory = (OWLReasonerFactory)PelletReasonerFactory.getInstance();
		
		bimQulityCheckManager = OWLManager.createOWLOntologyManager();
		//initialize the members of ontology
		initBimQulityCheckOntology();
		//initialize the mapping settings
		System.out.println("start initialize map setting");
		bimQualityCheckToIfcowl = initListMapFromJsonConf("bimQualityCheckToIfcowlMap.json");
		ifcowlTobimQualityCheck = initListMapFromJsonConf("ifcowlTobimQualityCheckMap.json");
		featureObjectPropertyToIfcEntity = initMapFromJsonConf("featureObjectPropertyToIfcEntityMap.json");
		relationshipObjectPropertyToPredicateList = initListMapFromJsonConf("relationshipObjectPropertyToPredicateListMap.json");
		modelUnitToRelatingFeatures = initListMapFromJsonConf("modelUnitToRelatingFeaturesMap.json");
		modelUnitToRelationship = initListMapFromJsonConf("modelUnitToRelationshipMap.json"
				+ "");
		
		//create a Jena model for .ttl file
		System.out.println("start load ontology");
		System.out.println(bimModelLoc);
		
		//Model instanceModel = RDFDataMgr.loadModel(bimModelLoc);
		
		Model instanceModel = ModelFactory.createDefaultModel() ;
		
		 try {
			 File f = new File(bimModelLoc);
			 instanceModel.read(new FileInputStream(f), null,"TTL");
		    } catch (FileNotFoundException e) { 
		        e.printStackTrace();
		    }
		 System.out.println("loaded ontology");
		//Model instanceModel = RDFDataMgr.loadModel("file:///"+bimModelLoc) ;
		
		 org.apache.jena.query.ARQ.init();
		//classes and properties in bim quality checking ontology
		Set<String> owlClassNamesSet = bimQualityCheckToIfcowl.keySet(); // read from bimQualityCheckToIfcowl				
		Set<String> owlFeatureObjectProperty = featureObjectPropertyToIfcEntity.keySet();
	
		// add named individuals into bim quality check ontology
		addAllNamedIndividuals(instanceModel,owlClassNamesSet);	
		System.out.println("add All Named Individuals");
		//add object Property into bim quality check ontology
		addAllObjectPropertyAxiomsForFeatures(instanceModel);		
		addAllObjectPropertyAxiomsForRelationship(instanceModel);
		
		System.out.println("add All Object Property Axioms For Features");
		//listAllObjectPropertyAssertionAxiom();
		//execute reason based on SWRL rules
		
		System.out.println("start to initialize reasoner");
		reasoner = reasonerFactory.createReasoner(bimQulityCheckOntology, new SimpleConfiguration());
		System.out.println("complete to initialize reasoner");
		reasonBasedOnSWRLRules();

//		listClassAssertionAxiom();
//		listAllObjectPropertyAssertionAxiom();
		OutputAllObjectPropertyAssertionAxiom();
//		listAllDataPropertyAssertionAxiom();
//		
//		 engine= QueryEngine.create(bimQulityCheckManager, reasoner,true); //////
//		 QueryResult result = processQuery("ComponentHasMaterial"); ////
//		 listQueryResult(result); 
		
	}
	
	private void initBimQulityCheckOntology()  throws OWLOntologyCreationException{
		
		bimQulityCheckOntology = bimQulityCheckManager.loadOntologyFromOntologyDocument(new File(ONTO_LOC));
		bimQulityCheckDatafactory = bimQulityCheckManager.getOWLDataFactory();
		
		bimQulityCheckPrefixManager.setDefaultPrefix(ONTO_URL + "#");
		bimQulityCheckPrefixManager.setPrefix("var:", "urn:swrl#");
	}
	
	@SuppressWarnings("unchecked")
	private HashMap<String, String> initMapFromJsonConf(String fileName){		
		ObjectMapper mapper = new ObjectMapper();
		HashMap<String, String> hashmap = null;		
		String fullFileName = System.getProperty("user.dir")+ "\\conf\\" + fileName;
		
		try {			
			hashmap = mapper.readValue(Files.readAllBytes(Paths.get(fullFileName)), HashMap.class);
			//System.out.println(hashmap);
        }
		catch (IOException e) {
			e.printStackTrace();
        }		
		return hashmap;
	}
	//initialize the map <String, List<String>>
	private HashMap<String, List<String>> initListMapFromJsonConf(String fileName){
		HashMap<String, List<String>> finalHashMap = new HashMap<String, List<String>>();
		HashMap<String, String> hashmap = initMapFromJsonConf(fileName);
		for(String key:hashmap.keySet()) {
			List<String> value = Arrays.asList(hashmap.get(key).split(","));
			finalHashMap.put(key, value);
		}
		//System.out.println(finalHashMap);
		return finalHashMap;
	}
	
	//DONE: List to set
	private List<String> getIndividualNamesInJenaModel(Model instanceModel, String owlClassName){	
		String instPrefix = instanceModel.getNsPrefixURI("inst");
		//System.out.println(instanceModel.getNsPrefixMap());
		List<String> individualNamesList = new ArrayList<>();
		List<String> ifcClassNames = bimQualityCheckToIfcowl.get(owlClassName);
		for(String ifcClassName:ifcClassNames) {
			String sparqlQueryForType = constructSparqlQueryFromClassName(ifcClassName);
			List<String> queryResults = carryOutQuery(instanceModel, sparqlQueryForType);
			for(String queryResult:queryResults) {
				individualNamesList.add(queryResult.replace(instPrefix, ""));
			}						
		}
		return individualNamesList;
	}
	// IfcWallStandardCase_3758 is an example of individualNameInJenaModel
	private OWLNamedIndividual addNamedIndividual(String individualNameInJenaModel) {
		//get ifc class name from the individual name
		List<String> ifcClassNameAndNumber = Arrays.asList(individualNameInJenaModel.split("_"));
		String ifcClassName;
		String individualNumber;
		if (ifcClassNameAndNumber.size()==2) {
			ifcClassName = ifcClassNameAndNumber.get(0);
			individualNumber = ifcClassNameAndNumber.get(1);
		}else {
			return null;
		}		
		String owlClassName = ifcowlTobimQualityCheck.get(ifcClassName).get(0);	
		
		//use ifcowlTobimQualityCheck to assign the class for individual
		OWLNamedIndividual owlNamedIndividual = bimQulityCheckDatafactory.getOWLNamedIndividual
				(ifcClassName.replace("Ifc","")+"_"+individualNumber, bimQulityCheckPrefixManager);
		bimQulityCheckManager.addAxiom(bimQulityCheckOntology, bimQulityCheckDatafactory.getOWLDeclarationAxiom
				(owlNamedIndividual));			
		//declare owl class for the individual
		OWLClass owlClass = bimQulityCheckDatafactory.getOWLClass(":"
				+ owlClassName,bimQulityCheckPrefixManager);
		bimQulityCheckManager.addAxiom(bimQulityCheckOntology, bimQulityCheckDatafactory.getOWLClassAssertionAxiom
				(owlClass, owlNamedIndividual));           	
		return owlNamedIndividual;
	}
	//such as{"IfcWallStandardCase_3758:corresponding_wall_individual"}	
	private HashMap<String, OWLNamedIndividual> addAllNamedIndividuals(Model instanceModel, Set<String> owlClassNamesSet ) {
		HashMap<String, OWLNamedIndividual> individualNameInJenaToNamedIndividualInBIMQC = new HashMap<String, OWLNamedIndividual>();
		for (String owlClassName:owlClassNamesSet) {
			//System.out.println(owlClassName);			
			List<String> individualNameListInJenaModel =  getIndividualNamesInJenaModel(instanceModel, owlClassName);
			//System.out.println(individualNameListInJenaModel);
			for (String individualName:individualNameListInJenaModel) {
				individualNameInJenaToNamedIndividualInBIMQC.put(individualName, 
				addNamedIndividual(individualName));
			}			
		}	
		//System.out.println(individualNameInJenaToNamedIndividualInBIMQC.size());
		return individualNameInJenaToNamedIndividualInBIMQC;
	}	
	
	//@parameter: individualNameInJenaModel-IfcWallStandardCase_3758
	//@parameter: featureObjectPropertyName-RelatingMaterial
	private void addObjectPropertyAxiomsForFeatures(Model instanceModel,String individualNameInJenaModel, String featureObjectPropertyName) {		
		InfoExtractorUtil infoExtractor=new InfoExtractorUtil(instanceModel,"IfcElement",
				"inst:"+individualNameInJenaModel, featureObjectPropertyToIfcEntity.get(featureObjectPropertyName));
		//System.out.println(individualNameInJenaModel);
		//System.out.println(featureObjectPropertyToIfcEntity.get(featureObjectPropertyName));
		List<String> relatingFeatureValuesList = infoExtractor.queryInfoForElement();    	
    	//System.out.println(relatingFeatureValuesList);
    	
    	List<String> ifcClassNameAndNumber = Arrays.asList(individualNameInJenaModel.split("_"));
		String ifcClassName;
		String individualNumber;
		if (ifcClassNameAndNumber.size()==2) {
			ifcClassName = ifcClassNameAndNumber.get(0);
			individualNumber = ifcClassNameAndNumber.get(1);
		}else {
			return;
		}		
		
		if(!ifcowlTobimQualityCheck.containsKey(ifcClassName)) {        			
			return;        			
		}
		
		String owlIndividualName = ifcClassName.replace("Ifc","")+"_"+individualNumber;	
    	//System.out.println(owlIndividualName);
    	
    	OWLNamedIndividual owlModelUnitIndividual = bimQulityCheckDatafactory.getOWLNamedIndividual
				(owlIndividualName, bimQulityCheckPrefixManager);
    	OWLObjectProperty RelatingFeatureObjectProperty = bimQulityCheckDatafactory.getOWLObjectProperty
    			(":"+featureObjectPropertyName, bimQulityCheckPrefixManager);
    	//System.out.println(RelatingFeatureObjectProperty.toString());
    	
    	String instPrefix = instanceModel.getNsPrefixURI("inst");
    	
    	for(String relatingFeatureValue:relatingFeatureValuesList) {
    		//System.out.println(relatingFeatureValue);
    		List<String> ifcFeatureValueTypeAndNumber = Arrays.asList(relatingFeatureValue.replace("inst:", "").split("_"));
    		String ifcFeatureValueType;
    		String ifcFeatureValueNumber;
    		if (ifcFeatureValueTypeAndNumber.size()==2) {
    			ifcFeatureValueType = ifcFeatureValueTypeAndNumber.get(0);
    			ifcFeatureValueNumber = ifcFeatureValueTypeAndNumber.get(1);
    		}else {
    			return;
    		}		
    		String owlFeatureValueTypeAndNumber = ifcFeatureValueType.replace("Ifc", "")+"_"+ifcFeatureValueNumber;	
        	//System.out.println(owlFeatureValueTypeAndNumber);
    		
    		OWLNamedIndividual owlFeatureValueIndividual = bimQulityCheckDatafactory.getOWLNamedIndividual
    				(owlFeatureValueTypeAndNumber, bimQulityCheckPrefixManager);
    		bimQulityCheckManager.addAxiom(bimQulityCheckOntology, 
    				bimQulityCheckDatafactory.getOWLObjectPropertyAssertionAxiom(RelatingFeatureObjectProperty, 
    						owlModelUnitIndividual, owlFeatureValueIndividual));
    	}
	}
	//@parameter: owlClassName-Wall
	//@parameter: featureObjectPropertyName-RelatingMaterial
	private void addTypeObjectPropertyAxiomsForFeatures(Model instanceModel,String owlClassName, String featureObjectPropertyName) {
		List<String> individualNameListInJenaModel =  getIndividualNamesInJenaModel(instanceModel, owlClassName);		
		for (String individualName:individualNameListInJenaModel) {
			addObjectPropertyAxiomsForFeatures(instanceModel, individualName, featureObjectPropertyName);
		}	
	}		
	private void addAllObjectPropertyAxiomsForFeatures(Model instanceModel) {
		for(String owlClassName: modelUnitToRelatingFeatures.keySet()) {
			List<String> featureObjectPropertyNameList = modelUnitToRelatingFeatures.get(owlClassName);
			for(String featureObjectPropertyName:featureObjectPropertyNameList) {
				addTypeObjectPropertyAxiomsForFeatures(instanceModel,owlClassName, featureObjectPropertyName);
			}
		}
		
	}	
	private void addObjectPropertyAxiomsForRelationship(Model instanceModel,String individualNameInJenaModel, String featureObjectPropertyName) {		
		List<String> ifcClassNameAndNumber = Arrays.asList(individualNameInJenaModel.split("_"));
		String ifcClassName;
		String individualNumber;
		if (ifcClassNameAndNumber.size()==2) {
			ifcClassName = ifcClassNameAndNumber.get(0);
			individualNumber = ifcClassNameAndNumber.get(1);
		}else {
			return;
		}		
		String owlIndividualName = ifcClassName.replace("Ifc","")+"_"+individualNumber;	
    	//System.out.println(owlIndividualName);
    			
    	OWLNamedIndividual owlModelUnitIndividual = bimQulityCheckDatafactory.getOWLNamedIndividual
				(owlIndividualName, bimQulityCheckPrefixManager);
    	OWLObjectProperty RelatingFeatureObjectProperty = bimQulityCheckDatafactory.getOWLObjectProperty
    			(":"+featureObjectPropertyName, bimQulityCheckPrefixManager);
    	//System.out.println(RelatingFeatureObjectProperty.toString());
    	
    	String instPrefix = instanceModel.getNsPrefixURI("inst");
    	List<String> predLists= relationshipObjectPropertyToPredicateList.get(featureObjectPropertyName);
    	
    	for(String predsString:predLists) {
    		
    		List<String> predList = Arrays.asList(predsString.split("&"));
    		String sparqlQueryString = constructSparqlQueryFromPredicateList(instPrefix,
    				individualNameInJenaModel,predList);
        	
    		//System.out.println(sparqlQueryString);
    		
        	List<String> resultList = carryOutQuery(instanceModel, sparqlQueryString);
        	
        	for(String resultString:resultList) {
        		//System.out.println(resultString);
        		
        		List<String> resultTypeAndNumber = Arrays.asList(resultString.replace(instPrefix, "").split("_"));
        		String resultType;
        		String resultNumber;
        		if (resultTypeAndNumber.size()==2) {
        			resultType = resultTypeAndNumber.get(0);
        			resultNumber = resultTypeAndNumber.get(1);
        		}else {
        			return;
        		}
        		if(!ifcowlTobimQualityCheck.containsKey(resultType)) {
        			System.out.print(resultType);
        			return;        			
        		}
        		String owlFeatureValueTypeAndNumber = resultType.replace("Ifc", "")+"_"+resultNumber;	
            	System.out.println(owlFeatureValueTypeAndNumber);
        		
        		OWLNamedIndividual owlResultIndividual = bimQulityCheckDatafactory.getOWLNamedIndividual
        				(owlFeatureValueTypeAndNumber, bimQulityCheckPrefixManager);
        		System.out.println(owlResultIndividual.getIRI().toString());
        		bimQulityCheckManager.addAxiom(bimQulityCheckOntology, 
        				bimQulityCheckDatafactory.getOWLObjectPropertyAssertionAxiom(RelatingFeatureObjectProperty, 
        						owlModelUnitIndividual, owlResultIndividual));
        	}
    	}
    	
    	
	}
	//@parameter: owlClassName-Wall
	//@parameter: featureObjectPropertyName-RelatingMaterial
	private void addTypeObjectPropertyAxiomsForRelationship(Model instanceModel,String owlClassName, String featureObjectPropertyName) {
		List<String> individualNameListInJenaModel =  getIndividualNamesInJenaModel(instanceModel, owlClassName);		
		for (String individualName:individualNameListInJenaModel) {
			addObjectPropertyAxiomsForRelationship(instanceModel, individualName, featureObjectPropertyName);
		}	
	}		
	private void addAllObjectPropertyAxiomsForRelationship(Model instanceModel) {
		for(String owlClassName: modelUnitToRelationship.keySet()) {
			List<String> featureObjectPropertyNameList = modelUnitToRelationship.get(owlClassName);
			for(String featureObjectPropertyName:featureObjectPropertyNameList) {
				addTypeObjectPropertyAxiomsForRelationship(instanceModel,owlClassName, featureObjectPropertyName);
			}
		}
		
	}	
	
	
	private void reasonBasedOnSWRLRules() {
		listSWRLRules();
		//create reasoner

//      // validate consistency for ontology
//      if (reasoner.isConsistent()) {
//          // an ontology can be consistent, but have unsatisfiable classes.
//          if (reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom().size() > 0) {
//          	// means: an ontology is consistent but unsatisfiable!
//              System.out.println("The ontology FAILED satisfiability test with Pellet reasoner. \n Unsatisfiable classes detected: "
//                      + reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom().size());                
//          } else {
//              System.out.println("The ontology PASSED the consistency test.");
//          }
//      } else {
//          System.out.println("The ontology FAILED the consistency test, please review the Axioms or debug using Protege");
//      }
        //carry out reasoning based on SWRL rules
      SWRLRuleEngine ruleEngine;
      ruleEngine = SWRLAPIFactory.createSWRLRuleEngine(bimQulityCheckOntology);
      System.out.println("Loaded rule engine");        
      ruleEngine.infer();
		System.out.println("start inferring");
		InferredOntologyGenerator inference = new  InferredOntologyGenerator(reasoner);
		// Infer
		inference.fillOntology(bimQulityCheckDatafactory, bimQulityCheckOntology);
		
		System.out.println("complete inferring");
        listAllDataPropertyAssertionAxiom();
    }
	
	//Here are methods for SPARQL query
	//@parameter-className:IfcWallStandardCase
	//SPARQL query method for Jena model
	private String constructSparqlQueryFromClassName(String className) {
		String sparqlQuery =  RDF_PREFIX + "\n" + IFCOWL_PREFIX + "\n"
        		+ "SELECT ?x\n"
        		+ "WHERE { \n"
        		+ "{?x"+ " rdf:type ifcowl:" + className + "}\n"
        		+ "}";
		return sparqlQuery;
	}
 	private String constructSparqlQueryFromPredicateList(String instPrefix, String subString, List<String> PredicateList) {
 		StringBuilder queryString = new StringBuilder();
 		
 		String INST_PREFIX = "PREFIX inst:<" +instPrefix + ">";
 		queryString.append(IFCOWL_PREFIX).append("\n").append(RDF_PREFIX).append("\n").append(LIST_PREFIX).append("\n").append(INST_PREFIX).append("\n");
 		
 		int predLength = PredicateList.size();

        queryString.append("SELECT ?variable_").append(predLength-1).append(" \nWHERE { \n");
        queryString.append(constructPartialSparqlQuery(subString, PredicateList.get(0)));

        if(predLength>1){
            for(int variableNum=1; variableNum<predLength; variableNum++){
                queryString.append(constructPartialSparqlQuery(PredicateList.get(variableNum), variableNum-1));
            }
        }
        queryString.append("}");
        
		return queryString.toString();
	}
 	
 	private String constructPartialSparqlQuery(String subString, String predString) {
 		StringBuilder partFirstSparql = new StringBuilder();
 		if (predString.startsWith("ifcowl:related")){
 			partFirstSparql.append("{");
            partFirstSparql.append("{?variable_0 ").append(predString)
                    .append(" ").append("inst:"+subString).append(" } UNION ");
        }
 		if (predString.startsWith("ifcowl:relating")){
 			partFirstSparql.append("{");
            partFirstSparql.append("{?variable_0 ").append(predString)
                    .append(" ").append("inst:"+subString).append(" } UNION ");
        } 		
 		partFirstSparql.append("{").append("inst:"+subString).append(" ").append(predString)
        .append(" ").append("?variable_0}");
 		
 		if (predString.startsWith("ifcowl:related")){
 			partFirstSparql.append("}");
        }
 		
 		if (predString.startsWith("ifcowl:relating")){
 			partFirstSparql.append("}");
 		}
 		
 		return partFirstSparql.toString();
 	}
 	
 	private String constructPartialSparqlQuery(String predString, int i) {
 		StringBuilder partSparql = new StringBuilder();
 		
 		if (predString.startsWith("ifcowl:related")){
 			partSparql.append("{");
            partSparql.append("{?variable_").append(i+1).append(" ").append(predString)
                    .append(" ").append("?variable_").append(i).append("} UNION ");
        }
 		
 		if (predString.startsWith("ifcowl:relating")){
 			partSparql.append("{");
            partSparql.append("{?variable_").append(i+1).append(" ").append(predString)
                    .append(" ").append("?variable_").append(i).append("} UNION ");
        }
 		
 		partSparql.append("{?variable_").append(i).append(" ").append(predString)
        .append(" ").append("?variable_").append(i + 1).append("}");
 		
 		if (predString.startsWith("ifcowl:related")){
 			partSparql.append("}");
        }
 		
 		if (predString.startsWith("ifcowl:relating")){
 			partSparql.append("}");
 		}
 		
		return partSparql.toString();
 	}
 	
    private List<String> carryOutQuery(Model instanceModel, String queryString) {
        List<String> queryResultStringList = new ArrayList<>();
        
        //System.out.println(queryString);
        org.apache.jena.query.Query query = QueryFactory.create(queryString);

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
	
	public OWLOntology getOntology() {
		return bimQulityCheckOntology;
	}
	//SPARQL query method for owlapi model
	public QueryResult processQuery(String dataPropertyName)
	{ 
		String queryStatement = "PREFIX bimqc: <http://www.semanticweb.org/bimqualitychecker/v1.0#>\n" +
      		"SELECT * WHERE { PropertyValue(?x, " + "bimqc:" + dataPropertyName +	" ,?y)" + 
       		"}"	;
		try {
			long startTime = System.currentTimeMillis();
			
			// Create a query object from it's string representation
			Query query = Query.create(queryStatement);
			
			System.out.println("Excecute the query:");
			System.out.println(queryStatement);
			System.out.println("-------------------------------------------------");
			
			// Execute the query and generate the result set
			QueryResult result = engine.execute(query);

			if(query.isAsk()) {
				System.out.print("Result: ");
				if(result.ask()) {
					System.out.println("yes");
				}
				else {
					System.out.println("no");
				}
			}
			else {
				if(!result.ask()) {
					System.out.println("Query has no solution.\n");
				}
				else {
					System.out.println("Results:");
					System.out.print(result);
					System.out.println("-------------------------------------------------");
					System.out.println("Size of result set: " + result.size());
				}
			}

			System.out.println("-------------------------------------------------");
			System.out.println("Finished in " + (System.currentTimeMillis() - startTime) / 1000.0 + "s\n");
			return result;
		}
        catch(QueryParserException e) {
        	System.out.println("Query parser error: " + e);
        }
        catch(QueryEngineException e) {
        	System.out.println("Query engine error: " + e);
        }
		return null;	
	}

	
	//Here are list methods for the members of ontology
	@SuppressWarnings("deprecation")
	private void listClassAssertionAxiom() {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (@KeyForBottom @NonNull @Initialized @Mutable OWLClassAssertionAxiom dataPropertyAssertion : 
	    	 bimQulityCheckOntology.getAxioms(AxiomType.CLASS_ASSERTION)) {	        
	       	System.out.println(renderer.render(dataPropertyAssertion));
	     }
	}
	
	private void listAllDataPropertyAssertionAxiom() {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (@KeyForBottom @NonNull @Initialized @Mutable OWLDataPropertyAssertionAxiom dataPropertyAssertion : 
	    	 bimQulityCheckOntology.getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {	        
	       	System.out.println(renderer.render(dataPropertyAssertion));
	     }
	}	 
	private void listAllObjectPropertyAssertionAxiom() {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (@KeyForBottom @NonNull @Initialized @Mutable OWLObjectPropertyAssertionAxiom objectPropertyAssertion : 
	    	 bimQulityCheckOntology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
	          	System.out.println(renderer.render(objectPropertyAssertion));
	     }
	}	
	
	private void OutputAllObjectPropertyAssertionAxiom() {
		StringBuilder allObjectPropertyAssertionAxiom = new StringBuilder();
		
		File outputFile= new File(System.getProperty("user.dir")+ "\\docs\\output\\allObjectPropertyAssertionAxiom.owl");
		try {
			BufferedWriter bw = new BufferedWriter(new FileWriter(outputFile));
			OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
		     for (@KeyForBottom @NonNull @Initialized @Mutable OWLObjectPropertyAssertionAxiom objectPropertyAssertion : 
		    	 bimQulityCheckOntology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
		    	 allObjectPropertyAssertionAxiom.append(renderer.render(objectPropertyAssertion)+"\n");
		     }
		     bw.write(allObjectPropertyAssertionAxiom.toString());
		     bw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	     
	     
	}	
	
	private void listSWRLRules() {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (SWRLRule rule : bimQulityCheckOntology.getAxioms(AxiomType.SWRL_RULE)) {	        
	       	System.out.println(renderer.render(rule));
	     }
	}
	public void listQueryResult(QueryResult result) {
		 if(result!=null) {
	       	 Iterator<QueryBinding> resultBindingIterator = result.iterator(); 
	        	 
	         while(resultBindingIterator.hasNext()) {
	          	QueryBinding resultBinding = resultBindingIterator.next();
	            Set<QueryArgument> keyset = resultBinding.getBoundArgs();
	           	for (QueryArgument arg:keyset) {            		 
	           		System.out.println(resultBinding.get(arg));
	           	}
	         }
       }
		 else {
			 System.out.println("query result is null");
		 }
	 }
	
	

}
