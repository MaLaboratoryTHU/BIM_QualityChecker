package org.bimserver.ifcvalidator.reasoner;

import org.bimserver.ifcvalidator.extractor.*;

import com.clarkparsia.pellet.rules.builtins.BuiltInRegistry;
import com.clarkparsia.pellet.rules.builtins.GeneralFunction;
import com.clarkparsia.pellet.rules.builtins.GeneralFunctionBuiltIn;
import com.google.common.collect.Multimap;
import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;

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
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.search.EntitySearcher;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.swrlapi.core.SWRLRuleEngine;
import org.swrlapi.factory.SWRLAPIFactory;

import org.apache.jena.rdf.model.*;
import org.apache.jena.riot.*;
import org.apache.jena.query.*;

import java.io.File;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;


public class CreateOntology {
	
	 private static final String DOC_URL = "http://www.semanticweb.org/bimqualitychecker/v1.0";
	 private static final String DOC_LOC = System.getProperty("user.dir")+ "\\docs\\owl\\bimqualitychecker.owl";
	 private static final String MODEL_LOC = System.getProperty("user.dir")+ "\\docs\\model\\Duplex_A_20110505.ttl";
	 
	
	 private static final String IFCOWL_PREFIX = "PREFIX ifcowl:<http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#>";
	 private static final String RDF_PREFIX = "PREFIX rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#>";
	 
	 private static Model instanceModel;
	 
	 public static void main(String[] args) throws OWLOntologyCreationException {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(DOC_LOC));
		OWLDataFactory factory = manager.getOWLDataFactory(); 
		
        //set prefixes
        DefaultPrefixManager pm = new DefaultPrefixManager();
        pm.setDefaultPrefix(DOC_URL + "#");
        pm.setPrefix("var:", "urn:swrl#");
        
        instanceModel = RDFDataMgr.loadModel(MODEL_LOC);
        
        String INST_URL = "http://linkedbuildingdata.net/ifc/resources20170627_104702/";
        
        String queryForWall = 
        		"PREFIX rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n"
        		+ "PREFIX ifcowl:<http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#>\n"
        		+ "SELECT ?x\n"
        		+ "WHERE { \n"
        		+ "{?x "+ "rdf:type " + "ifcowl:IfcWallStandardCase" + "}\n"
        		+ "}";
        
        String queryForMaterial = 
        		"PREFIX rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n"
        		+ "PREFIX ifcowl:<http://www.buildingsmart-tech.org/ifcOWL/IFC2X3_TC1#>\n"
        		+ "SELECT ?x\n"
        		+ "WHERE { \n"
        		+ "{?x "+ "rdf:type " + "ifcowl:IfcMaterial" + "}\n"
        		+ "}";
        
        
        List<String> wallInstances = carryOutQuery(instanceModel,  queryForWall);
        List<String> materialInstances = carryOutQuery(instanceModel,  queryForMaterial);    
        
        for (String materialFullName:materialInstances) {
        	//For each material instance, create an individual
        	OWLNamedIndividual owlMaterilIndividual = createIndividual(ontology, pm, manager, ":"+materialFullName);
        	OWLClass materialClass = factory.getOWLClass(":Material",pm);
    		manager.addAxiom(ontology, factory.getOWLClassAssertionAxiom(materialClass, owlMaterilIndividual));        	
        }
        
        OWLObjectProperty RelatingMaterial = factory.getOWLObjectProperty(":RelatingMaterial", pm);
        
        for (String wallFullName:wallInstances) {
        	
        	String wallName=wallFullName.replace(INST_URL, "");
        	
        	//For each wall instance, create an individual
        	OWLNamedIndividual owlWallIndividual = createIndividual(ontology, pm, manager, ":"+wallName);
        	OWLClass wallClass = factory.getOWLClass(":Wall",pm);
    		manager.addAxiom(ontology, factory.getOWLClassAssertionAxiom(wallClass, owlWallIndividual));
        	
    		//Extract material for a wall individual
        	InfoExtractorUtil infoExtractor = new InfoExtractorUtil(instanceModel, "IfcElement",
        			"inst:"+wallName, "IfcMaterial");        	
        	List<String> relatingMaterials = infoExtractor.queryInfoForElement();
        	
        	        	
        	//Create object property RelatingMaterial 
        	for(String material:relatingMaterials) {
        		OWLNamedIndividual owlMaterialIndividual = factory.getOWLNamedIndividual(material.replace("inst:", ""), pm);
        		//System.out.println(owlMaterialIndividual.toString());
        		manager.addAxiom(ontology, factory.getOWLObjectPropertyAssertionAxiom(RelatingMaterial, 
        				owlWallIndividual, owlMaterialIndividual));
        	}
        	
        	
       }        

        //reason
        OWLReasonerFactory reasonerFactory = PelletReasonerFactory.getInstance();
        OWLReasoner reasoner = reasonerFactory.createReasoner(ontology, new SimpleConfiguration());

        listSWRLRules(ontology);	     
//        
//        // validate consistency for ontology
//        if (reasoner.isConsistent()) {
//            // an ontology can be consistent, but have unsatisfiable classes.
//            if (reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom().size() > 0) {
//            	// means: an ontology is consistent but unsatisfiable!
//                System.out.println("The ontology FAILED satisfiability test with Pellet reasoner. \n Unsatisfiable classes detected: "
//                        + reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom().size());                
//            } else {
//                System.out.println("The ontology PASSED the consistency test.");
//            }
//        } else {
//            System.out.println("The ontology FAILED the consistency test, please review the Axioms or debug using Protege");
//        }
//        
        SWRLRuleEngine ruleEngine;
        ruleEngine = SWRLAPIFactory.createSWRLRuleEngine(ontology);
        System.out.println("Loaded rule engine"); 
        
        ruleEngine.infer();  
//        
//        //listAllObjectPropertyAssertionAxiom(ontology);
        listAllDataPropertyAssertionAxiom(ontology);
//        
//        //OWLDataProperty systemHasConsistentCoordSystem = factory.getOWLDataProperty(":SystemHasConsistentCoordSystem", pm);
        QueryEngine engine;
        engine=QueryEngine.create(manager, reasoner,true);
        
        String queryStatement = "PREFIX bimqc: <http://www.semanticweb.org/bimqualitychecker/v1.0#>\n" +
        		"SELECT * WHERE { PropertyValue(?x, " + "bimqc:ComponentHasMaterial" +	" ,?y)" + 
        		"}"	;
        QueryResult result = processQuery(engine,queryStatement);
       
        
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
        listAllObjectPropertyAssertionAxiom(ontology);
	 }
	 
	 private static OWLNamedIndividual createIndividual(OWLOntology ontology, DefaultPrefixManager pm, OWLOntologyManager manager, String name) {
		 OWLDataFactory factory = manager.getOWLDataFactory();
	     OWLNamedIndividual individual = factory.getOWLNamedIndividual(name, pm);
	     manager.addAxiom(ontology, factory.getOWLDeclarationAxiom(individual));
	     return individual;
	 }

	 private static OWLObjectProperty createObjectProperty(OWLOntology ontology, DefaultPrefixManager pm, OWLOntologyManager manager, String name) {
		 OWLDataFactory factory = manager.getOWLDataFactory();
	     OWLObjectProperty objectProperty = factory.getOWLObjectProperty(name, pm);
	     manager.addAxiom(ontology, factory.getOWLDeclarationAxiom(objectProperty));
	     return objectProperty;
    }
	
	 private static void listAllObjectPropertyAssertionAxiom(OWLOntology ontology) {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (@KeyForBottom @NonNull @Initialized @Mutable OWLObjectPropertyAssertionAxiom objectPropertyAssertion : ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
	          	System.out.println(renderer.render(objectPropertyAssertion));
	     }
	}
	 
	 private static void listAllDataPropertyAssertionAxiom(OWLOntology ontology) {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (@KeyForBottom @NonNull @Initialized @Mutable OWLDataPropertyAssertionAxiom dataPropertyAssertion : ontology.getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {
	        
	       	System.out.println(renderer.render(dataPropertyAssertion));
	     }
	}
	 
	 private static void listSWRLRules(OWLOntology ontology) {
	     OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
	     for (SWRLRule rule : ontology.getAxioms(AxiomType.SWRL_RULE)) {
	        
	       	System.out.println(renderer.render(rule));
	     }
	}
	 
	 private static void listDataPropertyValues(OWLNamedIndividual individual, OWLDataProperty dataProp, OWLOntology ontology, OWLReasoner reasoner) {
        OWLObjectRenderer renderer = new DLSyntaxObjectRenderer();
        Multimap<OWLDataPropertyExpression, OWLLiteral> assertedValues = EntitySearcher.getDataPropertyValues(individual, ontology);
      	for (OWLLiteral literal : reasoner.getDataPropertyValues(individual, dataProp)) {
      		Collection<OWLLiteral> literalSet = assertedValues.get(dataProp);
            boolean asserted = (literalSet != null && literalSet.contains(literal));
            System.out.println((asserted ? "asserted" : "inferred") + " data property for " + renderer.render(individual) + " : "
            	+ renderer.render(dataProp) + " -> " + renderer.render(literal));
      	}
    }    
	
	 public static QueryResult processQuery(QueryEngine engine, String q)
		{
			try {
				long startTime = System.currentTimeMillis();
				
				// Create a query object from it's string representation
				Query query = Query.create(q);
				
				System.out.println("Excecute the query:");
				System.out.println(q);
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
	
	 public static void listQueryResult(QueryResult result) {
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

	 private static List<String> carryOutQuery(Model instanceModel, String queryString) {
	        List<String> queryResultStringList = new ArrayList<>();
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
}
