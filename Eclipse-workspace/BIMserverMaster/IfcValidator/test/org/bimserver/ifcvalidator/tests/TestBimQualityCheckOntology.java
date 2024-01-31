package org.bimserver.ifcvalidator.tests;

import org.bimserver.ifcvalidator.reasoner.BimQualityCheckOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

public class TestBimQualityCheckOntology {
	public static void main(String[] args) {
		String MODEL_LOC = System.getProperty("user.dir")+ "\\docs\\model\\Duplex_A_20110505.ttl"
				;
		try {
			BimQualityCheckOntology bimQualityCheckOntology =new BimQualityCheckOntology(MODEL_LOC);
		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
