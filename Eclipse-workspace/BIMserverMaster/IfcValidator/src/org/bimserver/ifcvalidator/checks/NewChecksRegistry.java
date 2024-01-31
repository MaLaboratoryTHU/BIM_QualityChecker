package org.bimserver.ifcvalidator.checks;

import org.semanticweb.owlapi.model.OWLOntologyCreationException;

/******************************************************************************
 * Copyright (C) 2009-2018  BIMserver.org
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * 
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see {@literal<http://www.gnu.org/licenses/>}.
 *****************************************************************************/

public class NewChecksRegistry extends ModelCheckerRegistry {
	public NewChecksRegistry(){
		try {
			//BimQualityCheckOntology bimQualityCheckOntology = new BimQualityCheckOntology(System.getProperty("user.dir")+ "\\docs\\model\\Duplex_A_20110505.ttl");
			addCheck(new AllObjectsInBuildingStorey());
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
}
