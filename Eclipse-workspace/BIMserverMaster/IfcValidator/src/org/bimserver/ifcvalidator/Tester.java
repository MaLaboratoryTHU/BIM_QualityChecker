package org.bimserver.ifcvalidator;

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

import org.bimserver.emf.IfcModelInterface;
import org.bimserver.ifcvalidator.checks.FullModelCheckerRegistry;
import org.bimserver.ifcvalidator.checks.ModelCheck;
import org.bimserver.validationreport.IssueContainer;
import org.bimserver.validationreport.IssueException;

public class Tester {
	private FullModelCheckerRegistry modelCheckerRegistry;
	private IssueContainer issueContainer;

	public Tester() {
		issueContainer = new IssueContainer();
		modelCheckerRegistry = new FullModelCheckerRegistry();
	}
	
	public void test(IfcModelInterface model, String groupIdentifier, String identifier) {
		ModelCheck modelCheck = modelCheckerRegistry.getModelCheck(groupIdentifier, identifier);
		try {
			modelCheck.check(model, issueContainer, null);
		} catch (IssueException e) {
			e.printStackTrace();
		}
	}

	public IssueContainer getIssueContainer() {
		return issueContainer;
	}
}