package org.bimserver.ifcvalidator.checks;

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

import java.util.List;

import org.bimserver.emf.IfcModelInterface;
import org.bimserver.ifcvalidator.CheckerContext;
import org.bimserver.models.ifc2x3tc1.Ifc2x3tc1Package;
import org.bimserver.models.ifc2x3tc1.IfcSite;
import org.bimserver.validationreport.IssueContainer;
import org.bimserver.validationreport.IssueException;
import org.bimserver.validationreport.Type;

public class IfcSiteElevation extends ModelCheck {

	public IfcSiteElevation() {
		super("SITE", "ELEVATION");
	}

	@Override
	public void check(IfcModelInterface model, IssueContainer issueContainer, CheckerContext checkerContext) throws IssueException {
		List<IfcSite> sites = model.getAll(IfcSite.class);
		for (IfcSite ifcSite : sites) {
			if (ifcSite.eIsSet(Ifc2x3tc1Package.eINSTANCE.getIfcSite_RefElevation())) {
				issueContainer.builder().originatingCheck(this.getClass().getSimpleName()).author(checkerContext.getAuthor()).type(Type.SUCCESS).object(ifcSite).message("RefElevation").is(ifcSite.getRefElevation()).shouldBe("Not null").add();
			} else {
				issueContainer.builder().originatingCheck(this.getClass().getSimpleName()).author(checkerContext.getAuthor()).type(Type.ERROR).object(ifcSite).message("RefElevation").is(null).shouldBe("Not null").add();
			}
		}
	}
}
