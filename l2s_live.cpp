std::string CCreateCVC3Data::_smtlib2LoopClosedConstraints(short bound, std::string stateEqBase)
{
	std::string constraints="";
	std::string loop="";;
	std::string atMostOne="";

	char indexNum[1024];
	char preIndexNum[1024];
	char boundNum[1024];
	sprintf(boundNum, "_%u", bound);

	std::string indexStr;
	std::string preIndexStr;
	std::string boundStr = boundNum;

	sprintf(preIndexNum, "_%u", bound);
	indexStr = indexNum;
	preIndexStr = preIndexNum;

	std::string tmpStateEq = _smtlib2ReplaceSubStr(stateEqBase, "_preIndex_", preIndexStr);
	tmpStateEq = _smtlib2ReplaceSubStr(tmpStateEq, "_bound_", boundStr);
	
	// NOTE: loop string should be enclosed with "(and ... )"

	constraints = tmpStateEq;

	return constraints;
}

std::string CCreateCVC3Data::_smtlib2LiveTransConstraints(short bound, std::string stateEqBase)
{
	std::string constraints="";
	std::string loop="";;
	std::string atMostOne="";

	char indexNum[1024];
	char preIndexNum[1024];
	char boundNum[1024];
	sprintf(boundNum, "_%u", bound);

	std::string indexStr;
	std::string preIndexStr;
	std::string boundStr = boundNum;

	sprintf(preIndexNum, "_%u", bound - 1);
	indexStr = indexNum;
	preIndexStr = preIndexNum;

	std::string tmpStateEq = _smtlib2ReplaceSubStr(stateEqBase, "_preIndex_", preIndexStr);
	tmpStateEq = _smtlib2ReplaceSubStr(tmpStateEq, "_bound_", boundStr);
	
	// NOTE: loop string should be enclosed with "(and ... )"

	constraints = tmpStateEq;

	return constraints;
}

std::string CCreateCVC3Data::_smtlib2StateEqBaseOnceForAll()
{
	std::string finalStr;
	std::vector<std::string> exprContainer;

	std::vector<CDataVariableDetail*>::iterator varIte = _varDetail->begin();
	for (; varIte!=_varDetail->end(); varIte++)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);

// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1] generate state variable names
		std::stringstream sOfVarID;
		sOfVarID.imbue( std::locale::classic() );
		sOfVarID << tmpVar->getID();

		std::string firstVarName = "";
		std::string secondVarName = "";

		firstVarName.append("x").append(sOfVarID.str()).append("_preIndex_");
		secondVarName.append("x").append(sOfVarID.str()).append("_bound_");

		std::string eqStr = "(= " + firstVarName + " " + secondVarName + ")";
		exprContainer.push_back(eqStr);
	}

	finalStr = "(and ";
	for (size_t index=0; index<exprContainer.size(); index++)
	{
		finalStr = finalStr + " " + exprContainer[index];
	}
	finalStr = finalStr.append(")");

	return finalStr;
}

std::string CCreateCVC3Data::_smtlib2SaveStateOnceForAll()
{
	std::string finalStr;
	std::vector<std::string> exprContainer;

	std::vector<CDataVariableDetail*>::iterator varIte = _varDetail->begin();
	for (; varIte!=_varDetail->end(); varIte++)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);

// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1] generate state variable names
		std::stringstream sOfVarID;
		sOfVarID.imbue( std::locale::classic() );
		sOfVarID << tmpVar->getID();

		std::string firstVarName = "";
		std::string secondVarName = "";

		firstVarName.append("s").append(sOfVarID.str()).append("_bound_");
		secondVarName.append("x").append(sOfVarID.str()).append("_preIndex_");

		std::string eqStr = "(= " + firstVarName + " " + secondVarName + ")";
		exprContainer.push_back(eqStr);
	}

	finalStr = "(and ";
	for (size_t index=0; index<exprContainer.size(); index++)
	{
		finalStr = finalStr + " " + exprContainer[index];
	}
	finalStr = finalStr.append(")");

	return finalStr;
}

std::string CCreateCVC3Data::_smtlib2SavedStateTransOnceForAll()
{
	std::string finalStr;
	std::vector<std::string> exprContainer;

	std::vector<CDataVariableDetail*>::iterator varIte = _varDetail->begin();
	for (; varIte!=_varDetail->end(); varIte++)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);

// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1] generate state variable names
		std::stringstream sOfVarID;
		sOfVarID.imbue( std::locale::classic() );
		sOfVarID << tmpVar->getID();

		std::string firstVarName = "";
		std::string secondVarName = "";

		firstVarName.append("s").append(sOfVarID.str()).append("_bound_");
		secondVarName.append("s").append(sOfVarID.str()).append("_preIndex_");

		std::string eqStr = "(= " + firstVarName + " " + secondVarName + ")";
		exprContainer.push_back(eqStr);
	}

	finalStr = "(and ";
	for (size_t index=0; index<exprContainer.size(); index++)
	{
		finalStr = finalStr + " " + exprContainer[index];
	}
	finalStr = finalStr.append(")");

	return finalStr;
}

std::string CCreateCVC3Data::_smtlib2LoopedStateOnceForAll()
{
	std::string finalStr;
	std::vector<std::string> exprContainer;

	std::vector<CDataVariableDetail*>::iterator varIte = _varDetail->begin();
	for (; varIte!=_varDetail->end(); varIte++)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);

// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1] generate state variable names
		std::stringstream sOfVarID;
		sOfVarID.imbue( std::locale::classic() );
		sOfVarID << tmpVar->getID();

		std::string firstVarName = "";
		std::string secondVarName = "";

		firstVarName.append("x").append(sOfVarID.str()).append("_bound_");
		secondVarName.append("s").append(sOfVarID.str()).append("_preIndex_");

		std::string eqStr = "(= " + firstVarName + " " + secondVarName + ")";
		exprContainer.push_back(eqStr);
	}

	finalStr = "(and ";
	for (size_t index=0; index<exprContainer.size(); index++)
	{
		finalStr = finalStr + " " + exprContainer[index];
	}
	finalStr = finalStr.append(")");

	return finalStr;
}

std::string CCreateCVC3Data::_smtlib2LiveTransBaseOnceForAll() {
	std::stringstream str;
	str << "(and ";
	str << "(=> inloop_preIndex_ (not save_bound_))\n";
	str << "(= inloop_bound_ (or inloop_preIndex_ save_bound_))\n";
	str << "(=> save_bound_ ";
	str << _smtlib2SaveStateOnceForAll();
	str << ")\n";
	str << "(=> (not save_bound_) ";
	str << _smtlib2SavedStateTransOnceForAll();
	str << "))\n";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2LivePropBaseOnceForAll_G() {
	std::stringstream str;
	str << "(= acc_bound_ (or acc_preIndex_ flag_bound_))\n";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2LivePropBaseOnceForAll_F() {
	std::stringstream str;
	str << "(= acc_bound_ (and acc_preIndex_ flag_bound_))\n";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2LivePropBaseOnceForAll_FG() {
	std::stringstream str;
	str << "(= acc_bound_ (or acc_preIndex_ (and inloop_bound_ flag_bound_)))\n";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2LivePropBaseOnceForAll_GF() {
	std::stringstream str;
	str << "(= acc_bound_ (and acc_preIndex_ (=> inloop_bound_ flag_bound_)))\n";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2LoopClosedBaseOnceForAll() {
	std::stringstream str;
	str << "(and ";
	str << "(=> looped_bound_ inloop_bound_)\n";
	str << "(=> looped_bound_ ";
	str << _smtlib2LoopedStateOnceForAll();
	str << "))\n";
	//str << "(and looped_bound_ acc_bound_))";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2FinalPropBaseOnceForAll() {
	std::stringstream str;
	str << "(and looped_bound_ acc_bound_)";
	return str.str();
}

std::string CCreateCVC3Data::_smtlib2ReplaceSubStr(std::string source, std::string sub1, std::string sub2)
{
	size_t index = 0;
	while (true) {
		 /* Locate the substring to replace. */
		 index = source.find(sub1, index);
		 if (index == std::string::npos) break;

		 /* Make the replacement. */
		 source.replace(index, sub1.size(), sub2);

		 /* Advance index forward so the next iteration doesn't pick it up as well. */
		 index = index + sub1.size();
	}

	return source;
}