std::string CCreateCVC3Data::_smtlib2LoopFlagConstraintsOnceForAll(short bound, std::string stateEqBase)
{
	std::string loopConstraints="";
	std::string loop="";;
	std::string atMostOne="";

	char indexNum[1024];
	char preIndexNum[1024];
	char boundNum[1024];
	sprintf(boundNum, "_%u", bound);

	std::string indexStr;
	std::string preIndexStr;
	std::string boundStr = boundNum;

	for (int index=1; index<=bound; index++)
	{
		sprintf(indexNum, "%u", index);
		sprintf(preIndexNum, "_%u", index-1);
		indexStr = indexNum;
		preIndexStr = preIndexNum;

		std::string tmpStateEq = _smtlib2ReplaceSubStr(stateEqBase, "_preIndex_", preIndexStr);
		tmpStateEq = _smtlib2ReplaceSubStr(tmpStateEq, "_bound_", boundStr);
	
		if (index == 1)
		{
			loop = "(=> loop" + indexStr + " " + tmpStateEq + ")";
		}
		else
		{
			loop = loop + " " + "(=> loop" + indexStr + " " + tmpStateEq + ")";
		}
	}
	// NOTE: loop string should be enclosed with "(and ... )"

	atMostOne = _smtlib2AtMostOneLoopOnceForAll(bound);

	loopConstraints = "(and " + loop + " " + atMostOne + ")";

	return loopConstraints;
}

std::string CCreateCVC3Data::_smtlib2AtMostOneLoopOnceForAll(short bound)
{
	// NOTE: this fun is to generate an expression restricting that a smaller loop exists up to the given step (>1, since we can't define loop with only 0 step)
	std::string atMostOneLoop;
	std::vector<std::string> smallerExistsVector;

	for (int index=1; index<=bound; index++)
	{
		char indexMinusOne[1024];
		sprintf(indexMinusOne, "%u", index-1);
		std::string indexMinusOneStr = indexMinusOne;

		std::string tmpExpr="";
		if (index == 1)
		{
			tmpExpr = "false";
			smallerExistsVector.push_back(tmpExpr);
		}
		else
		{
			//tmpExpr = vc->orExpr(smallerExistsVector[index-2], loopVarExprVector[index-2]);
			tmpExpr = "(or " + smallerExistsVector[index-2] + " loop" + indexMinusOneStr + ")";
			smallerExistsVector.push_back(tmpExpr);
		}
	}

	for (int index=0; index<bound; index++)
	{
		char indexPlusOne[1024];
		sprintf(indexPlusOne, "%u", index+1);
		std::string indexPlusOneStr = indexPlusOne;

		if (index == 0)
		{
			atMostOneLoop = "(=> " + smallerExistsVector[index] + " (not loop" + indexPlusOneStr + "))";
		}
		else
		{
			std::string tmpStr = " (=> " + smallerExistsVector[index] + " (not loop" + indexPlusOneStr + "))";
			atMostOneLoop = atMostOneLoop.append(tmpStr); 
		}
	}
	
	if(bound != 1) 
	{
		std::string andStr = "(and ";
		atMostOneLoop = andStr + atMostOneLoop + ")";
	}

	smallerExistsVector.clear();

	return atMostOneLoop;
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