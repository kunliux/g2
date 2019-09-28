string CCreateCVC3Data::_smtlib2DeclareInitFlagAssumption()
{
	char tmpStr[1024];
	std::vector<std::string> varDeclareContainer;
	std::vector<std::string> varEquationContainer;

	std::vector<CDataVariableDetail*>::iterator varIte = _varDetail->begin();

	// [1] Generating Separate Equations of Variables with Their Values.
	for (; varIte!=_varDetail->end(); ++varIte)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);


// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1.1] Generating Variables
		// variable name
		std::string semiVarName = "x";
		std::stringstream sOfInt1;
		sOfInt1 << tmpVar->getID();
		semiVarName.append(sOfInt1.str());
		// variable name with bound
		std::stringstream sOfInt2;
		sOfInt2 << 0;
		semiVarName.append("_").append(sOfInt2.str());

		// [1.2] Generating Variable Values while declaring those variables
		// ID_BOOL = 1 <-- a boolean variable
		if (tmpVar->getType() == 1) 
		{
			// variable value
			if (tmpVar->getInitialValue() == 1) // 1 = true; 0 = false;
			{
				sprintf(tmpStr, "(declare-fun %s () Bool)\n", semiVarName.c_str());
				varDeclareContainer.push_back(tmpStr);
				sprintf(tmpStr, " %s", semiVarName.c_str());
				varEquationContainer.push_back(tmpStr);
			}
			else
			{
				sprintf(tmpStr, "(declare-fun %s () Bool)\n", semiVarName.c_str());
				varDeclareContainer.push_back(tmpStr);
				sprintf(tmpStr, " (not %s)", semiVarName.c_str());
				varEquationContainer.push_back(tmpStr);
			}
		}

		// Other Type of Variables, declare them as Real(Int)
		if ((tmpVar->getType() == 2) || (tmpVar->getType() == 3) || (tmpVar->getType() == 4) || (tmpVar->getType() == 5) || (tmpVar->getType() == 6))
		{
			sprintf(tmpStr, "(declare-fun %s () Real)\n", semiVarName.c_str());
			varDeclareContainer.push_back(tmpStr);
			if (tmpVar->getInitialValue() < 0)
			{
				sprintf(tmpStr, " (= %s (- %li))", semiVarName.c_str(), abs(tmpVar->getInitialValue()));
			}
			else
			{
				sprintf(tmpStr, " (= %s %li)", semiVarName.c_str(), tmpVar->getInitialValue());
			}
			varEquationContainer.push_back(tmpStr);
    	}
	}

	varIte = _varDetail->begin();

	// Generating Separate Equations of Variables with Their Values.
	for (; varIte!=_varDetail->end(); ++varIte)
	{
		CDataVariableDetail* tmpVar = static_cast<CDataVariableDetail*>(*varIte);


// at this time being, message checking uses the same method as flag checking; so must skip some variables
		// filter out those G2-Parser generated message variables
		if (tmpVar->getName().compare("RECVMESSAGEQUE") == 0 || tmpVar->getName().compare("SENDMESSAGEQUE") == 0 || tmpVar->getName().compare("MESSAGE") == 0
			|| tmpVar->getName().compare("IGNORECOMPUTINGFLAG") == 0)
		{
			continue;
		}

		// [1.1] Generating Variables
		// variable name
		std::string semiVarName = "s";
		std::stringstream sOfInt1;
		sOfInt1 << tmpVar->getID();
		semiVarName.append(sOfInt1.str());
		// variable name with bound
		std::stringstream sOfInt2;
		sOfInt2 << 0;
		semiVarName.append("_").append(sOfInt2.str());

		// [1.2] Generating Variable Values while declaring those variables
		// ID_BOOL = 1 <-- a boolean variable
		if (tmpVar->getType() == 1) 
		{
			sprintf(tmpStr, "(declare-fun %s () Bool)\n", semiVarName.c_str());
			varDeclareContainer.push_back(tmpStr);
		}

		// Other Type of Variables, declare them as Real(Int)
		if ((tmpVar->getType() == 2) || (tmpVar->getType() == 3) || (tmpVar->getType() == 4) || (tmpVar->getType() == 5) || (tmpVar->getType() == 6))
		{
			sprintf(tmpStr, "(declare-fun %s () Real)\n", semiVarName.c_str());
			varDeclareContainer.push_back(tmpStr);
    	}
	}

	// add 5 additional for-liveness varialbes
	std::string liveVarName1 = "save";
	std::string liveVarName2 = "inloop";
	std::string liveVarName3 = "acc";
	std::string liveVarName4 = "looped";
	std::string liveVarName5 = "flag";
	// variable name with bound
	std::stringstream sOfInt4;
	sOfInt4 << 0;
	liveVarName1.append("_").append(sOfInt4.str());
	liveVarName2.append("_").append(sOfInt4.str());
	liveVarName3.append("_").append(sOfInt4.str());
	liveVarName4.append("_").append(sOfInt4.str());
	liveVarName5.append("_").append(sOfInt4.str());

	sprintf(tmpStr, "(declare-fun %s () Bool)\n", liveVarName1.c_str());
	varDeclareContainer.push_back(tmpStr);
	sprintf(tmpStr, "(declare-fun %s () Bool)\n", liveVarName2.c_str());
	varDeclareContainer.push_back(tmpStr);
	sprintf(tmpStr, "(declare-fun %s () Bool)\n", liveVarName3.c_str());
	varDeclareContainer.push_back(tmpStr);
	sprintf(tmpStr, "(declare-fun %s () Bool)\n", liveVarName4.c_str());
	varDeclareContainer.push_back(tmpStr);
	sprintf(tmpStr, "(declare-fun %s () Bool)\n", liveVarName5.c_str());
	varDeclareContainer.push_back(tmpStr);

	std::string retStr = ";;;;; initial state information \n";

	initVariableStr = "";
	// output var declcaration
	for (int index = 0; index < (int) varDeclareContainer.size(); index++)
	{
		retStr = retStr + varDeclareContainer[index]; 
		initVariableStr = initVariableStr + varDeclareContainer[index];
	}

	// output var equation
	// retStr = retStr + "(assert (and";
	retStr = retStr + "\n\n";
	retStr = retStr + "(assert (!(and";
	for (int index = 0; index < (int) varEquationContainer.size(); index++)
	{
		retStr = retStr + varEquationContainer[index];
	}
	// retStr = retStr + "))\n\n";
	//retStr = retStr + "):named P0))\n\n";
	

	std::string initStr = "\n(and (not save_0) (not inloop_0)";
	/*
	0：[G](p)
    1：[F](p)
    2：[G][F](p)
    3：[F][G](p)
	*/
	switch (typeOfLTLFormulaG)
	{
	case 0:
	case 3:
		initStr += " (not acc_0) ";
		break;
	case 1:
	case 2:
		initStr += " acc_0 ";
		break;
	}
	initStr += "\n";
	std::string stateEqBase = _smtlib2SaveStateOnceForAll();
	std::string stateEqBaseConstraints = _smtlib2LoopClosedConstraints(0, stateEqBase);
	initStr = initStr + stateEqBaseConstraints;
	initStr = initStr + ")\n";

	retStr = retStr + initStr + "):named P0))\n\n";
	return retStr;
}
