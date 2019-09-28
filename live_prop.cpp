void CCreateCVC3Data::_MultiCoreTestSmtlib2OutputFiles(std::string initAssumptionStr, char* outputListFile, int checkBd, size_t propID, int zipcModelType)
{
// NOTE: this function is for NON-multicore computation.
	
// NOTE: the ofstream method is very slow: for the changer example (with [G][F](x > 0) property), writing 40-50 steps, costs 21 seconds
//       checked internet, c++ FILE library is much faster than vc++ ofstream, so change

	FILE* pFile;

////////////////// test time start
//
//	// 时间测试
//	struct tm *date;
//	time_t timer = time(NULL);
//	date = localtime(&timer);
//	char szTime[256] = {0};
//	strftime(szTime, sizeof(szTime), "%Y-%m-%d %H:%M:%S", date);
//	std::string strDate = szTime;
//
//	std::string timeFile = "C:\\Test\\timeFile.txt";
//	std::ofstream timeOutFile(timeFile.c_str(), std::ios::app);
//	timeOutFile << "start writing into files \n" << strDate << "\n";
//
////////////////// test time end


// (I) genereate folder/path name
	std::string pathName = this->outputFileDirectory;
	pathName = pathName.substr(0, pathName.find_last_of("\\")) + "\\SMTLIB2";
	
	// [1] generate mc file name and mc result file name
	// [1.1] mc file name
	char fullFileName[1024];
	sprintf(fullFileName, "%s\\tillBound_%d_property_%d.smt", pathName.c_str(), checkBd, propID);
	std::string pureFileName = fullFileName;
	pureFileName = pureFileName.substr(pureFileName.find_last_of("\\")+1);
	//// [1.2] mc result file name
	//char resultFile[1024];
	//sprintf(resultFile, "%s\\property_%d_tillBound_%d_result.txt", pathName.c_str(), propID, checkBd);
	//std::ofstream tmpFile(resultFile);
	////tmpFile.close();


	// [2] output contents into mc files

	// create a file 
	//std::ofstream outfile(fullFileName);
	//outfile.close();
	pFile = fopen(fullFileName, "w"); // wa := write and append
	if (!pFile) {throw /* 未通過 */ CG2Exception(M_105,__FILE__, __LINE__,"CVC3APIchecker.cpp","can't open smtlib2 file!");}

	// save the file name into the list of names generated
	std::ofstream fileListOutput(outputListFile, std::ios::app); // add rather than overwrite
	fileListOutput << pureFileName << "\n";

	// [2.1] preliminary information
	// outfile << _smtlib2LogicDeclareOutput();
	fwrite(_smtlib2LogicDeclareOutput(zipcModelType).c_str(), 1, _smtlib2LogicDeclareOutput(zipcModelType).size(), pFile);

	fwrite(initAssumptionStr.c_str(), 1, initAssumptionStr.size(), pFile);

	// [2.3] step assumptions, variables: initial state has been output, so start from 1
	for (int curBound = 1; curBound <= checkBd; curBound++)
	{
		// step variables
		// outfile << ";;;;; variables at step " << curBound << "\n";
		// outfile << stepVariableStrHolder[curBound] << "\n\n";
		char tmp1[1024];
		sprintf(tmp1, ";;;;; variables at step  %d \n", curBound);
		fputs(tmp1, pFile);

		// const char* tmpStr1 = stepVariableStrHolder[curBound].c_str();
		fwrite(stepVariableStrHolder[curBound].c_str(), 1, stepVariableStrHolder[curBound].size(), pFile);
		fputs("\n\n", pFile);

		// step assumption
		// outfile << ";;;;; assumptions at step " << curBound << "\n";
		// outfile << "(assert " << stepAssumptionStrHolder[curBound] << ")\n\n";
		char tmp2[1024];
		// sprintf(tmp2, ";;;;; assumptions at step  %d \n (assert ", curBound);
		sprintf(tmp2, ";;;;; assumptions at step  %d \n (assert (!(and ", curBound);
		fputs(tmp2, pFile);

		// const char* tmpStr2 = stepAssumptionStrHolder[curBound].c_str();
		fwrite(stepAssumptionStrHolder[curBound].c_str(), 1, stepAssumptionStrHolder[curBound].size(), pFile);
		char tmp3[1024];
		// sprintf(tmp3, ":named P%d))\n\n", curBound);
		// fputs(")\n\n", pFile);

		std::string liveTransBase = _smtlib2LiveTransBaseOnceForAll();

		liveTransBase = "\n(and " + liveTransBase;

		/*
		0：[G](p)
		1：[F](p)
		2：[G][F](p)
		3：[F][G](p)
		*/
		switch (typeOfLTLFormulaG)
		{
		case 0:
			liveTransBase += _smtlib2LivePropBaseOnceForAll_G();
			break;
		case 1:
			liveTransBase += _smtlib2LivePropBaseOnceForAll_F();
			break;
		case 2:
			liveTransBase += _smtlib2LivePropBaseOnceForAll_GF();
			break;
		case 3:
			liveTransBase += _smtlib2LivePropBaseOnceForAll_FG();
			break;
		}

		std::stringstream elementStream;
		elementStream << "SeqNo_" << 0 << "_Operator";
		std::map<std::string, std::vector<std::string>>::iterator operatorKIt;
		operatorKIt = ltlKStepTerms.find(elementStream.str());

		if(operatorKIt == ltlKStepTerms.end())
		{
			throw /* 成功 */ CG2Exception(M_105, __FILE__, __LINE__, "CVC3APIchecker.cpp", "Liveness Outreach");
		}

		std::string flagFormula = operatorKIt->second[curBound];//must exit
		
		liveTransBase = liveTransBase + "(= flag_bound_ "+ flagFormula +")";
		liveTransBase = liveTransBase + ")\n";

		liveTransBase = liveTransBase + _smtlib2LoopClosedBaseOnceForAll();

		std::string liveTransConstraints =_smtlib2LiveTransConstraints(curBound, liveTransBase);


		fwrite(liveTransConstraints.c_str(), 1, liveTransConstraints.size(), pFile);

		sprintf(tmp3, "):named P%d))\n\n", curBound);
		fputs(tmp3, pFile);
		//fputs(")\n\n", pFile);

		// step threshold
		if (stepThresholdStrHolder.size() != 0)
		{
			// outfile << ";;;;; threshold at step " << curBound << "\n";
			// outfile << "(assert " << stepThresholdStrHolder[curBound] << ")\n\n";
			char tmp3[1024];
			sprintf(tmp3, ";;;;; threshold at step %d \n (assert ", curBound);
			fputs(tmp3, pFile);

			// const char* tmpStr3 = stepThresholdStrHolder[curBound].c_str();
			fwrite(stepThresholdStrHolder[curBound].c_str(), 1, stepThresholdStrHolder[curBound].size(), pFile);
			fputs(")\n\n", pFile);
		}

		// step formula variable
		// outfile << ";;;;; property variable at step " << curBound << "\n";
		// outfile << stepFormulaVarStrHolder[curBound];
		char tmp4[1024];
		sprintf(tmp4, ";;;;; property variable at step %d \n", curBound);
		fputs(tmp4, pFile);

		// const char* tmpStr4 = stepFormulaVarStrHolder[curBound].c_str();
		fwrite(stepFormulaVarStrHolder[curBound].c_str(), 1, stepFormulaVarStrHolder[curBound].size(), pFile);
		fputs("\n\n", pFile);

	}

	// [2.4] step formula
	// outfile << ";;;;; property formula \n";
	// outfile << "(assert " << stepFormulaStrHolder[checkBd] << ")\n\n";
	// outfile << "(check-sat)" << "\n" << "(get-model)" << "\n" << "(exit)" << "\n";
	// fputs(";;;;; property formula \n (assert ", pFile);

	 fputs(";;;;; property formula \n ", pFile);
	//const char* tmpLtlStr = stepFormulaStrHolder[checkBd].c_str();
	//fwrite(stepLoopConstraintStrHolder[checkBd].c_str(), 1, stepLoopConstraintStrHolder[checkBd].size(), pFile);
	//fwrite(stepFormulaStrHolder[checkBd].c_str(), 1, stepFormulaStrHolder[checkBd].size(), pFile);
	//std::string formula = _smtlib2ConstructStepFormulaStrHolder3(checkBd);
	//fwrite(formula.c_str(), 1, formula.size(), pFile);
	
	std::string loopClosedBase = _smtlib2FinalPropBaseOnceForAll();
	//std::string loopClosedBase = _smtlib2LoopClosedBaseOnceForAll();
	std::string loopClosedConstraints =_smtlib2LoopClosedConstraints(checkBd, loopClosedBase);

	loopClosedConstraints = "(assert (!" + loopClosedConstraints;
	loopClosedConstraints = loopClosedConstraints + ":named PR))\n\n";

	fwrite(loopClosedConstraints.c_str(), 1, loopClosedConstraints.size(), pFile);

	std::stringstream outputStream;
	std::stringstream outputStream2;

	/*
	outputStream << " (assert (! (and LPC ";
	for (int i = 1; i <= ltlVarTerm.size(); i++)
	{
		outputStream << "SEQ" << i << " ";
	}
	outputStream << "):named PR))" <<"\n";
	std::string astr = outputStream.str();
	fwrite(astr.c_str(), 1, astr.size(), pFile);
	*/
	fputs("\n\n (check-sat) \n", pFile);
	
	outputStream2 << " (get-interpolants ";
	for (int i = 0; i < checkBd + 1; i++)
	{
		outputStream2 << "P" << i << " ";
	}
	outputStream2 << "PR)" <<"\n";
	std::string istr = outputStream2.str();
	fwrite(istr.c_str(), 1, istr.size(), pFile);
	
	fputs("\n (get-model) \n (exit) \n", pFile);

	fclose (pFile);

////////////////// test time start
//
//	// 时间测试
//	struct tm *date2;
//	time_t timer2 = time(NULL);
//	date2 = localtime(&timer2);
//	char szTime2[256] = {0};
//	strftime(szTime2, sizeof(szTime2), "%Y-%m-%d %H:%M:%S", date2);
//	std::string strDate2 = szTime2;
//
//	timeOutFile << "end writing into files \n" << strDate2 << "\n";
//	timeOutFile.close();
//
////////////////// test time end


	// [2.6] close files
	fileListOutput.close();
}