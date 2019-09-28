// 读取插值
void CCreateCVC3Data::_smtlib2ReadItpResults(std::string itpTxtFile)
{
	std::vector<std::string> itpLines;
	std::ifstream infile(itpTxtFile.c_str());
	std::string lineInFile;
	// the 1st line should be "UNSAT" since there is interpolant
	getline(infile, lineInFile);
	getline(infile, lineInFile);
	int size = lineInFile.size();
	std::string ss = lineInFile.substr(1, size - 2); //去除头尾括号
	std::string tmp;
	int counter = 0;
	int i = 0;
	for (i = 0; i < size - 2 ; i++) {
		if (i + 3 < size && ss[i] == 't' && ss[i + 1] == 'r' && ss[i + 2] == 'u' && ss[i + 3] == 'e') {
			itpLines.push_back("true");
			i += 4;
			continue;
		}
		switch (ss[i]) {
		case '(':
			tmp += ss[i];
			counter++;
			break;
		case ')':
			tmp += ss[i];
			counter--;
			if (counter == 0) {
				itpLines.push_back(tmp);
				tmp = "";
				i++;
			}
			break;
		case ' ':
			if (counter == 0 && tmp.size() != 0) {
				itpLines.push_back(tmp);
				tmp = "";
			}
			else {
				tmp += ss[i];
			}
			break;
		default:
			tmp += ss[i];
		}
	}
	// get current bound of cx
	std::string tmpString = itpTxtFile.substr(itpTxtFile.find("tillBound_")+10);
	std::string curBoundStr = tmpString.substr(0, tmpString.find("_result"));
	int curBound = atoi(curBoundStr.c_str());
	xxBound = curBound;
	std::string propStr = curBoundStr.substr(curBoundStr.find("property_") + 9);
	int propID = atoi(propStr.c_str());

	//stepInterpolantStrHolder.insert(std::pair<int, std::vector<std::string>>(curBound, itpLines));

	std::string pathName = this->outputFileDirectory;
	pathName = pathName.substr(0, pathName.find_last_of("\\")) + "\\SMTLIB2";
	
	char fullFileName[1024];
	sprintf(fullFileName, "%s\\tillBound_%d_interpolant_%d.txt", pathName.c_str(), curBound, propID);

	FILE* pFile;
	pFile = fopen(fullFileName, "w");
	if (!pFile) {throw CG2Exception(M_105,__FILE__, __LINE__,"CVC3APIchecker.cpp","can't write itp file!");}
	
	for (int i = 0; i < itpLines.size(); i++) {
		fwrite(itpLines[i].c_str(), 1, itpLines[i].size(), pFile);
		fwrite("\r\n",1,2,pFile);
	}
	fclose (pFile);

	updateReachable(curBound, propID, itpLines);
	return;
}

// 更新插值
void CCreateCVC3Data::updateReachable(int bound, int propId, std::vector<std::string> itpVector) {
	//插值为空
	if (stepRechabilityVector.empty()) {
		for (int i = 0; i < itpVector.size(); i++)
			stepRechabilityVector.push_back(itpVector[i]);
	}
	else if(stepRechabilityVector.size() == itpVector.size())
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			std::string itp_j;
			itp_j = "(or " + stepRechabilityVector[j] + " " + itpVector[j] + ")";
			stepRechabilityVector[j] = itp_j;
		}
	}
	else
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			std::string itp_j;
			itp_j = "(and " + stepRechabilityVector[j] + " " + itpVector[j] + ")";
			stepRechabilityVector[j] = itp_j;
		}

		for (; j < itpVector.size(); j++) {
			stepRechabilityVector.push_back(itpVector[j]);
		}
	}
	if(bound > 1)
		fixpointReached(bound, propId);
	return;
}

void CCreateCVC3Data::updateReachable2(int bound, int propId, std::vector<std::string> itpVector) {
	//插值为空
	if (stepRechabilityVector.empty()) {
		for (int i = 0; i < itpVector.size(); i++)
			stepRechabilityVector.push_back(itpVector[i]);
	}
	else if(stepRechabilityVector.size() == itpVector.size())
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			std::string itp_j;
			itp_j = "(or " + stepRechabilityVector[j] + " " + itpVector[j] + ")";
			stepRechabilityVector[j] = itp_j;
		}
	}
	else
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			stepRechabilityVector[j] = itpVector[j];
		}

		for (; j < itpVector.size(); j++) {
			stepRechabilityVector.push_back(itpVector[j]);
		}
	}
	if(bound > 1)
		fixpointReached(bound, propId);
	return;
}

bool CCreateCVC3Data::fixpointReached(int bound, int propId) 
{
	if(bound < 2)
		return false;
	std::string pathName = this->outputFileDirectory;
	pathName = pathName.substr(0, pathName.find_last_of("\\")) + "\\SMTLIB2";
	
	char fullFileName[1024];
	sprintf(fullFileName, "%s\\tillBound_%d_reachability_%d.smt", pathName.c_str(), bound, propId);

	FILE* pFile;
	pFile = fopen(fullFileName, "w");
	if (!pFile) {throw CG2Exception(M_105,__FILE__, __LINE__,"CVC3APIchecker.cpp","can't write rtc file!");}

	char tmp0[2048];

	sprintf(tmp0, "(set-option :print-success false)\n\
(set-logic QF_UFLRA)\n(set-info :smt-lib-version 2.0)\n\n");
	fputs(tmp0, pFile);

	// step variables
	char tmp1[1024];
	sprintf(tmp1, ";;;;; variables declaration\n");
	fputs(tmp1, pFile);

	fwrite(initVariableStr.c_str(), 1, initVariableStr.size(), pFile);
	fputs("\n", pFile);
	for (int curBound = 1; curBound <= bound; curBound++)
	{
		std::string stepVariableStr =  _smtlib2GenerateStrForStepVar(curBound);
		fwrite(stepVariableStr.c_str(), 1, stepVariableStr.size(), pFile);
	}

	// condition
	char tmp2[1024];
	sprintf(tmp2, ";;;;; condition\n");
	fputs(tmp2, pFile);

	std::string itpConstraints = "\n(define-fun ITP () Bool " + stepRechabilityVector.back() + ")\n";
	std::string rtcConstraints = "";
	if (bound > 1) {
		rtcConstraints += "(or ";
		for (int curBound = 1; curBound < bound; curBound++) {
			rtcConstraints += stepRechabilityVector[curBound] + " ";
		}
		rtcConstraints += ")";
	}
	else 
	{
		rtcConstraints += stepRechabilityVector[1];
		// rtcConstraints += stepRechabilityVector[0];
	}
	rtcConstraints = "\n(define-fun RTC () Bool " + rtcConstraints + ")\n";
	
	std::string assertionStr = "\n (assert (and ITP (not RTC))) \n (check-sat) \n (exit) \n";

	fwrite(itpConstraints.c_str(), 1, itpConstraints.size(), pFile);
	fwrite(rtcConstraints.c_str(), 1, rtcConstraints.size(), pFile);
	fwrite(assertionStr.c_str(), 1, assertionStr.size(), pFile);

	fclose (pFile);

	std::string filename(fullFileName);
	
	// fixpointFound = _smtlib2CheckingReachability(filename);
	return _smtlib2CheckingReachability(filename);
}

bool CCreateCVC3Data::_smtlib2CheckingReachability(std::string filename)
{
	bool checkResult = false;
	int cmdStatus = -1;

	// smtinterpol path compuation
	char buffer[MAX_PATH];
	GetModuleFileNameA(NULL, buffer, MAX_PATH);
	std::string::size_type pos = string(buffer).find_last_of("\\");
	
	std::string z3Path;
	z3Path = std::string(buffer).substr(0, pos + 1) + "z3.exe";

	// command string computation
	char command[2048];

	// generate the mc result file name
	std::string resultFileName = filename.substr(0, filename.find(".")) + "_result.txt";

	sprintf(command, "%s %s > %s", z3Path.c_str(), filename.c_str(), resultFileName.c_str());

	// execute mc
	cmdStatus = system(command);

	std::ifstream getMcResult(resultFileName.c_str());
	std::string resultLine = "";

	getline(getMcResult, resultLine);

	if (resultLine.compare("unsat") == 0) // fixpoint found
	{
		checkResult = true;
		  throw /* 成功 */ CG2Exception(M_105, __FILE__, __LINE__, "CVC3APIchecker.cpp", "Fixpoint found!");
	}
	else if (resultLine.compare("sat")==0) // cx
	{
		checkResult = false;
	}
	else
	{
		timeoutFlag = true;
		// throw /* 未通过 */ CG2Exception(M_105, __FILE__, __LINE__, "CVC3APIchecker.cpp", "Error finding fixpoint!");
	}
	return checkResult;

}

// 读取插值
void CCreateCVC3Data::_smtlib2MulticoreReadItpResults(std::string itpTxtFile)
{
	std::vector<std::string> itpLines;
	std::ifstream infile(itpTxtFile.c_str());
	std::string lineInFile;
	// the 1st line should be "UNSAT" since there is interpolant
	getline(infile, lineInFile);
	getline(infile, lineInFile);
	int size = lineInFile.size();
	std::string ss = lineInFile.substr(1, size - 2); //去除头尾括号
	std::string tmp;
	int counter = 0;
	int i = 0;
	for (i = 0; i < size - 2 ; i++) {
		if (i + 3 < size && ss[i] == 't' && ss[i + 1] == 'r' && ss[i + 2] == 'u' && ss[i + 3] == 'e') {
			itpLines.push_back("true");
			i += 4;
			continue;
		}
		switch (ss[i]) {
		case '(':
			tmp += ss[i];
			counter++;
			break;
		case ')':
			tmp += ss[i];
			counter--;
			if (counter == 0) {
				itpLines.push_back(tmp);
				tmp = "";
				i++;
			}
			break;
		case ' ':
			if (counter == 0 && tmp.size() != 0) {
				itpLines.push_back(tmp);
				tmp = "";
			}
			else {
				tmp += ss[i];
			}
			break;
		default:
			tmp += ss[i];
		}
	}

	updateMulticoreReachable(itpLines);
	return;
}

void CCreateCVC3Data::updateMulticoreReachable(std::vector<std::string> itpVector) {
	//插值为空
	if (stepRechabilityVector.empty()) {
		for (int i = 0; i < itpVector.size(); i++)
			stepRechabilityVector.push_back(itpVector[i]);
	}
	else if(stepRechabilityVector.size() == itpVector.size())
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			std::string itp_j;
			itp_j = "(or " + stepRechabilityVector[j] + " " + itpVector[j] + ")";
			stepRechabilityVector[j] = itp_j;
		}
	}
	else
	{
		int j = 0;
		for (; j < stepRechabilityVector.size(); j++) {
			stepRechabilityVector[j] = itpVector[j];
		}

		for (; j < itpVector.size(); j++) {
			stepRechabilityVector.push_back(itpVector[j]);
		}
	}
	return;
}

bool CCreateCVC3Data::fixpointMulticoreReached() 
{
	std::string pathName = this->outputFileDirectory;
	pathName = "C:\\Research\\Multi-Core-Test-ComputerJournal\\temp\\";
	
	char fullFileName[1024];
	int bound = stepRechabilityVector.size() - 1;
	if(bound < 0) {
		throw CG2Exception(M_105,__FILE__, __LINE__,"CVC3APIchecker.cpp","bound error!");
	}
	sprintf(fullFileName, "%s\\tillBound_%d_reachability.smt", pathName.c_str(), bound);

	FILE* pFile;
	pFile = fopen(fullFileName, "w+");
	if (!pFile) {throw CG2Exception(M_105,__FILE__, __LINE__,"CVC3APIchecker.cpp","can't write rtc file!");}

	char tmp0[2048];

	sprintf(tmp0, "(set-option :print-success false)\n\
(set-logic QF_UFLRA)\n(set-info :smt-lib-version 2.0)\n\n");
	fputs(tmp0, pFile);

	// step variables
	char tmp1[1024];
	sprintf(tmp1, ";;;;; variables declaration\n");
	fputs(tmp1, pFile);

	fwrite(initVariableStr.c_str(), 1, initVariableStr.size(), pFile);
	fputs("\n", pFile);
	for (int curBound = 1; curBound <= bound; curBound++)
	{
		std::string stepVariableStr =  _smtlib2GenerateStrForStepVar(curBound);
		fwrite(stepVariableStr.c_str(), 1, stepVariableStr.size(), pFile);
	}

	// condition
	char tmp2[1024];
	sprintf(tmp2, ";;;;; condition\n");
	fputs(tmp2, pFile);

	std::string itpConstraints = "\n(define-fun ITP () Bool " + stepRechabilityVector.back() + ")\n";
	std::string rtcConstraints = "";
	if (bound > 1) {
		rtcConstraints += "(or ";
		for (int curBound = 1; curBound < bound; curBound++) {
			rtcConstraints += stepRechabilityVector[curBound] + " ";
		}
		rtcConstraints += ")";
	}
	else 
	{
		rtcConstraints += stepRechabilityVector[1];
		// rtcConstraints += stepRechabilityVector[0];
	}
	rtcConstraints = "\n(define-fun RTC () Bool " + rtcConstraints + ")\n";
	
	std::string assertionStr = "\n (assert (and ITP (not RTC))) \n (check-sat) \n (exit) \n";

	fwrite(itpConstraints.c_str(), 1, itpConstraints.size(), pFile);
	fwrite(rtcConstraints.c_str(), 1, rtcConstraints.size(), pFile);
	fwrite(assertionStr.c_str(), 1, assertionStr.size(), pFile);

	fclose (pFile);

	std::string filename(fullFileName);
	
	// fixpointFound = _smtlib2CheckingReachability(filename);
	return _smtlib2CheckingReachability(filename);
}
