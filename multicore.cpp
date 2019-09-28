bool CCreateCVC3Data::_smtlib2StatelessInterativeDeepenMulticoreLtlFlagCheck(CVC3::ValidityChecker* vc, 
										    short upBound, 
										    CCounterExample** cx, 
										    std::vector<CDataVariableDetail*>& varDetail,
										    const CDataPropertyLtl *pPropLtl,
											size_t propID)
{
	//Sleep(10000);
// check result: false when cx, true when no cx
	bool bRet = true;
	bool boundIncFlg = false; // this flag is used in the bottom of this func to check the upbound

	fixpointFound = true;

	bool isHierStm = _analyzeDesignType();
	int externalProNum = _CVC3externalProcessNum();

	// set frontierStates etc
	std::list<cfgNode*> frontierStates; // the set of states at the frontier layer.
	std::list<cfgNode*> newFrontierStates; // the new set of states for the frontier layer.

	// set the number of incremental check
	short iterativeIncNum = 10; // check all the states in between every 10 layers
	if (iterativeIncNum >= upBound) // if the upBound input by user is too small, then set upBound as the maximum iterative number
	{
		iterativeIncNum = upBound;
	}
	short currentBound = iterativeIncNum;

	// (a) generate folder/path name, and create a folder
	// original std::string pathName = this->outputFileDirectory;
	// original pathName = pathName.substr(0, pathName.find_last_of("\\")) + "\\SMTLIB2";
	// original CreateDirectoryA(pathName.c_str(), NULL); // NOTE: this line works only for windows.
	// 2013/5/9 Multicore Test: 

	// std::string pathName = "C:\\Research\\Multi-Core-Test\\";
	std::string pathName = "C:\\Research\\Multi-Core-Test-ITP\\";
	// std::string pathName = this->outputFileDirectory;
	// pathName = pathName.substr(0, pathName.find_last_of("\\")) + "\\SMTLIB2";

	// CreateDirectoryA(pathName.c_str(), NULL); // NOTE: this line works only for windows.

	// reset signal.txt contents

	std::string signalFile = "C:\\Research\\Multi-Core-Test-ITP\\signal.txt";
	DeleteFileA(signalFile.c_str());
	std::ofstream oF(signalFile.c_str()); 
	oF << "0";
	oF.close();

	std::string itpFileList = "C:\\Research\\Multi-Core-Test-ITP\\itp_filelist.txt";
	DeleteFileA(itpFileList.c_str());
	std::ofstream oF1(itpFileList.c_str()); 
	oF1 << "";
	oF1.close();

	std::string cxFile = pathName + "\\cxFile.txt";
	DeleteFileA(cxFile.c_str());
	std::ofstream oF2(cxFile.c_str()); 
	oF2 << "";
	oF2.close();

	// (b) generate a file to list the names of all input files.
	char listFileName[1024];
	sprintf(listFileName, "%s\\smtlib_filelist.txt", pathName.c_str());
	DeleteFileA(listFileName);
	std::ofstream oF3(listFileName); 
	oF3 << "";
	oF3.close();

	// since using different logics for different models can accelerate cvc4, so judge zipc model first
	// (1) if contain: variable comparison, then "UFLRA + simplex"
	// (2) else: "LRA + r-e"
	int zipcModelType = _zipcModelAnalysis();

	// this does not reflect the optimization of multiple assignments. 
	// it is better to just use a copy of the process p', optimize p', and generate the transition string.
	// the explicit search below can use original process p
	// generate transition smtlib string once for all
	_newSmtlib2TranStrGenerationOnceForAll();

	// generate a state equal base, to be used for generating ltl string, whose original version is time consuming
	std::string stateEqBase = _smtlib2StateEqBaseOnceForAll();

	LTLTree *ltltree = new LTLTree();
	std::string newPropertyStr = pPropLtl->getPropertyString();

	ltltree->buildTree(newPropertyStr);

	CVC3Tree::buildVaribleInfo(ltltree->root, this->_varDetail);
	ltltree->negation();
	ltltree->NNF();

	// (1-0) declare the ltl object, which is to be encoded directly into SMT-LIB2
	CDataPropertyLtl *newLTL = NULL;
	newLTL = new CDataPropertyLtl();

	// (1-1) generate the negated LTL string by using original LTL tree functions
	std::string negatedLtlStr = _smtlib2LTLTree2Str(ltltree->root);

	// (1-2) generate new calculation data
	std::vector<CDataExp*> newCal;
	bool b = _compileCreateLTLStructure(negatedLtlStr, newCal);

	// (1-3) merge [G] and [F] if the properties contain ...[G][F](...), the the 
	std::vector<CDataExp*> newCal1;
	newCal1 = _smtlib2LTLMergeGF(newCal);

	// (1-4) set the new information into newPropLtl
	newLTL->setData(pPropLtl->getCxCheckType(), negatedLtlStr, newCal1);

	// set initial state and check property
	cfgNode* initCFGNode = new cfgNode();
	_createInitSystemState(initCFGNode);
	initCFGNode->current_bound = 0;
	initCFGNode->bcs = 0;
	frontierStates.push_back(initCFGNode);

	short lastbd = 0;

	// start iterative deepen BFS exploration for computing CFG (which is to be encoded for CVC3)
	while (currentBound <= upBound)
	{
		if (bRet == false) 
		{
			break; // already found cx in the previous loop. Next, quit the while loop and release memory which is to be done at the end of the function.
		}

		newFrontierStates = _boundedBfsFromFrontierFlagCheck(vc, upBound, cx, varDetail, pPropLtl, currentBound, frontierStates);


	// if user wish to check deadlock, and there does be a deadlock, then cx should have been generated 
		if (*cx!=NULL) {break;}


	// for optimize multiple assignment
		// here should have been multiple assignment optimization,
		// however, once optimized, the above computing also is affected, so firstly copy the _process and then only use the copy when encoding

		//// (a) generate a copy of process
		//std::vector<CDataProcess> newProcess;
		//
		//for (size_t p=0; p<_process.size(); p++)
		//{
		//	CDataProcess tmp = *_process[p];
		//	_optimizeTransitionActionList(&tmp);
		//	newProcess.push_back(tmp);
		//}

		// clean the contents of the fileList.txt, since it contains the file names of the previous loop. actually, this can be replaced by openning fileList in another mode, but that will have to revise the out file 
		// function, which may affect other non interative deepen methods, so give up. anyway, this implementation is just for experiments and paper.
		// currently, choosing the simplest way -- removing the file
		DeleteFileA(listFileName);

		std::string settingInfoStr = _smtlib2LogicDeclareOutput(zipcModelType);

		// generate transition path information summarized by all the states of "std::list<cfgNode*> newFrontierStates"
		// ------- divide newFrontier into subsets w.r.t. predicates, then for each subsets, do the following

		/* this is just a test to see the path info before separation
		std::vector<tranInformation> tranInfo2CurrentBound2(currentBound+1); //must declare some elements first, otherwise can't index into it.
		_summarizePathToFrontierStates(newFrontier, tranInfo2CurrentBound2);
		*/

		// [0] declare necessary variables
		std::vector<CVC3::Expr> varExprVector;
		std::vector<CVC3::Expr> loopVarExprVector;
		std::vector<CVC3::Expr> inLoopExprVector;
		std::vector<statusValueMapVector> layersForInvalidNodes;  // no actually used
		std::vector<statusValueMapVector> layersForNormalNodes;  // no actually used
		std::vector<tranInformation> layersTranInfoInvalid; // no actually used 

		std::string initAssumptionStr="";
		std::string stepThresholdStr="";
		std::string stepVariableStr="";
		std::string stepAssumptionStr="";
		std::string stepFormulaVarStr="";
		std::string stepFormulaStr="";

		bool ltlGenerated = false; // this restricts that for each currentbound (multiple splitting predicates), only 1 ltl formula string is generated (which is time consuming)

		// _declareInitCVC3FlagAssumption(vc, 0, varExprVector); // this should not be commented, since variables declared will still be used by latter codes.
		initAssumptionStr = _smtlib2DeclareInitFlagAssumption(); // this is for output a string format formula for initial state

		// spliting the paths till this bound into clusters, and generate models for each cluster
		std::vector<std::vector<cfgNode*>> predStates = _newSeparateStatesSet(varDetail, newFrontierStates, isHierStm);
		for (size_t i=0; i<predStates.size(); i++)
		{
			if (predStates[i].size()!=0)
			{
				std::vector<tranInformation> tranInfo2CurrentBound(currentBound+1); // must declare some elements first, otherwise can't index into it.
				_summarizePathToFrontierStatesVectorVer(predStates[i], tranInfo2CurrentBound, externalProNum);
			
    // if for some depth within bound, no transition is executable, then actually deadlock. but since coming to this step means that user did not check the box "checking deadlock"
	// so my considertation is to reset the bound to the depth where no transitions.
	// NOTE: another idea is just to copy the cvc3 formula in k-1 until the bound. but this is boring, but need to carefully consider again.
				for (size_t nd=1; nd<tranInfo2CurrentBound.size(); nd++)// nd=0 means initial state
				{
					if (tranInfo2CurrentBound[nd].size()==0)
					{
						currentBound = nd-1; // nd-1 guarantees that only steps till currentBound (before deadlock) will be encoded
						upBound = nd-2; // this random value nd-2 guarantees to quit while loop after checking till currentBound
						break;
					}
				}

				if (tranInfo2CurrentBound[1].size()!=0) // when no transition is executed, then this transInfo2CurrentBound contains empty vectors of tran names
				{
					// [1.1]---MODEL---: initial step

					// generate models etc for each predicates
					for (int bd=1; bd<=currentBound; bd++)
					{
						// [1.1]---MODEL VAR---
						stepVariableStr = _smtlib2GenerateStrForStepVar(bd);
						stepVariableStrHolder.insert(std::pair<int, std::string>(bd, stepVariableStr));					

						// [1.2]---MODEL---: step assumptions
						// CVC3::Expr stepAssumption = _declareStepCVC3FlagAssumptionOptimize(vc, bd, varExprVector, pPropLtl, layersForInvalidNodes, layersForNormalNodes, layersTranInfoInvalid, tranInfo2CurrentBound);
						// stepAssumptionStr = _smtlib2GenerateStrFromCVC3Expr(stepAssumption);
						// std::string stepAssumptionStr = _smtlib2StepAssumptionOptimizeOnceForAll(vc, bd, varExprVector, pPropLtl, layersForInvalidNodes, layersForNormalNodes, 
						//                                                                          layersTranInfoInvalid, tranInfo2CurrentBound);
						// comments 2013/11/10: actually this fun below is to use concrete values for the last bound, but effects are not good, so inside new ideas commented. thus same as above
						std::string stepAssumptionStr = _smtlib2StepAssumptionOptimizeOnceForAllLastBound(vc, bd, varExprVector, pPropLtl, layersForInvalidNodes, layersForNormalNodes, 
							                                                                     layersTranInfoInvalid, tranInfo2CurrentBound, predStates[i], externalProNum, isHierStm, currentBound);

						stepAssumptionStrHolder.insert(std::pair<int, std::string>(bd, stepAssumptionStr));
						//vc->assertFormula(stepAssumption);

						// [1.3]---MODEL---: threshold
						if (pPropLtl->getCxCheckType() != CE_THRESHOLD)
						{// only add threshold assumption when checking properties other than threshold property

							stepThresholdStr = _generateVarThresholdAssumption(bd, varDetail, pPropLtl);
							if (stepThresholdStr!="") // exist threshold declaration
							{
								// stepThresholdStr = _smtlib2GenerateStrFromCVC3Expr(thresholdExpr);
								stepThresholdStrHolder.insert(std::pair<int, std::string>(bd, stepThresholdStr));
							}
						}
						/*
						// [1.4]---Property---: LoopConstraints
						stepFormulaVarStr = _smtlib2GenerateStrForStepLTLVar(bd);
						stepFormulaVarStrHolder.insert(std::pair<int, std::string>(bd, stepFormulaVarStr));

						if (bd==currentBound && ltlGenerated == false)
						{
							std::string loopConstraints = _smtlib2LoopFlagConstraintsOnceForAll(bd, stateEqBase);
							std::string ltlFormulaStr = _smtlib2LTLEncodeHalfDone(bd, newLTL, lastbd); // 2013/7/15
							lastbd = bd; // this info is used in the ltl encode function

							// loopConstraints = "\n\n(assert " + loopConstraints + ") \n\n";
							loopConstraints = "\n\n(define-fun LPC () Bool " + loopConstraints + ")\n\n";
							stepLoopConstraintStrHolder.insert(std::pair<int, std::string>(bd, loopConstraints));
							ltlFormulaStr = "\n\n " + ltlFormulaStr + "\n\n";
							stepFormulaStrHolder.insert(std::pair<int, std::string>(bd, ltlFormulaStr));			

							ltlGenerated = true;
						}
						*/
					}
				}

				// output smtlib2 files
				// multicore test: _smtlib2OutputFiles(initAssumptionStr, listFileName, currentBound, i);
				_multiCoreTestSmtlib2OutputFiles(initAssumptionStr, listFileName, currentBound, i, zipcModelType);
				// But note, also generate multiple files, but checked later one by one.
				// _noMultiCoreTestSmtlib2OutputFiles(initAssumptionStr, listFileName, currentBound, i, zipcModelType);

				tranInfo2CurrentBound.clear();
			}
			else // there exist possibilities that no states satisifes a path predicate
			{
				continue;
			}

			// since the following will be generated again for another "currentBound"
			varExprVector.clear();
			loopVarExprVector.clear();
			inLoopExprVector.clear();
			stepThresholdStrHolder.clear();
			stepAssumptionStrHolder.clear();
			stepVariableStrHolder.clear();
		}

		// checking the files using cvc4
		// NOTE: in the future, if hope to generate all smtlib2 files, and then cvc4, the following operation should be moved out of the while loop
		//multicore test: bRet = _smtlib2GenerateCmdCVC3CheckingResult(pPropLtl, propID, cx, listFileName, varDetail);			
		bRet = _newMultiCoreTestSmtlib2GenerateCmdCVC3CheckingResult(pPropLtl, propID, cx, listFileName, varDetail);	
		// bRet = _multiCoreTestSmtlib2GenerateCmdCVC3CheckingResult(pPropLtl, propID, cx, listFileName, varDetail);	
		// bRet = _smtlib2GenerateCmdCVC3CheckingResult(pPropLtl, propID, cx, listFileName, varDetail, zipcModelType);	

		stepFormulaVarStrHolder.clear(); // since each currentbound only generate ltl formula string once, so can only clear at this point
		stepFormulaStrHolder.clear();

		// other vectors should also be cleared
		if (*cx!=NULL){break;} // already found cx

		// remove the set of states in current frontierStates. This should be done b/c its/their successors have been checked. its/their hash value has been saved as visited
		
		for(int j = 0; j < toBeRemoved.size(); j++) {
			int i = lookupMap[toBeRemoved[j]];
			std::vector<cfgNode*>::iterator tmpIt1 = predStates[i].begin();
			for (; tmpIt1!=predStates[i].end(); tmpIt1++)
			{
				cfgNode* tmpNode = static_cast<cfgNode*>(*tmpIt1);
				std::list<cfgNode*>::iterator tmpIt2 = std::find(newFrontierStates.begin(), newFrontierStates.end(), tmpNode);
				if (tmpIt2 != newFrontierStates.end())
				{
					cfgNode* tmpNode2 = static_cast<cfgNode*>(*tmpIt2);
					if (tmpNode2 != 0)
					{
						delete[] tmpNode2->sysVariable;
						delete tmpNode2;
						tmpNode2 = 0;
					}
					newFrontierStates.erase(tmpIt2);
				}
			}
		}

		toBeRemoved.clear();
		lookupMap.clear();
		
		std::list<cfgNode*>::iterator tmpIt = frontierStates.begin();
		for (; tmpIt!=frontierStates.end(); tmpIt++)
		{
			cfgNode* tmpNode = static_cast<cfgNode*>(*tmpIt);
			if (tmpNode != 0)
			{
				delete[] tmpNode->sysVariable;
				delete tmpNode;
				tmpNode = 0;
			}
		}

		// if already found cx, break (not go into the next bounds)
		if (*cx!=NULL) 
		{
			bRet = false;
			break;
		}

		// if newFrontier set is empty
		if (newFrontierStates.empty()) // two reasons: (1) deadlock happened, (2) all the states has been visited
		{
			// the deadlock case should be further considered: whether user has choose to check deadlock
			bRet = true;
			// Memo: the first deadlock possibility has been dismissed, b/c if deadlock, then can't come here, directly quit.
		}
		else
		{

			if (boundIncFlg) 
			{
				break;
			} // the states upBound 

			if (currentBound == upBound) {break;} // all states within the upbound have been checked.

			if ((currentBound + iterativeIncNum) > upBound)
			{
				currentBound = upBound;
				boundIncFlg = true; // the upper bound has already been carefully handled once. thus, next time
			}
			else 
			{
				currentBound = currentBound + iterativeIncNum;
			}
			frontierStates = newFrontierStates;
			newFrontierStates.clear();
		}
	}

// delete all explicit states that may still possibly exists ---------
	std::list<cfgNode*>::iterator it2 = newFrontierStates.begin();
	for (; it2!=newFrontierStates.end(); it2++)
	{
		cfgNode* tS2 = static_cast<cfgNode*>(*it2);
		if (tS2 != 0)
		{
			delete[] tS2->sysVariable;
			delete tS2;
			tS2 = 0;
		}
	}
// ----------------------------------------------------------	

	newLTL = NULL;
	delete newLTL;
	delete ltltree;


	stepThresholdStrHolder.clear();
	stepAssumptionStrHolder.clear();
	stepFormulaStrHolder.clear();
	stepVariableStrHolder.clear();
	stepFormulaVarStrHolder.clear();
	stepLoopConstraintStrHolder.clear(); 

	dumpLog("*** _ltlPropertyFlagCheck end ***\n");	// LOG_FOR_BOUND
	return bRet;
}