std::string CCreateCVC3Data::_smtlib2ConstructStepFormulaStrHolder3(int bound)
{
	std::string str1= "";
	int increment = 10;

	if(bound > increment) {
		str1= "(and";
		for (int i = 0; i <= bound - increment; i++) {
			stringstream ss;
			ss << " ";
			//ss << "(not (and  (= x13_" << i << " 1) (= x12_"<< i << " 0)))"; // [G]( speedCtl==1 => target!=0 )
			//ss << "(>= x16_" << i << " 0)"; //[G](stkSum >= 0)16 [G](s1 >= 0)17
			ss << "(< x10_" << i << " 9)"; //[G](dealCount < 4)
			//ss << "(not (and x3_" << bound << " (= x11_" << bound << " 0)))"; //[G](!(RequestProcessed && MainController == 0))
			//ss << "(< x2_" << i << " 5)"; //[G](c >= 0)
			//ss << "(>= x12_" << i << " 0)"; //[G](target >= 0)
			// ss << "(>= x1_" << i << " 0)";
			// [G]((vender==1 && xCoin && stkA==0 && stkB==0) => (coinRtn!=1))
			//ss << "(not (and (and (and (and (= x14_" << i << " 1) x8_" << bound << ") (= x11_" << i << " 0)) (= x12_" << i << " 0)) (= x9_" << i << " 1)))";
			str1 += ss.str();
		}
		str1 += ")";
	}

	stringstream ss;
	//ss << "(and (= x13_" << bound << " 1) (= x12_"<< bound << " 0))";
	//ss << "(< x16_" << bound << " 0)"; //[G](stkSum >= 0)
	ss << "(>= x10_" << bound << " 9) "; //[G](dealCount < 4)
	//ss << "(and x3_" << bound << " (= x11_"<< bound <<" 0))"; //[G](!(RequestProcessed && MainController == 0))
	//ss << "(>= x2_" << bound << " 5)"; //[G](c >= 0)
	//ss << "(>= x12_" << bound << " 0)"; //[G](target >= 0)
	// ss << "(< x1_" << bound << " 0)";
	//ss << "(and  (and  (and  (and  (= x14_" << bound << " 1) x8_" << bound << ")  (= x11_" << bound << " 0))  (= x12_" << bound << " 0))  (= x9_" << bound << " 1))";
	std::string str2 = ss.str();
	std::string str;
	if(bound > increment) {
		str = "(assert (! (and " + str1 +" "+ str2 +"):named PR))";
	} else {
		str = "(assert (! " + str2 + ":named PR))";
	}
	
	return str;
}

std::string CCreateCVC3Data::_smtlib2ConstructStepFormulaStrHolder4(int bound)
{
	std::string str1= "(or";
	for (int i = 0; i <= bound; i++) {
		stringstream ss;
		ss << " ";
		// ss << "(and (= x13_" << i << " 1) (= x12_"<< i << " 0))";
		//ss << "(< x16_" << i << " 0)"; //[G](stkSum >= 0)
		// ss << "(>= x10_" << i << " 4) "; //[G](dealCount < 4)
		// ss << "(and x3_" << i << " (= x11_"<< i <<" 0))"; //[G](!(RequestProcessed && MainController == 0))
		// ss << "(< x2_" << i << " 0)"; //[G](c >= 0)
		// ss << "(< x1_" << i << " 0)";
		str1 += ss.str();
	}
	str1 += ")";

	std::string str;

	str = "(assert (! " + str1 + ":named PR))";
	
	return str;
}