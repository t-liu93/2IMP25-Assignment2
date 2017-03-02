module ConvertOFG

import IO;
import Set;
import List;
import lang::ofg::ast::FlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::flow::JavaToObjectFlow;
import analysis::flow::ObjectFlow;
import lang::ofg::ast::Java2OFG;
import Relation;
import vis::Figure;
import vis::Render;


//Declare variables
private M3 projectM3;
private Program projectProgram;

//Create M3 and a flow program
//Slides getting facts
public void createM3AndFlowProgram(loc projectLoc) {
    projectM3 = createM3FromEclipseProject(projectLoc);
    projectProgram = createOFG(projectLoc);
}

//Get private variables
public M3 getM3() {
    return projectM3;
}
public Program getProgram() {
    return projectProgram;
}

//Initial flow graph 
//According to slides "TipsAndTricks"
alias OFG = rel[loc from, loc to]; //OFG alias


