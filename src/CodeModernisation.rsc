module CodeModernisation

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
private OFG ofg;

//A main entry to invoke all procedure
//It invokes all other stuffs
public void getAdvises(loc projectLoc) {
//TODO: Add sub methods
}

//Create M3 and a flow program
//Slides getting facts
public void createM3AndFlowProgram(loc projectLoc) {
    projectM3 = createM3FromEclipseProject(projectLoc);
    projectProgram = createOFG(projectLoc);
}

//Initial flow graph 
//According to slides "TipsAndTricks"
//Slightly changed from ObjectFlow.rsc
//In Jurgen Vinju's Github repository
//Apply theory of Figure 2.2 in Tonella
public void buildGraph(Program p) {
    ofg
    = { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) } 
    + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements } 
    + { <y, x> | assign(x, _, y) <- p.statements} 
    + { <as[i], fps[i]> | call(x, _, y, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) } 
    + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements } 
    + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
    ;
}

//Get private variables
public M3 getM3() {
    return projectM3;
}
public Program getProgram() {
    return projectProgram;
}
public OFG getOfg() {
    return ofg;
}


alias OFG = rel[loc from, loc to]; //OFG alias


    


