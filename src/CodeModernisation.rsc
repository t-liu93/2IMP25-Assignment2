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
alias OFG = rel[loc from, loc to]; //OFG alias
//Since classes(m) cannot get basic classes
//Add a set to store all Java's basic classes
set[loc] basicClasses = {
    |java+class:///java/lang/Byte|, 
    |java+class:///java/lang/Character|, 
    |java+class:///java/lang/Short|, 
    |java+class:///java/lang/Integer|, 
    |java+class:///java/lang/Long|, 
    |java+class:///java/lang/Float|, 
    |java+class:///java/lang/Double|, 
    |java+class:///java/lang/String|
};

//A main entry to invoke all procedure
//It invokes all other stuffs
public void getAdvises() {
//TODO: Add sub methods
	createM3AndFlowProgram(|project://eLib|); //TODO: make it more generic
	buildGraph(getProgram());
	//println(declarations(getM3()));
	//for(cl <- classes(getM3())) {
	//set[loc] innerClassSet = { e | e <- m@containment[cl], isClass(e)};
	//println(innerClassSet);
	//}
}

//Create M3 and a flow program
//Slides getting facts
public void createM3AndFlowProgram(loc projectLoc) {
    projectM3 = createM3FromEclipseProject(projectLoc);
    projectProgram = createOFG(projectLoc);
    buildGraph(getProgram());
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

//OFG propagation - usage unkown
//In Jurgen Vinju's Github repository
public OFG prop(OFG g, rel[loc,loc] gen, rel[loc,loc] kill, bool back) {
  OFG IN = { };
  OFG OUT = gen + (IN - kill);
  gi = g<to,from>;
  set[loc] pred(loc n) = gi[n];
  set[loc] succ(loc n) = g[n];
  
  solve (IN, OUT) {
    IN = { <n,\o> | n <- carrier(g), p <- (back ? pred(n) : succ(n)), \o <- OUT[p] };
    OUT = gen + (IN - kill);
  }
  
  return OUT;
}

//Get all classes from M3
public set[loc] getClasses(M3 m) {
    set[loc] allClasses = classes(m);
    for (cl <- basicClasses) {
        allClasses += cl;
    }
    return allClasses;
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

public void write() {
	writeFile(|file:///D:/ofg.txt|, getOfg());
	writeFile(|file:///D:/m3.txt|, getM3());
	writeFile(|file:///D:/program.txt|, getProgram());
}

//Draw extends class diagram
public void drawExtendsClassDiagram(M3 m) {
  classFigures = [box(text("<cl.path[1..]>"), id("<cl>")) | cl <- classes(m)]; 
  edges = [edge("<to>", "<from>") | <from,to> <- m@extends ];  
  
  render("Extends Class Diagram", 
        scrollable(graph(classFigures, edges, hint("layered"), std(gap(10)), std(font("Bitstream Vera Sans")), std(fontSize(20)))));
}

//Draw type dependency diagram
public void drawTypeDependencyDiagram(M3 m) {
    figures = [box(text("<cl.path[1..]>"), id("<cl>")) | cl <- getClasses(m) ];
    edges = [edge("<to>", "<from>") | <from, to> <- m@typeDependency ];
    render("Type Dependency Diagram", 
            scrollable(graph(figures, edges, hint("layered"), std(gap(10)), std(font("Bitstream Vera Sans")), std(fontSize(20)))));
}
//in order to store M3 or Ofg as a string for parsing
public str M3ToString(M3 m) {
    writeFile(|tmp:///m3.txt|, m);
    return readFile(|tmp:///m3.txt|);
}
public str OfgToString(OFG ofg) {
    writeFile(|tmp:///ofg.txt|, ofg);
    return readFile(|tmp:///ofg.txt|);
}




    


