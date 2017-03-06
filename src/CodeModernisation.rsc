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
import String;

alias OFG = rel[loc from, loc to]; //OFG alias
//Declare variables
private M3 projectM3;
private Program projectProgram;
private OFG ofg;
private OFG propagatedOfg;
private list[Edge] ofgEdges;
private list[Edge] propagatedOfgEdges;
private set[str] ofgNodes = {};
private set[str] propagatedOfgNodes = {};
private list[Edge] interfaceEdges;

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
//Container Classes
//These classes variables should be modified 
set[str] containerClasses =  {
     "/java/util/Map"
    ,"/java/util/HashMap"
    ,"/java/util/Collection"
    ,"/java/util/Set"
    ,"/java/util/HashSet"
    ,"/java/util/LinkedHashSet"
    ,"/java/util/List"
    ,"/java/util/ArrayList"
    ,"/java/util/LinkedList"
};

//A main entry to invoke all procedure
//It invokes all other stuffs
public void getAdvises() {
//TODO: Add sub methods
	createM3AndFlowProgram(|project://eLib|); //TODO: make it more generic
	//buildGraph(getProgram()); //BuildOFG
	propagatedOfg = propagate(getOfg());
	ofgEdges = makeOfgEdges();
	propagatedOfgEdges = makePropagatedOfgEdges();
	makeOfgNodes();
	makePropagatedOfgNodes();
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
    //initialEdgesOFG(getProgram());
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
    + { <cs + "this", x> | newAssign(x, _, cs, _) <- p.statements }
    + { <y, x> | assign(x, _, y) <- p.statements} 
    + { <as[i], fps[i]> | call(_, _, _, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) } 
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

//Get all edges of OFG
private list[Edge] makeOfgEdges() {
    return [edge("<to>", "<from>") | <from,to> <- getOfg() ];
}
//Get all edges of propagated OFG
private list[Edge] makePropagatedOfgEdges() {
    return [edge("<to>", "<from>") | <from,to> <- getPropagatedOfg() ];
}
//Store all OFG nodes
private void makeOfgNodes() {
    for (e <- ofgEdges) {
        ofgNodes += e.from;
        ofgNodes += e.to;
    }
}
//Store all propagated OFG nodes
private void makePropagatedOfgNodes() {
    for (e <- propagatedOfgEdges) {
        propagatedOfgNodes += e.from;
        propagatedOfgNodes += e.to;
    }
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
public OFG getPropagatedOfg() {
    return propagatedOfg;
}
public list[Edge] getOfgEdges() {
    return ofgEdges;
}
public list[Edge] getPropagatedOfgEdges() {
    return propagatedOfgEdges;
}
public list[str] getOfgNodes() {
    return toList(ofgNodes);
}
public list[str] getOfgNodes() {
    return toList(propagatedOfgNodes);
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

//Check ofg edges, such that field flows to Classes
//Indicates that data flows to/from that class
public void checkOfg(list[Edge] edges) {
    for (e <- edges) {
        if (contains(e.from, "class") && contains(e.to, "field")) {
            println(e);
        }
    }
}


//Propagation algorithm
//applies the propagation algorithm either forward or backwards, to obtain hidden relations.
private OFG propagate(OFG ofg) {
  rel[loc, loc] genFor;
  rel[loc, loc] genBack;
  genFor = { <constr + "this", class> | newAssign(_, class, constr, _) <- getProgram().statements, constructor(constr, _) <- getProgram().decls };
  genBack = { <x, caller> | assign(y, caller, x) <- getProgram().statements, caller != emptyId}
        + { <m + "return", caller> | call(caller, _, _, m, _) <- getProgram().statements, caller != emptyId};
  //if (!back) {
  //  gen = { <constr + "this", class> | newAssign(_, class, constr, _) <- prog.statements, constructor(constr, _) <- prog.decls };
  //  //gen = genFor;
  //}
  //else {
  //  //gen = { <s, ca> | assign(t, ca, s) <- prog.statements, ca != emptyId }
  //  //  + { <m + "return", ca> | call(t, ca, _, m, _) <- prog.statements, ca != emptyId };
  //  gen = genBack;
  //}
    
  OFG IN = { };
  OFG OUTFor = genFor;
  OFG OUTBack = genBack;
  
  invertedOfg = { <to,from> | <from, to> <- ofg};
  set[loc] pred(loc n) = invertedOfg[n];
  set[loc] succ(loc n) = ofg[n];
      
  solve (IN, OUTFor) {
    IN = { <n,\o> | n <- carrier(ofg), x <- (pred(n)), \o <- OUTFor[x] };
    OUTFor = genFor + IN;
  }
  solve (IN, OUTBack) {
    IN = { <n,\o> | n <- carrier(ofg), x <- (succ(n)), \o <- OUTBack[x] };
    OUTBack = genBack + IN;
  }
  
  return OUTFor + OUTBack;           
}




    


