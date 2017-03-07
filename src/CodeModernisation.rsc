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
private M3 projectM3; //M3 from project
private Program projectProgram; //Program from project
private OFG ofg; //Project OFG
private OFG propagatedOfg; //Project OFG, propagated using propagation algorithm
private list[Edge] ofgEdges = []; //Stores the edges of original OFG
private list[Edge] propagatedOfgEdges = []; //Stores the edges of propagated OFG
private set[str] ofgNodes = {}; //Stores the nodes of OFG
private set[str] propagatedOfgNodes = {}; //Stores the nodes of propagated OFG
private list[Edge] interfaceEdges = []; //Stores 
private list[Edge] typeDependencies = []; //
private list[Edge] edgeToModify = []; //
private list[Edge] classDependency = [];
private list[Edge] declarations = [];
private lrel[str field, set[str] class, str interface, int counter] fieldRelation = [];

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
     "/java/util/Map", 
     "/java/util/HashMap", 
     "/java/util/Collection", 
     "/java/util/Set", 
     "/java/util/HashSet", 
     "/java/util/LinkedHashSet", 
     "/java/util/List", 
     "/java/util/ArrayList", 
     "/java/util/LinkedList"
};

//A main entry to invoke all procedure
//It invokes all other stuffs
public void getAdvises() {
    projectLocation = |project://eLib|; //TODO: remove this and add parameter to the method
    createM3AndFlowProgram(projectLocation); //Create OFG
    getEdgesAndNodes(); //Get all edges and nodes we need
    checkOfgInflow(getPropagatedOfgEdges()); 
    checkEdgeToModify(getEdgeToModify());
    //println(declarations(getM3()));
    //for(cl <- classes(getM3())) {
    //set[loc] innerClassSet = { e | e <- m@containment[cl], isClass(e)};
    //println(innerClassSet);
    //}
    //println(getEdgeToModify());
    //println(interfaceEdges);
    buildRelation(edgeToModify, interfaceEdges);
    println(fieldRelation);
    //println(declarations);
    //for (e <- getEdgeToModify()) {
    //   println(stringToField(e.from));
    //}
}

//Create M3 and a flow program
//Slides getting facts
private void createM3AndFlowProgram(loc projectLoc) {
    projectM3 = createM3FromEclipseProject(projectLoc);
    projectProgram = createOFG(projectLoc);
    ofg = buildGraph(getProgram()); //original OFG
    propagatedOfg = propagate(getOfg()); //propagatedOFG
}

//Get edges and nodes
//From ofg, propagated ofg and M3
private void getEdgesAndNodes() {
    ofgEdges = makeOfgEdges();
    propagatedOfgEdges = makePropagatedOfgEdges();
    makeOfgNodes();
    makePropagatedOfgNodes();
    typeDependencies = makeTypeDependencyEdges(getM3());
    interfaceEdges = makeDependencyWithInterface(getTypeDependencies());
    declarations = makeDeclarations(getM3());
}

//Check ofg edges, such that field flows to Classes
//Indicates that data flows to/from that class
private void checkOfgInflow(list[Edge] edges) {
    for (e <- edges) {
        if (contains(e.from, "class") && contains(e.to, "field")) {
            edgeToModify += e;
        }
    }
}

//We only care about the build-in Java containers
//i.e. uses an interface like Map, Collection, etc. 
private void checkEdgeToModify(list[Edge] edges) {
    list[Edge] temp = [];
    for (e <- edges) {
        for (t <- getTypeDependencies()) {
            if (e.to == t.to && contains(t.from, "interface")) {
                temp += e;
            }
        }
    }
    edgeToModify = temp;
}

//Initial flow graph 
//According to slides "TipsAndTricks"
//Slightly changed from ObjectFlow.rsc
//In Jurgen Vinju's Github repository
//Apply theory of Figure 2.2 in Tonella
private OFG buildGraph(Program p) {
    return { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) } 
    + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements } 
    + { <cs + "this", x> | newAssign(x, _, cs, _) <- p.statements }
    + { <y, x> | assign(x, _, y) <- p.statements} 
    + { <as[i], fps[i]> | call(_, _, _, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) } 
    + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements } 
    + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
    ;
}

//Propagation algorithm
//Both forward and backward
private OFG propagate(OFG ofg) {
    rel[loc, loc] genFor;
    rel[loc, loc] genBack;
    genFor = { <constr + "this", class> | newAssign(_, class, constr, _) <- getProgram().statements, constructor(constr, _) <- getProgram().decls };
    genBack = { <x, caller> | assign(y, caller, x) <- getProgram().statements, caller != emptyId}
            + { <m + "return", caller> | call(caller, _, _, m, _) <- getProgram().statements, caller != emptyId};
        
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
    return [edge("<to>", "<from>") | <from, to> <- getOfg() ];
}
//Get all edges of propagated OFG
private list[Edge] makePropagatedOfgEdges() {
    return [edge("<to>", "<from>") | <from, to> <- getPropagatedOfg() ];
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
//Store all m3 type dependency edges
private list[Edge] makeTypeDependencyEdges(M3 m) {
    list[Edge] dependency = [edge("<to>", "<from>") | <from, to> <- m@typeDependency ];
    for (e <- dependency) {
        if (! contains(e.to, "field")) {
            dependency -= e;
        }
    }
    return dependency;
}
//Store all m3 type dependency with interfaces
private list[Edge] makeDependencyWithInterface(list[Edge] typeDependency) {
    for (e <- typeDependency) {
        if (! contains(e.from, "interface")) {
            typeDependency -= e;
        }
    }
    return typeDependency;
}
//Store all m3 declarations
//Only with java+field
private list[Edge] makeDeclarations(M3 m) {
    list[Edge] declarations = [edge("<to>", "<from>") | <from, to> <- m@declarations ];
    list[Edge] declarationsOutput = [];
    for (d <- declarations) {
        if (! contains(d.to, "field")) {
            declarations -= d;
        }
    }
    for (d <- declarations) {
        for (e <- edgeToModify) {
            //println(e);
            if (e.to == d.to) {
                //println(e);
                declarationsOutput += d;
                break;
            }
        }
    }
    return declarationsOutput;
}

//Change the edge string to a e.g. class, interface, field name for correction
private str edgeToString(str edge) {
    int length = size(edge);
    int startIndex;
    int endIndex;
    str newString = "";
    for (int i <- [length - 1..0]) {
        if (! (charAt(edge, i) == 124)) {
            endIndex = i + 1;
            break;
        }
    }
    for (int i <- [length - 1..0]) {
        if (charAt(edge, i) == 47) {
            startIndex = i + 1;
            break;
        }
    }
    for (int j <- [startIndex..endIndex]) {
        newString += stringChar(charAt(edge, j));
    }
    return newString;
}

//Build relation of correction
//The relation includes the field that need to be modified, 
//The related class, i.e. value type
//The used interface and counter
private void buildRelation(list[Edge] edgeToModify, list[Edge] interfaceEdges) {
    lrel[str field, str class, str interface, int counter] tempRel = [];
    for (e <- edgeToModify) {
        //str field = edgeToString(e.to);
        str field = e.to;
        //str class = edgeToString(e.from);
        //str class = e.from;
        int counter = 1;
        str interface = "";
        for (i <- interfaceEdges) {
            if (e.to == i.to) {
                interface = edgeToString(i.from);
            }
        }
        for (r <- tempRel) {
            if (r.field == field) {
                counter = r.counter + 1;
            }
        }
        tempRel += <field, class, interface, counter>;
    }
    for (r <- tempRel) {
        set[str] class = {};
        if (r.counter == 1) {
            int counter = 0;
            for (t <- tempRel) {
                if (r.field == t.field) {
                    class += t.class;
                    counter += 1;
                }
            }
            fieldRelation += <r.field, class, r.interface, counter>;
        }
    }
}

//Generate suggestions

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
public list[str] getPropagatedOfgNodes() {
    return toList(propagatedOfgNodes);
}
public list[Edge] getTypeDependencies() {
    return typeDependencies;
}
public list[Edge] getEdgeToModify() {
    return edgeToModify;
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




    


