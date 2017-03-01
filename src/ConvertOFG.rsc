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

//Create M3 and a flow program
M3 m = createM3FromEclipseProject(|project://eLib|);
Program p = createOFG(|project://eLib|);

//Initial flow graph 
//According to slides "TipsAndTricks"
alias OFG = rel[loc from, loc to]; //OFG alias
