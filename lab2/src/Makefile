JAVAC=javac
JAVAC_FLAGS=-sourcepath .
JAVA=java
JAVA_FLAGS=
CUP=java_cup.Main
CUPFLAGS=-nopositions -expect 100
JLEX=JLex.Main
all: test

test: absyn CPP/Yylex.class CPP/PrettyPrinter.class CPP/Test.class CPP/ComposVisitor.class CPP/AbstractVisitor.class CPP/FoldVisitor.class CPP/AllVisitor.class CPP/parser.class CPP/sym.class CPP/Test.class

.PHONY: absyn

%.class: %.java
	${JAVAC} ${JAVAC_FLAGS} $^

absyn: CPP/Absyn/Program.java CPP/Absyn/PDefs.java CPP/Absyn/Def.java CPP/Absyn/DFun.java CPP/Absyn/ListDef.java CPP/Absyn/Arg.java CPP/Absyn/ADecl.java CPP/Absyn/ListArg.java CPP/Absyn/Stm.java CPP/Absyn/SExp.java CPP/Absyn/SDecls.java CPP/Absyn/SInit.java CPP/Absyn/SReturn.java CPP/Absyn/SWhile.java CPP/Absyn/SBlock.java CPP/Absyn/SIfElse.java CPP/Absyn/ListStm.java CPP/Absyn/Exp.java CPP/Absyn/ETrue.java CPP/Absyn/EFalse.java CPP/Absyn/EInt.java CPP/Absyn/EDouble.java CPP/Absyn/EId.java CPP/Absyn/EApp.java CPP/Absyn/EPostIncr.java CPP/Absyn/EPostDecr.java CPP/Absyn/EPreIncr.java CPP/Absyn/EPreDecr.java CPP/Absyn/ETimes.java CPP/Absyn/EDiv.java CPP/Absyn/EPlus.java CPP/Absyn/EMinus.java CPP/Absyn/ELt.java CPP/Absyn/EGt.java CPP/Absyn/ELtEq.java CPP/Absyn/EGtEq.java CPP/Absyn/EEq.java CPP/Absyn/ENEq.java CPP/Absyn/EAnd.java CPP/Absyn/EOr.java CPP/Absyn/EAss.java CPP/Absyn/ListExp.java CPP/Absyn/Type.java CPP/Absyn/Type_bool.java CPP/Absyn/Type_int.java CPP/Absyn/Type_double.java CPP/Absyn/Type_void.java CPP/Absyn/ListId.java
	${JAVAC} ${JAVAC_FLAGS} $^

CPP/Yylex.java: CPP/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} CPP/Yylex

CPP/sym.java CPP/parser.java: CPP/CPP.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} CPP/CPP.cup
	mv sym.java parser.java CPP/

CPP/Yylex.class: CPP/Yylex.java CPP/sym.java

CPP/sym.class: CPP/sym.java

CPP/parser.class: CPP/parser.java CPP/sym.java

CPP/PrettyPrinter.class: CPP/PrettyPrinter.java

clean:
	rm -f CPP/Absyn/*.class CPP/*.class

distclean: vclean

vclean:
	 rm -f CPP/Absyn/Program.java CPP/Absyn/PDefs.java CPP/Absyn/Def.java CPP/Absyn/DFun.java CPP/Absyn/ListDef.java CPP/Absyn/Arg.java CPP/Absyn/ADecl.java CPP/Absyn/ListArg.java CPP/Absyn/Stm.java CPP/Absyn/SExp.java CPP/Absyn/SDecls.java CPP/Absyn/SInit.java CPP/Absyn/SReturn.java CPP/Absyn/SWhile.java CPP/Absyn/SBlock.java CPP/Absyn/SIfElse.java CPP/Absyn/ListStm.java CPP/Absyn/Exp.java CPP/Absyn/ETrue.java CPP/Absyn/EFalse.java CPP/Absyn/EInt.java CPP/Absyn/EDouble.java CPP/Absyn/EId.java CPP/Absyn/EApp.java CPP/Absyn/EPostIncr.java CPP/Absyn/EPostDecr.java CPP/Absyn/EPreIncr.java CPP/Absyn/EPreDecr.java CPP/Absyn/ETimes.java CPP/Absyn/EDiv.java CPP/Absyn/EPlus.java CPP/Absyn/EMinus.java CPP/Absyn/ELt.java CPP/Absyn/EGt.java CPP/Absyn/ELtEq.java CPP/Absyn/EGtEq.java CPP/Absyn/EEq.java CPP/Absyn/ENEq.java CPP/Absyn/EAnd.java CPP/Absyn/EOr.java CPP/Absyn/EAss.java CPP/Absyn/ListExp.java CPP/Absyn/Type.java CPP/Absyn/Type_bool.java CPP/Absyn/Type_int.java CPP/Absyn/Type_double.java CPP/Absyn/Type_void.java CPP/Absyn/ListId.java CPP/Absyn/Program.class CPP/Absyn/PDefs.class CPP/Absyn/Def.class CPP/Absyn/DFun.class CPP/Absyn/ListDef.class CPP/Absyn/Arg.class CPP/Absyn/ADecl.class CPP/Absyn/ListArg.class CPP/Absyn/Stm.class CPP/Absyn/SExp.class CPP/Absyn/SDecls.class CPP/Absyn/SInit.class CPP/Absyn/SReturn.class CPP/Absyn/SWhile.class CPP/Absyn/SBlock.class CPP/Absyn/SIfElse.class CPP/Absyn/ListStm.class CPP/Absyn/Exp.class CPP/Absyn/ETrue.class CPP/Absyn/EFalse.class CPP/Absyn/EInt.class CPP/Absyn/EDouble.class CPP/Absyn/EId.class CPP/Absyn/EApp.class CPP/Absyn/EPostIncr.class CPP/Absyn/EPostDecr.class CPP/Absyn/EPreIncr.class CPP/Absyn/EPreDecr.class CPP/Absyn/ETimes.class CPP/Absyn/EDiv.class CPP/Absyn/EPlus.class CPP/Absyn/EMinus.class CPP/Absyn/ELt.class CPP/Absyn/EGt.class CPP/Absyn/ELtEq.class CPP/Absyn/EGtEq.class CPP/Absyn/EEq.class CPP/Absyn/ENEq.class CPP/Absyn/EAnd.class CPP/Absyn/EOr.class CPP/Absyn/EAss.class CPP/Absyn/ListExp.class CPP/Absyn/Type.class CPP/Absyn/Type_bool.class CPP/Absyn/Type_int.class CPP/Absyn/Type_double.class CPP/Absyn/Type_void.class CPP/Absyn/ListId.class
	 rm -f CPP/Absyn/*.class
	 rmdir CPP/Absyn/
	 rm -f CPP/Yylex CPP/CPP.cup CPP/Yylex.java CPP/VisitSkel.java CPP/ComposVisitor.java CPP/AbstractVisitor.java CPP/FoldVisitor.java CPP/AllVisitor.java CPP/PrettyPrinter.java CPP/Skeleton.java CPP/Test.java CPP/sym.java CPP/parser.java CPP/*.class
	rm -f Makefile
	rmdir -p CPP/

