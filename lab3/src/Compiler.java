import java.util.*;
import CPP.Absyn.*;

public class Compiler {


 // The output of the compiler is a list of strings.
 LinkedList < String > output;

 public HashMap < String, String > signature = new HashMap < String, String > ();;
 public LinkedList < HashMap < String, Integer >> variables = new LinkedList < HashMap < String, Integer >> ();;
 Integer variableCounter = 0;
 Integer labelCounter = 0;
 String className = "";


 ///////////////////////////////////////////////////////////////////////////////////////

 //Adds function to signatures 
 public void addFun(DFun function) {
  Type functionType = function.type_;
  String functionName = function.id_;
  ListArg functionArgs = function.listarg_;

  String type = "(";
  for (Arg a: functionArgs) {
   ADecl tmp = (ADecl) a;
   if (tmp.type_ instanceof Type_int) {
    type = type + "I";
   } else if (tmp.type_ instanceof Type_bool) {
    type = type + "Z";
   } else if (tmp.type_ instanceof Type_void) {
    type = type + "V";
   }

  }
  type = type + ")";

  if (functionType instanceof Type_int) {
   type = type + "I";
  } else if (functionType instanceof Type_bool) {
   type = type + "Z";
  } else if (functionType instanceof Type_void) {
   type = type + "V";
  }
  signature.put(functionName, type);


 }
 ///////////////////////////////////////////////////////////////////////////////////////

 // Compile C-- AST to a .j source file (returned as String).
 // name should be just the class name without file extension.
 public String compile(String name, CPP.Absyn.Program p) {


  // Initialization of the output
  output = new LinkedList();
  className = name;
  pushBlock();
  // Output boilerplate
  output.add(".class public " + name);
  output.add(".super java/lang/Object");
  output.add("");
  output.add(".method public <init>()V");
  output.add("  .limit locals 500");
  output.add("  .limit stack  500");
  output.add("");
  output.add("  aload_0");
  output.add("  invokespecial java/lang/Object/<init>()V");
  output.add("  return");
  output.add("");
  output.add(".end method");
  output.add("");
  output.add(".method public static main([Ljava/lang/String;)V");
  output.add("  .limit locals 500");
  output.add("  .limit stack  500");
  output.add("");
  output.add("  invokestatic " + name + "/main()I");
  output.add("  pop");
  output.add("  return");
  output.add("");
  output.add(".end method");
  output.add("");

  PDefs defs = (PDefs) p;
  ListDef listOfDefs = defs.listdef_;

  //Symbol table.
  for (Def def: listOfDefs) {
   def.accept(new InitializeSymTable(), null);
  }

  for (Def def: listOfDefs) {
   def.accept(new Compile(), null);
  }

  // Concatenate strings in output to .j file content.
  StringBuilder jtext = new StringBuilder();
  for (String s: output) {
   jtext.append(s + "\n");
  }
  return jtext.toString();
 }

 ///////////////////////////////////////////////////////////////////////////////////////

 private class InitializeSymTable implements Def.Visitor < Void, Void > {
  public Void visit(DFun fun, Void arg) {

   addFun(fun);
   return null;
  }
 }

 ///////////////////////////////////////////////////////////////////////////////////////

 private class Compile implements Def.Visitor < Void, Void > {
  public Void visit(DFun fun, Void arg) {
   pushBlock();
   Type functionType = fun.type_;
   String functionName = fun.id_;
   ListArg functionArgs = fun.listarg_;
   ListStm functionStms = fun.liststm_;

   //Checks the declaration of main
   String signature = getSignature(functionName);

   output.add(".method public static " + functionName + signature);
   output.add(".limit locals 500");
   output.add(".limit stack 500");
   for (Arg a: functionArgs) {
    a.accept(new ArgVisitor(), arg);
   }
   //Checks all statement in the function
   for (Stm st: functionStms) {
    st.accept(new StmVisitor(), arg);
   }
   if (functionType instanceof Type_void) {
    output.add("return");
   }
   popBlock();
   output.add("nop");
   output.add(".end method");
   return null;
  }
 }

 ///////////////////////////////////////////////////////////////////////////////////////

 private class ArgVisitor implements Arg.Visitor < Void, Void > {
  public Void visit(ADecl a, Void arg) {
   addVar(a.id_);
   return null;
  }
 }

 ///////////////////////////////////////////////////////////////////////////////////////

 private class StmVisitor implements Stm.Visitor < Void, Void > {
  public Void visit(SDecls p, Void arg) {
   for (String id: p.listid_) {
    addVar(id);
   }
   return null;
  }
  public Void visit(SExp p, Void arg) {
   p.exp_.accept(new ExpVisitor(), arg);
   if (!(output.getLast().charAt(output.getLast().length() - 1) == 'V')) {
    output.add("pop");
   }
   return null;
  }
  public Void visit(SIfElse p, Void arg) {
   String trueLabel = getLabel();
   String endLabel = getLabel();

   p.exp_.accept(new ExpVisitor(), arg);
   output.add("iconst_1");
   output.add("if_icmpeq " + trueLabel);
   pushBlock();
   p.stm_2.accept(new StmVisitor(), arg);
   popBlock();
   output.add("goto " + endLabel);
   output.add(trueLabel + ":");
   pushBlock();
   p.stm_1.accept(new StmVisitor(), arg);
   popBlock();
   output.add(endLabel + ":");

   return null;
  }
  public Void visit(SBlock p, Void arg) {
   pushBlock();
   for (Stm stm: p.liststm_) {
    stm.accept(new StmVisitor(), arg);
   }
   popBlock();
   return null;
  }
  public Void visit(SInit p, Void arg) {
   addVar(p.id_);
   p.exp_.accept(new ExpVisitor(), arg);
   output.add("istore " + getReg(p.id_));
   return null;
  }
  public Void visit(SReturn p, Void arg) {
   p.exp_.accept(new ExpVisitor(), arg);
   output.add("ireturn");
   return null;
  }
  public Void visit(SWhile p, Void arg) {
   String startLabel = getLabel();
   String endLabel = getLabel();
   output.add(startLabel + ":");
   p.exp_.accept(new ExpVisitor(), arg);
   output.add("iconst_0");
   output.add("if_icmpeq " + endLabel);
   pushBlock();
   p.stm_.accept(new StmVisitor(), arg);
   popBlock();
   output.add("goto " + startLabel);
   output.add(endLabel + ":");

   return null;
  }
 }

 ///////////////////////////////////////////////////////////////////////////////////////

 private class ExpVisitor implements Exp.Visitor < Void, Void > {

  public Void visit(EInt p, Void arg) {
   if (p.integer_ <= 5) {
    output.add("iconst_" + p.integer_.toString());
   } else {
    output.add("ldc " + p.integer_.toString());
   }
   return null;
  }

  public Void visit(EDouble p, Void arg) {
   return null;
  }

  public Void visit(EFalse p, Void arg) {
   output.add("iconst_0");

   return null;
  }

  public Void visit(EId p, Void arg) {
   Integer register = getReg(p.id_);
   output.add("iload " + register.toString());

   return null;
  }

  public Void visit(ETrue p, Void arg) {
   output.add("iconst_1");
   return null;
  }

  public Void visit(EPlus p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("iadd");
   return null;
  }

  public Void visit(EAnd p, Void arg) {
   String falseLabel = getLabel();
   output.add("iconst_0");
   p.exp_1.accept(new ExpVisitor(), arg);
   output.add("ifeq " + falseLabel);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("ifeq " + falseLabel);
   output.add("pop");
   output.add("iconst_1");
   output.add(falseLabel + ":");
   return null;
  }

  public Void visit(EApp p, Void arg) {
   pushBlock();

   if (p.id_ == "readInt") {
    output.add("invokestatic Runtime/readInt()I");
   } else if (p.id_ == "printInt") {
    for (Exp exp: p.listexp_) {
     exp.accept(new ExpVisitor(), arg);
    }
    output.add("invokestatic Runtime/printInt(I)V");

   } else {
    for (Exp exp: p.listexp_) {
     exp.accept(new ExpVisitor(), arg);
    }
    output.add("invokestatic " + className + "/" + p.id_ + getSignature(p.id_));
   }
   popBlock();

   return null;
  }

  public Void visit(EAss p, Void arg) {
   Integer reg = getReg(p.id_);
   p.exp_.accept(new ExpVisitor(), arg);
   output.add("istore " + reg);
   output.add("iload " + reg);
   return null;

  }

  public Void visit(EDiv p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("idiv");
   return null;

  }

  public Void visit(EEq p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmpeq " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;

  }

  public Void visit(EGt p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmpgt " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;

  }

  public Void visit(EGtEq p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmpge " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;
  }

  public Void visit(ELt p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmplt " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;

  }

  public Void visit(ELtEq p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmple " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;

  }

  public Void visit(EMinus p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("isub");

   return null;

  }

  public Void visit(ENEq p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);

   String label1 = getLabel();
   String label2 = getLabel();
   output.add("if_icmpne " + label1);
   output.add("iconst_0");
   output.add("goto " + label2);
   output.add(label1 + ":");
   output.add("iconst_1");
   output.add(label2 + ":");

   return null;

  }

  public Void visit(EOr p, Void arg) {
   String trueLabel = getLabel();
   output.add("iconst_1");
   p.exp_1.accept(new ExpVisitor(), arg);
   output.add("ifne " + trueLabel);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("ifne " + trueLabel);
   output.add("pop");
   output.add("iconst_0");
   output.add(trueLabel + ":");

   return null;

  }

  public Void visit(EPostDecr p, Void arg) {
   Integer reg = getReg(p.id_);

   output.add("iload " + reg);
   output.add("iload " + reg);
   output.add("iconst_1");
   output.add("isub");
   output.add("istore " + reg);

   return null;

  }

  public Void visit(EPostIncr p, Void arg) {
   Integer reg = getReg(p.id_);

   output.add("iload " + reg);
   output.add("iload " + reg);
   output.add("iconst_1");
   output.add("iadd");
   output.add("istore " + reg);

   return null;

  }

  public Void visit(EPreDecr p, Void arg) {
   Integer reg = getReg(p.id_);

   output.add("iload " + reg);
   output.add("iconst_1");
   output.add("isub");
   output.add("istore " + reg);
   output.add("iload " + reg);

   return null;

  }

  public Void visit(EPreIncr p, Void arg) {
   Integer reg = getReg(p.id_);

   output.add("iload " + reg);
   output.add("iconst_1");
   output.add("iadd");
   output.add("istore " + reg);
   output.add("iload " + reg);

   return null;

  }

  public Void visit(ETimes p, Void arg) {
   p.exp_1.accept(new ExpVisitor(), arg);
   p.exp_2.accept(new ExpVisitor(), arg);
   output.add("imul");

   return null;

  }
 }

 //////////////////////////////////Exp / Type shape ///////////////////////////////////////////

 public String getSignature(String id) {
  if (signature.containsKey(id)) {
   return signature.get(id);
  }
  throw new RuntimeException(id + "is not defined");
 }

 public void addVar(String id) {
  if (variables.peek().containsKey(id)) {
   throw new RuntimeException(id + "is not defined");
  }
  variables.peek().put(id, variableCounter);
  variableCounter++;
 }

 public String getLabel() {
  labelCounter++;
  return ("L" + labelCounter.toString());

 }
 public Integer getReg(String id) {
  for (HashMap < String, Integer > scope: variables) {
   if (scope.containsKey(id)) {
    return (scope.get(id));

   }
  }

  throw new RuntimeException(id + "is not defined");
 }
 public void pushBlock() {
  variables.addFirst(new HashMap < String, Integer > ());
 }
 public void popBlock() {
  HashMap < String, Integer > poppedScope = variables.removeFirst();
  variableCounter -= poppedScope.size();
 }

}
