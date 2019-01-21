import CPP.Absyn.*;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Scanner;

abstract class Value {}

public class Interpreter {
 Scanner scanner = new Scanner(System.in);

 HashMap < String, Func > signature = new HashMap < String, Func > ();
 LinkedList < HashMap < String, Value >> context = new LinkedList < HashMap < String, Value >> ();;

 // Share type constants
 public final Type BOOL = new Type_bool();
 public final Type INT = new Type_int();
 public final Type DOUBLE = new Type_double();
 public final Type VOID = new Type_void();

 /**  Entry point for the interreter */
 public void interpret(Program p) {
  p.accept(new ProgramVisitor(), null);
 }


 public class ProgramVisitor implements Program.Visitor < Void, Void > {
  public Void visit(PDefs p, Void arg) {



   Func f = new Func();
   f.addArg("x");
   addFunc("printInt", f);
   f = new Func();
   f.addArg("x");
   addFunc("printDouble", f);
   f = new Func();
   addFunc("readInt", f);
   f = new Func();
   addFunc("readDouble", f);


   FirstDefPass fdp = new FirstDefPass();


   for (Def def: p.listdef_) {
    def.accept(fdp, arg);
   }


   pushBlock();

   DFun main = findFunc("main").func;
   main.accept(new DefinitionVisitor(), arg);

   popBlock();
   return null;
  }
 }


 public class FirstDefPass implements Def.Visitor < Void, Void > {
  public Void visit(DFun p, Void arg) {
   Func func = new Func(p);
   FirstArgPass fap = new FirstArgPass();
   for (Arg x: p.listarg_)
    func.addArg(x.accept(fap, null));
   addFunc(p.id_, func);
   return null;
  }
 }

 public class FirstArgPass implements Arg.Visitor < String, Void > {
  public String visit(ADecl p, Void v) {
   return p.id_;
  }
 }

 /************************************************************************************/
 /******************************************* Def ************************************/

 public class DefinitionVisitor implements Def.Visitor < Value, Void > {

  public Value visit(DFun p, Void arg) {
   StmVisitor stmExecuter = new StmVisitor();
   Value val = null;
   for (Stm stm: p.liststm_)
    if ((val = stm.accept(stmExecuter, arg)) != null) break;
   return val;
  }
 }

 /************************************************************************************/
 /*************************************** Statement **********************************/

 public class StmVisitor implements Stm.Visitor < Value, Void > {

  ExpVisitor evaluator = new ExpVisitor();

  public Value visit(SExp p, Void arg) {
   p.exp_.accept(evaluator, arg);
   return null;
  }
  public Value visit(SDecls p, Void arg) {
   for (String id: p.listid_)
    addVar(id, new Value(null, p.type_));
   return null;
  }
  public Value visit(SInit p, Void arg) {
   addVar(p.id_, p.exp_.accept(evaluator, arg));
   return null;
  }
  public Value visit(SReturn p, Void arg) {
   Value val = p.exp_.accept(evaluator, arg);
   return val;
  }
  public Value visit(SWhile p, Void arg) {
   Value cond = p.exp_.accept(evaluator, arg);
   while ((boolean)(cond.value)) {
    pushBlock();
    Value val = p.stm_.accept(this, arg);
    popBlock();
    if (val != null) return val;
    cond = p.exp_.accept(evaluator, arg);
   }
   return null;
  }
  public Value visit(SBlock p, Void arg) {
   pushBlock();
   Value val = null;
   for (Stm stm: p.liststm_)
    if ((val = stm.accept(this, arg)) != null) break;
   popBlock();
   return val;
  }
  public Value visit(SIfElse p, Void arg) {
   pushBlock();
   Value val = null;
   Value cond = p.exp_.accept(evaluator, arg);
   if ((boolean)(cond.value))
    val = p.stm_1.accept(this, arg);
   else
    val = p.stm_2.accept(this, arg);
   popBlock();
   return val;
  }
 }

 /************************************************************************************/
 /************************************** Expression **********************************/

 public class ExpVisitor implements Exp.Visitor < Value, Void > {

  final DefinitionVisitor definitionVisitor_ = new DefinitionVisitor();

  public Value visit(ETrue p, Void arg) {
   return new Value(true, BOOL);
  }
  public Value visit(EFalse p, Void arg) {
   return new Value(false, BOOL);
  }
  public Value visit(EInt p, Void arg) {
   return new Value(p.integer_, INT);
  }
  public Value visit(EDouble p, Void arg) {
   return new Value(p.double_, DOUBLE);
  }
  public Value visit(EId p, Void arg) {
   return findVar(p.id_);
  }
  public Value visit(EPostIncr p, Void arg) {
   Value newval = null;
   Value oldval = findVar(p.id_);
   if (oldval.isInt())
    newval = new Value((int)(oldval.value) + 1, INT);
   else if (oldval.isDouble())
    newval = new Value((double)(oldval.value) + 1, DOUBLE);
   updateVar(p.id_, newval);
   return oldval;
  }
  public Value visit(EPostDecr p, Void arg) {
   Value newval = null;
   Value oldval = findVar(p.id_);
   if (oldval.isInt())
    newval = new Value((int)(oldval.value) - 1, INT);
   else if (oldval.isDouble())
    newval = new Value((double)(oldval.value) - 1, DOUBLE);
   updateVar(p.id_, newval);
   return oldval;
  }
  public Value visit(EPreIncr p, Void arg) {
   Value newval = null;
   Value oldval = findVar(p.id_);
   if (oldval.isInt())
    newval = new Value((int)(oldval.value) + 1, INT);
   else if (oldval.isDouble())
    newval = new Value((double)(oldval.value) + 1, DOUBLE);
   updateVar(p.id_, newval);
   return newval;
  }
  public Value visit(EPreDecr p, Void arg) {
   Value newval = null;
   Value oldval = findVar(p.id_);
   if (oldval.isInt())
    newval = new Value((int)(oldval.value) - 1, INT);
   else if (oldval.isDouble())
    newval = new Value((double)(oldval.value) - 1, DOUBLE);
   updateVar(p.id_, newval);
   return newval;
  }
  public Value visit(ETimes p, Void arg) {
   Value newval = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && v2.isInt())
    newval = new Value((int)(v1.value) * (int)(v2.value), INT);
   else if (v1.isDouble() && v2.isDouble())
    newval = new Value((double)(v1.value) * (double)(v2.value), DOUBLE);
   return newval;
  }
  public Value visit(EDiv p, Void arg) {
   Value newval = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v2.isInt())
    if ((int)(v2.value) == 0) throw new RuntimeException("Cannot divide by 0");
    else newval = new Value((int)(v1.value) / (int)(v2.value), INT);
   if (v2.isDouble())
    if ((double)(v2.value) == 0) throw new RuntimeException("Cannot divide by 0");
    else newval = new Value((double)(v1.value) / (double)(v2.value), DOUBLE);
   return newval;
  }
  public Value visit(EPlus p, Void arg) {
   Value newval = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && v2.isInt())
    newval = new Value((int)(v1.value) + (int)(v2.value), INT);
   else if (v1.isDouble() && v2.isDouble())
    newval = new Value((double)(v1.value) + (double)(v2.value), DOUBLE);
   return newval;
  }
  public Value visit(EMinus p, Void arg) {
   Value newval = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && v2.isInt())
    newval = new Value((int)(v1.value) - (int)(v2.value), INT);
   else if (v1.isDouble() && v2.isDouble())
    newval = new Value((double)(v1.value) - (double)(v2.value), DOUBLE);
   return newval;
  }
  public Value visit(ELt p, Void arg) {
   Value val = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && (int)(v1.value) < (int)(v2.value)) return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) < (double)(v2.value)) return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(EGt p, Void arg) {
   Value val = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && (int)(v1.value) > (int)(v2.value))
    return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) > (double)(v2.value))
    return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(ELtEq p, Void arg) {
   Value val = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && (int)(v1.value) <= (int)(v2.value))
    return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) <= (double)(v2.value))
    return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(EGtEq p, Void arg) {
   Value val = null;
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isInt() && (int)(v1.value) >= (int)(v2.value))
    return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) >= (double)(v2.value))
    return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(EEq p, Void arg) {
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isBool() && (boolean)(v1.value) == (boolean)(v2.value))
    return new Value(true, BOOL);
   if (v1.isInt() && (int)(v1.value) == (int)(v2.value))
    return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) == (double)(v2.value))
    return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(ENEq p, Void arg) {
   Value v1 = p.exp_1.accept(this, arg);
   Value v2 = p.exp_2.accept(this, arg);
   if (v1.isBool() && (boolean)(v1.value) != (boolean)(v2.value))
    return new Value(true, BOOL);
   if (v1.isInt() && (int)(v1.value) != (int)(v2.value))
    return new Value(true, BOOL);
   if (v1.isDouble() && (double)(v1.value) != (double)(v2.value))
    return new Value(true, BOOL);
   else return new Value(false, BOOL);
  }
  public Value visit(EAnd p, Void arg) {
   Value v1 = p.exp_1.accept(this, arg);
   if ((boolean)(v1.value) == false)
    return new Value(false, BOOL);
   Value v2 = p.exp_2.accept(this, arg);
   if ((boolean)(v2.value) == false)
    return new Value(false, BOOL);
   return new Value(true, BOOL);
  }
  public Value visit(EOr p, Void arg) {
   Value v1 = p.exp_1.accept(this, arg);
   if ((boolean)(v1.value) == true)
    return new Value(true, BOOL);
   Value v2 = p.exp_2.accept(this, arg);
   if ((boolean)(v2.value) == true)
    return new Value(true, BOOL);
   return new Value(false, BOOL);
  }
  public Value visit(EAss p, Void arg) {
   Value val = p.exp_.accept(this, arg);
   updateVar(p.id_, val);
   return val;
  }
  public Value visit(EApp p, Void arg) {
   pushBlock();
   Func func = findFunc(p.id_);
   Value val = new Value(null, VOID);


   ArrayList < Value > argvalues = new ArrayList < Value > ();
   for (Exp exp: p.listexp_)
    argvalues.add(exp.accept(this, arg));
   for (int i = 0; i < argvalues.size(); ++i)
    addVar(func.argnames.get(i), argvalues.get(i));

   if (p.id_.equals("printInt")) {
    Value tmp = findVar(func.argnames.get(0));
    System.out.println((int)(tmp.value));
   } else if (p.id_.equals("printDouble")) {
    Value tmp = findVar(func.argnames.get(0));
    System.out.println((double)(tmp.value));
   } else if (p.id_.equals("readInt")) {
    val = new Value(scanner.nextInt(), INT);
   } else if (p.id_.equals("readDouble")) {
    val = new Value(scanner.nextDouble(), DOUBLE);
   } else
    val = func.func.accept(definitionVisitor_, arg);
   popBlock();
   return val;
  }
 }


 public class Value {

  Object value;
  Type type;

  public Value(Object val, Type type) {
   this.value = val;
   this.type = type;
  }
  public boolean isInt() {
   return type == INT;
  }
  public boolean isDouble() {
   return type == DOUBLE;
  }
  public boolean isBool() {
   return type == BOOL;
  }
 }

 public class Func {
  ArrayList < String > argnames;
  DFun func;

  public Func() {
   this.argnames = new ArrayList < String > ();
  }
  public Func(DFun func) {
   this.argnames = new ArrayList < String > ();
   this.func = func;
  }
  public void addArg(String arg) {
   argnames.add(arg);
  }
 }

 ///////////////////////// Context handling /////////////////////////
 public void pushBlock() {
  context.addFirst(new HashMap < String, Value > ());
 }
 public void popBlock() {
  context.removeFirst();
 }
 public Func findFunc(String id) {
  return signature.get(id);
 }
 public void addFunc(String id, Func func) {
  signature.put(id, func);
 }
 public void addVar(String id, Value val) {
  context.getFirst().put(id, val);
 }
 public Value findVar(String id) {
  Value val = null;
  for (HashMap < String, Value > scope: context) {
   val = scope.get(id);
   if (val != null && val.value == null) throw new RuntimeException("Variable" + id + "is not initialized");
   else if (val != null) break;
  }
  return val;
 }
 public void updateVar(String id, Value val) {
  for (HashMap < String, Value > scope: context) {
   if (scope.containsKey(id)) {
    scope.put(id, val);
    break;
   }
  }
 }

}
