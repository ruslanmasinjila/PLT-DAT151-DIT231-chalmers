import CPP.Absyn.*;
import java.util.*;

public class TypeChecker {

// Function types
public class FunType {
  final Type returnType;
  final ListArg args;
  public FunType (Type t, ListArg l) {
    returnType = t;
    args = l;
  }
}

 // Global signature of functions
 private HashMap < String, FunType > signature;

 // Stack of contexts
 private LinkedList < HashMap < String, Type >> contexts;

 // Return type of function we are checking
 private Type returnType;

 // Share type constants
 public final Type BOOL = new Type_bool();
 public final Type INT = new Type_int();
 public final Type DOUBLE = new Type_double();
 public final Type VOID = new Type_void();

 // Entry point

 public void typecheck(Program p) {
  p.accept(new ProgramVisitor(), null);
 }

 ////////////////////////////// Program //////////////////////////////

 public class ProgramVisitor implements Program.Visitor < Void, Void > {
  public Void visit(CPP.Absyn.PDefs p, Void arg) {
   // Put primitive functions into signature
   signature = new HashMap < String, FunType > ();
   signature.put("printInt", new FunType(VOID, singleArg(INT)));
   signature.put("readInt", new FunType(INT, new ListArg()));


   // TODO: other primitive functions
   signature.put("printDouble", new FunType(VOID, singleArg(DOUBLE)));
   signature.put("readDOUBLE", new FunType(DOUBLE, new ListArg()));

   // Extend signature by all the definitions
   for (Def d: p.listdef_) {
    d.accept(new DefIntoSigVisitor(), null);
   }

   // Check definitions
   for (Def d: p.listdef_) {
    d.accept(new DefVisitor(), arg);
   }

   // TODO: Check for main
   FunType ft = signature.get("main");
   if (ft == null) throw new TypeException("function main undefined");
   if (!ft.returnType.equals(INT)) throw new TypeException("function main should return int");
   if (!ft.args.isEmpty()) throw new TypeException("function main does not take parameters");

   return null;
  }
 }

 public ListArg singleArg(Type t) {
  ListArg l = new ListArg();
  l.add(new ADecl(t, "x"));
  return l;
 }

 ////////////////////////////// Function //////////////////////////////

 public class DefIntoSigVisitor implements Def.Visitor < Void, Void > {

  public Void visit(CPP.Absyn.DFun p, Void arg) {
   // Check that name is not present already
   if (signature.get(p.id_) != null)
    throw new TypeException("Function " + p.id_ + " already defined");

   // Add function to signature
   FunType ft = new FunType(p.type_, p.listarg_);
   signature.put(p.id_, ft);

   return null;
  }
 }

 // Type check a function definition.

 public class DefVisitor implements Def.Visitor < Void, Void > {
  public Void visit(CPP.Absyn.DFun p, Void arg) {
   // set return type and initial contexts
   returnType = p.type_;
   contexts = new LinkedList < HashMap < String, Type >> ();
   contexts.add(new HashMap < String, Type > ());

   // add all function parameters to contexts

   pushBlock();

   for (Arg a: p.listarg_) {
    a.accept(new ArgVisitor(), arg);
   }

   addVar("return", returnType);

   // check function statements
   for (Stm s: p.liststm_) {
    s.accept(new StmVisitor(), arg);
   }

   popBlock();

   return null;
  }
 }

 ///////////////////////// Function argument /////////////////////////

 // Add a type declaration to the contexts
 public class ArgVisitor implements Arg.Visitor < Void, Void > {
  public Void visit(CPP.Absyn.ADecl p, Void arg) {
   isVoid(p.type_);
   addVar(p.id_, p.type_);
   return null;
  }
 }

 ////////////////////////////// Statement //////////////////////////////

 public class StmVisitor implements Stm.Visitor < Void, Void > {
  public Void visit(CPP.Absyn.SExp p, Void arg) {
   p.exp_.accept(new ExpVisitor(), arg);
   return null;
  }

  public Void visit(CPP.Absyn.SDecls p, Void arg) {
   for (String id: p.listid_) {
    isVoid(p.type_);
    addVar(id, p.type_);
   }
   return null;
  }

  public Void visit(CPP.Absyn.SInit p, Void arg) {

   Type t = p.exp_.accept(new ExpVisitor(), arg);
   check(p.type_, t);
   addVar(p.id_, p.type_);
   return null;
  }

  public Void visit(CPP.Absyn.SReturn p, Void arg) {
   Type t = p.exp_.accept(new ExpVisitor(), arg);
   check(returnType, t);
   //TODO AddVar?
   return null;
  }

  public Void visit(CPP.Absyn.SWhile p, Void arg) {
   Type t = p.exp_.accept(new ExpVisitor(), arg);
   check(BOOL, t);

   pushBlock();
   p.stm_.accept(new StmVisitor(), arg);
   popBlock();

   return null;
  }

  public Void visit(CPP.Absyn.SBlock p, Void arg) {

   pushBlock();
   for (Stm stm: p.liststm_)
    stm.accept(new StmVisitor(), arg);
   popBlock();

   return null;
  }

  public Void visit(CPP.Absyn.SIfElse p, Void arg) {

   Type t = p.exp_.accept(new ExpVisitor(), arg);
   check(BOOL, t);

   pushBlock();
   p.stm_1.accept(new StmVisitor(), arg);
   popBlock();

   pushBlock();
   p.stm_2.accept(new StmVisitor(), arg);
   popBlock();

   return null;
  }
 }

 ////////////////////////////// Expression //////////////////////////////

 public class ExpVisitor implements Exp.Visitor < Type, Void > {

  // Literals
  public Type visit(CPP.Absyn.ETrue p, Void arg) {
   return BOOL;
  }
  public Type visit(CPP.Absyn.EFalse p, Void arg) {
   return BOOL;
  }
  public Type visit(CPP.Absyn.EInt p, Void arg) {
   return INT;
  }
  public Type visit(CPP.Absyn.EDouble p, Void arg) {
   return DOUBLE;
  }

  // Variable
  public Type visit(CPP.Absyn.EId p, Void arg) {
   return lookupVar(p.id_);
  }

  // Function call
  public Type visit(CPP.Absyn.EApp p, Void arg) {
   // Make sure function is defined.
   FunType ft = signature.get(p.id_);
   if (ft == null)
    throw new TypeException("Undefined function " + p.id_);

   // Check arity
   if (ft.args.size() != p.listexp_.size())
    throw new TypeException("Function " + p.id_ + " not applied to correct number of arguments");

   // Check function arguments
   int i = 0;
   for (Exp e: p.listexp_) {
    ADecl a = (ADecl)(ft.args.get(i));
    check(a.type_, e.accept(new ExpVisitor(), arg));
    i++;
   }
   return ft.returnType;
  }

  // Increment, decrement

  public Type visit(CPP.Absyn.EPostIncr p, Void arg) {
   return numericType(lookupVar(p.id_));

  }

  public Type visit(CPP.Absyn.EPostDecr p, Void arg) {
   return numericType(lookupVar(p.id_));

  }
  public Type visit(CPP.Absyn.EPreIncr p, Void arg) {
   return numericType(lookupVar(p.id_));

  }
  public Type visit(CPP.Absyn.EPreDecr p, Void arg) {
   return numericType(lookupVar(p.id_));
  }

  // Arithmetical operators

  public Type visit(CPP.Absyn.ETimes p, Void arg) {
   Type t1 = numericType(p.exp_1.accept(new ExpVisitor(), arg));
   Type t2 = numericType(p.exp_2.accept(new ExpVisitor(), arg));
   check(t1, t2);
   return t1;
  }

  public Type visit(CPP.Absyn.EDiv p, Void arg) {
   Type t1 = numericType(p.exp_1.accept(new ExpVisitor(), arg));
   Type t2 = numericType(p.exp_2.accept(new ExpVisitor(), arg));
   check(t1, t2);
   return t1;
  }

  public Type visit(CPP.Absyn.EPlus p, Void arg) {
   Type t1 = numericType(p.exp_1.accept(new ExpVisitor(), arg));
   Type t2 = numericType(p.exp_2.accept(new ExpVisitor(), arg));
   check(t1, t2);
   return t1;
  }

  public Type visit(CPP.Absyn.EMinus p, Void arg) {
   Type t1 = numericType(p.exp_1.accept(new ExpVisitor(), arg));
   Type t2 = numericType(p.exp_2.accept(new ExpVisitor(), arg));
   check(t1, t2);
   return t1;
  }

  // Comparison operators

  public Type visit(CPP.Absyn.ELt p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   numericType(t1);
   numericType(t2);
   check(t1, t2);
   return BOOL;
  }

  public Type visit(CPP.Absyn.EGt p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   numericType(t1);
   numericType(t2);
   check(t1, t2);
   return BOOL;
  }

  public Type visit(CPP.Absyn.ELtEq p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   numericType(t1);
   numericType(t2);
   check(t1, t2);
   return BOOL;

  }

  public Type visit(CPP.Absyn.EGtEq p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   numericType(t1);
   numericType(t2);
   check(t1, t2);
   return BOOL;
  }

  // Equality operators

  public Type visit(CPP.Absyn.EEq p, Void arg) {

   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   check(t1, t2);
   return BOOL;

  }
  public Type visit(CPP.Absyn.ENEq p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   isVoid(t1);
   isVoid(t2);
   check(t1, t2);
   return BOOL;
  }

  // Logic operators

  public Type visit(CPP.Absyn.EAnd p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   check(t1, BOOL);
   check(t2, BOOL);
   return BOOL;
  }
  public Type visit(CPP.Absyn.EOr p, Void arg) {
   Type t1 = p.exp_1.accept(new ExpVisitor(), arg);
   Type t2 = p.exp_2.accept(new ExpVisitor(), arg);
   check(t1, BOOL);
   check(t2, BOOL);
   return BOOL;
  }

  // Assignaturenment
  public Type visit(CPP.Absyn.EAss p, Void arg) {
   Type t = lookupVar(p.id_);

   check(t, p.exp_.accept(new ExpVisitor(), arg));

   return t;
  }
 }

 ///////////////////////// Context handling /////////////////////////

 public void addVar(String id, Type typeCode) {


  if (contexts.getFirst().containsKey(id)) {
   throw new TypeException("Variable " + id + " already defined");
  } else {
   contexts.getFirst().put(id, typeCode);
  }
 }

 public void pushBlock() {
  contexts.add(0, new HashMap < String, Type > ());
 }
 public void popBlock() {
  contexts.remove(0);
 }

 public Type lookupVar(String x) {
  for (HashMap < String, Type > m: contexts) {
   Type t = m.get(x);
   if (t != null) return t;
  }
  throw new TypeException("unbound variable " + x);
 }

 ////////////////////////////// Exp / Type shape //////////////////////////////

 public String isVar(Exp e) {
  if (e instanceof EId) {
   return ((EId) e).id_;
  } else throw new TypeException("expected variable, found " + e);
 }

 public void check(Type t, Type u) {
  if (!t.equals(u))
   throw new TypeException("Expected type " + u + ", but found type " + t);
 }

 public void isVoid(Type t) {
  if (t.equals(VOID))
   throw new TypeException(t + ", is Void ");
 }

 public Type numericType(Type t) {
  if (!t.equals(INT) && !t.equals(DOUBLE))
   throw new TypeException("expected expression of numeric type");
  return t;
 }
 public void equalTypes(Type t1, Type t2) {
  if (!t1.equals(t2))
   throw new TypeException("expected types " + t1 + " and " + t2 + " to be equal");
 }

}
