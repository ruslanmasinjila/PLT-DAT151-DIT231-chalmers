import java.util.*;
import Fun.Absyn.*;


class Interpreter {

 // Signature
 final Map < String, Exp > sig = new TreeMap();


 // Strategy
 final Strategy strategy;

 // Control debug printing.
 final boolean debug = false;

 public Interpreter(Strategy strategy) {
  this.strategy = strategy;
 }

 public void interpret(Program p) {
  System.out.println(p.accept(new ProgramVisitor(), null).intValue());
 }

 public class ProgramVisitor implements Program.Visitor < Value, Void > {
  public Value visit(Fun.Absyn.Prog p, Void arg) {

   // build signature
   for (Def d: p.listdef_) d.accept(new DefVisitor(), null);
   // execute main expression
   return p.main_.accept(new MainVisitor(), null);
  }
 }

 public class MainVisitor implements Main.Visitor < Value, Void > {
  public Value visit(Fun.Absyn.DMain p, Void arg) {
   return p.exp_.accept(new ExpVisitor(), new Empty());
  }
 }

 // visit defs only to build the signature.
 public class DefVisitor implements Def.Visitor < Void, Void > {
  public Void visit(Fun.Absyn.DDef p, Void arg) {
   // abstract over arguments from right to left
   Exp e = p.exp_;

   Collections.reverse(p.listident_);
   for (String x: p.listident_) e = new EAbs(x, e);

   // Add to signature
   sig.put(p.ident_, e);
   return null;
  }
 }

 class ExpVisitor implements Exp.Visitor < Value, Environment > {

  // variable
  public Value visit(EVar p, Environment env) {
   Value value = env.lookup(p.ident_);

   if (value != null) {
    return value;
   } else {
    Exp exp = sig.get(p.ident_);
    if (exp == null) {
     throw new RuntimeException("Unbound variable: " + p.ident_);
    }
    return exp.accept(new ExpVisitor(), new Empty());
   }
  }

  // literal
  public Value visit(EInt p, Environment env) {
   return new VInt(p.integer_);
  }

  //lambda
  public Value visit(EAbs p, Environment env) {

   return new VFun(p.ident_, p.exp_, env);

  }

  // application
  public Value visit(EApp p, Environment env) {

   Entry temp = new ValueEntry(new VInt(0));

   if (strategy == Strategy.CallByName) {
    temp = new CloseEntry(p.exp_2, env);

   } else {

    temp = new ValueEntry(p.exp_2.accept(new ExpVisitor(), env));

   }


   return (p.exp_1.accept(new ExpVisitor(), env)).apply(temp);



  }

  // plus
  public Value visit(EAdd p, Environment env) {
   Value u = p.exp_1.accept(new ExpVisitor(), env);
   Value v = p.exp_2.accept(new ExpVisitor(), env);

   return new VInt(u.intValue() + v.intValue());
  }

  // minus
  public Value visit(ESub p, Environment env) {
   Value u = p.exp_1.accept(new ExpVisitor(), env);
   Value v = p.exp_2.accept(new ExpVisitor(), env);

   return new VInt(u.intValue() - v.intValue());
  }

  // less-than
  public Value visit(ELt p, Environment env) {
   Value u = p.exp_1.accept(new ExpVisitor(), env);
   Value v = p.exp_2.accept(new ExpVisitor(), env);
   if (u.intValue() < v.intValue()) {
    return new VInt(1);
   }
   return new VInt(0);
  }

  // If
  public Value visit(EIf p, Environment env) {
   if (p.exp_1.accept(new ExpVisitor(), env).intValue() == 1) {
    return p.exp_2.accept(new ExpVisitor(), env);
   } else {
    return p.exp_3.accept(new ExpVisitor(), env);
   }
  }

 }

 // Environment ///////////////////////////////////////////////////////

 abstract class Environment {
  abstract Value lookup(String x);
 }

 class Empty extends Environment {
  Value lookup(String x) {
   return null;
  }
 }

 class Extend extends Environment {
  final Environment env;
  final String y;
  final Entry entry;

  Extend(String y, Entry entry, Environment env) {
   this.env = env;
   this.y = y;
   this.entry = entry;
  }
  Value lookup(String x) {
   if (x.equals(y)) return entry.value();
   else return env.lookup(x);
  }
 }

 // Environment entries ////////////////////////////////////////////////

 abstract class Entry {
  abstract Value value();
 }

 class ValueEntry extends Entry {
  final Value v;
  ValueEntry(Value v) {
   this.v = v;
  }
  Value value() {
   return v;
  }
 }

 class CloseEntry extends Entry {
  final Exp exp;
  final Environment env;
  CloseEntry(Exp exp, Environment env) {
   this.exp = exp;
   this.env = env;
  }
  Value value() {
   return exp.accept(new ExpVisitor(), env);
  }
 }

 // Value /////////////////////////////////////////////////////////////

 abstract class Value {
  abstract public int intValue();
  abstract public Value apply(Entry e);
 }

 private class VInt extends Value {
  final int val;
  public VInt(int i) {
   val = i;
  }

  public int intValue() {
   return val;
  }

  public Value apply(Entry e) {
   throw new RuntimeException("cannot apply integer value to argument");
  }
 }


 // Function values

 class VFun extends Value {
  final String x;
  final Exp body;
  final Environment env;

  VFun(String x, Exp body, Environment env) {
   this.x = x;
   this.body = body;
   this.env = env;
  }

  public int intValue() {
   throw new RuntimeException("VFun.intValue() is not possible");
  }
  public Value apply(Entry e) {
   return body.accept(new ExpVisitor(), new Extend(x, e, env));
  }
 }




}
