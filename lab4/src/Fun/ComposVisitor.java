package Fun;
import Fun.Absyn.*;
/** BNFC-Generated Composition Visitor
*/

public class ComposVisitor<A> implements
  Fun.Absyn.Program.Visitor<Fun.Absyn.Program,A>,
  Fun.Absyn.Main.Visitor<Fun.Absyn.Main,A>,
  Fun.Absyn.Def.Visitor<Fun.Absyn.Def,A>,
  Fun.Absyn.Exp.Visitor<Fun.Absyn.Exp,A>
{
/* Program */
    public Program visit(Fun.Absyn.Prog p, A arg)
    {
      ListDef listdef_ = new ListDef();
      for (Def x : p.listdef_)
      {
        listdef_.add(x.accept(this,arg));
      }
      Main main_ = p.main_.accept(this, arg);
      return new Fun.Absyn.Prog(listdef_, main_);
    }
/* Main */
    public Main visit(Fun.Absyn.DMain p, A arg)
    {
      Exp exp_ = p.exp_.accept(this, arg);
      return new Fun.Absyn.DMain(exp_);
    }
/* Def */
    public Def visit(Fun.Absyn.DDef p, A arg)
    {
      String ident_ = p.ident_;
      ListIdent listident_ = p.listident_;
      Exp exp_ = p.exp_.accept(this, arg);
      return new Fun.Absyn.DDef(ident_, listident_, exp_);
    }
/* Exp */
    public Exp visit(Fun.Absyn.EVar p, A arg)
    {
      String ident_ = p.ident_;
      return new Fun.Absyn.EVar(ident_);
    }    public Exp visit(Fun.Absyn.EInt p, A arg)
    {
      Integer integer_ = p.integer_;
      return new Fun.Absyn.EInt(integer_);
    }    public Exp visit(Fun.Absyn.EApp p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new Fun.Absyn.EApp(exp_1, exp_2);
    }    public Exp visit(Fun.Absyn.EAdd p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new Fun.Absyn.EAdd(exp_1, exp_2);
    }    public Exp visit(Fun.Absyn.ESub p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new Fun.Absyn.ESub(exp_1, exp_2);
    }    public Exp visit(Fun.Absyn.ELt p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new Fun.Absyn.ELt(exp_1, exp_2);
    }    public Exp visit(Fun.Absyn.EIf p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      Exp exp_3 = p.exp_3.accept(this, arg);
      return new Fun.Absyn.EIf(exp_1, exp_2, exp_3);
    }    public Exp visit(Fun.Absyn.EAbs p, A arg)
    {
      String ident_ = p.ident_;
      Exp exp_ = p.exp_.accept(this, arg);
      return new Fun.Absyn.EAbs(ident_, exp_);
    }
}