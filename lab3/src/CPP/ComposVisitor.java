package CPP;
import CPP.Absyn.*;
/** BNFC-Generated Composition Visitor
*/

public class ComposVisitor<A> implements
  CPP.Absyn.Program.Visitor<CPP.Absyn.Program,A>,
  CPP.Absyn.Def.Visitor<CPP.Absyn.Def,A>,
  CPP.Absyn.Arg.Visitor<CPP.Absyn.Arg,A>,
  CPP.Absyn.Stm.Visitor<CPP.Absyn.Stm,A>,
  CPP.Absyn.Exp.Visitor<CPP.Absyn.Exp,A>,
  CPP.Absyn.Type.Visitor<CPP.Absyn.Type,A>
{
/* Program */
    public Program visit(CPP.Absyn.PDefs p, A arg)
    {
      ListDef listdef_ = new ListDef();
      for (Def x : p.listdef_)
      {
        listdef_.add(x.accept(this,arg));
      }
      return new CPP.Absyn.PDefs(listdef_);
    }
/* Def */
    public Def visit(CPP.Absyn.DFun p, A arg)
    {
      Type type_ = p.type_.accept(this, arg);
      String id_ = p.id_;
      ListArg listarg_ = new ListArg();
      for (Arg x : p.listarg_)
      {
        listarg_.add(x.accept(this,arg));
      }
      ListStm liststm_ = new ListStm();
      for (Stm x : p.liststm_)
      {
        liststm_.add(x.accept(this,arg));
      }
      return new CPP.Absyn.DFun(type_, id_, listarg_, liststm_);
    }
/* Arg */
    public Arg visit(CPP.Absyn.ADecl p, A arg)
    {
      Type type_ = p.type_.accept(this, arg);
      String id_ = p.id_;
      return new CPP.Absyn.ADecl(type_, id_);
    }
/* Stm */
    public Stm visit(CPP.Absyn.SExp p, A arg)
    {
      Exp exp_ = p.exp_.accept(this, arg);
      return new CPP.Absyn.SExp(exp_);
    }    public Stm visit(CPP.Absyn.SDecls p, A arg)
    {
      Type type_ = p.type_.accept(this, arg);
      ListId listid_ = p.listid_;
      return new CPP.Absyn.SDecls(type_, listid_);
    }    public Stm visit(CPP.Absyn.SInit p, A arg)
    {
      Type type_ = p.type_.accept(this, arg);
      String id_ = p.id_;
      Exp exp_ = p.exp_.accept(this, arg);
      return new CPP.Absyn.SInit(type_, id_, exp_);
    }    public Stm visit(CPP.Absyn.SReturn p, A arg)
    {
      Exp exp_ = p.exp_.accept(this, arg);
      return new CPP.Absyn.SReturn(exp_);
    }    public Stm visit(CPP.Absyn.SWhile p, A arg)
    {
      Exp exp_ = p.exp_.accept(this, arg);
      Stm stm_ = p.stm_.accept(this, arg);
      return new CPP.Absyn.SWhile(exp_, stm_);
    }    public Stm visit(CPP.Absyn.SBlock p, A arg)
    {
      ListStm liststm_ = new ListStm();
      for (Stm x : p.liststm_)
      {
        liststm_.add(x.accept(this,arg));
      }
      return new CPP.Absyn.SBlock(liststm_);
    }    public Stm visit(CPP.Absyn.SIfElse p, A arg)
    {
      Exp exp_ = p.exp_.accept(this, arg);
      Stm stm_1 = p.stm_1.accept(this, arg);
      Stm stm_2 = p.stm_2.accept(this, arg);
      return new CPP.Absyn.SIfElse(exp_, stm_1, stm_2);
    }
/* Exp */
    public Exp visit(CPP.Absyn.ETrue p, A arg)
    {
      return new CPP.Absyn.ETrue();
    }    public Exp visit(CPP.Absyn.EFalse p, A arg)
    {
      return new CPP.Absyn.EFalse();
    }    public Exp visit(CPP.Absyn.EInt p, A arg)
    {
      Integer integer_ = p.integer_;
      return new CPP.Absyn.EInt(integer_);
    }    public Exp visit(CPP.Absyn.EDouble p, A arg)
    {
      Double double_ = p.double_;
      return new CPP.Absyn.EDouble(double_);
    }    public Exp visit(CPP.Absyn.EId p, A arg)
    {
      String id_ = p.id_;
      return new CPP.Absyn.EId(id_);
    }    public Exp visit(CPP.Absyn.EApp p, A arg)
    {
      String id_ = p.id_;
      ListExp listexp_ = new ListExp();
      for (Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new CPP.Absyn.EApp(id_, listexp_);
    }    public Exp visit(CPP.Absyn.EPostIncr p, A arg)
    {
      String id_ = p.id_;
      return new CPP.Absyn.EPostIncr(id_);
    }    public Exp visit(CPP.Absyn.EPostDecr p, A arg)
    {
      String id_ = p.id_;
      return new CPP.Absyn.EPostDecr(id_);
    }    public Exp visit(CPP.Absyn.EPreIncr p, A arg)
    {
      String id_ = p.id_;
      return new CPP.Absyn.EPreIncr(id_);
    }    public Exp visit(CPP.Absyn.EPreDecr p, A arg)
    {
      String id_ = p.id_;
      return new CPP.Absyn.EPreDecr(id_);
    }    public Exp visit(CPP.Absyn.ETimes p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.ETimes(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EDiv p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EDiv(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EPlus p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EPlus(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EMinus p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EMinus(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.ELt p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.ELt(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EGt p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EGt(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.ELtEq p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.ELtEq(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EGtEq p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EGtEq(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EEq p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EEq(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.ENEq p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.ENEq(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EAnd p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EAnd(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EOr p, A arg)
    {
      Exp exp_1 = p.exp_1.accept(this, arg);
      Exp exp_2 = p.exp_2.accept(this, arg);
      return new CPP.Absyn.EOr(exp_1, exp_2);
    }    public Exp visit(CPP.Absyn.EAss p, A arg)
    {
      String id_ = p.id_;
      Exp exp_ = p.exp_.accept(this, arg);
      return new CPP.Absyn.EAss(id_, exp_);
    }
/* Type */
    public Type visit(CPP.Absyn.Type_bool p, A arg)
    {
      return new CPP.Absyn.Type_bool();
    }    public Type visit(CPP.Absyn.Type_int p, A arg)
    {
      return new CPP.Absyn.Type_int();
    }    public Type visit(CPP.Absyn.Type_double p, A arg)
    {
      return new CPP.Absyn.Type_double();
    }    public Type visit(CPP.Absyn.Type_void p, A arg)
    {
      return new CPP.Absyn.Type_void();
    }
}