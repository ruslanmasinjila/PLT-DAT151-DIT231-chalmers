package CPP;
import CPP.Absyn.*;
/*** BNFC-Generated Visitor Design Pattern Skeleton. ***/
/* This implements the common visitor design pattern.
   Tests show it to be slightly less efficient than the
   instanceof method, but easier to use. 
   Replace the R and A parameters with the desired return
   and context types.*/

public class VisitSkel
{
  public class ProgramVisitor<R,A> implements Program.Visitor<R,A>
  {
    public R visit(CPP.Absyn.PDefs p, A arg)
    { /* Code For PDefs Goes Here */
      for (Def x: p.listdef_)
      { /* ... */ }
      return null;
    }
  }
  public class DefVisitor<R,A> implements Def.Visitor<R,A>
  {
    public R visit(CPP.Absyn.DFun p, A arg)
    { /* Code For DFun Goes Here */
      p.type_.accept(new TypeVisitor<R,A>(), arg);
      //p.id_;
      for (Arg x: p.listarg_)
      { /* ... */ }
      for (Stm x: p.liststm_)
      { /* ... */ }
      return null;
    }
  }
  public class ArgVisitor<R,A> implements Arg.Visitor<R,A>
  {
    public R visit(CPP.Absyn.ADecl p, A arg)
    { /* Code For ADecl Goes Here */
      p.type_.accept(new TypeVisitor<R,A>(), arg);
      //p.id_;
      return null;
    }
  }
  public class StmVisitor<R,A> implements Stm.Visitor<R,A>
  {
    public R visit(CPP.Absyn.SExp p, A arg)
    { /* Code For SExp Goes Here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.SDecls p, A arg)
    { /* Code For SDecls Goes Here */
      p.type_.accept(new TypeVisitor<R,A>(), arg);
      for (String x: p.listid_)
      { /* ... */ }
      return null;
    }    public R visit(CPP.Absyn.SInit p, A arg)
    { /* Code For SInit Goes Here */
      p.type_.accept(new TypeVisitor<R,A>(), arg);
      //p.id_;
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.SReturn p, A arg)
    { /* Code For SReturn Goes Here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.SWhile p, A arg)
    { /* Code For SWhile Goes Here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.stm_.accept(new StmVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.SBlock p, A arg)
    { /* Code For SBlock Goes Here */
      for (Stm x: p.liststm_)
      { /* ... */ }
      return null;
    }    public R visit(CPP.Absyn.SIfElse p, A arg)
    { /* Code For SIfElse Goes Here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.stm_1.accept(new StmVisitor<R,A>(), arg);
      p.stm_2.accept(new StmVisitor<R,A>(), arg);
      return null;
    }
  }
  public class ExpVisitor<R,A> implements Exp.Visitor<R,A>
  {
    public R visit(CPP.Absyn.ETrue p, A arg)
    { /* Code For ETrue Goes Here */
      return null;
    }    public R visit(CPP.Absyn.EFalse p, A arg)
    { /* Code For EFalse Goes Here */
      return null;
    }    public R visit(CPP.Absyn.EInt p, A arg)
    { /* Code For EInt Goes Here */
      //p.integer_;
      return null;
    }    public R visit(CPP.Absyn.EDouble p, A arg)
    { /* Code For EDouble Goes Here */
      //p.double_;
      return null;
    }    public R visit(CPP.Absyn.EId p, A arg)
    { /* Code For EId Goes Here */
      //p.id_;
      return null;
    }        public R visit(CPP.Absyn.EApp p, A arg)
    { /* Code For EApp Goes Here */
      //p.id_;
      for (Exp x: p.listexp_)
      { /* ... */ }
      return null;
    }    public R visit(CPP.Absyn.EPostIncr p, A arg)
    { /* Code For EPostIncr Goes Here */
      //p.id_;
      return null;
    }    public R visit(CPP.Absyn.EPostDecr p, A arg)
    { /* Code For EPostDecr Goes Here */
      //p.id_;
      return null;
    }        public R visit(CPP.Absyn.EPreIncr p, A arg)
    { /* Code For EPreIncr Goes Here */
      //p.id_;
      return null;
    }    public R visit(CPP.Absyn.EPreDecr p, A arg)
    { /* Code For EPreDecr Goes Here */
      //p.id_;
      return null;
    }        public R visit(CPP.Absyn.ETimes p, A arg)
    { /* Code For ETimes Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.EDiv p, A arg)
    { /* Code For EDiv Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.EPlus p, A arg)
    { /* Code For EPlus Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.EMinus p, A arg)
    { /* Code For EMinus Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.ELt p, A arg)
    { /* Code For ELt Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.EGt p, A arg)
    { /* Code For EGt Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.ELtEq p, A arg)
    { /* Code For ELtEq Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.EGtEq p, A arg)
    { /* Code For EGtEq Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.EEq p, A arg)
    { /* Code For EEq Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }    public R visit(CPP.Absyn.ENEq p, A arg)
    { /* Code For ENEq Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.EAnd p, A arg)
    { /* Code For EAnd Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.EOr p, A arg)
    { /* Code For EOr Goes Here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }        public R visit(CPP.Absyn.EAss p, A arg)
    { /* Code For EAss Goes Here */
      //p.id_;
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }                            
  }
  public class TypeVisitor<R,A> implements Type.Visitor<R,A>
  {
    public R visit(CPP.Absyn.Type_bool p, A arg)
    { /* Code For Type_bool Goes Here */
      return null;
    }    public R visit(CPP.Absyn.Type_int p, A arg)
    { /* Code For Type_int Goes Here */
      return null;
    }    public R visit(CPP.Absyn.Type_double p, A arg)
    { /* Code For Type_double Goes Here */
      return null;
    }    public R visit(CPP.Absyn.Type_void p, A arg)
    { /* Code For Type_void Goes Here */
      return null;
    }
  }
}