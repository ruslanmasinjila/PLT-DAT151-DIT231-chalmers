package CPP;
import CPP.Absyn.*;
/** BNFC-Generated Abstract Visitor */
public class AbstractVisitor<R,A> implements AllVisitor<R,A> {
/* Program */
    public R visit(CPP.Absyn.PDefs p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(CPP.Absyn.Program p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Def */
    public R visit(CPP.Absyn.DFun p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(CPP.Absyn.Def p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Arg */
    public R visit(CPP.Absyn.ADecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(CPP.Absyn.Arg p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Stm */
    public R visit(CPP.Absyn.SExp p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SDecls p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SInit p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SReturn p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SWhile p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SBlock p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.SIfElse p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(CPP.Absyn.Stm p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Exp */
    public R visit(CPP.Absyn.ETrue p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EFalse p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EInt p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EDouble p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EId p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EApp p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EPostIncr p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EPostDecr p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EPreIncr p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EPreDecr p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.ETimes p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EDiv p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EPlus p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EMinus p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.ELt p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EGt p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.ELtEq p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.EGtEq p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EEq p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.ENEq p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EAnd p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EOr p, A arg) { return visitDefault(p, arg); }

    public R visit(CPP.Absyn.EAss p, A arg) { return visitDefault(p, arg); }







    public R visitDefault(CPP.Absyn.Exp p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Type */
    public R visit(CPP.Absyn.Type_bool p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.Type_int p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.Type_double p, A arg) { return visitDefault(p, arg); }
    public R visit(CPP.Absyn.Type_void p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(CPP.Absyn.Type p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }

}
