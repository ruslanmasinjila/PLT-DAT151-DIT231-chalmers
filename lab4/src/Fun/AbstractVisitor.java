package Fun;
import Fun.Absyn.*;
/** BNFC-Generated Abstract Visitor */
public class AbstractVisitor<R,A> implements AllVisitor<R,A> {
/* Program */
    public R visit(Fun.Absyn.Prog p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(Fun.Absyn.Program p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Main */
    public R visit(Fun.Absyn.DMain p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(Fun.Absyn.Main p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Def */
    public R visit(Fun.Absyn.DDef p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(Fun.Absyn.Def p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Exp */
    public R visit(Fun.Absyn.EVar p, A arg) { return visitDefault(p, arg); }
    public R visit(Fun.Absyn.EInt p, A arg) { return visitDefault(p, arg); }

    public R visit(Fun.Absyn.EApp p, A arg) { return visitDefault(p, arg); }

    public R visit(Fun.Absyn.EAdd p, A arg) { return visitDefault(p, arg); }
    public R visit(Fun.Absyn.ESub p, A arg) { return visitDefault(p, arg); }
    public R visit(Fun.Absyn.ELt p, A arg) { return visitDefault(p, arg); }

    public R visit(Fun.Absyn.EIf p, A arg) { return visitDefault(p, arg); }
    public R visit(Fun.Absyn.EAbs p, A arg) { return visitDefault(p, arg); }

    public R visitDefault(Fun.Absyn.Exp p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }

}
