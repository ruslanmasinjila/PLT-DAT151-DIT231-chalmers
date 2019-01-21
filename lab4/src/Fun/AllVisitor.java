package Fun;

import Fun.Absyn.*;

/** BNFC-Generated All Visitor */
public interface AllVisitor<R,A> extends
  Fun.Absyn.Program.Visitor<R,A>,
  Fun.Absyn.Main.Visitor<R,A>,
  Fun.Absyn.Def.Visitor<R,A>,
  Fun.Absyn.Exp.Visitor<R,A>
{}
