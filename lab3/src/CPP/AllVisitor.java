package CPP;

import CPP.Absyn.*;

/** BNFC-Generated All Visitor */
public interface AllVisitor<R,A> extends
  CPP.Absyn.Program.Visitor<R,A>,
  CPP.Absyn.Def.Visitor<R,A>,
  CPP.Absyn.Arg.Visitor<R,A>,
  CPP.Absyn.Stm.Visitor<R,A>,
  CPP.Absyn.Exp.Visitor<R,A>,
  CPP.Absyn.Type.Visitor<R,A>
{}
