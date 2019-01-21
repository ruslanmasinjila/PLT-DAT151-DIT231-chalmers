package CPP;
import CPP.Absyn.*;

public class PrettyPrinter
{
  //For certain applications increasing the initial size of the buffer may improve performance.
  private static final int INITIAL_BUFFER_SIZE = 128;
  private static final int INDENT_WIDTH = 2;
  //You may wish to change the parentheses used in precedence.
  private static final String _L_PAREN = new String("(");
  private static final String _R_PAREN = new String(")");
  //You may wish to change render
  private static void render(String s)
  {
    if (s.equals("{"))
    {
       buf_.append("\n");
       indent();
       buf_.append(s);
       _n_ = _n_ + INDENT_WIDTH;
       buf_.append("\n");
       indent();
    }
    else if (s.equals("(") || s.equals("["))
       buf_.append(s);
    else if (s.equals(")") || s.equals("]"))
    {
       backup();
       buf_.append(s);
       buf_.append(" ");
    }
    else if (s.equals("}"))
    {
       int t;
       _n_ = _n_ - INDENT_WIDTH;
       for(t=0; t<INDENT_WIDTH; t++) {
         backup();
       }
       buf_.append(s);
       buf_.append("\n");
       indent();
    }
    else if (s.equals(","))
    {
       backup();
       buf_.append(s);
       buf_.append(" ");
    }
    else if (s.equals(";"))
    {
       backup();
       buf_.append(s);
       buf_.append("\n");
       indent();
    }
    else if (s.equals("")) return;
    else
    {
       buf_.append(s);
       buf_.append(" ");
    }
  }


  //  print and show methods are defined for each category.
  public static String print(CPP.Absyn.Program foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Program foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.Def foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Def foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.ListDef foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.ListDef foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.Arg foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Arg foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.ListArg foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.ListArg foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.Stm foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Stm foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.ListStm foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.ListStm foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.Exp foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Exp foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.ListExp foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.ListExp foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.Type foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.Type foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(CPP.Absyn.ListId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(CPP.Absyn.ListId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  /***   You shouldn't need to change anything beyond this point.   ***/

  private static void pp(CPP.Absyn.Program foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.PDefs)
    {
       CPP.Absyn.PDefs _pdefs = (CPP.Absyn.PDefs) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_pdefs.listdef_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.Def foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.DFun)
    {
       CPP.Absyn.DFun _dfun = (CPP.Absyn.DFun) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_dfun.type_, 0);
       pp(_dfun.id_, 0);
       render("(");
       pp(_dfun.listarg_, 0);
       render(")");
       render("{");
       pp(_dfun.liststm_, 0);
       render("}");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.ListDef foo, int _i_)
  {
     for (java.util.Iterator<Def> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(CPP.Absyn.Arg foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.ADecl)
    {
       CPP.Absyn.ADecl _adecl = (CPP.Absyn.ADecl) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_adecl.type_, 0);
       pp(_adecl.id_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.ListArg foo, int _i_)
  {
     for (java.util.Iterator<Arg> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render(",");
       } else {
         render("");
       }
     }  }

  private static void pp(CPP.Absyn.Stm foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.SExp)
    {
       CPP.Absyn.SExp _sexp = (CPP.Absyn.SExp) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_sexp.exp_, 0);
       render(";");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SDecls)
    {
       CPP.Absyn.SDecls _sdecls = (CPP.Absyn.SDecls) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_sdecls.type_, 0);
       pp(_sdecls.listid_, 0);
       render(";");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SInit)
    {
       CPP.Absyn.SInit _sinit = (CPP.Absyn.SInit) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_sinit.type_, 0);
       pp(_sinit.id_, 0);
       render("=");
       pp(_sinit.exp_, 0);
       render(";");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SReturn)
    {
       CPP.Absyn.SReturn _sreturn = (CPP.Absyn.SReturn) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("return");
       pp(_sreturn.exp_, 0);
       render(";");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SWhile)
    {
       CPP.Absyn.SWhile _swhile = (CPP.Absyn.SWhile) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("while");
       render("(");
       pp(_swhile.exp_, 0);
       render(")");
       pp(_swhile.stm_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SBlock)
    {
       CPP.Absyn.SBlock _sblock = (CPP.Absyn.SBlock) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("{");
       pp(_sblock.liststm_, 0);
       render("}");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.SIfElse)
    {
       CPP.Absyn.SIfElse _sifelse = (CPP.Absyn.SIfElse) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("if");
       render("(");
       pp(_sifelse.exp_, 0);
       render(")");
       pp(_sifelse.stm_1, 0);
       render("else");
       pp(_sifelse.stm_2, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.ListStm foo, int _i_)
  {
     for (java.util.Iterator<Stm> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(CPP.Absyn.Exp foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.ETrue)
    {
       CPP.Absyn.ETrue _etrue = (CPP.Absyn.ETrue) foo;
       if (_i_ > 15) render(_L_PAREN);
       render("true");
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EFalse)
    {
       CPP.Absyn.EFalse _efalse = (CPP.Absyn.EFalse) foo;
       if (_i_ > 15) render(_L_PAREN);
       render("false");
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EInt)
    {
       CPP.Absyn.EInt _eint = (CPP.Absyn.EInt) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_eint.integer_, 0);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EDouble)
    {
       CPP.Absyn.EDouble _edouble = (CPP.Absyn.EDouble) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_edouble.double_, 0);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EId)
    {
       CPP.Absyn.EId _eid = (CPP.Absyn.EId) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_eid.id_, 0);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EApp)
    {
       CPP.Absyn.EApp _eapp = (CPP.Absyn.EApp) foo;
       if (_i_ > 14) render(_L_PAREN);
       pp(_eapp.id_, 0);
       render("(");
       pp(_eapp.listexp_, 0);
       render(")");
       if (_i_ > 14) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EPostIncr)
    {
       CPP.Absyn.EPostIncr _epostincr = (CPP.Absyn.EPostIncr) foo;
       if (_i_ > 14) render(_L_PAREN);
       pp(_epostincr.id_, 0);
       render("++");
       if (_i_ > 14) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EPostDecr)
    {
       CPP.Absyn.EPostDecr _epostdecr = (CPP.Absyn.EPostDecr) foo;
       if (_i_ > 14) render(_L_PAREN);
       pp(_epostdecr.id_, 0);
       render("--");
       if (_i_ > 14) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EPreIncr)
    {
       CPP.Absyn.EPreIncr _epreincr = (CPP.Absyn.EPreIncr) foo;
       if (_i_ > 13) render(_L_PAREN);
       render("++");
       pp(_epreincr.id_, 0);
       if (_i_ > 13) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EPreDecr)
    {
       CPP.Absyn.EPreDecr _epredecr = (CPP.Absyn.EPreDecr) foo;
       if (_i_ > 13) render(_L_PAREN);
       render("--");
       pp(_epredecr.id_, 0);
       if (_i_ > 13) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.ETimes)
    {
       CPP.Absyn.ETimes _etimes = (CPP.Absyn.ETimes) foo;
       if (_i_ > 12) render(_L_PAREN);
       pp(_etimes.exp_1, 12);
       render("*");
       pp(_etimes.exp_2, 13);
       if (_i_ > 12) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EDiv)
    {
       CPP.Absyn.EDiv _ediv = (CPP.Absyn.EDiv) foo;
       if (_i_ > 12) render(_L_PAREN);
       pp(_ediv.exp_1, 12);
       render("/");
       pp(_ediv.exp_2, 13);
       if (_i_ > 12) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EPlus)
    {
       CPP.Absyn.EPlus _eplus = (CPP.Absyn.EPlus) foo;
       if (_i_ > 11) render(_L_PAREN);
       pp(_eplus.exp_1, 11);
       render("+");
       pp(_eplus.exp_2, 12);
       if (_i_ > 11) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EMinus)
    {
       CPP.Absyn.EMinus _eminus = (CPP.Absyn.EMinus) foo;
       if (_i_ > 11) render(_L_PAREN);
       pp(_eminus.exp_1, 11);
       render("-");
       pp(_eminus.exp_2, 12);
       if (_i_ > 11) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.ELt)
    {
       CPP.Absyn.ELt _elt = (CPP.Absyn.ELt) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_elt.exp_1, 10);
       render("<");
       pp(_elt.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EGt)
    {
       CPP.Absyn.EGt _egt = (CPP.Absyn.EGt) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_egt.exp_1, 10);
       render(">");
       pp(_egt.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.ELtEq)
    {
       CPP.Absyn.ELtEq _elteq = (CPP.Absyn.ELtEq) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_elteq.exp_1, 10);
       render("<=");
       pp(_elteq.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EGtEq)
    {
       CPP.Absyn.EGtEq _egteq = (CPP.Absyn.EGtEq) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_egteq.exp_1, 10);
       render(">=");
       pp(_egteq.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EEq)
    {
       CPP.Absyn.EEq _eeq = (CPP.Absyn.EEq) foo;
       if (_i_ > 8) render(_L_PAREN);
       pp(_eeq.exp_1, 9);
       render("==");
       pp(_eeq.exp_2, 9);
       if (_i_ > 8) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.ENEq)
    {
       CPP.Absyn.ENEq _eneq = (CPP.Absyn.ENEq) foo;
       if (_i_ > 8) render(_L_PAREN);
       pp(_eneq.exp_1, 9);
       render("!=");
       pp(_eneq.exp_2, 9);
       if (_i_ > 8) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EAnd)
    {
       CPP.Absyn.EAnd _eand = (CPP.Absyn.EAnd) foo;
       if (_i_ > 4) render(_L_PAREN);
       pp(_eand.exp_1, 4);
       render("&&");
       pp(_eand.exp_2, 5);
       if (_i_ > 4) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EOr)
    {
       CPP.Absyn.EOr _eor = (CPP.Absyn.EOr) foo;
       if (_i_ > 3) render(_L_PAREN);
       pp(_eor.exp_1, 3);
       render("||");
       pp(_eor.exp_2, 4);
       if (_i_ > 3) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.EAss)
    {
       CPP.Absyn.EAss _eass = (CPP.Absyn.EAss) foo;
       if (_i_ > 2) render(_L_PAREN);
       pp(_eass.id_, 0);
       render("=");
       pp(_eass.exp_, 2);
       if (_i_ > 2) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.ListExp foo, int _i_)
  {
     for (java.util.Iterator<Exp> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render(",");
       } else {
         render("");
       }
     }  }

  private static void pp(CPP.Absyn.Type foo, int _i_)
  {
    if (foo instanceof CPP.Absyn.Type_bool)
    {
       CPP.Absyn.Type_bool _type_bool = (CPP.Absyn.Type_bool) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("bool");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.Type_int)
    {
       CPP.Absyn.Type_int _type_int = (CPP.Absyn.Type_int) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("int");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.Type_double)
    {
       CPP.Absyn.Type_double _type_double = (CPP.Absyn.Type_double) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("double");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof CPP.Absyn.Type_void)
    {
       CPP.Absyn.Type_void _type_void = (CPP.Absyn.Type_void) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("void");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(CPP.Absyn.ListId foo, int _i_)
  {
     for (java.util.Iterator<String> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render(",");
       } else {
         render("");
       }
     }  }


  private static void sh(CPP.Absyn.Program foo)
  {
    if (foo instanceof CPP.Absyn.PDefs)
    {
       CPP.Absyn.PDefs _pdefs = (CPP.Absyn.PDefs) foo;
       render("(");
       render("PDefs");
       render("[");
       sh(_pdefs.listdef_);
       render("]");
       render(")");
    }
  }

  private static void sh(CPP.Absyn.Def foo)
  {
    if (foo instanceof CPP.Absyn.DFun)
    {
       CPP.Absyn.DFun _dfun = (CPP.Absyn.DFun) foo;
       render("(");
       render("DFun");
       sh(_dfun.type_);
       sh(_dfun.id_);
       render("[");
       sh(_dfun.listarg_);
       render("]");
       render("[");
       sh(_dfun.liststm_);
       render("]");
       render(")");
    }
  }

  private static void sh(CPP.Absyn.ListDef foo)
  {
     for (java.util.Iterator<Def> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(CPP.Absyn.Arg foo)
  {
    if (foo instanceof CPP.Absyn.ADecl)
    {
       CPP.Absyn.ADecl _adecl = (CPP.Absyn.ADecl) foo;
       render("(");
       render("ADecl");
       sh(_adecl.type_);
       sh(_adecl.id_);
       render(")");
    }
  }

  private static void sh(CPP.Absyn.ListArg foo)
  {
     for (java.util.Iterator<Arg> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(CPP.Absyn.Stm foo)
  {
    if (foo instanceof CPP.Absyn.SExp)
    {
       CPP.Absyn.SExp _sexp = (CPP.Absyn.SExp) foo;
       render("(");
       render("SExp");
       sh(_sexp.exp_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.SDecls)
    {
       CPP.Absyn.SDecls _sdecls = (CPP.Absyn.SDecls) foo;
       render("(");
       render("SDecls");
       sh(_sdecls.type_);
       render("[");
       sh(_sdecls.listid_);
       render("]");
       render(")");
    }
    if (foo instanceof CPP.Absyn.SInit)
    {
       CPP.Absyn.SInit _sinit = (CPP.Absyn.SInit) foo;
       render("(");
       render("SInit");
       sh(_sinit.type_);
       sh(_sinit.id_);
       sh(_sinit.exp_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.SReturn)
    {
       CPP.Absyn.SReturn _sreturn = (CPP.Absyn.SReturn) foo;
       render("(");
       render("SReturn");
       sh(_sreturn.exp_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.SWhile)
    {
       CPP.Absyn.SWhile _swhile = (CPP.Absyn.SWhile) foo;
       render("(");
       render("SWhile");
       sh(_swhile.exp_);
       sh(_swhile.stm_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.SBlock)
    {
       CPP.Absyn.SBlock _sblock = (CPP.Absyn.SBlock) foo;
       render("(");
       render("SBlock");
       render("[");
       sh(_sblock.liststm_);
       render("]");
       render(")");
    }
    if (foo instanceof CPP.Absyn.SIfElse)
    {
       CPP.Absyn.SIfElse _sifelse = (CPP.Absyn.SIfElse) foo;
       render("(");
       render("SIfElse");
       sh(_sifelse.exp_);
       sh(_sifelse.stm_1);
       sh(_sifelse.stm_2);
       render(")");
    }
  }

  private static void sh(CPP.Absyn.ListStm foo)
  {
     for (java.util.Iterator<Stm> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(CPP.Absyn.Exp foo)
  {
    if (foo instanceof CPP.Absyn.ETrue)
    {
       CPP.Absyn.ETrue _etrue = (CPP.Absyn.ETrue) foo;
       render("ETrue");
    }
    if (foo instanceof CPP.Absyn.EFalse)
    {
       CPP.Absyn.EFalse _efalse = (CPP.Absyn.EFalse) foo;
       render("EFalse");
    }
    if (foo instanceof CPP.Absyn.EInt)
    {
       CPP.Absyn.EInt _eint = (CPP.Absyn.EInt) foo;
       render("(");
       render("EInt");
       sh(_eint.integer_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EDouble)
    {
       CPP.Absyn.EDouble _edouble = (CPP.Absyn.EDouble) foo;
       render("(");
       render("EDouble");
       sh(_edouble.double_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EId)
    {
       CPP.Absyn.EId _eid = (CPP.Absyn.EId) foo;
       render("(");
       render("EId");
       sh(_eid.id_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EApp)
    {
       CPP.Absyn.EApp _eapp = (CPP.Absyn.EApp) foo;
       render("(");
       render("EApp");
       sh(_eapp.id_);
       render("[");
       sh(_eapp.listexp_);
       render("]");
       render(")");
    }
    if (foo instanceof CPP.Absyn.EPostIncr)
    {
       CPP.Absyn.EPostIncr _epostincr = (CPP.Absyn.EPostIncr) foo;
       render("(");
       render("EPostIncr");
       sh(_epostincr.id_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EPostDecr)
    {
       CPP.Absyn.EPostDecr _epostdecr = (CPP.Absyn.EPostDecr) foo;
       render("(");
       render("EPostDecr");
       sh(_epostdecr.id_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EPreIncr)
    {
       CPP.Absyn.EPreIncr _epreincr = (CPP.Absyn.EPreIncr) foo;
       render("(");
       render("EPreIncr");
       sh(_epreincr.id_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EPreDecr)
    {
       CPP.Absyn.EPreDecr _epredecr = (CPP.Absyn.EPreDecr) foo;
       render("(");
       render("EPreDecr");
       sh(_epredecr.id_);
       render(")");
    }
    if (foo instanceof CPP.Absyn.ETimes)
    {
       CPP.Absyn.ETimes _etimes = (CPP.Absyn.ETimes) foo;
       render("(");
       render("ETimes");
       sh(_etimes.exp_1);
       sh(_etimes.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EDiv)
    {
       CPP.Absyn.EDiv _ediv = (CPP.Absyn.EDiv) foo;
       render("(");
       render("EDiv");
       sh(_ediv.exp_1);
       sh(_ediv.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EPlus)
    {
       CPP.Absyn.EPlus _eplus = (CPP.Absyn.EPlus) foo;
       render("(");
       render("EPlus");
       sh(_eplus.exp_1);
       sh(_eplus.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EMinus)
    {
       CPP.Absyn.EMinus _eminus = (CPP.Absyn.EMinus) foo;
       render("(");
       render("EMinus");
       sh(_eminus.exp_1);
       sh(_eminus.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.ELt)
    {
       CPP.Absyn.ELt _elt = (CPP.Absyn.ELt) foo;
       render("(");
       render("ELt");
       sh(_elt.exp_1);
       sh(_elt.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EGt)
    {
       CPP.Absyn.EGt _egt = (CPP.Absyn.EGt) foo;
       render("(");
       render("EGt");
       sh(_egt.exp_1);
       sh(_egt.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.ELtEq)
    {
       CPP.Absyn.ELtEq _elteq = (CPP.Absyn.ELtEq) foo;
       render("(");
       render("ELtEq");
       sh(_elteq.exp_1);
       sh(_elteq.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EGtEq)
    {
       CPP.Absyn.EGtEq _egteq = (CPP.Absyn.EGtEq) foo;
       render("(");
       render("EGtEq");
       sh(_egteq.exp_1);
       sh(_egteq.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EEq)
    {
       CPP.Absyn.EEq _eeq = (CPP.Absyn.EEq) foo;
       render("(");
       render("EEq");
       sh(_eeq.exp_1);
       sh(_eeq.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.ENEq)
    {
       CPP.Absyn.ENEq _eneq = (CPP.Absyn.ENEq) foo;
       render("(");
       render("ENEq");
       sh(_eneq.exp_1);
       sh(_eneq.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EAnd)
    {
       CPP.Absyn.EAnd _eand = (CPP.Absyn.EAnd) foo;
       render("(");
       render("EAnd");
       sh(_eand.exp_1);
       sh(_eand.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EOr)
    {
       CPP.Absyn.EOr _eor = (CPP.Absyn.EOr) foo;
       render("(");
       render("EOr");
       sh(_eor.exp_1);
       sh(_eor.exp_2);
       render(")");
    }
    if (foo instanceof CPP.Absyn.EAss)
    {
       CPP.Absyn.EAss _eass = (CPP.Absyn.EAss) foo;
       render("(");
       render("EAss");
       sh(_eass.id_);
       sh(_eass.exp_);
       render(")");
    }
  }

  private static void sh(CPP.Absyn.ListExp foo)
  {
     for (java.util.Iterator<Exp> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(CPP.Absyn.Type foo)
  {
    if (foo instanceof CPP.Absyn.Type_bool)
    {
       CPP.Absyn.Type_bool _type_bool = (CPP.Absyn.Type_bool) foo;
       render("Type_bool");
    }
    if (foo instanceof CPP.Absyn.Type_int)
    {
       CPP.Absyn.Type_int _type_int = (CPP.Absyn.Type_int) foo;
       render("Type_int");
    }
    if (foo instanceof CPP.Absyn.Type_double)
    {
       CPP.Absyn.Type_double _type_double = (CPP.Absyn.Type_double) foo;
       render("Type_double");
    }
    if (foo instanceof CPP.Absyn.Type_void)
    {
       CPP.Absyn.Type_void _type_void = (CPP.Absyn.Type_void) foo;
       render("Type_void");
    }
  }

  private static void sh(CPP.Absyn.ListId foo)
  {
     for (java.util.Iterator<String> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }


  private static void pp(Integer n, int _i_) { buf_.append(n); buf_.append(" "); }
  private static void pp(Double d, int _i_) { buf_.append(d); buf_.append(" "); }
  private static void pp(String s, int _i_) { buf_.append(s); buf_.append(" "); }
  private static void pp(Character c, int _i_) { buf_.append("'" + c.toString() + "'"); buf_.append(" "); }
  private static void sh(Integer n) { render(n.toString()); }
  private static void sh(Double d) { render(d.toString()); }
  private static void sh(Character c) { render(c.toString()); }
  private static void sh(String s) { printQuoted(s); }
  private static void printQuoted(String s) { render("\"" + s + "\""); }
  private static void indent()
  {
    int n = _n_;
    while (n > 0)
    {
      buf_.append(" ");
      n--;
    }
  }
  private static void backup()
  {
     if (buf_.charAt(buf_.length() - 1) == ' ') {
      buf_.setLength(buf_.length() - 1);
    }
  }
  private static void trim()
  {
     while (buf_.length() > 0 && buf_.charAt(0) == ' ')
        buf_.deleteCharAt(0); 
    while (buf_.length() > 0 && buf_.charAt(buf_.length()-1) == ' ')
        buf_.deleteCharAt(buf_.length()-1);
  }
  private static int _n_ = 0;
  private static StringBuilder buf_ = new StringBuilder(INITIAL_BUFFER_SIZE);
}

