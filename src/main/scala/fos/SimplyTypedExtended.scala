package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import scala.util.parsing.combinator.Parsers

/** This object implements a parser and evaluator for the
  * simply typed lambda calculus found in Chapter 9 of
  * the TAPL book.
  */
object SimplyTypedExtended extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
    "=>", "|")
  lexical.reserved ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
    "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
    "case", "of", "inl", "inr", "as")


  def parse(s: String): ParseResult[Term] = phrase(Term)(new lexical.Scanner(s))

  def parseType(s: String): ParseResult[Type] = phrase(typeParser)(new lexical.Scanner(s))

  def getPathStream(trees: Term): Stream[Term] =
    path(trees, reduce)

  /** Term     ::= SimpleTerm { SimpleTerm }
    */ 
  
  def Term: Parser[Term] =
    chainl1[Term](SimpleTerm , success(App))  
     
    

  /** SimpleTerm ::= "true"
    * | "false"
    * | number
    * | "succ" Term
    * | "pred" Term
    * | "iszero" Term
    * | "if" Term "then" Term "else" Term
    * | ident
    * | "\" ident ":" Type "." Term
    * | "(" Term ")"
    * | "let" ident ":" Type "=" Term "in" Term
    * | "{" Term "," Term "}"
    * | "fst" Term
    * | "snd" Term
    * | "inl" Term "as" Type
    * | "inr" Term "as" Type
    * | "case" Term "of" "inl" ident "=>" Term "|" "inr" ident "=>" Term
    * | "fix" Term
    * | "letrec" ident ":" Type "=" Term "in" Term</pre>
    */

  def SimpleTerm: Parser[Term] =
    "fst" ~> Term ^^ First |
      "snd" ~> Term ^^ Second |
      ("{" ~> Term <~ ",") ~ (Term <~ "}") ^^ {
        case t1 ~ t2 => TermPair(t1, t2)
      } |
      valuesParser |
      ident ^^ Var |
      ("if" ~> Term) ~ ("then" ~> Term) ~ ("else" ~> Term) ^^ {
        case cond ~ thenPart ~ elsePart => If(cond, thenPart, elsePart)
      } |
      "pred" ~> Term ^^ Pred |
      "succ" ~> Term ^^ Succ |
      "iszero" ~> Term ^^ IsZero |
      ("letrec" ~> ident) ~ (":" ~> typeParser) ~ ("=" ~> Term) ~ ("in" ~> Term) ^^ {
        case varName ~ varType ~ argument ~ body =>
          App(Abs(varName, varType, body), Fix(Abs("x", varType, argument)))
      } |
      ("let" ~> ident) ~ (":" ~> typeParser) ~ ("=" ~> Term) ~ ("in" ~> Term) ^^ {
        case varName ~ varType ~ argument ~ body =>
          App(Abs(varName, varType, body), argument)
      } |
      "(" ~> Term <~ ")" |
      (("inl" ~> Term) <~ "as") ~ typeParser ^^ (a => Inl(a._1, a._2)) |
      "inr".~>(Term).<~("as").~(typeParser) ^^ (a => Inr(a._1, a._2)) |
      matchCase |
      "fix" ~> Term ^^ Fix.apply

  def matchCase: Parser[Term] =
    "case".~>(Term).<~("of").<~("inl").~(ident).<~("=>").~(Term).<~("|").<~("inr").~(ident).<~("=>").~(Term)
      .^^ { case caseTerm ~ inlIdent ~ inlBody ~ inrIdent ~ inrBody => 
          Case(caseTerm, inlIdent, inlBody, inrIdent, inrBody)
      }

  def valuesParser: Parser[Term] =
    ("\\" ~> ident) ~ (":" ~> typeParser) ~ ("." ~> Term) ^^ {
      case (paramName ~ parsedType ~ term) => Abs(paramName, parsedType, term)
    } |
      "true" ^^^ True() |
      "false" ^^^ False() |
      numericLit ^^ { litteral =>
        val number = Integer.parseInt(litteral)
        (0 until number).foldLeft[Term](Zero()) { case (t, _) => Succ(t) }
      }

  /** BaseType ::= "Bool" | "Nat" | "(" Type ")"
    */
  def baseType: Parser[Type] =
    "Bool" ^^^ TypeBool |
      "Nat" ^^^ TypeNat |
      "(" ~> typeParser <~ ")"

  /*
   * pour l'instant on accepte qu'un seul séparateur, il faudrait en accepter plusieurs
   * ensuite il faudrait un autre argument qui soit une map prenant un séparateur (i.e. "*" ou "+")
   * et qui retourne un combinateur
   */

  def createRightAssociativeParser[T](p: Parser[T], sepToCombiner: Map[String, (T, T) => T]): Parser[T] = {
    val sepsParser = sepToCombiner.keys.foldLeft[Option[Parser[String]]](None) {
      case (None, sep)         => Some(sep)
      case (Some(parser), sep) => Some(parser | sep)
    }.getOrElse(sys.error("empty keys"))

    def combine(t1: T, sep: String, t2: T): T = sepToCombiner(sep)(t1, t2)

    def helper(firstTerm: T, sepsStack: List[String],
        termsStack: List[T], treatedOpt: Option[T]): T = (sepsStack, termsStack, treatedOpt) match {
      case (Nil, Nil, None) => firstTerm
      case (sep :: Nil, Nil, Some(treated)) => combine(firstTerm, sep, treated)
        
      case (Nil, t :: rest, _) => sys.error("error: there should have been a separator parsed")
      
      case (sep :: otherSeps, term :: otherTerms, Some(treated)) => 
        helper(firstTerm, otherSeps, otherTerms, Some(combine(term, sep, treated)))
        
      case (sep :: otherSeps, last :: beforeLast :: otherTerms, None) => 
        helper(firstTerm, otherSeps, otherTerms, Some(combine(beforeLast, sep, last)))
        
      case (sep :: Nil, last :: Nil, None) => 
        combine(firstTerm, sep, last) 
        
      case _ => sys.error("error on ${firstTerm}, ${sepsStack}, ${termsStack}, ${treatedOpt}")

    }

    p ~ rep(sepsParser ~ p) ^^ { // TODO add the case of Nil input (of repsep)
      case t ~ rest => //TODO use t at the end
        val (seps, terms) = rest.reverse.map { case sep ~ t => (sep, t) }.unzip
        helper(t, seps, terms, None)
    }
  }

  /** SimpleType ::= BaseType [ ("*" SimpleType) | ("+" SimpleType) ]
    */
  def typeSimple: Parser[Type] =
    createRightAssociativeParser[Type](baseType, Map("*" -> TypePair, "+" -> TypeSum))

  /**
   * Type       ::= SimpleType [ "->" Type ]
   */
  def typeParser: Parser[Type] = createRightAssociativeParser[Type](typeSimple, Map("->" -> TypeFun))

  def isNumerical(t: Term): Boolean = t match {
    case Succ(subTerm) => isNumerical(subTerm)
    case Pred(subTerm) => isNumerical(subTerm)
    case Zero() => true
    case _ => false
  }

  def alpha(t: Term): Term = t match {
    case Abs(varName, varType, body) =>
      val newX = Stream.from(1).map(i => varName + i).find(str => !fv(body).contains(str)).get
      Abs(newX, varType, replace(body, varName, newX))
    case term => term
  }

  def replace(t: Term, x: String, x1: String): Term = {
    def r(t: Term): Term = replace(t, x, x1)

    t match {

      case Var(v) if v == x => Var(x1)
      case v: Var => v
      case Abs(v, varType, t) => Abs(v, varType, r(t))
      case App(t1, t2) => App(r(t1), r(t2))
      case If(cond, t1, t2) => If(r(cond), r(t1), r(t2))
      case Pred(t1) => Pred(r(t1))
      case Succ(t1) => Succ(r(t1))
      case IsZero(t1) => IsZero(r(t1))
      case TermPair(t1, t2) => TermPair(r(t1), r(t2))
      case First(t1) => First(r(t1))
      case Second(t1) => Second(r(t1))
      case Inr(t, tpe) => Inr(r(t), tpe)
      case Inl(t, tpe) => Inl(r(t), tpe)
      case Case(t, xa, t1, xb, t2) => Case(r(t), xa, r(t1), xb, r(t2))
      case Fix(t) => Fix(r(t))
      case _ => t
    }
  }

  def fv(t: Term): List[String] = t match {
    case Var(v) => List(v)
    case Abs(str, varType, t1) => fv(t1).filter(s => s != str)
    case App(t1, t2) => fv(t1) ++ fv(t2)
    case If(cond, t1, t2) => fv(cond) ++ fv(t1) ++ fv(t2)
    case Pred(t1) => fv(t1)
    case Succ(t1) => fv(t1)
    case IsZero(t1) => fv(t1)
    case TermPair(t1, t2) => fv(t1) ++ fv(t2)
    case First(t1) => fv(t1)
    case Second(t1) => fv(t1)
    case Inr(t, _) => fv(t)
    case Inl(t, _) => fv(t)
    case Case(t, _, t1, _, t2) => fv(t) ++ fv(t1) ++ fv(t2)
    case Fix(t) => fv(t)
    case _ => Nil
  }

  /**
    * Straight forward substitution method
    * (see definition 5.3.5 in TAPL book).
    * [x -> s]t
    *
    * @param t the term in which we perform substitution
    * @param x the variable name
    * @param s the term we replace x with
    * @return ...
    */
  def subst(t: Term, x: String, s: Term): Term = {
    def f(t: Term) = subst(t, x, s)

    t match {
      case Var(v) if v == x => s
      case v: Var => v
      case a@Abs(y, _, _) if y == x => a
      case Abs(y, varType, t1) if !fv(s).contains(y) => Abs(y, varType, f(t1))
      case a: Abs => f(alpha(a))
      case a: App => App(f(a.t1), f(a.t2))
      case If(cond, t1, t2) => If(f(cond), f(t1), f(t2))
      case Pred(t1) => Pred(f(t1))
      case Succ(t1) => Succ(f(t1))
      case IsZero(t1) => IsZero(f(t1))
      case TermPair(t1, t2) => TermPair(f(t1), f(t2))
      case Second(t1) => Second(f(t1))
      case First(t1) => First(f(t1))
      case i@Inr(term, _) => i.copy(t = f(term))
      case i@Inl(term, _) => i.copy(t = f(term))
      case Case(t1, x1, t2, x2, t3) =>
        val t1p = f(t1)
        val (x1p, t2p) =
          if (x1 == x) (x1, t2)
          else if (!fv(s).contains(x1)) (x1, f(t2))
          else alpha(x1, t2)
        val (x2p, t3p) =
          if (x2 == x) (x2, t3)
          else if (!fv(s).contains(x2)) (x2, f(t3))
          else alpha(x2, t3)
        Case(t1p, x1p, t2p, x2p, t3p)
      case Fix(t) => Fix(f(t))
      case _ => t
    }
  }

  def alpha(x: String, term: Term): (String, Term) = {
    val newX = Stream.from(1).map(i => x + i).find(str => !fv(term).contains(str)).get
    (newX, replace(term, x, newX))
  }

  def isValue(t: Term): Boolean = t match {
    case s: Succ => isNumerical(s.t)
    case Zero() => true
    case True() => true
    case False() => true
    case _: Abs => true
    case TermPair(v1, v2) if isValue(v1) && isValue(v2) => true
    case Inr(t1, _) => isValue(t1)
    case Inl(t1, _) => isValue(t1)
    case _ => false
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case App(t1, t2) =>
      val res = (t1, t2) match {
        case (Abs(v, _, tin), t2) if isValue(t2) => subst(tin, v, t2)
        case (t1: Abs, t2: Term) => App(t1, reduce(t2))
        case _ => App(reduce(t1), t2)
      }
      res
    case i: If =>
      i.cond match {
        case True() => i.t1
        case False() => i.t2
        case Zero() => throw NoRuleApplies(i)
        case term => If(reduce(term), i.t1, i.t2)
      }
    case z: IsZero =>
      z.t match {
        case Zero() => True()
        case s: Succ if isNumerical(s.t) => False()
        case False() => throw NoRuleApplies(z)
        case True() => throw NoRuleApplies(z)
        case term => IsZero(reduce(term))
      }
    case p: Pred =>
      p.t match {
        case Zero() => Zero()
        case s: Succ if isNumerical(s.t) => s.t
        case False() => throw NoRuleApplies(p)
        case True() => throw NoRuleApplies(p)
        case term => Pred(reduce(term))
      }
    case s: Succ =>
      s.t match {
        case Zero() => throw NoRuleApplies(s)
        case False() => throw NoRuleApplies(s)
        case True() => throw NoRuleApplies(s)
        case term => Succ(reduce(term))
      }
    case First(TermPair(t1, t2)) if isValue(t1) && isValue(t2) => t1
    case Second(TermPair(t1, t2)) if isValue(t1) && isValue(t2) => t2
    case First(t) => First(reduce(t))
    case Second(t) => Second(reduce(t))
    case TermPair(t1, t2) if isValue(t1) => TermPair(t1, reduce(t2))
    case TermPair(t1, t2) => TermPair(reduce(t1), t2)
    case Case(Inl(v, _), x1, t1, _, _) if isValue(v) => subst(t1, x1, v)
    case Case(Inr(v, _), _, _, x2, t2) if isValue(v) => subst(t2, x2, v)
    case c @ Case(t, _, _, _, _) => c.copy(t = reduce(t))
    case Inr(t, tpe) => Inr(reduce(t), tpe)
    case Inl(t, tpe) => Inl(reduce(t), tpe)
    case Fix(Abs(x, tpe, t)) => subst(t, x, Fix(Abs(x, tpe, t)))
    case Fix(t) => Fix(reduce(t))
    case term => throw NoRuleApplies(term)
  }

  /**
    * Returns the type of the given term <code>t</code>.
    *
    * @param ctx the initial context
    * @param t   the given term
    * @return the computed type
    */
  def typeof(ctx: Context, t: Term): Type = {
    def f = (termArg: Term) => typeof(ctx, termArg)

    def throwError(msg: String) = throw new TypeError(t, msg)

    t match {
      case True() => TypeBool
      case False() => TypeBool
      case Zero() => TypeNat
      case Pred(t1) => f(t1) match {
        case TypeNat => TypeNat
        case _ => throwError("content of pred is not a Nat")
      }
      case Succ(t1) => f(t1) match {
        case TypeNat => TypeNat
        case _ => throwError("content of succ is not a Nat")
      }
      case IsZero(t1) => f(t1) match {
        case TypeNat => TypeBool
        case _ => throwError("content of iszero is not a Nat")
      }
      case If(t1, t2, t3) =>
        if (f(t1) != TypeBool) throwError("condition of if is not a boolean")
        val (typeThen, typeElse) = (f(t2), f(t3))
        if (typeThen != typeElse) throwError("then part has not the same type as the else part")
        typeThen
      case Var(x) =>
        val optTuple: Option[(String, Type)] = ctx.find { case (s, _) => s == x }
        optTuple.map(_._2).getOrElse(throwError("untyped variable"))

      case Abs(x, typeOfParam, body) => TypeFun(typeOfParam, typeof((x, typeOfParam) :: ctx, body))

      case App(t1, t2) => (f(t1), f(t2)) match {
        case (TypeFun(type1, type2), typeT2) if type1 == typeT2 =>
          type2
        case _ => throwError("the parameter type and the argument given do not have matching types")
      }
      case TermPair(t1, t2) => TypePair(f(t1), f(t2))
      case First(t1) => f(t1) match {
        case TypePair(type1, _) => type1
        case _ => throwError("element is not a pair and thus we cannot call fst upon it")
      }
      case Second(t1) => f(t1) match {
        case TypePair(_, type2) => type2
        case _ => throwError("element is not a pair and thus we cannot call snd upon it")
      }
      case c @ Case(t, x1, t1, x2, t2) => typeof(ctx, t) match {
        case TypeSum(ltpe, rtpe) =>
          val tpe1 = typeof(ctx :+ (x1, ltpe), t1)
          val tpe2 = typeof(ctx :+ (x2, rtpe), t2)
          if (tpe1 == tpe2) tpe1
          else throwError("the two part of match case does not have the same type")
        case _ => throwError("term matched have to be of type TypeSum")
      }
      case Inr(t, ts @ TypeSum(_, t2)) => if(typeof(ctx, t) == t2) ts else throwError("term is not the same as the declared type")
      case Inl(t, ts @ TypeSum(t1, _)) => if(typeof(ctx, t) == t1) ts else throwError("term is not the same as the declared type")
      case Inr(_, _) => throwError("inr have to be of type TypeSum")
      case Inl(_, _) => throwError("inl have to be of type TypeSum")
      case Fix(t) => typeof(ctx, t) match {
        case TypeFun(t1, t2) if t1 == t2 => t1
        case _ => throwError("fix takes a function of type T -> T as parameter")
      }
    }
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[Pair[String, Type]]

  /** Returns a stream of terms, each being one step of reduction.
    *
    * @param t      the initial term
    * @param reduce the evaluation strategy used for reduction.
    * @return the stream of terms representing the big reduction.
    */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("parsed: " + trees)
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
