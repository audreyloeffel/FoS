package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = (
     rep1(parseTerm) ^^ {
      case x::Nil => x
      case l =>  l.reduceLeft(App(_,_))
    }
  )
  
  def parseStar: Parser[Type] =(
       rep1sep(parseType, "*") ^^{
      case x::Nil => x
      case list => list.reduceRight(TypePair(_,_))
    }
      )
  
  def Type: Parser[Type] = (
    rep1sep(parseStar, "->") ^^{
      case x::Nil => x
      case list => list.reduceRight(TypeFun(_,_))
    }
  )
  
  def parseTerm: Parser[Term] = (
    "true" ^^^ True()
  | "false" ^^^ False()
  | "if" ~ Term ~ "then" ~ Term ~ "else" ~ Term ^^ {
      case "if" ~ cond ~ "then" ~ t1 ~ "else" ~ t2 => If(cond, t1, t2)  
  }
  | "succ" ~> Term ^^ Succ
  | "pred" ~> Term ^^ Pred
  | "iszero" ~> Term ^^ IsZero
  | ident ^^ { x => Var(x)}
  | "0" ^^^ Zero()
  | "(" ~> Term <~ ")"
  | numericLit ^^ { x => numericTerm(x.toInt)}
  | "\\" ~ ident ~ ":" ~ Type ~ "." ~ Term ^^ {
        case "\\" ~ x ~ ":" ~ tp~ "." ~ t => Abs(x, tp, t)
      } 
  |  "let" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ {
    case "let" ~ x ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(x, tp, t2), t1)
    }
  | "{" ~ Term ~ "," ~ Term ~ "}" ^^ {
    case "{" ~ t1 ~ "," ~ t2 ~ "}" => TermPair(t1, t2)
  }
  | "fst" ~> Term ^^ First
  | "snd" ~> Term ^^ Second  
  )
  
  def parseType: Parser[Type] =(
    "Bool" ^^^ TypeBool
  | "Nat" ^^^ TypeNat
  | "(" ~> Type <~ ")" 
  | Type ~ "*" ~ Type ^^{
    case t1 ~ "*" ~ t2 => TypePair(t1, t2)
  }
  
  )
  
  def numericTerm(i: Int): Term = (
      i match {
        case 0 => Zero()
        case x => Succ(numericTerm(x-1))
      }
  )

  def isNumeric(t: Term): Boolean = (
      
      t match {
        case Zero() => true
        case Succ(i) => isNumeric(i)
        case _ => false
      }
  )
  
  def isValue(t: Term): Boolean = (
  
      t match {
        case True() => true
        case False() => true
        case Abs(_,_,_) => true
        case TermPair(a, b) => isValue(a) && isValue(b)
        case _ => isNumeric(t)
      }
  
  )

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Call by value reducer. */
  def reduce(t: Term): Term = {  
    
      t match {
        case If(True(), t1, _) => t1
        case If(False(), _, t2) => t2
        case IsZero(Zero()) => True()
        case IsZero(Succ(n))if isNumeric(n) => False()
        case Pred(Zero()) => Zero()
        case Pred(Succ(n)) if isNumeric(n)=> n
        case App(Abs(x, ty, t1), v) if isValue(v) => subst(t1, x, v)
        case If(Reducable(t1p), t2, t3) => If(t1p, t2, t3)
        case IsZero(Reducable(t1p)) => IsZero(t1p)
        case Pred(Reducable(t1p)) => Pred(t1p)
        case Succ(Reducable(t1p)) => Succ(t1p)
        case App(Reducable(t1p), t2) => App(t1p, t2)
        case App(v1, Reducable(t2p)) if isValue(v1) => App(v1, t2p)
        case First(TermPair(v1, v2)) if isValue(v1)&&isValue(v2) => v1
        case Second(TermPair(v1, v2)) if isValue(v1)&&isValue(v2) => v2
        case First(Reducable(t1)) => First(t1)
        case Second(Reducable(t2)) => Second(t2)
        case TermPair(Reducable(t1p), t2) => TermPair(t1p, t2)
        case TermPair(t1, Reducable(t2p)) => TermPair(t1, t2p)
        case _ => throw new NoRuleApplies(t)
      }
      
  }
  
    object Reducable{
    def unapply(t: Term):
    Option[Term] =
        try {
          //println(t.toString);
          Some(reduce(t))
        } catch {
          case t: NoRuleApplies => None
    }
    
  }
  
    def freeVariable(t: Term): Set[String] = (
      t match {
        case Var(x) => Set(x)
        case Abs(a, _, b) => freeVariable(b) - a
        case App(a, b) => freeVariable(a) ++ freeVariable(b) 
        case Pred(t1) => freeVariable(t1)
        case Succ(t1) => freeVariable(t1)
        case IsZero(t1) => freeVariable(t1)
        case If(cond, t1, t2) => freeVariable(cond) ++ freeVariable(t1) ++ freeVariable(t2)
        case TermPair(t1, t2) => freeVariable(t1) ++ freeVariable(t2)
        case First(t1) => freeVariable(t1)
        case Second(t1) => freeVariable(t1)
        case _ => Set.empty
      }
   )
  
  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t</code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Term): Term = (
      
      t match {
        case Abs(x, ty, t2) => {
          val uuid = java.util.UUID.randomUUID().toString
          Abs(uuid, ty, subst(t2, x, Var(uuid)))
        }
        case _ => t
      }    
  )
  
  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = {
     // println("subst "+t.toString)
      t match {
        case Var(`x`) => s
        case Abs(y, ty, t1) if (y != x && !(freeVariable(s)(y))) => Abs(y, ty, subst(t1, x, s))
        case Abs(y, _, t1) if (y != x && (freeVariable(s)(y))) => subst(alpha(t), x, s)
        case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
        case Pred(t1) => Pred(subst(t1, x, s))
        case Succ(t1) => Succ(subst(t1, x, s))
        case IsZero(t1) => IsZero(subst(t1, x, s))
        case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
        case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
        case First(t1) => First(subst(t1, x, s))
        case Second(t1) => Second(subst(t1, x, s))
        case _ => t
      }
  
  }
  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = (
      
    t match {
      case True() => TypeBool
      case False() => TypeBool
      case Zero() => TypeNat
      case Succ(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeNat
        case ty => throw new TypeError(t, "parameter type mismatch: expected: Nat, found "  + ty.toString)
        }
      case Pred(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeNat
        case ty => throw new TypeError(t, "parameter type mismatch: expected: Nat, found "  + ty.toString)
      }
      case IsZero(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeBool
        case ty => throw new TypeError(t, "parameter type mismatch: expected: Bool, found "  + ty.toString)
      }
      case If(cond, t1, t2) => (typeof(ctx, cond), typeof(ctx, t1), typeof(ctx, t2)) match {
        case (TypeBool, tp1, tp2) if tp1 == tp2 => tp1
        case (tp1, tp2, tp3) => throw new TypeError(t, "parameter type mismatch: expected: (Bool, t, t), found If "+tp1.toString +" then "+ tp2.toString +" else "+tp3.toString())
      }
      case Var(x) => ctx.find(_._1 == x).getOrElse(throw new TypeError(t, "variable " + x + " is undefined"))._2
      case Abs(x, ty, t2)  => TypeFun(ty, typeof((x, ty)::ctx, t2))
      case App(t1, t2) => (typeof(ctx, t1), typeof(ctx, t2)) match {
        case (TypeFun(tp1, tp2), tp3) if tp1 == tp3 => tp2 
        case (tp1, tp2) => throw new TypeError(t, "parameter type mismatch: expected: Fun, found: "+tp1.toString +", "+ tp2.toString)
      }
      case TermPair(t1, t2) =>  TypePair(typeof(ctx, t1), typeof(ctx, t2))
      case First(t1) => typeof(ctx, t1) match {
        case TypePair(t1p, t2p) => t1p
        case ty => throw new TypeError(t, "parameter type mismatch: expected: Pair, found "  + ty.toString)
        }
      case Second(t1) => typeof(ctx, t1) match {
        case TypePair(t1p, t2p) => t2p
        case ty => throw new TypeError(t, "parameter type mismatch: expected: Pair, found "  + ty.toString)
        }
      }
  )

    
  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
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
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => tperror.printStackTrace
        }
      case e =>
        println(e)
    }
  }
}
