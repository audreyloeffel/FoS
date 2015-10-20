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
  
  def Type: Parser[Type] = (
    rep1sep(parseType, "->") ^^{
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
  
  )
  
  def parseType: Parser[Type] =(
    "Bool" ^^^ TypeBool
  | "Nat" ^^^ TypeNat
  | "(" ~> Type <~ ")" 
  
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
        case _ if isNumeric(t) => true
        case _ => false
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
  def reduce(t: Term): Term = (
      t match {
        case If(True(), t1, t2) => t1
        case If(False(), t1, t2) => t2
        case IsZero(Zero()) => True()
        case IsZero(Succ(n))if isNumeric(n) => False()
        case Pred(Zero()) => Zero()
        case Pred(Succ(n)) if isNumeric(n)=> n
        case Abs(t1, ty, v2) if isValue(v2) => subst(t, t1, v2)
        case If(t1, t2, t3) => If(reduce(t1), t2, t3)
        case IsZero(t1) => IsZero(reduce(t1))
        case Pred(t1) => Pred(reduce(t1))
        case Succ(t1) => Succ(reduce(t1))
        case App(t1, t2) => App(reduce(t1), t2)
        case App(v1, t2) if isValue(v1) => App(v1, reduce(t2))
        case _ => throw new NoRuleApplies(t)
      }
      
  )
  
    object Reducable{
    def unapply(t: Term):
    Option[Term] =
        try {
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
          val uuid = java.util.UUID.randomUUID().toString()
          Abs(uuid, ty, replaceUUID(x, uuid, t2))
        }
        case _ => t
      }    
  )
  def replaceUUID(x: String, uuid: String, t: Term): Term = (
      
    t match {
      case Var(`x`) => Var(uuid)
      case Var(y) if y!=x => t
      case App(t1, t2) => App(replaceUUID(x, uuid, t1), replaceUUID(x, uuid, t2))
      case Abs(`x`, ty, t1 ) => Abs(uuid, ty, replaceUUID(x, uuid, t1))
      case Abs(y, ty, t1) => Abs(y, ty, replaceUUID(x, uuid, t1))
      case Pred(t1) => Pred(replaceUUID(x, uuid, t1))
      case Succ(t1) => Succ(replaceUUID(x, uuid, t1))
      case IsZero(t1) => IsZero(replaceUUID(x, uuid, t1))
      case If(cond, t1, t2) => If(replaceUUID(x, uuid, cond), replaceUUID(x, uuid, t1), replaceUUID(x, uuid, t2))
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
  def subst(t: Term, x: String, s: Term): Term = (
      
      t match {
        case Var(`x`) => s
        case Var(i) if i!="x" => t        
        case Abs(`x`, _, t1) => t
        case Abs(y, ty, t1) if (y != x && !(freeVariable(s) contains y)) => Abs(y, ty, subst(t1, x, s))
        case Abs(y, _, t1) if (y != x && (freeVariable(s) contains y)) => subst(alpha(t), x, s)
        case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
        case Pred(t1) => Pred(subst(t1, x, s))
        case Succ(t1) => Succ(subst(t1, x, s))
        case IsZero(t1) => IsZero(subst(t1, x, s))
        case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
        case _ => t
      }
  
  )

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = (
    t match {
      case _ => ???
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
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
