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
     rep1(parse) ^^ {
      case x::Nil => x
      case l =>  l.reduceLeft(App(_,_))
    }
  )
  
  def Type: Parser[Type] = (
    "Bool" ^^^ TypeBool
  | "Nat" ^^^ TypeNat
  | "(" ~> Type <~ ")"
  | Type ~ "->" ~ Type ^^ {
    case t1 ~ "->" ~ t2 => TypeFun(t1, t2)
  }
  )
  
  def parse: Parser[Term] = (
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
  
  def numericTerm(i: Int): Term = (
      i match {
        case 0 => Zero()
        case x => Succ(numericTerm(x-1))
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
  def reduce(t: Term): Term =
    ???


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???


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
