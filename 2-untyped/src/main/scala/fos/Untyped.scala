package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] = (
    rep1(a) ^^ {
      case x::Nil => x
      case l =>  l.reduceLeft(App(_,_))
    }
  )
  
  def a: Parser[Term] = (
      ident ^^ { x => Var(x)}
      | "\\" ~ ident ~ "." ~ term ^^ {
        case "\\" ~ x ~ "." ~ t => Abs(x, t)
      }
      | "(" ~> term <~ ")"
  )
    
  
  def freeVariable(t: Term): Set[String] = (
      t match {
        case Var(x) => Set(x)
        case Abs(a,b) => freeVariable(b) - a
        case App(a,b) => freeVariable(a) ++ freeVariable(b) 
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
        case Abs(x,t2) => {
          val uuid = java.util.UUID.randomUUID().toString()
          Abs(uuid, replaceUUID(x, uuid, t2))
        }
        case _ => t
      }    
  )
  def replaceUUID(x: String, uuid: String, t: Term): Term = (
      
    t match {
      case Var(`x`) => Var(uuid)
      case Var(y) if y!=x => t
      case App(t1, t2) => App(replaceUUID(x, uuid, t1), replaceUUID(x, uuid, t2))
      case Abs(`x`, t1 ) => Abs(uuid, replaceUUID(x, uuid, t1))
      case Abs(y, t1) => Abs(y, replaceUUID(x, uuid, t1))
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
        case Abs(`x`, t1) => t
        case Abs(y, t1) if (y != x && !(freeVariable(s) contains y)) => Abs(y, subst(t1, x, s))
        case Abs(y, t1) if (y != x && (freeVariable(s) contains y)) => subst(alpha(t), x, s)
        case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
        case _ => t
      }
  
  )

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  object ReducableNormalOrder{
    def unapply(t: Term):
    Option[Term] =
        try {
          Some(reduceNormalOrder(t))
        } catch {
          case t: NoReductionPossible => None
    }
    
  }
  
    object ReducableCallByValue{
    def unapply(t: Term):
    Option[Term] =
        try {
          Some(reduceCallByValue(t))
        } catch {
          case t: NoReductionPossible => None
    }
    
  }
  
  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = (
      
      t match {
        case App(Abs(x, t), t2) => subst(t, x, t2)  
        case App(ReducableNormalOrder(t1p), t2) =>  App(t1p, t2)
        case App(t1, ReducableNormalOrder(t2p)) => App(t1, t2p)
        case Abs(x, ReducableNormalOrder(tp)) => Abs(x, tp)    
        case _ => throw new NoReductionPossible(t)        
      }
  
  )

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = (
      t match {
        case App(Abs(x, t1), Var(t2)) => subst(t1, x, Var(t2))
        case App(Abs(x,t1), Abs(y, t2)) => subst(t1, x, Abs(y, t2))
        case App(Var(t1), ReducableCallByValue(t2p)) => App(Var(t1), t2p)   
        case App(Abs(y, t2), ReducableCallByValue(t2p)) => App(Abs(y, t2), t2p)   
        case App(ReducableCallByValue(t1p), t2) => App(t1p, t2)
        case _ => throw new NoReductionPossible(t)
      }
  
  )

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
