package compiler

import UsrInstr._
import junit.framework.Assert.assertEquals
import ASTB._
import ASTBfun._
import scala.collection._
import ASTL._
import AST._
import repr._
import ProgData._

/**
 * Adds boolean spatial operator to AST of spatial types
 * Also used to bridge the gap with AST. ASTL is inheriting from ASTLtrait,
 * an ASTL is therefore a more specific instance of ASTLtrait which  makes use of the catalog of ASTL's contructors.
 * ASTLtrait = AST + ASTL, therefore we should process them separately with a preliminary match, at the level of ASTLtrait.
 * ASTL's constructor uses ASTLtrait for children in order to incorporate AST's nodes.
 * Identifies AST corresponding to int or bool, plus a locus, excludes those obtained with cons
 */

trait ASTLt[L <: Locus, R <: Ring] extends AST[Tuple2[L, R]] with MyOp[L, R] with MyOpInt2[L, R] {

  self: AST[Tuple2[L, R]] =>
  def locus = mym.name._1; def ring = mym.name._2;
  def extendMe(n: Int): ASTLt[L, R] = ASTL.extend(n, this)(new repr(locus), new repr(ring))

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved, and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   * @nUser the number of other expression using this expression
   * @return the Dag where expression used more than once are replaced by read.
   *  generates ASTs such as READ that preserve the implementation of  ASTLscal by using "with"
   */
  override def deDag(usedTwice: immutable.HashSet[AST[_]], repr: Map[AST[_], AST[_]], replaced: Map[AST[_], AST[_]]): ASTLt[L, R] = {
    val newD = if (usedTwice.contains(this) && usedTwice.contains(this)) new Read[Tuple2[L, R]](repr(this).name)(mym) with ASTLt[L, R]
    else if (replaced.contains(this)) replaced(this).deDag(usedTwice, repr, replaced)
    else this match {

      case a: ASTL[_, _] =>
        if (a.isInstanceOf[Layer[_, _]]) new Read[Tuple2[L, R]]("l" + repr(this).name)(mym) with ASTLt[L, R]
        else a.propagate((d: ASTLt[L, R]) => d.deDag(usedTwice, repr, replaced))
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(s) => new Read[Tuple2[L, R]]("p" + repr(this).name)(mym) with ASTLt[L, R]
        case Read(s)  => throw new RuntimeException("Deja dedagifié!")
        case _        => this.propagate((d: AST[(L, R)]) => d.deDag(usedTwice, repr, replaced))
      }
    }
    newD.setName(this.name); newD.asInstanceOf[ASTLt[L, R]]
  }

  /**For AST created with ASTLscal, we cannot do simple copy, because the ''with ASTLscal is lost. */
  def propagate(g: bij2[(L, R)]): ASTLt[L, R] = { //to allow covariance on R, second argument of bij2 is l
    val m = mym.asInstanceOf[repr[Tuple2[L, R]]];
    val newThis = this.asInstanceOf[AST[_]] match {
      case Read(s)         => this
      case Param(s)        => this
      case e @ Taail(a)    => new Taail[(L, R)](g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[(Any, (L, R))]])(m) with ASTLt[L, R]
      case e @ Heead(a)    => new Heead[(L, R)](g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[((L, R), Any)]])(m) with ASTLt[L, R]
      case e @ Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, (L, R)]], g(a.asInstanceOf[AST[(L, R)]]))(m) with ASTLt[L, R]
      case e @ Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, (L, R)]], g(a.asInstanceOf[AST[(L, R)]]),
        g(a2.asInstanceOf[AST[(L, R)]]))(m) with ASTLt[L, R]
      case e @ Call3(f, a, a2, a3) => new Call3(
        f.asInstanceOf[Fundef3[Any, Any, Any, (L, R)]],
        g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]], g(a2.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]],
        g(a3.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]])(m) with ASTLt[L, R]
      case _ => throw new RuntimeException("ciel ")
    }
    newThis.setName(this.name); newThis
  }

  /**  @nbitLB: computes the #bit of all the ASTL sub expressions, there can be several.   */
  override def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): ASTLt[L, R] = {
    var newThis = this.propagate((d: AST[(L, R)]) => d.nbit(cur, nbitLB, tSymb, newFuns))
    nbitLB += (newThis -> newThis.newNbitAST(nbitLB, tSymb, newFuns))
    newThis.setName(this.name); newThis //.asInstanceOf[ASTLt[L, R]]
  }

  /**  Only read node are non ASTL nodes and are treated in ASTLt.*/
  override def unfoldSpace(m: Machine): List[ASTBt[_]] =
    this.asInstanceOf[AST[_]] match {
      case Read(s) =>
        val r = rpart(mym.asInstanceOf[repr[Tuple2[L, R]]]);
        deploy(s, this.locus).map(new Read(_)(r) with ASTBt[R])
      case _ => this.locus match {
        case s: S      => this.unfoldSimplic(m).toList
        case T(s1, s2) => this.unfoldTransfer(m).map(_.toList).toList.flatten
      }
    }

  override def unfoldSimplic(m: Machine): ArrAst = this.asInstanceOf[AST[_]] match {
    case Read(s) =>
      val r = rpart(mym.asInstanceOf[repr[Tuple2[L, R]]]);
      this.locus.sufx.map((suf: String) => (new Read[R](s+ suf)(r) with ASTBt[R]). asInstanceOf[ ASTBt[_<:Ring ]] ) 
    case _ => throw (new RuntimeException("unfoldSpace act only on Reads for ASTL "))
  }
  override def unfoldTransfer(m: Machine): ArrArrAst = this.asInstanceOf[AST[_]] match {
    case Read(s) =>
      val T(s1, s2) = this.locus; val r = rpart(mym.asInstanceOf[repr[Tuple2[L, R]]]);
      s1.sufx.map((suf1: String) => this.locus.sufx.map((suf2: String) =>(new Read(s+suf1+suf2)(r) with ASTBt[R]). asInstanceOf[ ASTBt[_<:Ring ]] )) 
    case _ => throw (new RuntimeException("unfoldSpace act only on Reads for ASTL "))
  }
  override def align:iTabSymb[Array[Int]] =  this.asInstanceOf[AST[_]] match {
    case Read(s) =>  immutable.HashMap( s->locus.neutral)
    case Param(s) => immutable.HashMap( s->locus.neutral)
}
  
}