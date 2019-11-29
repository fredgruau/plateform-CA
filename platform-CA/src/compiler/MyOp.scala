package compiler
import ASTL._
import AST._
import ASTB._
import ASTBfun._
/**
 * Defines boolean operations to be applied on ASTLtrait, also applicable between two integer
 * Internally, within ASTB integers without consideration for Unsigned, or Signed are used,
 * this avoids codes duplication, and allows to introduce fundefs as vals.
 * However, when applied, only Signed or Unsigned UI must be used, (nameI=repr[I] is not implicit)
 * and it is guaranteed that
 * unsigned (resp. signed) are combined with unsigned (resp. signed) and produce unsigned (resp. signed)
 */
trait MyOp[L <: Locus, R <: Ring] {
  this: ASTLt[L, R] =>
  /**
   * In order to obtain covariance, we would need to introduc types L,U
   *   def ^[U >: R <: Ring ](that: ASTLscal[L,U])(implicit m: repr[L],n:repr[U]): ASTL[L, U] =    {      val res = ring match {
   * case B() => Binop(xorB, this.asInstanceOf[ASTLscal[L, B]], that.asInstanceOf[ASTLscal[L, B]],m,repr.nomB)
   * case _   => Binop(xorUISI.asInstanceOf[Fundef2[R,U,U]], this , that ,m,n)
   * }; res.asInstanceOf[ASTL[L, U]]    }
   */
  def |(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = or(this, that)
  def &(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = and(this, that)
  def ^(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = xor(this, that)
  def unary_~(implicit m: repr[L], n: repr[R]): ASTL[L, R] = neg(this)

}
/** Integer spatial operators:  we cannot directly check the type constraint R<:I, ( clash with ASTLs, but we can impose that U<:I and U>:R,  which implies that R<:I*/
trait MyOpInt2[L <: Locus, R <: Ring] { this: ASTLt[L, R] =>
  /**  adds does not imposes all the operands to be equal type (SI, or UI), no message is given, but compilation fails due to lack of implicit repr[I] */
  def +[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = add(this, that)
  /**   minus  imposes signed SI.*/
  def -[U >: R <: SI](that: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTL[L, SI] = add[L, SI](this.asInstanceOf[ASTL[L, SI]], -that)

//  def unary_-(implicit m: repr[L]): ASTLt[L, SI] = { ASTL.Unop(opp.asInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }
  def unary_-(implicit m: repr[L], n: repr[R]): ASTLt[L, SI] = opp(this)
 
}