package compiler
import ASTL._
import AST._
import ASTB._
/**Defines boolean operations to be applied on ASTLtrait, also applicable between two integer*/
trait MyOp[L <: Locus, R <: Ring] {
  this: ASTLtrait[L, R] =>
  // def unary_~[U >: R <: Ring](implicit m: repr[L], n: repr[U]): AST2[L, U] = ASTL.Unop2(neg.asInstanceOf[AST.Fundef1[R, U]], this);
  def unary_~(implicit m: repr[L], n: repr[R]): ASTLtrait[L, R] =
    { val xr = new Param[R]("x") with ASTBtrait[R]; ASTL.Unop(Fundef1("neg", Neg(xr), xr), this,m,n) }
  def |(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(orB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]],m,repr.nomB)
        case _   => Binop(orI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]],m,repr.nomI)
      }; res.asInstanceOf[ASTL[L, R]]
    }
  def &(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(andB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]],m,repr.nomB)
        case _   => Binop(andI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]],m,repr.nomI)
      }; res.asInstanceOf[ASTL[L, R]]
    }
  def ^(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(xorB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]],m,repr.nomB)
        case _   => Binop(xorI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]],m,repr.nomI)
      }; res.asInstanceOf[ASTL[L, R]]
    }

  //   def ^[U >: R <: Ring](that: AST2[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop2(xor.asInstanceOf[Fundef2[R, U, U]], this, that);
}

/** Integer spatial operators*/
trait MyOpInt2[L <: Locus, R <: Ring] { this: ASTLtrait[L, R] =>
  //we cannot directly check the type constraint R<:I, otherwise it clash with AST2, but we can impose that U<:I and U>:R,
  //and in fact, this implies that R<:I
  def +[U >: R <: I](that: ASTLtrait[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop(add.asInstanceOf[Fundef2[R, U, U]], this, that,m,n);
  def -[U >: R <: SI](that: ASTLtrait[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop(add.asInstanceOf[Fundef2[R, U, U]], this, -that,m,n);
  def unary_-(implicit m: repr[L], n: repr[R]): ASTLtrait[L, R] = { ASTL.Unop(opp.asInstanceOf[Fundef1[R, I]], this,m,repr.nomI).asInstanceOf[ASTLtrait[L, R]] }
  // def unary_-  (implicit m: repr[L],n: repr[R]): AST2[L, R] = { val xr=Param[R]("x") ;
  //    ASTL.Unop(Fundef1("opp", Call1(inc, Neg(xr).asInstanceOf[AST[I]]),xr ) , this).asInstanceOf[AST2[L,R]]}
}