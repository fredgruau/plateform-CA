package compiler

import junit.framework.Assert.fail
import ASTB._
import AST._
import scala.collection.immutable.HashMap
sealed class Dir
final case class Left() extends Dir
final case class Right() extends Dir
final case class Both() extends Dir

sealed class Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.
final case class B() extends Ring //le type boolean
class I extends Ring //le type entier etends boolean, car or, and, xor sont defini pour les entiers.
final case class UI() extends I //unsigned int
final case class SI() extends I //signed int
//partial int will be treated using library

trait ASTBtrait[+R <: Ring] extends AST[R]

/** node of Abstract Syntax Tree corresponding to an arithmetic field  boolean, integer (signed or unsigned)
 *  We wish to be able to preserve covariance of R.  */
sealed abstract class ASTB[+R <: Ring]()(implicit m: repr[R]) extends ASTBtrait[R] /** not necessary, just to remember how to retrieve the name*/ {
  // override val ( locus , ring) = m.name; val l = new repr(locus); val r = new repr(ring)
  override def ring = m.name;
}

/** -1 for integer (to work with reduction) */
case class True[R <: Ring]()(implicit n: repr[R]) extends ASTB[R] with EmptyBag[AST[_]]
/** 0 for integer */
case class False[R <: Ring]()(implicit n: repr[R]) extends ASTB[R] with EmptyBag[AST[_]]
/**  LSB, Least significant bit has index 0, and is therefore head of list. */
case class ConstInt[R <: I](val value: Int)(implicit n: repr[R]) extends ASTB[R] with EmptyBag[AST[_]]
case class ConstSignedInt(val value: Int, val size: Int)(implicit n: repr[SI]) extends ASTB[SI] with EmptyBag[AST[_]] { assert(value < Math.pow(2, size - 1) && value >= -Math.pow(2, size - 1), "not enough bits") }
case class ConstUnsignedInt(val value: Int, val size: Int)(implicit n: repr[UI]) extends ASTB[UI] with EmptyBag[AST[_]] { assert(value < Math.pow(2, size) && value >= 0, "not enough bits") }
/** builds an int from several booleans*/
case class Concat[R <: I](exps: Seq[ASTBtrait[R]])(implicit n: repr[R]) extends ASTB[R] with Neton1[AST[_]]
case class Concat2[R1 <: Ring, R2 <: Ring](exp: ASTBtrait[R1], exp2: ASTBtrait[R2])(implicit n: repr[I]) extends ASTB[I] with Doubleton1[AST[_]]
/** returns bit at position i*/
case class Elt[R <: I](i: Int, exp: ASTBtrait[R])(implicit n: repr[B]) extends ASTB[B] with Singleton1[AST[_]]()
/** will copy the msb*/
case class Extend[R <: I](i: Int, exp: ASTBtrait[R])(implicit n: repr[R]) extends ASTB[R] with Singleton1[AST[_]]()

//case class Extend[R<:I]( i:Int, x:ASTB[R]) extends ASTB[R](i){assert(x.nbit<i)}
//case class Reduce[R<:I](x:ASTB[R],op:redop[ASTB[B]]) extends ASTB[B]

/**
 *  @d is a direction. left means from the least significant bits towards the msb, and   right is the other way round.
 */
abstract class ParOp[R <: Ring](d: Dir)(implicit n: repr[R]) extends ASTB[R]

case class Or[R <: Ring](val exp: ASTBtrait[R], val exp2: ASTBtrait[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
case class And[R <: Ring](val exp: ASTBtrait[R], val exp2: ASTBtrait[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
case class Xor[R <: Ring](val exp: ASTBtrait[R], val exp2: ASTBtrait[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
case class Neg[R <: Ring](val exp: ASTBtrait[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton1[AST[_]]

//case class Mapp[R <: I](exp: ASTBtrait[B], exp2: ASTBtrait[R], op: (ASTB[B], ASTB[B]) => ASTB[B])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]]
case class Mapp1[R <: I](exp: ASTBtrait[B], exp2: ASTBtrait[R], op: Fundef2[B, B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]]
case class Mapp2[R <: I](exp: ASTBtrait[R], exp2: ASTBtrait[R], op: Fundef2[B, B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]]

/**  init, is  part of the result */
case class Scan1[R <: I](exp: ASTBtrait[R], op: Fundef2R[B], init: ASTBtrait[B], d: Dir, initUsed: Boolean)(implicit n: repr[R]) extends ParOp[R](d) with Singleton1[AST[_]]
case class Scan2[R <: I](exp: ASTBtrait[R], exp2: ASTBtrait[R], op: Fundef3R[B], init: ASTBtrait[B], d: Dir, initUsed: Boolean)(implicit n: repr[R]) extends ParOp[R](d) with Doubleton1[AST[_]]
case class Reduce[R <: I](exp: ASTBtrait[R], op: Fundef2R[B], init: ASTBtrait[B])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton1[AST[_]]
/*
case class ScanRight1Init[R <: I](exp: ASTBtrait[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanLeft1Init[R <: I](exp: ASTB1[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanLeft2Init2[R <: I](exp: ASTB1[R], y: ASTB1[R], op: Fundef3R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]] //{assert(y.nbit==x.nbit)}
/**  init, is not part of the result */
case class ScanRight1[R <: I](exp: ASTB1[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanRight2[R <: I](exp: ASTB1[R], exp2: ASTB1[R], op: Fundef3R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
*/
/** static object using arithmetic parse trees, operators gets a name, using another method, with the letter 'n' appended  */
object ASTB { //
  // implicit def toASTB[ R<:I](int i):ASTB[R]=
  val lnOf2 = scala.math.log(2) // natural log of 2
  def log2(x: Double): Int = scala.math.ceil(scala.math.log(x) / lnOf2).toInt
  /**
   * @nbit stores the number of bits of parameters
   * @d the AST we want to know how many bits it has
   */

  def computeNbit(nbit: scala.collection.immutable.HashMap[AST[_], Int], d: AST[_]): Int =
    d match {
      case ConstSignedInt(_,   size ) => size
      case ConstUnsignedInt(_,   size ) => size
      case ConstInt(n) => log2(n) // new Read[Tuple2[L2, R2]](n)(d.mym.asInstanceOf[repr[Tuple2[L2, R2]]]) with ASTLtrait[L2, R2]
      case True()      => 1 //ca sera augmenté ensuite.
      case False()     => 1
      case Call1(f, e) => computeNbit( nbit + (f.p1 ->  computeNbit(nbit, e)),       f.body)      
      case Call2(f, e,e2) => computeNbit( nbit + (f.p1 ->  computeNbit(nbit, e)) + (f.p2 ->  computeNbit(nbit, e2)),  f.body)
      case e @ Param(x)                        => nbit(e)
      case Neg(x)                              => computeNbit(nbit, x)
      case Xor(x, y)                           => math.max(computeNbit(nbit, x), computeNbit(nbit, y))
      case Or(x, y)                            => math.max(computeNbit(nbit, x), computeNbit(nbit, y))
      case And(x, y)                           => math.max(computeNbit(nbit, x), computeNbit(nbit, y))
      case Scan1(exp, _, _, _, initused)       => computeNbit(nbit, exp) + (if (initused) 0 else 0)
      case Scan2(exp, exp2, _, _, _, initused) => math.max(computeNbit(nbit, exp), computeNbit(nbit, exp2))
      case Reduce(exp, op, init)               => 1 //TODO ici on suppose que la reduction est booleenne.
      case Mapp2(exp, exp2, opp)               => math.max(computeNbit(nbit, exp), computeNbit(nbit, exp2))
      case Mapp1(exp, exp2, opp)               => computeNbit(nbit, exp2)
      case Elt(i, exp)                         => 1;
      case Concat2(exp, exp2)                  => computeNbit(nbit, exp2) + computeNbit(nbit, exp) //
     case Extend(n, exp)                  =>  n
    }

  import AST._
  //  def nbit[R1<:Ring,R2<:Ring,R3<:Ring](n1:Int,n2:Int, op:(ASTB[R1],ASTB[R2] )=>ASTB[R3]):Int={val t=op(True[R1](n1),True[R2](n2));t.nbit}
  //  def nbit[R1<:Ring,R2<:Ring](n1:Int,  op: ASTB[R1] =>ASTB[R2]) :Int={val t=op(True[R1](n1));t.nbit}
  // def nbit[R1<:Ring,R2<:Ring](n1:List[Int],  op: Seq[ASTB[R1]] =>ASTB[R2]) :Int={val t=op( n1.map(x=>True[R1](x) ));t.nbit}
  type ASTB1[R <: Ring] = ASTBtrait[R]
  type ASTBg = ASTB[_ <: Ring]
  type Fundef3R[R <: Ring] = Fundef3[R, R, R, R]
  type Fundef2R[R <: Ring] = Fundef2[R, R, R]
  type Fundef1R[R <: Ring] = Fundef1[R, R]

  private def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBtrait[R]
  val carry: Fundef3R[B] = {
    val (xb, yb, zb) = (p[B]("x"), p[B]("y"), p[B]("z"))
    Fundef3("carry", Or(And(xb, yb), And(zb, Or(xb, yb))), xb, yb, zb)
  } //boolean computation used by add
  import repr._
  val add: Fundef2R[I] = { val (x, y) = (p[I]("x")(nomI), p[I]("y")); Fundef2("add", Xor(Xor(x, y), Scan2(x, y, carry, False[B], Left(), true)), x, y) }
  val orB: Fundef2R[B] = { val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("orB", Or(xb, yb), xb, yb) }
  val orI: Fundef2R[I] = { val (x, y) = (p[I]("x"), p[I]("y")); Fundef2("orI", Mapp2(x, y, orB), x, y) }
  val andB: Fundef2R[B] = { val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("andB", And(xb, yb), xb, yb) }
  val andI: Fundef2R[I] = { val (x, y) = (p[I]("x"), p[I]("y")); Fundef2("andI", Mapp2(x, y, andB), x, y) }
  val xorB: Fundef2R[B] = { val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("xorB", Xor(xb, yb), xb, yb) }
  val xorI: Fundef2R[I] = { val (x, y) = (p[I]("x"), p[I]("y")); Fundef2("xorI", Mapp2(x, y, xorB), x, y) }
  val minSI: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi")); Fundef2("minSI", Mapp2(xsi, ysi, xorB), xsi, ysi)
  } //TODO a faire correct en utilisant gt.
  val minUI: Fundef2R[UI] = {
    val (xui, yui) = (p[UI]("xui"), p[UI]("yui")); Fundef2("minUI", Mapp2(xui, yui, xorB), xui, yui)
  } //TODO a faire correct en utilisant .
  val andLBtoR: Fundef2[B, I, I] = { val (xb, y) = (p[B]("xb"), p[I]("y")); Fundef2("andLBtoR", Mapp1(xb, y, andB), xb, y) }
  def elt(i: Int): Fundef1[I, B] = { val x = p[I]("x"); Fundef1("elt", Elt[I](i, x), x) }
  def extend(i: Int): Fundef1[I, I] = { val x = p[I]("x"); Fundef1("extend"+i, Extend[I](i, x), x) }
  // addition must be programmed
  val inc: Fundef1R[I] = { val x = p[I]("x"); Fundef1("inc", Xor(x, Scan1(x, andB, True[B], Left(), true)), x) } //TODO a tester
  //val gtB: Fundef1[SI,B] = { val xsi = Param[SI]("xsi"); Fundef1("gt",   Concat2( Elt(2), x) } //TODO a tester
  val notNullB: Fundef1[I, B] = { val x12 = p[I]("x"); Fundef1("notNull", Reduce(x12, orB, False[B]), x12) }
  val sign: Fundef1R[I] = { val x = p[I]("x"); Fundef1("sign", Concat2(new Call1(notNullB, x) with ASTBtrait[B], Elt(2, x)), x) } //TODO remplacer 2 par size.

  //Attention, lorsq'on prend le opp d'un unsigned, faut vérifier que ca devient un signe, et que la taille augmente. (commencer par concateter 0)
  val opp: Fundef1R[I] = { val x = p[I]("x"); ; Fundef1("opp", new Call1(inc, Neg(x).asInstanceOf[AST[I]]) with ASTBtrait[I], x) }
  val other: Fundef2R[B] = { val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("other", yb, xb, yb) }
  /** result in shifting bits towards the tail, entering a zero at the end of the list  */
  val halveB: Fundef1R[I] = { val x = p[I]("x"); Fundef1("halve", Scan1(x, other, False[B], Right(), true), x) } //TODO a tester
  val orScanRightB: Fundef1R[I] = { val x = p[I]("x"); Fundef1("orScanRight", Scan1(x, orB, False[B], Right(), false), x) }
  // def notNull[R <: I](x: ASTB[R]) = FoldLeft1(x, Or[B])

  class NamedFunction2[T1, T2, R](name: String, f: Function2[T1, T2, R]) extends Function2[T1, T2, R] {
    def apply(a: T1, b: T2): R = f.apply(a, b); override def toString = name
  }
  class NamedFunction1[T1, R](name: String, f: Function1[T1, R]) extends Function1[T1, R] {
    def apply(a: T1): R = f.apply(a); override def toString = name
  }
  type op2B[R <: Ring] = NamedFunction2[ASTB[B], ASTB[R], ASTB[R]];
  type op2[R <: Ring] = NamedFunction2[ASTB[R], ASTB[R], ASTB[R]];
  type op1[R1 <: Ring, R2 <: Ring] = NamedFunction1[ASTB[R1], ASTB[R2]];
  type opN[R1 <: Ring, R2 <: Ring] = NamedFunction1[Seq[ASTB[R1]], ASTB[R2]];
  def concatN[R <: I](implicit n: repr[R]) = new opN[R, R]("concat", Concat[R](_))
  type redop[A <: Ring] = (Fundef2R[A], ASTB[A]);

}

 

