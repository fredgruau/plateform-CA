package compiler

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail
import ASTB._
import scala.collection.immutable.HashMap

/**Test the correct implementation of integer operation, by evaluating them */
class ASTBtest extends TestCase {
  /** Binary code, LSB at head */
  def toBinary(n: Int, size: Int): List[Boolean] =
    if (size == 0) List() else (if (n % 2 == 1) true else false) :: toBinary(n / 2, size - 1)

  def toInt(xs: List[Boolean]): Int = (xs :\ 0)((x, y) => 2 * y + (if (x) 1 else 0))
  // def toASTB(x: Boolean) = if (x) True() else False()
  //def carryFromCode(x: Boolean, y: Boolean, z: Boolean) = eval(carry(toASTB(x), toASTB(y), toASTB(z)))
  // def fromASTB(x: Boolean, y: Boolean, z: Boolean, op: (ASTB[B], ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y), toASTB(z)));
  // def fromASTB(x: Boolean, y: Boolean, op: (ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y)));
  private def condReverseIn[T](l: List[T], d: Dir): List[T] = d match { case Right() => l.reverse case _ => l }
  private def condReverseOut[T](l: List[T], d: Dir): List[T] = d match { case Right() => l case _ => l.reverse }
  private def scan[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1, d: Dir, initTaken: Boolean): List[T1] = {
    var result = if (initTaken) List(init) else List();
    var carry = init;
    for (elt <- condReverseIn(xs, d)) { carry = op(carry, elt); result = carry :: result }
    return (condReverseOut( (if(initTaken) result.tail else result), d)) //le # bit reste le meme, parcequ'on enléve la derniere carry si y a init
  }

  def scanRight[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init); var carry = init;
    for (elt <- xs) { carry = op(carry, elt); result = carry :: result }
    return (result.tail)
  }
  /**Forget the additional most significant new bits. */
  def scanLeft[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init); var carry = init;
    for (elt <- xs) { carry = op(carry, elt); result = carry :: result }
    return (result.tail.reverse)
  } // the .tail forget the supplementary bit.
  import AST._
  /*   private def eval2(b: ASTB[B], env: HashMap[Param[_<:I], List[Boolean]] ,  envb: HashMap[Param[B], Boolean]  ): Boolean = b match {
   case Or(x, y)  => eval2(x,env,envb) | eval2(y,env,envb)
    case And(x, y) => eval2(x,env,envb) & eval2(y,env,envb)
    case Xor(x, y) => eval2(x,env,envb) ^ eval2(y,env,envb)
  }*/

  private def eval(exp: AST[_], env: HashMap[Param[_], List[Boolean]]): List[Boolean] = exp match {
    case Caall1(op, x)                  => eval(op.body, env + (op.p1 -> eval(x, env)))
    case Call2(op, x, y)               => eval(op.body, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)))
    case Call3(op, x, y, z)            => eval(op.body, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)) + (op.p3 -> eval(z, env)))
    case u @ Param(x)                  => env(u)
    case Or(x, y)                      => (eval(x, env), eval(y, env)).zipped.map(_ | _)
    case And(x, y)                     => (eval(x, env), eval(y, env)).zipped.map(_ & _)
    case Xor(x, y)                     => (eval(x, env), eval(y, env)).zipped.map(_ ^ _)
    case ConstSignedInt(n, size)       => toBinary(n, size)
    case ConstSignedInt(n, size)       => toBinary(n, size)
    case True()                        => List(true)
    case False()                       => List(false)
    case Scan1(x,   op, v, dir, init) => scan[Boolean,  Boolean ]( eval(v, env).head,
         eval(x, env) ,
         (u: Boolean, w: Boolean) => eval(op.body, env + (op.p1 -> List(u)) + (op.p2 -> List(w))).head,
        dir,init
     )
    case Scan2(x, y, op, v, dir, init) => scan[Boolean, (Boolean, Boolean)]( eval(v, env).head,
        (eval(x, env), eval(y, env)).zipped.map((x, y) => (x, y)),
         (u: Boolean, v: (Boolean, Boolean)) => v match {
        case (v1, v2) => eval(op.body,
          (env + (op.p1 -> List(u)) + (op.p2 -> List(v1))  + (op.p3 -> List(v2)))).head
        case _ => throw new RuntimeException("operand of unequal number of bits");
      } ,
        dir,init
     )
     
   /* case ScanLeft2Init2(x, y, op, v) => scanLeft[Boolean, (Boolean, Boolean)](
      eval(v, env).head,
      (eval(x, env), eval(y, env)).zipped.map((x, y) => (x, y)),
      (u: Boolean, v: (Boolean, Boolean)) => v match {
        case (v1, v2) => eval(
          op.body,
          (env + (op.p1 -> List(u))
            + (op.p2 -> List(v1))
            + (op.p3 -> List(v2)))).head
        case _ => throw new RuntimeException("operand of unequal number of bits");
      })
    case ScanLeft1Init(x, op, v) => scanLeft[Boolean, Boolean](
      eval(v, env).head,
      eval(x, env), (u: Boolean, w: Boolean) => eval(op.body, env + (op.p1 -> List(u)) + (op.p2 -> List(w))).head)
    case ScanRight2(x, y, op, v) => scanRight[Boolean, (Boolean, Boolean)](
      eval(v, env).head,
      (eval(x, env).reverse, eval(y, env).reverse).zipped.map((x, y) => (x, y)),
      (u: Boolean, v: (Boolean, Boolean)) => v match { case (v1, v2) => eval(op.body, (env + (op.p1 -> List(u)) + (op.p2 -> List(v1)) + (op.p3 -> List(v2)))).head })
    // case _ => List(true, false)*/
  }
  val env = HashMap.empty[Param[_], List[Boolean]]
  def testBinary() { println(toInt(toBinary(3, 5))); assertEquals(toInt(toBinary(3, 5)), 3) }
  def testCarry() {
    assertEquals(eval(Call3(carry, True[B], True[B], False[B]), env), List(true));
    assertEquals(eval(Call3(carry, True[B], False[B], False[B]), env), List(false));
  }
  val quatre = ConstSignedInt(4, 5); val trois = ConstSignedInt(3, 5); def testConstInt() { assert(toInt(eval(trois, env)) == 3) }
  val sept = Or(trois, quatre); def testOr() { assert(toInt(eval(sept, env)) == 7) }
  val un = ConstSignedInt(1, 5); val cinq = Call2(add, quatre, un);
  def testAdd1() { assert(toInt(eval(cinq, env)) == 5) }
  val six = Call2(add, trois, trois);
  def testAdd2() { assert(toInt(eval(six, env)) == 6) }
  val huit= Caall1(inc, sept)
  def testInc() {assert(toInt(eval(huit,env)) ==8)}
  val quatrebis= Caall1(halveB,huit)
 def testHalve() {assert(toInt(eval(quatrebis,env)) ==4)}
   val unbis = ConstSignedInt(1, 7);
    val testNbit=   HashMap.empty[AST[_], Int]
   def testComputeNbit(){
      val n=computeNbit(testNbit ,Call2(add, un, unbis) ) 
      assert(n==7) }
}