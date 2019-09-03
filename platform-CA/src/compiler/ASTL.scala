package compiler

import junit.framework.Assert.assertEquals
import ASTB._
import scala.collection.mutable.ListBuffer
import scala.language.higherKinds
import scala.collection.immutable.HashMap
import ASTL._
import AST._
/**The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, */
sealed abstract class Locus
class S extends Locus; final case class V() extends S; final case class E() extends S; final case class F() extends S
/** T stands for Transfer, and uses two simplicial locus. The first is the simplicial. T[V,E] corresponds to  eV  */
final case class T[+S1 <: S, +S2 <: S](from: S1, to: S2) extends Locus

/**Adds boolean spatial operator to AST of spatial types */
trait ASTLtrait[L <: Locus, R <: Ring] extends AST[Tuple2[L, R]] with MyOp[L, R] with MyOpInt[L, R] {

}

/**Defines boolean operations to be applied on AST2, also applicable between two integer*/
trait MyOp[L <: Locus, R <: Ring] { this: ASTLtrait[L, R] =>
  // def unary_~[U >: R <: Ring](implicit m: repr[L], n: repr[U]): AST2[L, U] = ASTL.Unop2(neg.asInstanceOf[AST.Fundef1[R, U]], this);
  def unary_~(implicit m: repr[L], n: repr[R]): ASTLtrait[L, R] = { val xr = new Param[R]("x") with ASTBtrait[R]; ASTL.Unop(Fundef1("neg", Neg(xr), xr), this) }

  def |(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(orB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]])
        case _   => Binop(orI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]])
      }; res.asInstanceOf[ASTL[L, R]]
    }
  def &(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(andB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]])
        case _   => Binop(andI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]])
      }; res.asInstanceOf[ASTL[L, R]]
    }
  def ^(that: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    {
      val res = ring match {
        case B() => Binop(xorB, this.asInstanceOf[ASTLtrait[L, B]], that.asInstanceOf[ASTLtrait[L, B]])
        case _   => Binop(xorI, this.asInstanceOf[ASTLtrait[L, I]], that.asInstanceOf[ASTLtrait[L, I]])
      }; res.asInstanceOf[ASTL[L, R]]
    }

  //   def ^[U >: R <: Ring](that: AST2[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop2(xor.asInstanceOf[Fundef2[R, U, U]], this, that);
}

/** Integer spatial operators*/
trait MyOpInt[L <: Locus, R <: Ring] { this: ASTLtrait[L, R] =>
  //we cannot directly check the type constraint R<:I, otherwise it clash with AST2, but we can impose that U<:I and U>:R,
  //and in fact, this implies that R<:I
  def +[U >: R <: I](that: ASTLtrait[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop(add.asInstanceOf[Fundef2[R, U, U]], this, that);
  def -[U >: R <: SI](that: ASTLtrait[L, U])(implicit m: repr[L], n: repr[U]): ASTL[L, U] = Binop(add.asInstanceOf[Fundef2[R, U, U]], this, -that);
  def unary_-(implicit m: repr[L], n: repr[R]): ASTLtrait[L, R] = { ASTL.Unop(opp.asInstanceOf[Fundef1[R, I]], this).asInstanceOf[ASTLtrait[L, R]] }
  // def unary_-  (implicit m: repr[L],n: repr[R]): AST2[L, R] = { val xr=Param[R]("x") ;
  //    ASTL.Unop(Fundef1("opp", Call1(inc, Neg(xr).asInstanceOf[AST[I]]),xr ) , this).asInstanceOf[AST2[L,R]]}
}

/**
 *  AST of spatial type
 *  @tparam L: the locus in V,E or F
 *  @tparam R: the  type
 *  @constructor
 *  @implicit param m: used to compute the locus and scala type
 */
sealed abstract class ASTL[L <: Locus, R <: Ring]()(implicit m: repr[Tuple2[L, R]]) extends ASTLtrait[L, R] {
  override val (locus, ring) = m.name
  val l = new repr(locus)
  val r: repr[Ring] = new repr(ring)

  override def toString: String = {
    this.asInstanceOf[ASTL[_, _]] match {
      case Layer(_)              => "Layer" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case Const(cte)            => "Const" + cte.toString + locus.toString.charAt(0) + "_" + ring.toString.substring(0, ring.toString.length() - 2);
      case Binop(op, arg1, arg2) => op.toString
      case Multop(op, args)      => op.toString
      case Unop(op, arg)         => op.toString
      case Redop(op, arg)        => "red" + op.toString
      case Redop2(op, arg)       => "red2" + op.toString
      case e @ Broadcast(arg)    => "Broadcast" + ("" + (e.locus.asInstanceOf[T[_, _]] match { case T(x, y) => y })).charAt(0)
      case Transfer(arg)         => "Transfer"
      case Sym(arg)              => "sym "
    }
  }
}

object ASTL {
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): Const[L, R] = Const(ConstInt(d))

  /**stores a list of  ensure boolV and display in order to get name related to the layers, and because we define layers independantly from circuit.  */
  abstract case class Layer[L <: Locus, R <: Ring](val nbit: Int)(implicit m: repr[L], n: repr[R]) extends ASTL[L, R]() with EmptyBag[AST[_]] {
    /** the value at t, which  is represented as  the layer itself.*/
    val pred: ASTL[L, R] = this;
    /**value of the layer at t+1, it is abstract, since before computing the next value, we need probably to create other layers.  */
    val next: ASTLtrait[L, R];
    /**needed to visite the next fields */
    override def other = List(next)

    //for the following three lists, we must put ORs to make sure user is updated correctly.?
    /** Boolean fields which must be true, otherwise bug is detected in layer.*/
    var bugif: List[ASTL[_ <: Locus, B]] = List(); def bugif(a: ASTL[_ <: Locus, B]) { bugif = a :: bugif }
    /**  fields   representing the layer on screen */
    var render: List[AST2g] = List(); def render(a: AST2g) { render = a :: render }
    /**  fields which could be displayed for undertanding a bug */
    var inspect: List[AST2g] = List(); def inspect(a: AST2g) { inspect = a :: inspect }
  }
  final case class Const[L <: Locus, R <: Ring](cte: ASTB[R])(implicit m: repr[L], n: repr[R]) extends ASTL[L, R]() with EmptyBag[AST[_]]
  final case class Broadcast[S1 <: S, S2 <: S, R <: Ring](var arg: ASTLtrait[S1, R])(implicit m: repr[T[S1, S2]], n: repr[R]) extends ASTL[T[S1, S2], R]() with Singleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[S1, R]] }
  case class Transfer[S1 <: S, S2 <: S, R <: Ring](var arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]) extends ASTL[T[S2, S1], R]() with Singleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[T[S1, S2], R]] }
  final case class Unop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundef1[R1, R2], var arg: ASTLtrait[L, R1])(implicit m: repr[L], n: repr[R2]) extends ASTL[L, R2]() with Singleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[L, R1]] }
  final case class Binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](op: Fundef2[R1, R2, R3], var arg: ASTLtrait[L, R1], var arg2: ASTLtrait[L, R2])(implicit m: repr[L], n: repr[R3]) extends ASTL[L, R3]() with Doubleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[L, R1]]; def setArg2(a: AST[_]) = arg2 = a.asInstanceOf[ASTLtrait[L, R2]] }
  //multop est traités sans Fundefn, parcequ'on sait pas nommer les parametres?
  final case class Multop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Seq[ASTB[R1]] => ASTB[R2], var args: Seq[ASTLtrait[L, R1]])(implicit m: repr[L], n: repr[R2]) extends ASTL[L, R2]() with Neton[AST[_]] { def setArgs(a: Seq[AST[_]]) = args = a.asInstanceOf[Seq[ASTLtrait[L, R1]]] }
  final case class Multop2[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundefn[R1, R2], var args: Seq[ASTLtrait[L, R1]])(implicit m: repr[L], n: repr[R2]) extends ASTL[L, R2]() with Neton[AST[_]] { def setArgs(a: Seq[AST[_]]) = args = a.asInstanceOf[Seq[ASTLtrait[L, R1]]] }
  final case class Redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], var arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) extends ASTL[S1, R]() with Singleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[T[S1, S2], R]] }
  /** This is the redop used from one transfer site to its brother. to be replaced by clock and anticlock operators which are more elementary. */
  final case class Redop2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], var arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]) extends ASTL[T[S1, S2new], R]() with Singleton[AST[_]] { def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[T[S1, S2], R]] }
  final case class Sym[S1 <: S, S2 <: S, S3 <: S, R <: Ring](var arg: ASTLtrait[T[S2, S1], R])(implicit m: repr[T[S2, S3]], t: CentralSym[S1, S2, S3], n: repr[R]) extends ASTL[T[S2, S3], R]() with Singleton[AST[_]] { val tsave = t; def setArg(a: AST[_]) = arg = a.asInstanceOf[ASTLtrait[T[S2, S1], R]] }
  type AST2g = ASTLtrait[_ <: Locus, _ <: Ring]
 type AST2Int = ASTLtrait[_ <: Locus, _ <: I]
  type ASTbool = ASTLtrait[_ <: Locus, _ <: B]
  type Layerg = Layer[_ <: Locus, _ <: Ring]
  //read2 a déplacer dans ASTL

  /**
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   * @d the Dag to be transformed
   * @nUser the number of other expression using this expression
   * @return the Dag where expression used more than once are replaced by read.
   */
  def deDag(nUser: HashMap[AST2g, Int], repr: HashMap[AST2g, AST2g], d: AST2g): AST2g = {
    def read[L <: Locus, R <: Ring](which: String)(implicit m: repr[Tuple2[L, R]]): ASTLtrait[L, R] = new Read[Tuple2[L, R]](which) with ASTLtrait[L, R]
    def deDag[L2 <: Locus, R2 <: Ring](d: ASTLtrait[L2, R2]): ASTLtrait[L2, R2] =
      if (nUser.contains(d) && nUser(d) > 1) read(repr(d).name)(d.mym.asInstanceOf[repr[Tuple2[L2, R2]]])
      //     new Read[Tuple2[L2, R2]](repr(d).name)(d.mym.asInstanceOf[repr[Tuple2[L2, R2]]]) with AST2[L2, R2] //faut chercher le nom dans la représentation.
      else {
        val newD = d.asInstanceOf[AST[_]] match {
          case Delayed(arg)        => deDag(arg().asInstanceOf[AST2g])
          case e: EmptyBag[_]      => e
          case e @ Binop(o, a, a2) => e.copy(arg = deDag(a), arg2 = deDag(a2))(e.l, e.r)
          case e @ Multop(op, a)   => e.copy(args = a.map(arg => deDag(arg)))(e.l, e.r)
          case e @ Unop(op, a)     => e.copy(arg = deDag(a))(e.l, e.r)
          case e @ Redop(op, a)    => e.copy(arg = deDag(a))(e.l, e.r)
          case e @ Redop2(op, a)   => e.copy(arg = deDag(a))(e.l, e.r)
          case e @ Broadcast(a)    => e.copy(arg = deDag(a))(e.l, e.r)
          case e @ Transfer(a)     => e.copy(arg = deDag(a))(e.l, e.r)
          case e @ Sym(a)          => e.copy(arg = deDag(a))(e.l, e.tsave, e.r)
          // ToDo case Sym(arg) =>  Sym(deDag(arg))(d.m2)
        }
        newD.setName(d.name)
        newD.asInstanceOf[ASTLtrait[L2, R2]]
      }
    return deDag(d).asInstanceOf[AST2g]
  }

  def computeNbit(nbit: scala.collection.mutable.HashMap[AST2g, Int], affectmap: Map[String, Affect[AST2g]], d: AST2g): AST2g = {
    val nbitB = scala.collection.immutable.HashMap.empty[AST[_], Int]
    val lnOf2 = scala.math.log(2) // natural log of 2
    def log2(x: Double): Int = scala.math.ceil(scala.math.log(x) / lnOf2).toInt
    def nbitou0(e: AST2g) = if (nbit.contains(e)) nbit(e) else 0
    def computeNbit[L2 <: Locus, R2 <: Ring](d: ASTLtrait[L2, R2]): ASTLtrait[L2, R2] =
      {
        val newD = d.asInstanceOf[AST[_]] match {
          case Read(n)  =>
            nbit += d -> nbit(affectmap(n).exp); d
          case Layer(n) =>
            nbit += d -> n; d
          case Const(c) =>
            nbit += d -> ASTB.computeNbit(nbitB, c); d
          case e @ Unop(op, arg) =>
            val enew = e.copy(arg = computeNbit(arg))(e.l, e.r);
            nbit += d -> ASTB.computeNbit(
              nbitB + (op.p1.asInstanceOf[ASTBtrait[_ <: Ring]] -> nbitou0(arg)),
              op.body.asInstanceOf[ASTBtrait[_ <: Ring]]); enew

          case e @ Binop(op, a, a2) => val anew= computeNbit(a);val a2new=computeNbit(a2)
            nbit += d -> ASTB.computeNbit(
              nbitB + (op.p1.asInstanceOf[ASTBtrait[_ <: Ring]] -> nbit(a)) +
                (op.p2.asInstanceOf[ASTBtrait[_ <: Ring]] -> nbit(a2)),
              op.body.asInstanceOf[ASTBtrait[_ <: Ring]]); 
              val operandEqual= op match{
                case add => true 
                case _ => false
              }
          //   val aanew=extend(nbit(a2),anew.asInstanceOf[AST2Int])(e.l,e.r )
          //  if (operandEqual){ if (nbit(a) < nbit(a2)) anew=extend(nbit(a2),anew) }
              val enew = e.copy(arg = anew, arg2 = a2new)(e.l, e.r)
          
          case e @ Redop(op, a) =>
            val enew = e.copy(arg = computeNbit(a))(e.l, e.r); nbit += d -> nbit(a); enew
          //TODO généraliser en fonction du redop, ici on assume qu'il conserve le nombre de bit, mais c'est pas vrai pour concat par exemple.
          case e @ Broadcast(a) =>
            val enew = e.copy(arg = computeNbit(a))(e.l, e.r); nbit += d -> nbit(a); enew
          case e @ Transfer(a)  =>
            val enew = e.copy(arg = computeNbit(a))(e.l, e.r); nbit += d -> nbit(a); enew
          case e @ Sym(a)       => val enew = e.copy(arg = computeNbit(a))(e.l, e.tsave, e.r); nbit += d -> nbit(a); enew

          //case e @ Redop2(op, a)   => e.copy(arg = computeNbit(a))(e.l, e.r)
          // case e @ Multop(op, a)   => e.copy(args = a.map(arg => computeNbit(arg)))(e.l, e.r)

          // case _ => throw new RuntimeException("case missing");
        }
        // newD.setName(d.name)
        newD.asInstanceOf[ASTLtrait[L2, R2]]
      }
    return computeNbit(d)
  }

/*****************the wrapper*******************/
  def displayableIn(l: Layer[_ <: Locus, _ <: Ring], f: AST2g) = l.inspect(f)
  def displayIn(l: Layer[_ <: Locus, _ <: Ring], f: AST2g) = l.render(f)
  def bugIfIn(l: Layer[_ <: Locus, _ <: Ring], f: ASTL[_ <: Locus, B]) = l.bugif(f)

  def const[L <: Locus, R <: Ring](cte: ASTB[R])(implicit m: repr[L], n: repr[R]) = Const(cte);
  def sym[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLtrait[T[S2, S1], R])(implicit m: repr[T[S2, S3]], t: CentralSym[S1, S2, S3], n: repr[R]) = Sym(arg);
  def v[S1 <: S, R <: Ring](arg: ASTLtrait[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]) = Broadcast[S1, V, R](arg); // for broadcast, we want to specify only the direction where broadcasting takes place.
  def e[S1 <: S, R <: Ring](arg: ASTLtrait[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]) = Broadcast[S1, E, R](arg); // this is done using three function e,v,f.
  def f[S1 <: S, R <: Ring](arg: ASTLtrait[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]) = Broadcast[S1, F, R](arg);
  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );

  // def opp[L <: Locus](arg: AST2[L, SI])(implicit m: repr[L], n: repr[SI]) = Unop[L, SI, SI](oppN, arg);
  //def extend[L<:Locus, R<:I]   (i:Int , arg : AST[L,R]  ) (implicit m : repr[L]) = Unop[L,R,R](extendN[R](i),arg)   ;
  //def sign[L<:Locus] ( arg1 : AST[L,SI] )(implicit m : repr[L]) = Unop[L,SI,SI ](signN,arg1 );
  def halve[L <: Locus, R <: I](arg1: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTLtrait[L, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1)
  def sign[L <: Locus](arg1: ASTLtrait[L, SI])(implicit m: repr[L], n: repr[SI]): ASTLtrait[L, SI] = 
      Unop[L, SI, SI](ASTB.sign.asInstanceOf[Fundef1[SI, SI]], arg1)
  def orScanRight[L <: Locus, R <: I](arg1: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]) =
      Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1)
  def gt[L <: Locus](arg1: ASTLtrait[L, SI])(implicit m: repr[L]) = Unop[L, SI, B](elt(2).asInstanceOf[Fundef1[SI, B]], arg1); //TODO remplacer 2 par un delayed de arg1.nbit
  def notNull[L <: Locus, R <: I](arg1: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]) = Unop[L, I, B](notNullB, arg1.asInstanceOf[ASTLtrait[L, I]]); //TODO remplacer 2 par un delayed de arg1.nbit

  def addL2[L <: Locus, R <: I](arg1: ASTLtrait[L, R], arg2: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = Binop(add.asInstanceOf[Fundef2[R, R, R]], arg1, arg2);
  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool*/
  def andLB2R[L <: Locus, R <: I](arg1: ASTLtrait[L, B], arg2: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]) = Binop[L, B, R, R](andLBtoR.asInstanceOf[Fundef2[B, R, R]], arg1, arg2);
  def elem[L <: Locus, R <: I](i: Int, arg: ASTLtrait[L, R])(implicit m: repr[L], n: repr[B]) = Unop[L, R, B](elt(i).asInstanceOf[Fundef1[R, B]], arg);
  def extend[L <: Locus, R <: I](i: Int, arg: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]) = Unop[L, R, R](ASTB.extend(i).asInstanceOf[Fundef1[R, R]], arg);

  def concat[L <: Locus, R <: I](arg1: Seq[ASTLtrait[L, R]])(implicit m: repr[L], n: repr[R]) = Multop[L, R, R](concatN, arg1);
  // def addL[L <: Locus, R <: I](arg1: AST2[L, R], arg2: AST2[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = Binop[L, R, R, R](addN, arg1, arg2);
  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) = Redop[S1, S2, R]((orI.asInstanceOf[Fundef2[R, R, R]], False[R]), arg);
  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) = Redop[S1, S2, R]((xorI.asInstanceOf[Fundef2[R, R, R]], False[R]), arg);
  def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]) = Redop2[S1, S2, S2new, R]((xorI.asInstanceOf[Fundef2[R, R, R]], False[R]()), arg);
  //minR has two implementations depending if the integers to be compared are signed or unsigned.
  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): ASTLtrait[S1, R] = if (arg.ring == SI())
    Redop[S1, S2, SI]((minSI, ConstSignedInt(0, 1)), arg.asInstanceOf[ASTLtrait[T[S1, S2], SI]]).asInstanceOf[ASTLtrait[S1, R]];
  else Redop[S1, S2, UI]((minUI, ConstUnsignedInt(0, 0)), arg.asInstanceOf[ASTLtrait[T[S1, S2], UI]]).asInstanceOf[ASTLtrait[S1, R]];
  /** Delayed uses a trick found on the net, to have a call by name, together with a case class necessary to make the match*/
  def delayedL[L <: Locus, R <: Ring](_arg: => ASTLtrait[L, R])(implicit m: repr[Tuple2[L, R]]): ASTLtrait[L, R] = { lazy val delayed = _arg; new Delayed[Tuple2[L, R]](() => delayed) with ASTLtrait[L, R] }

  //def delayed[T](_arg: => AST[T])(implicit m: repr[T]): AST[T] = { lazy val delayed = _arg; Delayed(() => delayed) }
  //def delayed2[L<:Locus,R<:Ring](which: String)(implicit m:repr[Tuple2[L,R]]):AST2[L,R]= new Read[Tuple2[L,R]](which) with AST2[L,R]
  //  def delayed[L<:Locus,R<:Ring](_arg: => AST2[L,R]) (implicit m: repr[Tuple2[L,R]]): AST2[L,R] = { lazy val delayed = _arg; Delayed(() => delayed).asInstanceOf[AST2[L,R]] }
  // def redOp[S1 <: S, S2 <: S, R <: Ring](arg: AST2[T[S1, S2], R], op: redop[ASTB[R]], m: repr[S1], n: repr[R]) = Redop[S1, S2, R](op, arg)(m, n);
  def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLtrait[T[S1, S2], R], op: redop[R], m: repr[T[S1, S2new]], n: repr[R]) = Redop2[S1, S2, S2new, R](op, arg)(m, n);
  def broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLtrait[S1, R], m: repr[T[S1, S2]], n: repr[R]) = Broadcast[S1, S2, R](arg)(m, n);
  def transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLtrait[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]) = new Transfer(arg)(m, n);

  type IntV = ASTL[V, SI]; type IntE = ASTL[E, SI]; type IntF = ASTL[F, SI];
  type IntvE = ASTLtrait[T[E, V], SI]; type InteV = ASTL[T[V, E], SI];
  type IntvF = ASTL[T[F, V], SI]; type IntfV = ASTL[T[V, F], SI];
  type IntfE = ASTL[T[E, F], SI]; type InteF = ASTL[T[F, E], SI];
  type UintV = ASTL[V, UI]; type UintE = ASTL[E, UI]; type UintF = ASTL[F, UI];
  type UintvE = ASTL[T[E, V], UI]; type UinteV = ASTL[T[V, E], UI];
  type UintvF = ASTL[T[F, V], UI]; type UintfV = ASTL[T[V, F], UI];
  type UintfE = ASTL[T[E, F], UI]; type UinteF = ASTL[T[F, E], UI];
  type BoolV = ASTL[V, B]; type BoolE = ASTL[E, B]; type BoolF = ASTL[F, B];
  type BooleV = ASTL[T[V, E], B]; type BoolvE = ASTL[T[E, V], B];
  type BoolvF = ASTL[T[F, V], B]; type BoolfV = ASTL[T[V, F], B];
  type BoolfE = ASTL[T[E, F], B]; type BooleF = ASTL[T[F, E], B];
  //  def neg2[L <: Locus, R <: Ring](arg: AST2[L, R])(implicit m: repr[L], n: repr[R]) = Unop[L, R, R](negN[R], arg);
  // implicit def fromAST2[L<:Locus,R<:Ring](x:AST2[L, R]):ASTL[L,R]=x.asInstanceOf[ASTL[L,R]]
  def cond[L <: Locus, R <: I](b: ASTLtrait[L, B], arg1: ASTLtrait[L, R], arg2: ASTLtrait[L, R])(implicit m: repr[L], n: repr[R]) =
    andLB2R[L, R](b, arg1) | andLB2R(~b, arg2)
  /**computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O. */
  /**this is an example of boolean function with a reused value: orScanRight.*/
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = {
    val y: ASTL[L, R] = orScanRight[L, R](arg1);
    y ^ halve(y)
  }

}

