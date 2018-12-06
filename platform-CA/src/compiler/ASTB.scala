package compiler

import junit.framework.Assert.fail 
import ASTB._

sealed abstract class Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.
class B extends Ring  //le type boolean
class  I extends B     //le type entier etends boolean, car or,and,xor sont defini pour les entiers.
final class UI extends I    //unsigned int
final class SI extends I    //signed int
 //partial int will be treated using library

/**  parse tree of arithmetic expression   */
sealed abstract class ASTB[+R<:Ring](val nbit:Int)
		//boolean expression
case class Or[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
case class And[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
case class Xor[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
case class Neg[R<:Ring](x:ASTB[R]) extends ASTB[R](x.nbit)
/** value is minus one, for signed  integer */
case class True[R<:Ring] (override val nbit:Int) extends ASTB[R](nbit)//definit aussi pour les entiers
/** value is zero for  integer */
case class False[R<:Ring](override val nbit:Int) extends ASTB[R](nbit)  
/**  LSB, Least significant bit has index 0, and is therefore head of list. */
case class ConstInt[R<:I](value:Int,size:Int) extends ASTB[R](size){assert(value < Math.pow(2,size),"not enough bits")}
/** builds an int from several booleans*/
case class Concat[R<:I](booleans:Seq[ASTB[B]]) extends ASTB[R](booleans.size)  
/** returns bit at position i*/
case class Elt[R<:I]( i:Int, x:ASTB[R]) extends ASTB[B](1)
/** will copy the msb*/
case class Extend[R<:I]( i:Int, x:ASTB[R]) extends ASTB[R](i){assert(x.nbit<i)}
//case class Reduce[R<:I](x:ASTB[R],op:redop[ASTB[B]]) extends ASTB[B]
/**used to compute andB2R */
case class Mapp[R<:I](x: ASTB[B],y:ASTB[R], op:( ASTB[B],ASTB[B])=>ASTB[B] ) extends ASTB[R](y.nbit)
 case class FoldLeft1[R<:I](x: ASTB[R],  op:(ASTB[B],ASTB[B] )=>ASTB[B] ) extends ASTB[B](1)
 /**  init, is  part of the result */
case class ScanRight1Init[R<:I](x: ASTB[R],  op:(ASTB[B], ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit)
case class ScanLeft1Init[R<:I](x: ASTB[R],  op:(ASTB[B], ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit)
case class ScanLeft2Init[R<:I](x: ASTB[R],y:ASTB[R], op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
/**  init, is noy part of the result */
case class ScanRight1 [R<:I](x: ASTB[R],  op:(ASTB[B], ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit) 
case class ScanLeft2 [R<:I](x: ASTB[R],y:ASTB[R], op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
case class ScanRight2 [R<:I](x: ASTB[R],y:ASTB[R], op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R](x.nbit){assert(y.nbit==x.nbit)}
/** static object using arithmetic parse trees, operators gets a name, using another method, with the letter 'n' appended  */
object ASTB{
   def nbit[R1<:Ring,R2<:Ring,R3<:Ring](n1:Int,n2:Int, op:(ASTB[R1],ASTB[R2] )=>ASTB[R3]):Int={val t=op(True[R1](n1),True[R2](n2));t.nbit}
   def nbit[R1<:Ring,R2<:Ring](n1:Int,  op: ASTB[R1] =>ASTB[R2]) :Int={val t=op(True[R1](n1));t.nbit}
  def nbit[R1<:Ring,R2<:Ring](n1:List[Int],  op: Seq[ASTB[R1]] =>ASTB[R2]) :Int={val t=op( n1.map(x=>True[R1](x) ));t.nbit}
  class NamedFunction2[T1,T2,R](name: String, f: Function2[T1,T2,R])   extends Function2[T1,T2,R] {
	  def apply(a: T1, b: T2): R = f.apply(a, b); 	override def toString = name}
  class NamedFunction1[T1, R](name: String, f: Function1[T1 ,R])     extends Function1[T1,R] {
	  def apply(a: T1): R = f.apply(a ); override def toString = name}
	type op2B[R<:Ring]=NamedFunction2[ASTB[B],ASTB[R],ASTB[R]];
	type op2[R<:Ring]=NamedFunction2[ASTB[R],ASTB[R],ASTB[R]];
	type op1[R1<:Ring,R2<:Ring]=NamedFunction1[ASTB[R1],ASTB[R2]];
	type opN[R1<:Ring,R2<:Ring]=NamedFunction1[Seq[ASTB[R1]],ASTB[R2]];
	type redop[A] = ( (A, A)=> A  , A);
//  def castB2RN[R<:I]=new NamedFunction1[ASTB[B],ASTB[R]]("B2I",CastB2R[R](_)    ) 
	def orN[R<:Ring]=new op2[R]("Or", Or[R](_,_) ) 
	def xorN[R<:Ring]=new op2[R]("Xor", Xor[R](_,_) ) 
	def andN[R<:Ring]=new op2[R]("And", And[R](_,_) ) 
	def negN[R<:Ring]=new op1[R,R]("Not", Neg[R](_) ) 
	def concatN[R<:I]= new opN[B,R]("concat", Concat[R](_) ) 
//	def or[R<:Ring]:redop[ASTB[R]]=(orN[R] ,False[R])   
	def carry (x:ASTB[B],y:ASTB[B],z:ASTB[B]) = Or(And(x,y),And(z,Or(x,y) ) )   //boolean computation used by add
	def add[R<:I](x:ASTB[R],y:ASTB[R]) = {assert(x.nbit==y.nbit);  Xor(Xor(x,y),ScanLeft2Init(x,y, carry, False[B](1)))}  // addition must be programmed
	def inc[R<:I](x:ASTB[R]) = {    Xor(x,ScanLeft1Init(x,  And(_,_), True[B](1)))}  // addition must be programmed
	def addN[R<:I]  = new op2[R]("add", add )  
	def andLB2R[R<:I](x:ASTB[B],y:ASTB[R]) = Mapp(x,y,And[B])  // a tester
	def andLB2RN[R<:I]  = new op2B[R]("andLB2R", andLB2R )  
	def opp ( x:ASTB[SI]): ASTB[SI]= inc(Neg(x) ) 
	def oppN   = new op1[SI,SI]("opp", opp )   
	def elt[R<:I] (  i:Int ):  ASTB[R] => ASTB[B]= x => Elt[R](i,x)  
	def eltN[R<:I] (  i:Int )  = new op1[R,B]("elt["+i+"]", elt[R](i ))   
	def extend[R<:I] (  i:Int ):  ASTB[R] => ASTB[R]= x => Extend[R](i,x)  
	def extendN[R<:I] (  i:Int )  = new op1[R,R]("extendTo "+i+ " bits" , extend[R](i ))   
	def minus[R<:I](x:ASTB[SI],y:ASTB[SI]) =  add(x,opp(y))  
	def minusN[R<:I]  = new op2[SI]("minus", minus ) 
	def sign (x:ASTB[SI]) = Concat(List(notNull(x),gt(x)))
	def signN   = new op1[SI,SI]("sign", sign ) 
	def halveN[R<:I]   = new op1[R,R]("sign", halve ) 
	/** result in shifting bits towards the tail, entering a zero at the end of the list  */
	def halve[R<:I] ( x:ASTB[R]) = ScanRight1Init(x, (x,y)=>x ,False[B](1))
	def orScanRightN [R<:I]  = new op1[R,R]("orscanRight", orScanRight ) 
	def orScanRight[R<:I]  ( x:ASTB[R]) =   ScanRight1(x,Or[B](_,_) ,False[B](1))   
	def gt(x:ASTB[SI]) = elt[SI](x.nbit)(x);// TODO
  def gtN   = new op1[SI,B]("gt", gt ) 
	/**IntV mask with only one   not null boolV component, equal to the most significant bit where arg is not null
	 * There is a reused expression!  */
 	def minN[R<:I]  = new op2[R]("min", (arg1,arg2)=> arg1 ) 
//	def notNull[R<:I](x:ASTB[R])= FoldLeft1(x,or[B])  // LUID: or2 ne prends pas de parenthèse, même vide
	def notNull[R<:I](x:ASTB[R])= FoldLeft1(x,Or[B])   
}

 

