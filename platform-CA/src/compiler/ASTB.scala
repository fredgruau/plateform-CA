package compiler

sealed trait Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.
sealed trait B extends Ring  //le type boolean
sealed trait I extends B     //le type entier etends boolean, car or,and,xor sont defini pour les entiers.
sealed trait P extends I     //le type partial entier etends entiers.


import ASTB._

/**  parse tree of arithmetic expression   */
sealed abstract class ASTB[+R<:Ring]
//we start with boolean expression
case class Or[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R]
case class And[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R]
case class Xor[R<:Ring](x:ASTB[R],y:ASTB[R]) extends ASTB[R]
case class Neg[R<:Ring](x:ASTB[R]) extends ASTB[R]
case  class True[R<:Ring]() extends ASTB[R] //definit aussi pour les entiers
case  class False[R<:Ring]() extends ASTB[R] //definit aussi pour les entiers, vaut -1
//a present, les operations valables juste pour traiter les entiers:
case  class Zero[R<:I]() extends ASTB[R]
case  class One[R<:I]() extends ASTB[R]
case  class Two[R<:I]() extends ASTB[R]
case  class MinusTwo[R<:I]() extends ASTB[R]
/** replicate the bit to transfor a boolean into an integer, or a defined partial integer
 * @ x is a boolean expression*/
case class CastB2R[R<:I](x:ASTB[B]) extends ASTB[R]
case class Reduce[R<:I](x:ASTB[R],op:redop[ASTB[B]]) extends ASTB[B]
case class FoldLeft2[R<:I](x: ASTB[R],y:ASTB[R], op:(ASTB[B],ASTB[B],ASTB[B])=>ASTB[B],init:ASTB[B]) extends ASTB[R]
case class FoldLeft1[R<:I](x: ASTB[R],  op:(ASTB[B],ASTB[B] )=>ASTB[B],init:ASTB[B]) extends ASTB[R]


 class NamedFunction2[T1,T2,R](name: String, f: Function2[T1,T2,R])   extends Function2[T1,T2,R] {
  def apply(a: T1, b: T2): R = f.apply(a, b)
  override def toString = name
}

 class NamedFunction1[T1, R](name: String, f: Function1[T1 ,R])     extends Function1[T1,R] {
  def apply(a: T1): R = f.apply(a )
  override def toString = name
}
 
/**  static object using arithmetic parse trees  */
object ASTB{
type redop[A] = ( (A, A)=> A  , A);
type op2[R<:Ring]=NamedFunction2[ASTB[R],ASTB[R],ASTB[R]]
type op1[R<:Ring]=NamedFunction1[ASTB[R],ASTB[R]]
def castB2RN[R<:I]=new NamedFunction1[ASTB[B],ASTB[R]]("B2I",CastB2R[R](_)    )
def orN[R<:Ring]=new op2[R]("Or", Or[R](_,_) )
def andN[R<:Ring]=new op2[R]("And", And[R](_,_) )
def negN[R<:Ring]=new op1[R]("Not", Neg[R](_) )
def or[R<:Ring]:redop[ASTB[R]]=(orN[R] ,False[R]) // LUID: Tu avais R au lieu de ASTB[R]
  def carry (x:ASTB[B],y:ASTB[B],z:ASTB[B]) = Or(And(x,y),And(z,Or(x,y) ) )  //boolean computation used by add
  def add[R<:I](x:ASTB[R],y:ASTB[R]) = Xor(Xor(x,y),FoldLeft2(x,y, carry, True())) // addition must be programmed
 def addN[R<:I]  = new op2[R]("add", add ) 
 def opp[R<:I]( x:ASTB[R])= add(Neg(x),One())
 def oppN[R<:I]  = new op1[R]("opp", opp )  
 def minus[R<:I](x:ASTB[R],y:ASTB[R]) =  add(x,opp(y)) // addition must be programmed
def minusN[R<:I]  = new op2[R]("minus", minus ) 
  def sign[R<:I](x:ASTB[R]) = x// TODO
 def signN[R<:I]  = new op1[R]("sign", opp )  
 def minN[R<:I]  = new op2[R]("min", (arg1,arg2)=> arg1 )
 def notNull[R<:I](x:ASTB[R])= Reduce(x,or[B]) // LUID: or2 ne prends pas de parenthèse, même vide
}


object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
   def main(args: Array[String]) { 
     
     
     
   }
}
 
