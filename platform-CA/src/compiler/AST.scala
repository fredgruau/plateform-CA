package compiler

import junit.framework.Assert.assertEquals
import ASTB._
import scala.collection.mutable.ListBuffer
import scala.language.higherKinds


/**The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, 
 * T stands for Transfer, and uses two simplicial locus*/
sealed abstract  class Locus
class S extends Locus;  final class V extends S;  final class E extends S ;  final class F  extends S
/*le premier parametre de type dans T[S1,S2] represente le locus simplicial T[V,E] se note eV dans ma notation habituelle **/
final class T[S1<:S,S2<:S] extends Locus //here S1 should allways be different from S2. LUIDNEL, tu sais comment faire cela?
 

trait LanguageLuid {
  type LayerLuid[L <: Locus, R <: Ring]
  type Field[L <: Locus, R <: Ring]

  def const[L <: Locus](b : Boolean) : Field[L,B]
  def and[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) : Field[L,B]
  def or[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) : Field[L,B]
  def not[L <: Locus](arg1 : Field[L,B]) : Field[L,B]
}

trait LanguageStdlibLuid extends LanguageLuid {
  def xor[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = or( and( arg1, not(arg2)), and( not(arg1), arg2))
}

abstract class Program extends LanguageStdlibLuid {
  val t = const[V](true)
  val f = const[V](false)
  val d = and(t,f)
  def getT = t
}


/**used to compute a string encoding the locus, at compile time. */
class repr[L <: Locus](val name: String)
object repr { implicit val nomV = new repr[V]( "V");
implicit val nomE = new repr[E]( "E");
implicit val nomF = new repr[F]( "F"); 
implicit val nomTVE = new repr[T[V,E]]( "vE");  
implicit val nomTVF = new repr[T[V,F]]( "vF");
implicit val nomTEV = new repr[T[E,V]]( "eV");
implicit val nomTEF = new repr[T[E,F]]( "eF");
implicit val nomTFV = new repr[T[F,V]]( "fV");
implicit val nomTFE = new repr[T[F,E]]( "fE");
/*
  implicit def nomT[L1<:S,L2<:S](implicit m1 : repr[L1], m2 : repr[L2]) = //compiler call it because it cannot find implicit variable
    new repr[T[L1,L2]]( m1.name.toLowerCase + m2.name);                 //with type T[X][Y] so it look for implicit fonction returning some.
 */ 
}

class CentralSym[S1,S2,S3]
		object CentralSym{
	implicit val vEv= new CentralSym[V,E,V];
	implicit val fEf= new CentralSym[F,E,F];
	implicit val vFe= new CentralSym[V,F,E];
	implicit val eFv= new CentralSym[E,F,V];
}




trait LanguageImplLuid extends LanguageLuid {
  case class FieldImpl[L <: Locus, R <: Ring](b : Boolean)
  type LayerLuid[L <: Locus, R <: Ring] = FieldImpl[L,R]
  type Field[L <: Locus, R <: Ring] = FieldImpl[L,R]

  def const[L <: Locus](b : Boolean) = FieldImpl[L,B](b)
  def and[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = FieldImpl[L,B](arg1.b & arg2.b)
  def or[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = FieldImpl[L,B](arg1.b | arg2.b)
  def not[L <: Locus](arg1 : Field[L,B]) : Field[L,B] = FieldImpl[L,B](! arg1.b)
}


/** The possible fields type, which combine a locus and a ring type.*/
object AST {
	type IntV = AST[V,I]; type IntE = AST[E,I]; type IntF = AST[F,I];
	type IntvE = AST[T[E,V],I]; type InteV = AST[T[V,E],I];
	type IntvF = AST[T[F,V],I]; type IntfV = AST[T[V,F],I];
	type IntfE = AST[T[E,F],I]; type InteF = AST[T[F,E],I];
	type BoolV = AST[V,B]; type BoolE = AST[E,B]; type BoolF = AST[F,B];
	type BooleV = AST[T[E,V],B]; type BoolvE = AST[T[V,E],B];
	type BoolfV = AST[T[F,V],B]; type BoolvF = AST[T[V,F],B];
	type BooleF = AST[T[E,F],B]; type BoolfE = AST[T[F,E],B];
//	def v[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,V]],  m2 : repr[T[V,S1]])=Broadcast[S1,V,R](arg); // for broadcast, we want to specify only the direction where broadcasting takes place.
//	def e[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,E]],  m2 : repr[T[E,S1]])=Broadcast[S1,E,R](arg); // this is done using three function e,v,f. 
//	def f[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,F]],  m2 : repr[T[F,S1]])=Broadcast[S1,F,R](arg);
//	def castB2RL[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
//	def negL[L<:Locus, R<:Ring] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,R,R](negN[R],arg)   ;
//	def oppL[L<:Locus, R<:I] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,R,R](oppN[R],arg)   ;
//	//def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  ;
//	def orL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L]) = Binop[L,R,R,R](orN,arg1,arg2 );
//	def andL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R]) (implicit m : repr[L]) = Binop[L,R,R,R](andN,arg1,arg2 );
//	def addL[L<:Locus] ( arg1 : AST[L,I], arg2 : AST[L,I])(implicit m : repr[L]) = Binop[L,I,I,I](addN,arg1,arg2 ) ;
//	def minR[S1<:S,S2<:S,R<:I] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((minN[R],ConstInt[R](0,1)),arg );   
//	def signL[L<:Locus] ( arg1 : AST[L,I] )(implicit m : repr[L]) = Unop[L,I,I ](signN,arg1 ) ;
//
// 	def andLB2R [L<:Locus,R<:I]( arg1 : AST[L,B],arg2 : AST[L,R])(implicit m : repr[L])= andL[L,R](castB2RL[L,R](arg1),arg2);
//	def cond[L<:Locus,R<:I] (b:AST[L,B],  arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L])= orL(andLB2R[L,R](b,arg1),andLB2R(negL(b),arg2));
//  def minusL[L<:Locus] ( arg1 : AST[L,I], arg2 : AST[L,I])(implicit m : repr[L]) = Binop[L,I,I,I](minusN,arg1,arg2 ) ;
 
  def toString2(firstCall:Boolean,a:AST[_,_]):String =
   if(!firstCall & a.affected ) a.name
	 else 	a   match {
	case Binop(op,arg1,arg2)=>  op.toString+ "("+  toString2(false,arg1)+ ","+toString2(false,arg2)+")"
	case Unop(op, arg)=>  op.toString +" "+  toString2(false,arg)
	case Redop(op, arg)=> "/"+op.toString +" "+ toString2(false,arg)
	case Broadcast(arg) =>  "*"+arg.locus+" "+ toString2(false,arg) 
	case Transfer(arg) =>  "receive " //+  toString2(false,arg) 
	case Sym(arg) =>  "<-> "+ toString2(false,arg)
	case Const(_,cte) =>cte.toString+a.locus
	case Layer(_) =>  "Layer"+a.locus
	}
}

trait Language  {
 //class Field[L <: Locus, R <: Ring]( val c :Circuit) (implicit m : repr[L])
// abstract class LayerTest[L <: Locus, R <: Ring]( c:Circuit )(implicit m : repr[L]) extends Field[L,R](c)(m)  {val next: Field[L,R]; }
 
  
 type Field[L <: Locus, R <: Ring]<:{ val c :Circuit   }
 //type  LayerTest[L <: Locus, R <: Ring]  <: Field[L,R]  { val next :Field[L,R]    }
 
//def layer[L<:Locus,R<:Ring]( c:Circuit )(implicit m : repr[L]):LayerTest[L,R]  
def const[L<:Locus,R<:Ring](c:Circuit ,cte:ASTB[R])(implicit m : repr[L]) :Field[L,R] ; 

def transfer[S1<:S,S2<:S,R<:Ring](arg : Field[T[S1,S2],R])(implicit m : repr[T[S2,S1]]):Field[T[S2,S1],R]  ;
def sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : Field[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) :Field[T[S2,S3],R]   ;
  
def v[S1<:S, R<:Ring](arg : Field[S1 ,R])(implicit m : repr[T[S1,V]],  m2 : repr[T[V,S1]]):Field[T[S1,V],R] ; // for broadcast, we want to specify only the direction where broadcasting takes place.
	def e[S1<:S, R<:Ring](arg : Field[S1,R])(implicit m : repr[T[S1,E]],  m2 : repr[T[E,S1]]):Field[T[S1,E],R]  ; // this is done using three function e,v,f. 
	def f[S1<:S, R<:Ring](arg : Field[S1,R])(implicit m : repr[T[S1,F]],  m2 : repr[T[F,S1]]):Field[T[S1,F],R];
	def castB2RL[L<:Locus,R<:I]( arg: Field[L,B] )(implicit m : repr[L]) : Field[L,R];
	def negL[L<:Locus, R<:Ring] ( arg : Field[L,R]) (implicit m : repr[L]) : Field[L,R]  ;
	/**returns a signed int */
	def oppL[L<:Locus] ( arg : Field[L,SI]) (implicit m : repr[L]) :  Field[L,SI]  ;
//	def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  ;
	def orL[L<:Locus, R<:Ring]( arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R];
	def andL[L<:Locus, R<:Ring]( arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R];
	def addL[L<:Locus,R<:I] ( arg1 : Field[L,R], arg2 : Field[L,R])(implicit m : repr[L]) : Field[L,R] ;
	def minR[S1<:S,S2<:S,R<:I] (arg :  Field[T[S1,S2],R])(implicit m : repr[S1]) : Field[S1,R] ; 
	/** signL is defined only for signed Int */
	def signL[L<:Locus] ( arg1 : Field[L,SI] )(implicit m : repr[L]) :Field[L,SI] ;  
}


trait LanguageStdlib extends Language  { 
 	def andLB2R [L<:Locus,R<:I]( arg1 : Field[L,B],arg2 : Field[L,R])(implicit m : repr[L])= andL[L,R](castB2RL[L,R](arg1),arg2);
  def cond[L<:Locus,R<:I] (b:Field[L,B],  arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L])= orL(andLB2R[L,R](b,arg1),andLB2R(negL(b),arg2))
  	/**  defined only for signed Int */
  def minusL[L<:Locus] ( arg1 :  Field[L,SI], arg2 : Field[L,SI])(implicit m : repr[L]) = addL( arg1,oppL(arg2)) ;
	
}
 

trait LanguageImpl extends Language { 
  type Field[L <: Locus, R <: Ring] = AST[L,R]
  // type LayerTest[L <: Locus, R <: Ring] = Layer[L,R]
  def const[L<:Locus,R<:Ring](c:Circuit ,cte:ASTB[R])(implicit m : repr[L])     = Const(c,cte)(m) ;
 // def layer[L<:Locus,R<:Ring]( c:Circuit )(implicit m : repr[L])   =  Layer (c)(m)
 def transfer[S1<:S,S2<:S,R<:Ring](arg : Field[T[S1,S2],R])(implicit m : repr[T[S2,S1]]) = Transfer(arg)(m)  ;
 def sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : Field[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) = Sym(arg)(m,t)   ;
 def v[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,V]],  m2 : repr[T[V,S1]])=Broadcast[S1,V,R](arg); // for broadcast, we want to specify only the direction where broadcasting takes place.
	def e[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,E]],  m2 : repr[T[E,S1]])=Broadcast[S1,E,R](arg); // this is done using three function e,v,f. 
	def f[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,F]],  m2 : repr[T[F,S1]])=Broadcast[S1,F,R](arg);
	def castB2RL[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
	def negL[L<:Locus, R<:Ring] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,R,R](negN[R],arg)   ;
	def oppL[L<:Locus ] ( arg : AST[L,SI]) (implicit m : repr[L]) = Unop[L,SI,SI](oppN,arg)   ;
	//def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  ;
	def orL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L]) = Binop[L,R,R,R](orN,arg1,arg2 );
	def andL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R]) (implicit m : repr[L]) = Binop[L,R,R,R](andN,arg1,arg2 );
	def addL[L<:Locus,R<:I] ( arg1 : AST[L,R], arg2 : AST[L,R])(implicit m : repr[L]):AST[L,R] = Binop[L,R,R,R](addN,arg1,arg2 ) ;
	def minR[S1<:S,S2<:S,R<:I] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((minN[R],ConstInt[R](0,1)),arg );   
	def signL[L<:Locus] ( arg1 : AST[L,SI] )(implicit m : repr[L]) = Unop[L,SI,SI ](signN,arg1 );
 

}
 
sealed abstract class AST[+L<:Locus,+R<:Ring]( val c :Circuit) (implicit m : repr[L]) { import AST._
/** not necessary, just to remember how to retrieve the name*/
 var name:String=null;  def setName(value: String) {name = value  };def addAfter(value: String) {name =   name+value  };def addBefore(value: String) {name =  value+name  }
 val locus:String = m.name 
 /**  records all the places that use this AST.*/
  var user= new ListBuffer[AST[_,_]]()
 /**Circuit to which belong the node, initialized on leaf, and then transmitted */
  this+=:c.nodes;
  /**true if expression is stored in a variable */
  def affected:Boolean=c.affect.contains(this)
  def shown()=if(affected) c.affect(this).shown else false
  def hidden()=if(affected) c.affect(this).hidden else false
 	override def toString:String=AST.toString2(true,this)
} 
/**stores ensure and display in order to get name related to the layers.  */
abstract  case class Layer[L<:Locus,R<:Ring](override val   c:Circuit )(implicit m : repr[L]) extends AST[L,R](c){
  /**value of the layer at t+1, the value at t is the layer itself.  */
  val next: AST[L,R]; //next.user += this // attention ca peut créer une boucle faire plus tard
  /**for the following three lists, we must put ORs to make sure user is updated correctly.?*/
  /** Boolean fields which must be true, otherwise bug is detected in layer.*/ 
	 var ensure: List[AST[_<:Locus,B]] =List() ;def ensure(a:AST[_<:Locus,B]){ensure=a::ensure}
	  /**  fields   representing the layer on screen */
	 var display: List[AST[_<:Locus,_<:Ring]] =List();def display(a:AST[_<:Locus,_<:Ring]){display=a::display}
	 /**  fields which could be displayed for undertanding a bug */
	 var displayable: List[AST[_<:Locus,_<:Ring]] =List();def displayable(a:AST[_<:Locus,_<:Ring]){displayable=a::displayable}
	 def affect=   displayable.map (e=>(e,Displayable(e))) :::   display.map (e=>(e,Display(e))) :::    ensure.map (e=>(e,Ensure(e))) 
}
case class Const[L<:Locus,R<:Ring](override val  c:Circuit ,cte:ASTB[R])(implicit m : repr[L]) extends AST[L,R](c) 
case class Binop[L<:Locus, R1<:Ring, R2<:Ring, R3<:Ring] (op:(ASTB[R1],ASTB[R2] )=>ASTB[R3], arg1 : AST[L,R1], arg2 : AST[L,R2])(implicit m : repr[L]) 
   extends AST[L,R3](arg1.c)
 {arg1.user+=this;arg2.user+=this;assertEquals(arg1.c, arg2.c) }
case class Broadcast[S1<:S,S2<:S,R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,S2]],m2 : repr[T[S2,S1]]) extends AST[T[S1,S2],R](arg.c)
 {arg.user+=this  }
case class Transfer[S1<:S,S2<:S,R<:Ring](arg : AST[T[S1,S2],R])(implicit m : repr[T[S2,S1]]) extends AST[T[S2,S1],R](arg.c)
 {arg.user+=this } 
case class Unop[L<:Locus, R1<:Ring, R2<:Ring] (op:ASTB[R1]=>ASTB[R2], arg : AST[L,R1])(implicit m : repr[L]) extends AST[L,R2](arg.c)
 {arg.user+=this }
case class Redop[S1<:S,S2<:S,R<:Ring](op: redop[ASTB[R]],arg : AST[T[S1,S2],R])(implicit m : repr[S1]) extends AST[S1,R](arg.c)
 {arg.user+=this }
case class Sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : AST[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) extends AST[T[S2,S3],R](arg.c) 
 {arg.user+=this }


