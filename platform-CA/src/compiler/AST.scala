package compiler

import junit.framework.Assert.assertEquals
import ASTB._
import scala.collection.mutable.ListBuffer
import scala.language.higherKinds




/**used to compute a string encoding the locus, at compile time. */
class repr[L <: Locus](val name: String)
object repr { implicit val nomV = new repr[V]( "V");
implicit val nomE = new repr[E]( "E");implicit val nomF = new repr[F]( "F"); 
implicit val nomTVE = new repr[T[V,E]]( "vE"); implicit val nomTVF = new repr[T[V,F]]( "vF");
implicit val nomTEV = new repr[T[E,V]]( "eV");implicit val nomTEF = new repr[T[E,F]]( "eF");
implicit val nomTFV = new repr[T[F,V]]( "fV");implicit val nomTFE = new repr[T[F,E]]( "fE");
/*  implicit def nomT[L1<:S,L2<:S](implicit m1 : repr[L1], m2 : repr[L2]) = //compiler call it because it cannot find implicit variable
    new repr[T[L1,L2]]( m1.name.toLowerCase + m2.name);                 //with type T[X][Y] so it look for implicit fonction returning some. */ 
 }

class CentralSym[S1,S2,S3]
object CentralSym{
	implicit val vEv= new CentralSym[V,E,V];	implicit val fEf= new CentralSym[F,E,F];
	implicit val vFe= new CentralSym[V,F,E];	implicit val eFv= new CentralSym[E,F,V];
}

object AST { 
def toString3( a:AST[_,_]):String =  
 ( a   match {
	case LayerAST(_,_) =>  "Layer"+a.locus
	case Const(_,cte) =>cte.toString+a.locus	
	case Binop(op,arg1,arg2)=>  op.toString    
  case Multop(op,args)=>  op.toString  
	case Unop(op, arg)=>  op.toString  
	case Redop(op, arg)=> "/"+op.toString  
	case Redop2(op, arg)=> "//"+op.toString  
 	case Broadcast(arg) =>  "*"+arg.locus 
	case Transfer(arg) =>  "receive " 
	case Sym(arg) =>  "<-> " 
	case Delayed(arg,c,nbit) => "delayed "  
	}) + "_"+ (if(a.name==null) "null" else a.name)
   
  
  def toString2(firstCall:Boolean,a:AST[_,_]):String =
   if(!firstCall & a.affected ) a.name
	 else 	a   match {
	case LayerAST(_,_) =>  "Layer"+a.locus
	case Const(_,cte) =>cte.toString+a.locus	case Binop(op,arg1,arg2)=>  op.toString+ "("+  toString2(false,arg1)+ ","+toString2(false,arg2)+")"
  case Multop(op,args)=>  op.toString + "(" + " "+  ("" /: args) (_ +" "+ toString2(false,_))  + ")"
	case Unop(op, arg)=>  op.toString +" "+  toString2(false,arg)
	case Redop(op, arg)=> "/"+op.toString +" "+ toString2(false,arg)
	case Redop2(op, arg)=> "//"+op.toString +" "+ toString2(false,arg)
 	case Broadcast(arg) =>  "*"+arg.locus+" "+ toString2(false,arg) 
	case Transfer(arg) =>  "receive " //+  toString2(false,arg) 
	case Sym(arg) =>  "<-> "+ toString2(false,arg)
	case Delayed(arg,c,nbit) => "delayed " +  toString2(false,arg())
	}
}

sealed abstract class AST[+L<:Locus,+R<:Ring]( val c :Circuit, val nbit:Int) (implicit m : repr[L]) extends Named with Bag { 
  /** not necessary, just to remember how to retrieve the name*/
  val locus:String = m.name 
 /**  records user of this AST so as to detect when  it is used more than once, and e should be stored. */
  var user= new ListBuffer[AST[_,_]]() //  Careful Expression can be stored also if displayed, displayable, ensured-condition, live 
 /**Circuit to which belong the node, initialized on leaf, and then transmitted */
  c.addNode(this)
  /**true if expression is stored in a variable */
  def affected:Boolean=c.affect.contains(this)
  def shown()=if(affected) c.affect(this).shown else false
  def hidden()=if(affected) c.affect(this).hidden else false
 	override def toString:String=AST.toString3( this)
} 
/**stores a list of  ensure boolV and display in order to get name related to the layers.  */
 case class LayerAST[L<:Locus, R<:Ring](override val  c:Circuit,override val nbit:Int )(implicit m : repr[L]) extends AST[L,R](c,nbit) with EmptyBag{
   /** the value at t, which  is represented as  the layer itself.*/
   val pred:AST[L,R]=this;  
  /**value of the layer at t+1, mutable, since before computing the next value, we need to create other layers.  */
 var next:AST[L,R]=this;
    def setNext(l:AST[L,R]){next=l};
  
//for the following three lists, we must put ORs to make sure user is updated correctly.? 
  /** Boolean fields which must be true, otherwise bug is detected in layer.*/ 
 	 var bugIf: List[AST[_<:Locus,B]] =List() ;def bugIf(a:AST[_<:Locus,B]){bugIf=a::bugIf}
	  /**  fields   representing the layer on screen */
	 var display: List[AST[_<:Locus,_<:Ring]] =List();def display(a:AST[_<:Locus,_<:Ring]){display=a::display}
	 /**  fields which could be displayed for undertanding a bug */
	 var displayable: List[AST[_<:Locus,_<:Ring]] =List();def displayable(a:AST[_<:Locus,_<:Ring]){displayable=a::displayable}
	 /** computes affectation for debug, displayed, displayable variables
	  *  The elements of the right operand will "overwrite" the elements of the left one, because ensure > displayed > displayable */
	 def affect=   displayable.map (e=>(e,Displayable(e))) :::   display.map (e=>(e,Display(e))) :::    bugIf.map (e=>(e,Ensure(e))) 
}
case class Const[L<:Locus,R<:Ring](override val  c:Circuit ,cte:ASTB[R])(implicit m : repr[L]) extends AST[L,R](c,cte.nbit) with EmptyBag
case class Binop[L<:Locus, R1<:Ring, R2<:Ring, R3<:Ring] (op:(ASTB[R1],ASTB[R2] )=>ASTB[R3], arg1 : AST[L,R1], arg2 : AST[L,R2])(implicit m : repr[L]) 
   extends AST[L,R3](arg1.c, nbit[R1,R2,R3](arg1.nbit, arg2.nbit, op)) with Doubleton
 {arg1.user+=this;arg2.user+=this;assertEquals(arg1.c, arg2.c) }
case class Broadcast[S1<:S,S2<:S,R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,S2]],m2 : repr[T[S2,S1]]) extends AST[T[S1,S2],R](arg.c,arg.nbit) with Singleton
 {arg.user+=this  }
case class Transfer[S1<:S,S2<:S,R<:Ring](arg : AST[T[S1,S2],R])(implicit m : repr[T[S2,S1]]) extends AST[T[S2,S1],R](arg.c,arg.nbit) with Singleton
 {arg.user+=this } 
case class Unop[L<:Locus, R1<:Ring, R2<:Ring] (op:ASTB[R1]=>ASTB[R2], arg : AST[L,R1])(implicit m : repr[L]) extends AST[L,R2](arg.c, nbit[R1,R2](arg.nbit,  op)) with Singleton
 {arg.user+=this }
case class Multop[L<:Locus, R1<:Ring, R2<:Ring] (op:Seq[ASTB[R1]]=>ASTB[R2], args : Seq[AST[L,R1]])
  (implicit m : repr[L]) extends AST[L,R2](args(0).c,  nbit[R1,R2](args.toList.map (x=>x.nbit), op)) with Neton
 { for (arg <- args) arg.user+=this}
case class Redop[S1<:S,S2<:S,R<:Ring](op: redop[ASTB[R]],arg : AST[T[S1,S2],R])(implicit m : repr[S1]) extends AST[S1,R](arg.c, arg.nbit) with Singleton
 {arg.user+=this }
case class Redop2[S1<:S,S2<:S,S2new<:S,R<:Ring](op: redop[ASTB[R]],arg : AST[T[S1,S2],R])(implicit m : repr[T[S1,S2new]]) extends AST[T[S1,S2new],R](arg.c, arg.nbit) with Singleton
 {arg.user+=this }
case class Sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : AST[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) extends AST[T[S2,S3],R](arg.c,arg.nbit)  with Singleton
 {arg.user+=this }
case  class Delayed[L<:Locus, R<:Ring](_arg:() => AST[L,R],override val c:Circuit, override val nbit:Int)(implicit m : repr[L]) extends AST[L,R]( c, nbit)  with Singleton
 {c.addDelayed(this);lazy val arg={ _arg().user+=this;_arg() } }

   
 
