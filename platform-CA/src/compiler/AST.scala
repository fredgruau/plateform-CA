package compiler
import ASTB._
/**The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, 
 * T stands for Transfer, and uses two simplicial locus*/

sealed abstract  class Locus
 class S extends Locus;  final class V extends S;  final class E extends S ;  final class F  extends S
 /*le premier parametre de type dans T[S1,S2] represente le locus simplicial T[V,E] se note eV dans ma notation habituelle **/
 final class T[S1<:S,S2<:S] extends Locus //here S1 should allways be different from S2. LUIDNEL, tu sais comment faire cela?

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
  */}

 class CentralSym[S1,S2,S3]
object CentralSym{
  implicit val vEv= new CentralSym[V,E,V]
  implicit val fEf= new CentralSym[F,E,F]
  implicit val vFe= new CentralSym[V,F,E]
  implicit val eFv= new CentralSym[E,F,V]
}

 /** The possible fields type, which combine a locus and a ring type.*/
object AST {
 type IntV = AST[V,I]; type IntE = AST[E,I]; type IntF = AST[F,I]
 type IntvE = AST[T[E,V],I]; type InteV = AST[T[V,E],I]
 type IntvF = AST[T[F,V],I]; type IntfV = AST[T[V,F],I]
 type IntfE = AST[T[E,F],I]; type InteF = AST[T[F,E],I]
 type BoolV = AST[V,B]; type BoolE = AST[E,B]; type BoolF = AST[F,B]
 type BooleV = AST[T[E,V],B]; type BoolvE = AST[T[V,E],B]
 type BoolfV = AST[T[F,V],B]; type BoolvF = AST[T[V,F],B]
 type BooleF = AST[T[E,F],B]; type BoolfE = AST[T[F,E],B]
 def v[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,V]])=Broadcast[S1,V,R](arg) // for broadcast, we want to specify only the direction where broadcasting takes place.
 def e[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,E]])=Broadcast[S1,E,R](arg) // this is done using three function e,v,f. 
 def f[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,F]])=Broadcast[S1,F,R](arg)
//  def binop [L<:Locus, R<:Ring](op:(ASTB[R],ASTB[R] )=>ASTB[R])(implicit m : repr[L]) = Binop[L,R,R,R](op,_:AST[L,R],_:AST[L,R])
// def orL2[L<:Locus, R<:Ring](implicit m : repr[L]) = binop[L,R](Or[R](_,_))(m) //LUIDNEL ca va pas, je sais meme pas quoi passer dans le code doit y avoir une solution qu'on pige pas. 
//   def cond[L<:Locus,R<:I] (b:AST[L,B],  arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L])= orL2(m)(andLB2R[L,R](b,arg1),andLB2R(negL(b),arg2))
 def castB2RL[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg )
    def negL[L<:Locus, R<:Ring] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,R,R](negN[R],arg)   
   def oppL[L<:Locus, R<:I] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,I,I](oppN,arg)   
   def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  
  def orL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L]) = Binop[L,R,R,R](orN,arg1,arg2 )
  def andL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R]) (implicit m : repr[L]) = Binop[L,R,R,R](andN,arg1,arg2 )
 def andLB2R [L<:Locus,R<:I]( arg1 : AST[L,B],arg2 : AST[L,R])(implicit m : repr[L])= andL[L,R](castB2RL[L,R](arg1),arg2)
 def cond[L<:Locus,R<:I] (b:AST[L,B],  arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L])= orL(andLB2R[L,R](b,arg1),andLB2R(negL(b),arg2))
 def addL[L<:Locus] ( arg1 : AST[L,I], arg2 : AST[L,I])(implicit m : repr[L]) = Binop[L,I,I,I](addN,arg1,arg2 ) 
 def minR[S1<:S,S2<:S,R<:I] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((minN[R],Zero[R]()),arg )   
 def signL[L<:Locus] ( arg1 : AST[L,I] )(implicit m : repr[L]) = Unop[L,I,I ](signN,arg1 ) 
 def minusL[L<:Locus] ( arg1 : AST[L,I], arg2 : AST[L,I])(implicit m : repr[L]) = Binop[L,I,I,I](minusN,arg1,arg2 )  
}

sealed abstract class AST[+L<:Locus,+R<:Ring](implicit m : repr[L]) { val s:String = m.name // not necessary, just to remember how to retrieve the name.
 //  lazy val negl=negL(this)
 // lazy val oppl=oppL(this)
}
//
//trait printType[+L<:Locus,+R<:Ring] extends AST[L,R]{
//abstract override def toString() = super.toString() + s 
//}

case class Broadcast[S1<:S,S2<:S,R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,S2]]) extends AST[T[S1,S2],R]
case class Transfer[S1<:S,S2<:S,R<:Ring](arg : AST[T[S1,S2],R])(implicit m : repr[T[S2,S1]]) extends AST[T[S2,S1],R] // on souhaite inférer S1 et S2,
case class Unop[L<:Locus, R1<:Ring, R2<:Ring] (op:ASTB[R1]=>ASTB[R2], arg : AST[L,R1])(implicit m : repr[L]) extends AST[L,R2] 
case class Binop[L<:Locus, R1<:Ring, R2<:Ring, R3<:Ring] (op:(ASTB[R1],ASTB[R2] )=>ASTB[R3], arg1 : AST[L,R1], arg2 : AST[L,R2])(implicit m : repr[L]) extends AST[L,R3] 
//case class Triop[L<:Locus, R1<:Ring, R2<:Ring, R3<:Ring, R4<:Ring] (op:(ASTB[R1],ASTB[R2],ASTB[R3] )=>ASTB[R4], arg1 : AST[L,R1], arg2 : AST[L,R2], arg3 : AST[L,R3])(implicit m : repr[L]) extends AST[L,R4] 
 case class Redop[S1<:S,S2<:S,R<:Ring](op: redop[ASTB[R]],arg : AST[T[S1,S2],R])(implicit m : repr[S1]) extends AST[S1,R] // on souhaite inférer S1 et S2
case class Const[L<:Locus,R<:Ring](cte:ASTB[R])(implicit m : repr[L]) extends AST[L,R] // on souhaite spécifier L
case class Sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : AST[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) extends AST[T[S2,S3],R]
//case class SymF[S2<:S ,R<:Ring] (arg : AST[T[F,S2],R])  extends AST[ T[F,S2==E?V:E]  ,R]  //LUIDNEL pour eviter la prolifération de constructeur,
   //je voudrais regroupesr SymvF et SymeF en SymF, et ensuite aussi regrouper avec SymE, pour avoir un seul constructeur Sym



import AST._

/*A layer is defined as a function on a basic spatial type **/
abstract class Layer[L<:Locus,R<:Ring]  extends Function1[AST[L,R],AST[L,R]]{
 // var ensure: List[AST[_,B]] /* Boolean fields which must be true, otherwise bug is detected in layer.*/  
 //var display: List[AST[_,_]] /*  fields which must be displayed to represent the layer on screen */
 // var displayable: List[AST[_,_]] /*  fields which could be displayed for undertanding a bug */
}
