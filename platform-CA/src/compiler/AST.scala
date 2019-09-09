package compiler
  trait EmptyBag[T <: Dag[T]] extends MutableDag[T] { def neighbor2: List[T] = List.empty; def substituteInArg = {} }
  trait Singleton[T <: Dag[T]] extends MutableDag[T] {def setArg(a: T); def arg: T; def substituteInArg = { setArg(neighbor.head) };  def neighbor2: List[T] = List(arg)  } 
  trait Doubleton[T <: Dag[T]] extends MutableDag[T] {    def setArg(a: T); def arg: T; def setArg2(a: T); def arg2: T;    def substituteInArg = { setArg(neighbor.head); setArg2(neighbor.tail.head) }; def neighbor2: List[T] = List(arg, arg2)  }
  trait Tripleton[T <: Dag[T]] extends MutableDag[T] {    def setArg(a: T); def arg: T; def setArg2(a: T); def arg2: T;def setArg3(a: T); def arg3: T;    def substituteInArg = { setArg(neighbor.head); 
  setArg2(neighbor.tail.head); setArg3(neighbor.tail.tail.head) }; def neighbor2: List[T] = List(arg, arg2,arg3)  }
  trait Neton[T <: Dag[T]] extends MutableDag[T] { def args: Seq[T]; def neighbor2: List[T] = args.toList;def setArgs(a: Seq[T]); def substituteInArg = {setArgs(neighbor)} }
  trait Singleton1[T <: Dag[T]] extends MutableDag[T] {   def exp: T; def substituteInArg = { };  def neighbor2: List[T] = List(exp)  } 
  trait Doubleton1[T <: Dag[T]] extends MutableDag[T] {   def exp: T;   def exp2: T;    def substituteInArg = {}; def neighbor2: List[T] = List(exp,exp2)  }
  trait Neton1[T <: Dag[T]] extends MutableDag[T] { def exps: Seq[T]; def neighbor2: List[T] = exps.toList;  def substituteInArg = { } }

  /**Represent an Asbstract Syntax Tree using Function definition, and calls, reading of variables, delaying of evaluation. 
   *Reused to implement the AST of integer function and the AST of spatial functions.
   *The parameter type T is the type of the associated expression
   *covariant because 
   *@m implicit parameter used to compute this type.
   */
     
abstract  class AST[+T]()(implicit m: repr[T]) extends MutableDag[AST[_]] with Named {
  val mym:repr[_]  = m //type of mym is set to repr[_] to allow covariance. 
  def locus=m.name.asInstanceOf[Tuple2[_ <: Locus, _ <: Ring]]._1  //we need to get locus and ring for read node. 
  def ring ={ m.name.asInstanceOf[Tuple2[_ <: Locus, _ <: Ring]]._2 }
  def checkName() = { if (name == null) name = "_aux" +  AST.getCompteur; }
  import AST._
 
}

//la fonction read2 montre qu'on peut generer des constructeur Read qui implémente AST2, bingo. donc les operateur AST2 auront des arg AST2, et des OP AST.
object AST{
 //  implicit def toAST2I[L<:Locus,R<:I](a:AST[Tuple2[L,R]]):AST2I[L,R]=this.asInstanceOf[AST2I[L,R]]
private var nameCompteur = 0;
def getCompteur: Int = { nameCompteur += 1; nameCompteur }
class Fundef[T](val name:String, val body:T , val p :Param[_]*) 
case class Fundef1[Ti1, To1   ](override val name:String,override val body:AST[To1],   val p1:Param[Ti1]) extends Fundef[AST[To1]](name,body,p1){override def toString = name}
case class Fundef2[Ti1, Ti2 , To1   ](override val name:String,override val body:AST[To1],   val p1:Param[Ti1], val p2:Param[Ti2]) extends Fundef[AST[To1]](name,body,p1,p2){override def toString = name}
case class Fundef3[Ti1, Ti2, Ti3 , To1   ](override val name:String,override val body:AST[To1],   val p1:Param[Ti1], val p2:Param[Ti2], val p3:Param[Ti3]) extends Fundef[AST[To1]](name,body,p1,p2,p3){override def toString = name}
//on peut pas utiliser fundefn, car faudrait savoir a l'avance le nombre de paramétres, pour maj l'environnement. 
case class Fundefn[Ti1, To1   ](override val name:String,override val body:AST[To1],   val pn:Param[Ti1]*,
     ) extends Fundef[AST[To1]](name,body,pn: _*){override def toString = name}
case class Param[T](val s:String)(implicit n: repr[T]) extends AST[T] with EmptyBag[AST[_]]
 
case class Caall1[Ti1, To1 ](val f:Fundef1[Ti1,To1],var arg:AST[Ti1])(implicit n: repr[To1]) extends AST[To1]with Singleton[AST[_]]
    { def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Ti1]];  }
case class Call2[Ti1 , Ti2<:Ring, To1<:Ring  ](val f:Fundef2[Ti1 ,Ti2, To1 ],var arg:AST[Ti1],var arg2:  AST[Ti2])(implicit n: repr[To1]) extends AST[To1] with Doubleton[AST[_]]
  { def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Ti1]]; def setArg2(a: AST[_]) = arg2 = a.asInstanceOf[AST[Ti2]] }
case class Call3[Ti1 , Ti2<:Ring, Ti3<:Ring, To1<:Ring  ](val f:Fundef3[Ti1 ,Ti2,Ti3, To1 ],var arg:AST[Ti1],var arg2:  AST[Ti2],var arg3:  AST[Ti3])(implicit n: repr[To1]) extends AST[To1] with Tripleton[AST[_]]
  { def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Ti1]]; def setArg2(a: AST[_]) = arg2 = a.asInstanceOf[AST[Ti2]]; def setArg3(a: AST[_]) = arg3 = a.asInstanceOf[AST[Ti3]] }
case class Reead[T](which: String)(implicit m: repr[T]) extends AST[T]() with EmptyBag[AST[_]] 
case class Delayed[T](_arg: () => AST[T])(implicit m: repr[T]) extends AST[T]() with Singleton[AST[_]] {
    lazy val arg = { /* _arg().user+=this;*/ _arg() }
    def setArg(a: AST[_]) = { // throw new RuntimeException("cannot substitute in a delayed")
} 
  } 
 
  //on se sert de DELAYED que dans ASTL, donc on va directement l'y mettre. 
  //def delayed3[L<:Locus,R<:Ring](_arg: => AST[Tuple2[L,R]])(implicit m: repr[Tuple2[L,R]])   = { lazy val delayed4 = _arg with AST2[L,R];new Delayed(() => delayed4) }
 

} 
  
