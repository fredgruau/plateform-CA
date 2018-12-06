//  
//
//import scala.language.higherKinds
//
//abstract class Locus
//abstract class V extends Locus
//
//abstract class Ring
//abstract class B extends Ring
//
//trait Language {
//  type Layer[L <: Locus, R <: Ring]
//  type Field [L <: Locus, R <: Ring]
//
//  def const[L <: Locus](b : Boolean) : Field[L,B]
//  def and[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) : Field[L,B]
//  def or[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) : Field[L,B]
//  def not[L <: Locus](arg1 : Field[L,B]) : Field[L,B]
//}
//
//trait LanguageStdlib extends Language {
//  def xor[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = or( and( arg1, not(arg2)), and( not(arg1), arg2))
//}
//
//abstract class Program extends LanguageStdlib {
//  class A{
//    val t = const[V](true)
//  }
//  val a=new A;
//  val t = const[V](true)
//  val f = const[V](false)
//  val d = xor(t,t)
//  def getT = d  
//}
//
//trait LanguageImpl extends Language {
//  type Layer[L <: Locus, R <: Ring] = FieldImpl[L,R]
//  type Field[L <: Locus, R <: Ring] = FieldImpl[L,R]
//
//  def const[L <: Locus](b : Boolean) = FieldImpl[L,B](b)
//  def and[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = FieldImpl[L,B](arg1.b & arg2.b)
//  def or[L <: Locus](arg1 : Field[L,B], arg2 : Field[L,B]) = FieldImpl[L,B](arg1.b | arg2.b)
//  def not[L <: Locus](arg1 : Field[L,B]) : Field[L,B] = FieldImpl[L,B](! arg1.b)
//}
//case class FieldImpl[L <: Locus, R <: Ring](b : Boolean)
//
//object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
//   def main(args: Array[String]) { 
//val p = new Program with LanguageImpl; 
// 
//
//println("toto"+ p.getT)}
//   
//}
