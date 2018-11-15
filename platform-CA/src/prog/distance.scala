package prog

import compiler.ASTB._
import compiler.AST._
import compiler._
import Compiler._
//
//  class Distance(c:Circuit, val source:BoolV)(implicit m : repr[V]) extends Layer[V,I](c)  {
//    val Ethis=transfer(e(this))
//    val next=addL(this,cond(source, signL(oppL(this)), minR(Transfer(signL(minusL(Ethis, addL(Ethis ,Const[T[E,V],I](c,ConstInt(-2,2)))))))))
//    next.user+=this  
//    }

//
//
//  class Distance2(c:Circuit, val source:BoolV)(implicit m : repr[V]) extends Layer[V,I](c)  with LanguageStdlib {
//    val Ethis=transfer(e(this))
//    val next=addL(this,cond(source, signL(oppL(this)), minR(Transfer(signL(minusL(Ethis, addL(Ethis ,Const[T[E,V],I](c,ConstInt(-2,2)))))))))
//    next.user+=this  
//    }
  
  
//  
//abstract class TestAPI extends LanguageStdlib {
//  val c =new Circuit() 
//  val source = const[V,B](c, True()) 
//  val Ethis=transfer(e(t));
//  val next=addL(t,cond(source, signL(oppL(t)), minR(transfer(signL(minusL(Ethis, addL(Ethis ,const[T[E,V],SI](c,ConstInt(-2,2)))))))));
//}


 class Program extends   LanguageStdlib  with  LanguageImpl  { 
 class DistanceAPI(c:Circuit, val source:Field[V,B])  extends Layer[V,SI](c)     {
    val fauxThis= const[V,SI](c, True())
    val Ethis=transfer(e(this))
    val toto=addL(fauxThis,cond(source, signL(oppL(fauxThis)), minR(transfer(signL(minusL(Ethis, addL(Ethis ,const[T[E,V],SI](c,ConstInt(-2,2)))))))))
  
    val next=toto
    // next.user+=this  
    }
  val c1=new Circuit(){
    val src = const[V,B](this,True()); 
    val dist = new DistanceAPI(this,src);
  }
}

object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
   def main(args: Array[String]) { 
//     val c1=new Circuit(){
//      val source = Const[V,B](this,True()); 
     //val dist = new Distance(this,source);
     
     
      //println(test+" "+    test.s) 
    //println(dd.next)
   }
     val p  = new Program()  
     compile(p.c1);     println(p.c1)
 
}