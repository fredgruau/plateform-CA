package prog

import compiler.ASTB._
import compiler.AST._

import compiler._

case class Distance(source:BoolV) extends Layer[V,I]{
    def apply(d:IntV)=addL(d,cond(source, signL(oppL(d)), minR(Transfer(signL(minusL(Transfer(e(d)), addL(Transfer(e(d)) ,Const[T[E,V],I](MinusTwo()))))))))
                 
  }

object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
   def main(args: Array[String]) {
     val t= Const[V,B](True[B]()) 
     val d=Const[V,I](One())
    //val e=orL2()(d,d) LUIDNEL ca marche pas.
     val u=e(d) 
     val source=Const[V,B](Two())
     val dE=Transfer(e(d))
     val gradient:IntvE=minusL(dE , Sym(dE ))
     val test  =  addL(d,cond(source, signL(oppL(d)), minR(Transfer(signL(addL(gradient,Const[T[E,V],I](MinusTwo()) ))))))
     val dd=Distance(source)
      println(test+" "+   test.s) 
     println ( dd)
   }
}