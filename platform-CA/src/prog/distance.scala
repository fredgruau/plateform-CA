package prog

//import compiler.ASTB._
//import compiler.AST._
import compiler.Circuit 
import compiler.LayerUsr
import compiler.repr

import compiler.API
import compiler.APIstdlib
import compiler.LanguageImpl 
import compiler._
import Compiler._

  abstract   class  CycleLayer (c:Circuit, nbit:Int )extends  LayerUsr[V,SI] (c,nbit)   {
  lazy val x:IntV=opp(opp(opp(opp(addL(next,pred ))))); 
  val next=delayed(x,c,nbit); //préciser le circuit et le nombre de bit. 
  setNext(pred,next);  
}

  abstract  class Program2 extends   APIstdlib {
       
  
  val testCycle=new Circuit(){val chip= new CycleLayer(this,3)with  LanguageImpl  ;}
    
  
  }
abstract class Program extends   APIstdlib   {  
  
 
  case class Dist(c:Circuit, val source:BoolV) extends LayerUsr[V,SI]  (c,3)  {
    display(elt(2,pred ))
   val grad:IntvE= minusL(transfer(e(pred)), transfer(e(pred)));
   val greater:BoolvE=gt(grad) 
   val greaterOptimized:BoolvE= andL(transfer(e(pred)),v(mstb(xorR(transfer(e(pred)))))) //same as greater, but cost in gates is diminished.
   val vortex:BoolF= orR(transfer(xorR2 (transfer(greater))));   bugIf(vortex) 
   val next=addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3))))))))) 
    setNext(pred,next)  
 }
  
  val c1=new Circuit(){
    val src = const[V,B](this,True[SI](1)); 
    val dist = Dist(this,src);
  } 

/**returns a constant layer. */ 
case class ConstLayer[L<:Locus, R<:Ring](c:Circuit, nbit:Int )(implicit m : repr[L]) extends LayerUsr[L,R]  (c,nbit) {
  val next=pred;  setNext(pred,next);
}


  case class  CycleLayer (c:Circuit, nbit:Int )(implicit m : repr[V]) extends  LayerUsr[V,SI] (c,nbit)   {
  lazy val x:IntV=opp(opp(opp(opp(addL(next,pred ))))); 
  val next=delayed(x,c,nbit); //préciser le circuit et le nombre de bit. 
  setNext(pred,next);  
}
  
  
  val testCycle=new Circuit(){val chip= CycleLayer(this,3);}
    
}

object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
   def main(args: Array[String]) { 
     
//     val c1=new Circuit(){
//      val source = Const[V,B](this,True()); 
     //val dist = new Distance(this,source);
     
     
      //println(test+" "+    test.s) 
    //println(dd.next)
   
     val p  = new Program()  with  LanguageImpl  
     //compile(p.c1);     println(p.c1)
     compile(p.testCycle);  //   println(p.testCycle)
   }
 
}