package prog
//import compiler.ASTB._
//import compiler.AST._
import compiler.Circuit 
import compiler.repr
import compiler.AST._
import compiler._
import Compiler._

  class Dist(c:Circuit, val source:BoolV) extends LayerAST[V,SI]  (c,3)  {
    display(elem(2,this ))
   val grad:IntvE= minusL(transfer(e(pred)), transfer(e(pred)));
   val greater:BoolvE=gt(grad) 
   val greaterOptimized:BoolvE= andL(transfer(e(pred)),v(mstb(xorR(transfer(e(pred)))))) //same as greater, but cost in gates is diminished.
   val temp:BoolfV=xorR2(transfer(greater))
   val vortex:BoolF= orR(transfer(temp));
   bugIf(vortex) 
   val next=addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3))))))))) 
 }
  

/**returns a constant layer. */ 
class ConstLayer[L<:Locus, R<:Ring](c:Circuit, nbit:Int )(implicit m : repr[L]) extends LayerAST[L,R]  (c,nbit) {
  val next=this; 
}


  class  CycleLayer (c:Circuit, nbit:Int )(implicit m : repr[V]) extends  LayerAST[V,SI] (c,nbit)   {
  lazy val x:IntV=opp(opp(opp(opp(addL(next,pred ))))); 
  val next=delayed(x,c,nbit); //préciser le circuit et le nombre de bit. 
  //setNext(pred,next);  
}



object Test { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
   def main(args: Array[String]) { 
   
  val testDist=new Circuit(){
    val src = const[V,B](this,True[SI](1)); 
    val dist = new Dist(this,src);
  } 
  val testCycle=new Circuit(){val chip= new CycleLayer(this,3);}
    
     compile(testCycle);  //   println(p.testCycle)
   }
 
}