package compiler
import scala.collection.immutable.Map
import scala.collection.mutable.ListBuffer

 /**Analysed by the compiler to produce a CA rule */
class Circuit{
//  var layers= new ListBuffer[Layer[_<:Locus,_<:Ring]]()  
 /** records all the AST nodes, in order to easily iterate on them */
   var nodes= new ListBuffer[AST[_<:Locus,_<:Ring]]()  
 /**computes affectation for debug, displayed, displayable variables, and finally for reused variable*/
   lazy val layers:List[ Layer[_<:Locus,_<:Ring]]=  nodes.toList.collect{ case l:Layer[_,_ ] =>l }
   lazy  val affect:Map[AST[_<:Locus,_<:Ring],Affect] 
     //  the elements of the right operand will "overwrite" the elements of the left one: 
       = (nodes.toList.filter(_ .user.size > 1).map(e=>(e,new Affect(e))) :::layers.foldLeft(List[(AST[_<:Locus,_<:Ring],Affect)]())(_ :::_.affect)).toMap
       
  lazy val instr: List[Instruction]= layers.map{ e  => Memorize(e)} :::nodes.toList.collect { case Transfer(e) => Send(e)} ::: affect.values.toList 
 /** records all the expressions used more than once, should be called when circuit building is finished. */
  //lazy val reused:List[AST[_,_]]=nodes.toList.filter(_ .user.size > 1);
   
   override def toString:String=   instr.map( _ .toString).foldLeft("")(_ + ",\n " + _)
}
object Circuit{
  
  
  
}