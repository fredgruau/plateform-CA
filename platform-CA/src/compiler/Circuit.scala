package compiler
import scala.collection.immutable.Map
import scala.collection.mutable.ListBuffer
import compiler.AST._ 
 
 /**Analysed by the compiler to produce a CA rule */
class Circuit extends    Named{
  private var delayed:Vector[Delayed[_<:Locus,_<:Ring]]=Vector.empty
  def addDelayed(d:Delayed[_<:Locus,_<:Ring])={delayed=delayed:+d}
  /**for evaluation of arg which was lazy, delayed, this can result in adding more arg.  */
  def evalDelayed()={var i=0; while(i<delayed.size){delayed(i).arg;i+=1}}
  def all=nodes.toSet
//  var layers= new ListBuffer[Layer[_<:Locus,_<:Ring]]()  
 /** records all the AST nodes, in order to easily iterate on them */
   private var nodes= new ListBuffer[AST[_<:Locus,_<:Ring]]()  
   /**traversal of nodes goes downward the Abstract Syntax Tree, not completely guaranteed, though, due to delayed evaluation */
   def addNode(d:AST[_<:Locus,_<:Ring])={d+=:nodes }
   lazy val layers:List[ Layer[_<:Locus,_<:Ring]]=  nodes.toList.collect{ case l:Layer[_,_ ] =>l }
 /** Creates a mapping linking expression, to Affectation that uses them. Needed to find out dependencies between instruction*/  
   lazy  val affect:Map[AST[_<:Locus,_<:Ring],Affect] 
        = (nodes.toList.filter(_ .user.size > 1).map(e=>(e,new Affect(e))) :::            //affectation for reused expressions
           layers.foldLeft(List[(AST[_<:Locus,_<:Ring],Affect)]())(_ :::_.affect)).toMap  //affectation for ensure, displayed, displayable expression
 /** Three kind of instrucitons: 1- memorizing, 2- sending to another simplicial locus, 3-  affectation.  */
  lazy val instr: List[Instruction]= layers.map{ e  => Memorize(e)}  ::: affect.values.toList // :::nodes.toList.collect { case Transfer(e) => Send(e)}
        
 /** records all the expressions used more than once, should be called when circuit building is finished. */
  //lazy val reused:List[AST[_,_]]=nodes.toList.filter(_ .user.size > 1);
 /**Prints all the instructions */
   override def toString:String= "AST has "+ nodes.size + " nodes, grouped into " + instr.size + " instructions " + 
   instr.map( _ .toString).foldLeft("")(_ + ",\n " + _)
}

object Circuit{
  
  
  
}