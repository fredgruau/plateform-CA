package compiler 
import scala.collection.mutable.Map
import Circuit._ 
object Compiler {
  
  def makeInstr (a:AST[_<:Locus,_<:Ring]):Instruction= a   match {
	case l:Layer[_,_]  => Memorize(l)  
	case _ =>   null
  }
  
  
  def compile(c:Circuit){
//    /**to find out dependencies between instruction, we need to know which affectation affects a given expression to a variable */
//    val affect=Map[AST[_<:Locus,_<:Ring],Affect]()
//    /**we generate affect for debug, displayed, displayable variables, and finally for reused variable*/
//    c.layers.foreach( l =>  {
//         l.ensure.foreach( e => affect+=(e->Ensure(e)))
//         l.display.foreach( e => if(!affect.contains(e) )affect+=(e->Display(e)))
//         l.displayable.foreach ( e =>  if(!affect.contains(e) )affect+=(e->Displayable(e)))
//    });
//     c.nodes.foreach ( e =>  if(!affect.contains(e) & e.user.size > 1 ) affect+=(e->new Affect(e)) )
////     val sendInst:List[Send]=c.nodes.toList.filter(Transfer ).map (_ case l:Transfer(e) => Send(e)
//  
//      val sendInst:List[Send]= c.nodes.toList collect { case Transfer(e) => Send(e)}
//      val memInst:List[Memorize] =  c.nodes.toList collect { case e:Layer[_,_] => Memorize(e)} //je voudrais Memorize(e.next) mais ca marche pas avec les types
    Name.setName(c," ");
  
  }
}