package compiler
import compiler.AST.Layer

/**Each instruction uses an expression*/ 
sealed abstract class Instruction  (val exp:AST[_<:Locus,_<:Ring])    {override def toString:String=exp.toString;}
/**use to store results which are reused more than once */
case class Affect (override val exp:AST[_<:Locus,_<:Ring])  extends Instruction (exp)
 {override def toString:String=exp.name+"= " +AST.toStringTree(true,exp); val shown=false;val hidden=true;}
/**used to store a boolean consition that if no true indicates a bug in the layer. */
class Ensure (override val exp:AST[_<:Locus,_<:B])  extends Affect (exp)
/**used For Dispaly */
class Display(override val exp:AST[_<:Locus,_<:Ring])  extends Affect (exp){override val shown=true; override  val hidden=false;}
/**used For Potential Dispaly */
class Displayable(override val exp:AST[_<:Locus,_<:Ring])  extends Affect (exp){override val shown=false; override  val hidden=false;}
/**use to store result in the CA memory */
case class Send  (override val exp:AST[_<:Locus,_<:Ring])  extends Instruction (exp)
  {override def toString:String="send() " + exp.toString}
case class Memorize (val l:Layer[_<:Locus,_<:Ring])  extends Instruction (l.next) 
 {override def toString:String="mem[]= " + AST.toStringTree(true,exp)}
/**to send an expression being transfered.*/