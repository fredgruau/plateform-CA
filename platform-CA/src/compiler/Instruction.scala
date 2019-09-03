package compiler
import compiler.ASTL._
/**
 * Instruction are five possible types. 
 * display and inspect change dynamically so they are not instructions.
 * @exp Each instruction uses an expression
 */


sealed abstract class Instruction[+T<:Dag[_]](val exp: T) {
  override def toString: String = { " "+  (this match {
      case Affect(e, n)     => n + "= "
      case Memorize2(e)      => "mem[]= "
      case Bugif(e)         => e.name + " bugIf "
      case ComputeMinimal(e) => "compute "
//      case TransferI(e)      => "send"
    }) + exp.toStringTree
  } 
}
  
object Instruction 
{
   def computeNbit(nbit: scala.collection.mutable.HashMap[AST2g, Int], affectmap: Map[String,Affect[AST2g]], i: Instruction[AST2g]):  Instruction[AST2g] = {
     val inew =    i.asInstanceOf[Instruction[ASTL[_,_]]]  match {
      case af @ Affect(e, n)  => af.copy(exp=ASTL.computeNbit(nbit, affectmap,af.exp.asInstanceOf[AST2g]))
      case mem@Memorize2(e)      => mem.copy(exp=ASTL.computeNbit(nbit, affectmap,mem.exp))
      case bug@Bugif(e)         => bug.copy(exp=ASTL.computeNbit(nbit, affectmap,bug.exp).asInstanceOf[ASTbool]) 
      case min@ComputeMinimal(e) =>  min.copy(exp=ASTL.computeNbit(nbit, affectmap,min.exp.asInstanceOf[AST2g]))
        }
     return inew.asInstanceOf[Instruction[AST2g]]
      
  }
   
}
/**use to store results which are reused more than once */
case class Affect[T<:Dag[_]](override val exp: T, val name: String) extends Instruction[T](exp) 
/**Update the memory*/
case class Memorize2[T<:AST2g](override val exp: T ) extends Instruction[T](exp) 
/** For checking invariant, must be all false */
case class Bugif[T<:ASTbool](override val exp: T) extends Instruction[T](exp)
/**computation not necesseary for relaxation but for display or debug */
case class ComputeMinimal[T<:Dag[_]](override val exp: T) extends Instruction[T](exp)
/**to send an expression being transfered so that it is also an instruction*/
//case class TransferI(override val exp: ASTL[_ <: Locus, _ <: Ring]) extends Instruction(exp)
 