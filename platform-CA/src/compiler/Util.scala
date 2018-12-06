package compiler 

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail 
 
class  Util  extends TestCase {
  
  class Node(  e : => List[Node],val name:String) extends Bag{def elt=e; override def toString=name;}
  case class  DAG(val a :Set[Bag]) extends Bags with BagLibrary {def all=a }

  def node(n : => Node,na:String):Node={lazy val delayed = List(n); new Node(delayed,na)}
  val n1=new Node(List.empty ,"toto")
  val n2=new Node(List.empty ,"tata")
  val n3=new Node(List(n1,n2) ,"tutu")
  val d1=DAG(Set(n1,n2,n3))
  def testWithoutCycle=  assertEquals(d1.getCycle, None) 
  val n4:Node=node(n5,"n4")
  val n4bis:Node=new Node(List(n4),"n4bis ")

  lazy val n5=new  Node(List(n1,n4bis) ,"n5")
  val n6=new Node(List(n4bis),"n6")
  val d2=DAG(Set(n1,n4,n5,n6))
    def testWithCycle=  assert (d2.getCycle match {case Some(c) => {println(c);true}; case None => false  })
    
 // val testCycle=new Circuit(){val chip= CycleLayer(this,3);}
  
}

trait Bag {def elt:List[Bag]}
trait EmptyBag extends Bag{  def elt:List[Bag]=List.empty}
trait Singleton extends Bag{ val arg:Bag; def elt:List[Bag]=List(arg)}
trait Doubleton extends Bag{ val arg1:Bag;val arg2:Bag; def elt:List[Bag]=List(arg1,arg2)}
trait Neton extends Bag{ val args:Seq[Bag] ; def elt:List[Bag]=args.toList}

trait Bags {  def all:Set[Bag]}

/**Contains a public method to find a cycle if there exists one. */
trait BagLibrary extends Bags{
  private var visited: Set[Bag]=Set.empty
  private def dfs (b:Bag,visiting:Vector[Bag]):Option[Vector[Bag]]={
      if( visited(b))  return None
      else if (visiting.contains(b)) return Some(visiting.drop(visiting.indexOf(b)-1))
      else {val visiting2=visiting:+b;
        for(e<-b.elt)   dfs(e, visiting2) match { case Some(c) => return Some(c) case _ =>}
      }
      visited+=b
      return None
      
    }  
    def getCycle  :Option[Vector[Bag]]=
    {    visited=Set.empty;
         for(b<-all)   dfs(b,Vector.empty) match{ case Some(c) => return Some(c) case _ => }
         None
    } 
}
  
  
  
//  
//  
//object Util {
//  
//object PrettyPrint{
//	/**
//	 * Pretty prints a Scala value similar to its source represention.
//	 * Particularly useful for case classes.
//	 * @param a - The value to pretty print.
//	 * @param indentSize - Number of spaces for each indent.
//	 * @param maxElementWidth - Largest element size before wrapping.
//	 * @param depth - Initial depth to pretty print indents.
//	 * @return
//	 */
//	def prettyPrint(a: Any, indentSize: Int = 2, maxElementWidth: Int = 30, depth: Int = 0): String = {
//			val indent = " " * depth * indentSize
//					val fieldIndent = indent + (" " * indentSize)
//					val thisDepth = prettyPrint(_: Any, indentSize, maxElementWidth, depth)
//					val nextDepth = prettyPrint(_: Any, indentSize, maxElementWidth, depth + 1)
//					a match {
//				// Make Strings look similar to their literal form.
//					case s: String =>
//					val replaceMap = Seq(
//							"\n" -> "\\n",
//							"\r" -> "\\r",
//							"\t" -> "\\t",
//							"\"" -> "\\\""
//							)
//					'"' + replaceMap.foldLeft(s) { case (acc, (c, r)) => acc.replace(c, r) } + '"'
//					// For an empty Seq just use its normal String representation.
//					case xs: Seq[_] if xs.isEmpty => xs.toString()
//					case xs: Seq[_] =>
//					// If the Seq is not too long, pretty print on one line.
//					val resultOneLine = xs.map(nextDepth).toString()
//					if (resultOneLine.length <= maxElementWidth) return resultOneLine
//							// Otherwise, build it with newlines and proper field indents.
//							val result = xs.map(x => s"\n$fieldIndent${nextDepth(x)}").toString()
//							result.substring(0, result.length - 1) + "\n" + indent + ")"
//							// Product should cover case classes.
//					case p: Product =>
//					val prefix = p.productPrefix
//					// We'll use reflection to get the constructor arg names and values.
//					val cls = p.getClass
//					val fields = cls.getDeclaredFields.filterNot(_.isSynthetic).map(_.getName)
//					val values = p.productIterator.toSeq
//					// If we weren't able to match up fields/values, fall back to toString.
//					if (fields.length != values.length) return p.toString
//							fields.zip(values).toList match {
//						// If there are no fields, just use the normal String representation.
//							case Nil => p.toString
//									// If there is just one field, let's just print it as a wrapper.
//							case (_, value) :: Nil => s"$prefix(${thisDepth(value)})"
//							// If there is more than one field, build up the field names and values.
//							case kvps =>
//							val prettyFields = kvps.map { case (k, v) => s"$fieldIndent$k = ${nextDepth(v)}" }
//							// If the result is not too long, pretty print on one line.
//							val resultOneLine = s"$prefix(${prettyFields.mkString(", ")})"
//							if (resultOneLine.length <= maxElementWidth) return resultOneLine
//									// Otherwise, build it with newlines and proper field indents.
//									s"$prefix(\n${prettyFields.mkString(",\n")}\n$indent)"
//					}
//					// If we haven't specialized this type, just use its toString.
//					case _ => a.toString
//			}
//	}
//}
//}