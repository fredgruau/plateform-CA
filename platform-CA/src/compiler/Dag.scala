package compiler

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail
import scala.collection.immutable.HashMap
 
/* trait Dag2[+T <: Dag2[T]] {
  def neighbor: List[_<: Dag2[_]]
  /**by default there is no new fiedls to visit */
  def other: List[T] = List.empty
  def toStringTree: String = toString + (neighbor.size match {
    case 0 => " "
    case 1 => " " + neighbor.head.toStringTree
    case _ => "(" + (neighbor.map(_.toStringTree)).foldLeft("")(_ + ", " + _) + ")" //TODO virer la premiere virgule
  })
} */
/**
 * Node of a directed acyclic graph
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 *  whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 *     to complete on the fly an initial set of minimals
 */
trait Dag[T <: Dag[T]] {
  def neighbor: List[T ]
  /**by default there is no new fiedls to visit */
  def other: List[T] = List.empty
  def toStringTree: String = toString + (neighbor.size match {
    case 0 => " "
    case 1 => " " + neighbor.head.toStringTree
    case _ => "(" + (neighbor.map(_.toStringTree)).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
  })
}
//(neighbor.map( _ .toString)).foldLeft("")(_ + ", " + _)
  

/** offer the additional possibility to do substitution on the neighbor by using
 *  an ad hoc implementation of a lazzy var */ 
//TODO je pense qu'il y a un bug dans le substitute, parce que cela ne modifie pas l'AST lui meme avec ses cases class.
trait MutableDag[T <: Dag[T]] extends Dag[T] {
  def neighbor2: List[T]
  private[this] var _field: List[T] = _
  def substituteInArg() 
  def neighbor = {
    if (_field == null) {
      _field = neighbor2
    }
    _field 
  } 
  def field_=(str: List[T]) {
    _field = str
  }
  /**New added functionality brough by the trait, allowing substitution of one node by others.*/
  def substitute(t: T, newt: T):Boolean = {
    var changed=false
    _field = _field.map(n => if (n == t){changed=true; newt} else n)
    if (changed) substituteInArg() 
    return changed
  }
  /**Produit un dag fidéle a ce qui imprimé, en factorisant lorsqu'il y a des sous-arbres identiques.  */
   def fold( repres: HashMap[T, T]) = { 
    _field = _field.map(n =>  repres(n))
     substituteInArg()  
  } 
}

object Dag {
  /**
   * Used to instanciate a hashset "visited" of the right type T <: Dag[T]
   */
  import scala.collection.immutable.HashSet
  class Dfs[T <: Dag[T]](var visited: HashSet[T]) {
    def this() = this(HashSet.empty)
    /**VisitedL is used to preserve the order */
    var visitedL: List[T] = List.empty;
    /**
     * verify that there is no cycle within a graph, starting from a given node n
     * using a depth first search (dfs)
     * simultaneously update visited which contains all the node that can be reached from b
     * @n  node to test
     * @return option type with a cycle is there is one.
     */
    def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
      if (visited(n)) return None
      else if (visiting.contains(n))
        return Some(visiting.drop(visiting.indexOf(n) - 1))
      else {
        val visiting2 = visiting :+ n;
        for (e <- n.neighbor)
          dfs(e, visiting2) match { case Some(c) => return Some(c) case _ => }
        visited = visited + n
        visitedL = n :: visitedL
        //visit "other" nodes met on the fly (in the next part of layers
        for (e <- n.other) if (!visiting.contains(e) && e != n)
          dfs(e, Vector.empty) match { case Some(c) => return Some(c) case _ => }
      }
      return None
    }
  }
  /**
   * Compute the set of nodes of a DAG
   * throw an exeption if the graph is not a DAG
   * T<:Dag[T] means that neighbor are also of the same type
   * @param minimals, set of DAG's minimal. easier to process as a list.
   * @param visited, already visited nodes.
   * @return nodes greater than those
   */
  def getGreater[T <: Dag[T]](minimals: List[T]): (List[T], HashSet[T]) = getGreater(minimals, HashSet.empty[T])
  def getGreater[T <: Dag[T]](minimals: List[T], visited: HashSet[T]) =
    {
      val dfs = new Dfs[T](visited)
      for (b <- minimals)
        dfs.dfs(b, Vector.empty) match {
          case Some(path) => throw new RuntimeException("cycle detected in AST:" + path)
          case None       =>
        }
      (dfs.visitedL, dfs.visited);
    }

  /**
   * Tries to find a cycle
   * @param n starting node to reach the cycle
   * @return the cycle if a cycle is found, else none
   */
  def getCycle[T <: Dag[T]](n: T): Option[Vector[T]] =
    { val dfs = new Dfs[T]; return dfs.dfs(n, Vector.empty) }

}

