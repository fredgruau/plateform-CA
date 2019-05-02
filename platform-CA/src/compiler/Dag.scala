package compiler 

import junit.framework.TestCase
import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail 

  /**  
  * Node of a directed acyclic graph
  * getCycle is used to test the absence of cycle
  * getGreater is used to collect all the nodes of a Dag, 
  *    whose set of minimum is known.
  */
trait Dag {def neighbor:List[Dag]}

object Dag{
  import   scala.collection.immutable.HashSet
  var visited:HashSet[Dag]=HashSet.empty;
   /**  
  * verify that there is no cycle within a graph, starting from a given node n
  * using a depth first search (dfs)
  * simultaneously update visited which contains all the node that can be reached from b
  * @n  node to test
  * @return option type with a cycle is there is one. 
  */
  private def dfs(n: Dag, visiting: Vector[Dag]): Option[Vector[Dag]] = {
    if (visited(n)) return None
    else if (visiting.contains(n)) return Some(visiting.drop(visiting.indexOf(n) - 1))
    else {
      val visiting2 = visiting :+ n;
      for (e <- n.neighbor)
        dfs(e, visiting2) match { case Some(c) => return Some(c) case _ => }
    }
    visited = visited + n
    return None
  }
  /**  
  * Compute a set of nodes from a DAG 
  * throw an exeption if the graph is not a DAG
  * @param minimals  some elements
  * @return nodes greater than those  
  */
    def getGreater( minimals:Set[Dag]):Set[Dag]=
    {  visited=HashSet.empty
       for(b<-minimals)   dfs(b,Vector.empty) match{ 
          case Some(path) => throw new RuntimeException("cycle detected in AST:"+path )
          case None =>
          }
       return visited;
    }
     /**  
  * Tries to find a cycle 
  * throw an exeption if the graph is not a DAG
  * @param n starting node to reach the cycle
  * @return the cycle if a cycle is found, else none
  */ 
    def getCycle(n:Dag)  :Option[Vector[Dag]]= 
      {visited=HashSet.empty;return dfs(n,Vector.empty)}
 
}

