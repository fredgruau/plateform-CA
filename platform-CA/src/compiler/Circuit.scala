package compiler 
import compiler.ASTL._  
import scala.collection.immutable.HashMap
import Dag.getGreater
import scala.collection.immutable.HashSet

 /**Analysed by the compiler to produce a CA rule */
trait Circuit  extends   Named{
  /** to be defined in the circuit for collecting all the nodes participating in usefull computation, defined as a method, because knwon latter*/
  def computeRoot: List[ASTLg]
   /**  
  * Scan all AST nodes to modify the neighbors in order to do a substitution
  * @param l: layer to be replaced.
  * @param newExp computation that replaces l, once substitution is completed
  */  
  def substitute[T<:compiler.Locus,R<:compiler.Ring](l:Layer[T,R],newExp:ASTL[T,R]):Unit={
    val (computeNodes, visited1) = getGreater(computeRoot.asInstanceOf[List[AST[_]]])
    val layers: List[Layer[_ <: Locus, _ <: Ring]] = computeNodes.collect { case l: Layer[_, _] => l } 
    val minimals =  layers.map { g: Layerg => g.bugif:::g.render:::g.inspect }.flatten;   
    val (otherNodes, visited2) = getGreater(minimals, visited1)
     println("nombre de compute node:"+computeNodes.size);
    var compteur:Int=0
    val allASTNodes=computeNodes:::otherNodes
      val represent: HashMap[AST[_], AST[_]] = HashMap.empty[AST[_],AST[_]] ++ allASTNodes.map(x => (x -> x))
     for(n<-allASTNodes) n.fold(represent );
   for(n<-allASTNodes) if( n.substitute(l,newExp)) compteur+=1;
    println("nombre de noeuds subissant une substitution:"+compteur);
  }
   
   /**  
  *  Compiles the circuit
  *  The DAG stores AST[T], it it designed to work both for ASTL and ASTB, 
  *  this explains, why we must contantly cast back and forth between AST and ASTL 
  *  when calling getGreater from DAG.
  */ 
  def compile: Unit={ 
    ////////////STEP1 compute  the minimals of the AST DAG
  /**  compute AST nodes, sorted in  topological order (opposite to dependance), modulo an equivalence relation of having identical structure*/
  val (computeNodes, visited1) = getGreater(computeRoot.asInstanceOf[List[AST[_]]]).asInstanceOf[Tuple2[ List[ASTLg],HashSet[ASTLg] ]]
  val layers: List[Layerg] = computeNodes.collect { case l: Layer[_, _] => l }
  /**non constant layers ==> their next need to be computed */
  val nextRoot: List[ASTLg] = layers.filter(l => l.next != l).map(_.next)
  /**Compute DAG's minimal associated to bugif, render and inspect */
  val (bugIfRoot, renderRoot, inspect) = { def f[T](g: Layerg => List[T]) = layers.map { g }.flatten; (f[ASTbool](_.bugif), f[ASTLg](_.render), f[ASTLg](_.inspect)) }
   // Retrieve the associated additional nodes needed to compute bugIfRoot ,renderRoot ,inspect
   // "visited" is updated in order to avoid recomputing a hashSet of computeNodes from a list of computeNodes
  val (bugIfNodes, visited2) = getGreater(bugIfRoot, visited1.asInstanceOf[HashSet[AST[_]]]).asInstanceOf[Tuple2[ List[ASTLg],HashSet[ASTLg] ]]
  val (renderNodes, visited3) = getGreater(renderRoot, visited2.asInstanceOf[HashSet[AST[_]]]).asInstanceOf[Tuple2[ List[ASTLg],HashSet[ASTLg] ]]
  val (inspectNodes, visited4) = getGreater(renderRoot, visited3.asInstanceOf[HashSet[AST[_]]]).asInstanceOf[Tuple2[ List[ASTLg],HashSet[ASTLg] ]]
  //we can inspect only already existing computation
  if (inspectNodes.size > 0) throw new RuntimeException("inspectnodes involved new computation")
  /**   Total list of AST Nodes that can be computed */
  val allASTNodes:List[ASTLg]  =  (renderNodes ::: bugIfNodes ::: computeNodes )  
  
  /**Nodes with identical structure cannot be distinguished, the represent hashtable is used to get the representative of each equivalence class */
  val represent: HashMap[ASTLg, ASTLg] = HashMap.empty[ASTLg, ASTLg] ++ allASTNodes.map(x => (x -> x))
 // for(n<-allASTNodes) n.fold(represent.asInstanceOf[HashMap[AST[_], AST[_]]] );
  /**the number of times each equivalence class is used */
  val nUser: HashMap[ASTLg, Int] = HashMap.empty[ASTLg, Int] ++ (allASTNodes.map(_.neighbor.asInstanceOf[ List[ASTLg]]).flatten ::: nextRoot ::: bugIfRoot).groupBy(identity).mapValues(_.size)
  val usedMoreThanOnce=allASTNodes.filter(e=>nUser.contains(e)&&nUser(e)> 1)
  //we give a name using a number to those expression that needs it.
  Name.setName(this," ")
  for(e<-usedMoreThanOnce:::renderNodes:::inspectNodes) e.checkName()
  /**Instruction affect points to expressions reused two times or more, which needs to be given a name  nUser is temporary set to 1 to avoid generating read*/
  val affect   =  (usedMoreThanOnce.map(e=>  Affect(e.deDag3 (nUser+(e->1),represent  ),e.name)  ) ).asInstanceOf[List[Affect[ASTLg]]]
  //verifies that each affectation uses a non null name for the recipient variable
    //val affect:List[Affect[AST2g]]=affect2
      for(a<-affect) if(a.name==null) throw new RuntimeException("name is not defined for affectation of "+ a.exp.toStringTree  )
  val affectMap:Map[String,Affect[ASTLg]]    =  affect.map(e=>(e.name,e)).toMap 
  //verifies that each affectation uses a distinct name for the recipient variable
  if(affectMap.size<affect.size) throw new RuntimeException("a name is reused two times"  )
 
  //computing three kinds of instructions:
  val memorize=nextRoot.map( e  =>   Memorize2(e.deDag3(nUser,represent  ))).asInstanceOf[List[Memorize2[ASTLg]]]   // :::nodes.toList.collect { case Transfer(e) => Send(e)}
  val bugifInstr=  bugIfRoot.map( e  =>  Bugif(e.deDag3(nUser,represent ).asInstanceOf[ASTbool]) ).asInstanceOf[List[Bugif[ASTbool]]]  // :::nodes.toList.collect { case Transfer(e) => Send(e)}
  /**values that need not be computed when relaxing the circuit without looking at it*/
  val computeMinimals = ((computeRoot:::renderRoot). filter(e=> !nUser.contains(e) ).map (e  => ComputeMinimal(e.deDag3(nUser,represent)))).asInstanceOf[List[ComputeMinimal[ASTLg]]]
  println("AST has " + computeNodes.size  + "compute Nodes")
  val allInstructions=bugifInstr:::computeMinimals:::memorize:::affect
  //println(usedMoreThanOnce)
  val nbit   = scala.collection.mutable.HashMap.empty[ASTLg, Int] 
  println(allInstructions.reverse)
  val allIntructionsNbit=allInstructions.reverse.map(i=>Instruction.computeNbit(nbit,affectMap,i ))
 // println(allIntructionsNbit.map( i=> i.toString + (if(nbit.contains(i.exp)) "nbit"+nbit(i.exp) else "*")).foldLeft("")(_ + ",\n " + _))
  }
  
 /**Prints all the instructions */
 override def toString:String= "macache"
   //   "\n AST has " + computeNodes.size  + "compute Nodes" +
      //  computeNodes.map( _ .toString).foldLeft("")(_ + ",\n " + _) + " \n and **********"+
      //  bugIfNodes.size  + "bugIf Nodes" +
      //  bugIfNodes.map( _ .toString).foldLeft("")(_ + ",\n " + _)+ " \n and **********" +
      // renderNodes.size  + "renderNodes" + 
      //  renderNodes.map( _ .toString).foldLeft("")(_ + ",\n " + _)    +  
         
}

object Circuit{
  
  
// var nBit: HashMap[ASTg2, Int] = HashMap.empty[ASTg2, Int]
  
}