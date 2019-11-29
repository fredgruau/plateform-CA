package compiler
import ASTBfun.ASTBg
import VarKind._
import AST._
import ASTL._
import Dag._
import UsrInstr._
import scala.collection._
import ProgData._
import ASTB._

/**The most elementary info stored in symbol table: type and kind */
class InfoType[+T](val t: T, val k: VarKind) { override def toString = t.toString + " " + k.toString }
object InfoType {
  def apply(e: AST[_], k: VarKind): InfoType[_] = new InfoType(e.mym.name, k)
  def addSymb(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind) = t += e.name -> InfoType(e, k)
  def addSymbL(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind) = t += "l" + e.name -> InfoType(e, k)
}

/** info stored in symbol table, after computing nbit: type and kind and nbit */
class InfoNbit[+T](override val t: T, override val k: VarKind, val nb: Int) extends InfoType(t, k) {
  val u = 2; override def toString = t.toString + " " + k.toString + " " + nb
}

object ProgData {
  private var nameCompteur = 0;
  def getCompteur: Int = { nameCompteur += 1; nameCompteur }
  def newFunName() = "_fun" + getCompteur;
  def string(l: List[_], c: String): String = l.foldLeft("")(_ + c + _)
  def listOf[T](t: Map[String, T]) = { val (anon, definedMacros) = t.partition((x: (String, T)) => x._1.startsWith("_fun")); anon.toList ::: definedMacros.toList }
 // def string(t: iTabSymb[_], c: String): String = t.map { case (k, v) ⇒ k → v.toString }.foldLeft(" ")(_ + c + _)
 /**pring a map on several small lines, instead of one big line */
  def string[T](t: TabSymb[T], s: String) = t.toList.grouped(4).toList.map(_.mkString(s)).mkString("\n") + "\n"

  /**add one (resp. two) suffixes to the variable names, for simplicial (resp. tranfer) variable */
  def deploy(n: String, tSymb: TabSymb[InfoNbit[_]]): List[String] = deploy(n, tSymb(n).t.asInstanceOf[Tuple2[_ <: Locus, _]]_1)
  def deploy(n: String, l: Locus): List[String] = l match {
    case s: S      => s.sufx.map(n + _).toList
    case T(s1, s2) => s1.sufx.map((suf1: String) => l.sufx.map(n + suf1 + _).toList).toList.flatten
  }

  //=> s1.sufixeS.map(s:String=>

  type TabSymb[T] = mutable.HashMap[String, T]; type AstField[T] = mutable.HashMap[AST[_], T]
  type iTabSymb[T] = Map[String, T]; type iAstField[T] = Map[AST[_], T]
  /**spatial unfolding of an ASTL of "simplicial" type creates an array of array of ASTB. The cardinal of first array is 1,2,3 for V,F,E,  */
  type ArrAst = Array[ASTBg]
  /**spatial unfolding of an ASTL of "transfer type" creates an array of array of ASTB. The cardinal of first array is 1,2,3 for V,F,E, the seconds array is 6,3,2  */
  type ArrArrAst = Array[Array[ASTBg]]
  /**
   * The only place where a machine differs from another is when compiling the transfer function,
   * it is parameterise by One function for each pair of simplicial type.
   * Type of input is transfer(src,des) type of output is transfer(des,src) , where "src" is first S, and "des" is second S
   */
  type Machine = (S, S, ArrArrAst) => ArrArrAst

  /**
   * The hexagon machine models communication according to the perfect hexagonal grid.
   * diagonal (d1,d2) and antidiagonla (ad1,ad2) are oriented so that all the shift and delay gets applied on d1 (up), so that the same computation is applied
   * on d2 and ad2, when the vE fields is obtain by a broadcast followed by a transfer.
   */

  val hexagon: Machine = (src: S, des: S, t: ArrArrAst) => {
    implicit val scalarType = t(0)(0).mym; src match {
      case V() => des match {
        case E() => /*eV->vE*/
          val Array(e, ne, nw, w, sw, se) = t(0);
          Array(Array(shiftL(Tminus1(w)), Tminus1(e)), Array(Tminus1(se), nw), Array(shiftL(Tminus1(sw)), ne))
        case F() => /*fV->vF*/
          val Array(ne, n, nw, sw, s, se) = t(0); Array(Array(n, Tminus1(sw), Tminus1(se)), Array(shiftL(Tminus1(s)), ne, shiftL(nw)))
      }
      case E() =>
        val Array(Array(h1, h2), Array(d1, d2), Array(ad1, ad2)) = t; //common to vE and fE
        des match {
          case V() => /*vE->eV*/
            Array(Array(h2, Tminus1(ad2), shiftR(Tminus1(d2)), shiftR(h1), shiftR(ad1), shiftR(d1)))
          case F() => /*fE->eF*/
            Array(Array(Tminus1(h1), ad1, d1), Array(shiftL(h2), ad2, d2))
        }
      case F() => des match {
        case V() => /*vF->fV*/
          val Array(Array(ub, us1, us2), Array(db, ds1, ds2)) = t; Array(Array(Tminus1(ds1), Tminus1(ub), shiftR(Tminus1(ds2)), shiftR(us1), shiftR(db), us2))
        case E() => /*eF->fE*/
          val Array(Array(up, ub1, ub2), Array(dp, db1, db2)) = t; Array(Array(up, Tminus1(dp)), Array(ub2, db2), Array(ub1, shiftR(db1)))
      }
    }
  }

  val transfers: List[(S, S)] = List((V(), E()), (E(), V()), (V(), F()), (F(), V()), (E(), F()), (F(), E()))

  /** generates an input array*/
  def inAr(s1: S, s2: S):ArrArrAst  = {var i = -1;def nameInt ={ i += 1; "" + i};  def myp() = new Param[B](nameInt)with ASTBt[B]; Array.fill(s1.arity)(Array.fill(6/s1.arity)(myp()))  }
  /** automatically computes permutation implied by hexagon*/
   val hexPermut: immutable.Map[(S, S), Array[Int]] = immutable.HashMap.empty ++ transfers.map((ss: (S, S)) => ss ->
   { val (s1,s2)=ss;val t=hexagon(s1,s2,inAr(s1,s2));   val l=t.map(_.toList).toList.flatten;  //compute the permutation of T[S1,S2] => T[S2,S1]
     val r=new Array[Int](6); var i=0; for(a<-l){ r(i)=a.symbols.head.toInt;i+=1};  r})


  def apply[T](f: Fundef[T], repl: iAstField[AST[_]] = immutable.HashMap.empty): ProgData[_] = {
    val (computeNodes, visited1) = getGreater(
      f.body.asInstanceOf[AST[_]] :: repl.values.toList,
      immutable.HashSet.empty[AST[_]] ++ repl.keys) //those are passed so as not to be visited.
    val allNodes = computeNodes ::: repl.keys.toList //the keys have not been visited, so we must explicitely add them into all nodes.
    Name.setName(f, ""); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ (computeNodes.collect { case l: Call[_] => (l.f.namef, l.f) })
    new ProgData[T](f, funs.map { case (k, v) ⇒ k → ProgData(v) }, allNodes)
  }
 
}

/**
 * Retrieves all the compute nodes associated to a function
 * @f the function,
 * @funs functions decomposing the code in a modular way
 * @allnodes all the AST nodes.
 */
class ProgData[+T](val f: Fundef[T], val funs: iTabSymb[ProgData[_]], val allNodes: List[AST[_]]) {

  /**
   * Replaces DAG by a list of trees, adding a read node using names, and building  a list  of affect instruction.
   *  also does Substitution is usefull only for the main body,
   *     @replaced   substitution map
   */
  def deDagise(replaced: iAstField[AST[_]] = immutable.HashMap.empty): ProgData1[T] = {
    val instrs = allNodes.map(_.sysInstrs).flatten;
    val represent = immutable.HashMap.empty[AST[_], AST[_]] ++ (allNodes).map(x => (x -> x)) //necessary because distinct AST can be equals  when compared as case class hierarchie
    val invertReplaced = replaced.map { _.swap }; //whenever the value is used, we need to count 1 for the key, so we compute the invertReplace map
    val users = f.body :: instrs.map(_.exp) //instruction using exp needs to be considered as users of exp also
    val nUser = immutable.HashMap.empty[AST[_], Int] ++ (allNodes.map(_.neighbor).flatten ++ users).map(l => invertReplaced.getOrElse(l, l))
      .groupBy(identity).map { case (k, v) ⇒ k → v.size }
    val usedTwice = allNodes.filter(e => nUser.contains(e) && nUser(e) > 1)
    // for (e <- usedTwice /**  ++ allNodes*/ ) e.checkName() //donne un nom. -- TODO verify if we should really name all the nodes, its better to name only the reused expression to avoid generating big numbers for aux.

    val usedTwiceAsValue = usedTwice.map(e => replaced.getOrElse(e, e)) //among the ast being reused, if one is among those to be substituted, then it is substituted.
    val UsedTwiceAskey = usedTwiceAsValue.filter(t => invertReplaced.contains(t)).map(e => invertReplaced(e))

    //  val needAffect: immutable.HashSet[AST[_]] = immutable.HashSet.empty ++ allNodes.filter { e => //we force affectation on those to facilitate latter processing @TODO forcer aussi l'affect sur les parametres données.
    //    e match { case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => !usedTwiceAsValue.contains(e) case _ => false }    }

    val callAndHeadAndRedop = allNodes.filter(_ match {
      case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => true
      case a: ASTL[_, _] => a.shouldAffect
      case _ => false
    })
    val inCall = callAndHeadAndRedop.map(_ match { case c: Call[_] => c.args.filter(!_.neighbor.isEmpty).toList case _ => List[AST[_]]() }).flatten
    val needAffect2 = callAndHeadAndRedop ::: inCall //.filter(  !usedTwiceAsValue.contains(_))
    //  for (e <- needAffect2   ) e.checkName()
    val affectExpList2 = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ needAffect2
    val affectExpList2ordered = allNodes.filter(affectExpList2.contains(_)) //exploits the fact that allNodes are naturally topologically ordered to peserve the order for the list of affectations.
    for (e <- affectExpList2ordered) e.checkName()
    if ((immutable.HashSet.empty ++ affectExpList2ordered.map(_.name)).size < affectExpList2ordered.size) throw new RuntimeException("a name is reused two times") //since name are given by hand we check that no two names are equals
    for ((k, v) <- replaced) represent(v).setName(k.name) //the name of the key (to be replaced) is transfered to the replacing value.
    val toBeReplaced = affectExpList2 ++ UsedTwiceAskey
    val affectExpList = affectExpList2ordered.map(e => e.deDag(toBeReplaced - e, represent, replaced)).reverse //we remove e from usedTwice to avoid generate e=read(e) !!!!
    val t: TabSymb[InfoType[_]] = mutable.HashMap.empty
    t ++= affectExpList.map(e => (e.name, new InfoType(e.mym.name.asInstanceOf[T], Field())))
    t ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD()))) //type of parameters this statement must happen after the addition of affects otherwise paramD varkind will be replaced by Affectk

    val affectInstr = affectExpList.map(e => Affect(e.name, e))
    val allUsedTwice = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ UsedTwiceAskey

    val newInstrsSys = (allNodes).map(e => {
      e.sysInstrs.map(i => new UsrInstr(i.c, i.exp.deDag(toBeReplaced, represent, replaced)) //  dedagify   exp used in system instructions
        .affectize(e, allUsedTwice.contains(i.exp), t))
    }).flatten.flatten //one flatten for list of list, and another one for None/Some

    f.body = f.body.deDag(toBeReplaced, represent, replaced)
    return new ProgData1(f, affectInstr ::: newInstrsSys.reverse, funs.map { case (k, v) ⇒ k → v.deDagise() }, t, f.p.toList.map("p" + _.name), List()) //result parameter to be added letter by procedure step.
  }
}

/**
 * Stores all the data associated to a program, used for compilation
 *  @ tabSymbVar,  stores info about parameters or re-used expression,
 * @ Info: Type associated to variable, number of bits, to be completed progressively.
 * @ instrs instructions of the program (return, display, debug,...), the return instruction is stored separately.
 * @ funs list of functions used by the program, indexed by names.
 * * @ signature, list of parameters, Information of results.
 */

class ProgData1[+T](val f: Fundef[T], val instrs: List[Instr], val funs: iTabSymb[ProgData1[_]], val tSymbVar: TabSymb[InfoType[_]],
                    val paramD: List[String], val paramR: List[String]) {
    override def toString: String =  paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" + instrs.mkString("") +
    string(tSymbVar, "  |  \n ") + "\n"+   listOf(funs).mkString("\n \n  ")

    
 // override def toString: String = string(paramD, " ") + "=>" + string(paramR, " ") + "\n" + string(instrs, " ") + "\n" + tSymbVar.toString + "\n" + string(funs, "\n Macro:") + "\n"
  /**replaces function call by procedure call, introduces new names in tabSymb*/
  def procedurise(): ProgData1[T] = {
    val procedureFun = funs.map { case (k, v) => k -> v.procedurise() }
    val hd: TabSymb[String] = mutable.HashMap.empty; val tl: TabSymb[String] = mutable.HashMap.empty;
    val paramRmut = mutable.LinkedHashSet.empty[String] //we use LinkedHashSet as opposed to Hashset, to preserve the order of insertion because order of parameter is informational
    for (i <- instrs) i.buildhdtl(hd, tl)
    val paraResAffect = Instr.affectizeReturn(tSymbVar, paramRmut, f.body).map(_.procedurise(hd, tl, tSymbVar)).flatten
    return new ProgData1(f, instrs.map(i => i.procedurise(hd, tl, tSymbVar)).flatten ::: paraResAffect, procedureFun, tSymbVar, paramD, paramRmut.toList)
  }
  /**
   * Computes the number of bits of parameters, and affectation, and also internal nodes of all the ASTs.
   *   @nbitP: list of number of bits for each parameter assumed to be ASTLs.
   */
  def nbit(nbitP: List[Int]): ProgData2 = {
    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[ProgData2] = mutable.HashMap.empty
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty //we store the number of bits of parameters in newTabSymbVar:
    //Initalize the nbit of layers
    tSymbVar.map { case (nom, v) => if (v.k.isLayer) newtSymb += nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, v.k.asInstanceOf[LayerField].nb) }

    newtSymb ++= (paramD zip nbitP).map { case (nom, nbi) => (nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi)) } //we assume that parameter are ASTLs
    val newInstrs = instrs.map(_.nbit(this, nbitExp, newtSymb, newFuns))
    return new ProgData2(newInstrs, newFuns, newtSymb, paramD, paramR)
  }

}

class ProgData2(val instrs: List[Instr], val funs: iTabSymb[ProgData2], val tSymbVar: TabSymb[InfoNbit[_]],
                val paramD: List[String], val paramR: List[String] //, val nbitExp: AstField[Int]
                ) {
  /** place anonymous macros first. */

  override def toString: String =(if (isMacro) "Macro:" else "Loop: ")+ paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" + instrs.mkString("") +
    string(tSymbVar, "  |  ") + "\n"+   listOf(funs).mkString("\n \n  ")

  def needStored(s: String): Boolean = tSymbVar(s).k.needStored
  def needStored(i: Instr): Boolean = needStored(i.names.head)

  def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
    for (i <- finstrs) if (!(i.asInstanceOf[Affect[_]].exp.concatElt)) return true
    return false
  }

  /**
   * Creates a subFunction from a set of Affectation supposed to be in topological order (not completely sure, though)
   * DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
   * @Iterable[Instr] a set of affectation forming a connected component.
   */
  def builtFun(finstrs: Iterable[Instr]) = {
    val fparamD = (immutable.HashSet.empty[String] ++ finstrs.map(_.asInstanceOf[Affect[_]].exp.symbols.filter(needStored(_))).toList.flatten).toList
    val fparamR = finstrs.filter(needStored(_)).toList
    val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    for (p <- fparamD) { val old = tSymbVar(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb) }
    for (p <- finstrs) {
      val n = p.names(0); val old = tSymbVar(n);
      newtSymbVar += n -> new InfoNbit(old.t, if (!needStored(p)) Field() else if (fparamD.contains(n)) ParamDR() else ParamR(), old.nb)
    }
    new ProgData2(finstrs.toList, mutable.HashMap.empty, newtSymbVar, fparamD.toList, fparamR.map(_.names(0)))
  }

  /**Compute the Dag of instructions, where a neighbor is an input neigbor, i.e. affectation which set variables which are used, needs to compute definedBy*/
  def readDependancy(instrs: List[Instr], t: TabSymb[InfoNbit[_]]): iTabSymb[Instr] = {
    val definedBy: iTabSymb[Instr] = immutable.HashMap.empty ++ instrs.map(a => (a.names.map(_ -> a))).flatten
    for (a <- instrs) a.neighbor = List.empty[Instr] ++ a.usedVars.filter(v => definedBy.contains(v) && !t(v).k.isLayer).map(definedBy(_));
    definedBy
  }
  /**Obsolete, We now use a simpler way, visting from min element, where min is determined by varKind  */
  def writeDependency(instrs: List[Instr], t: TabSymb[InfoNbit[_]]) = {
    val usedBy: TabSymb[mutable.HashSet[Instr]] = mutable.HashMap.empty
    for (i <- instrs) for (v <- i.usedVars) {
      if (!usedBy.contains(v)) usedBy += v -> mutable.HashSet.empty[Instr]
      usedBy(v) += i
    }
    for (a <- instrs) a.neighbor = a.neighbor ++ a.names.filter(t(_).k.isLayer).map(s => (usedBy(s) - a).toList).flatten
    //if a layer is updated using its previous value it will create a loop on the updating instruction a.neighbor contains a, that's why we have to remove a explicitely
  }

  /**
   * we are carefull about the fact that the new value memorized in a layer is stored, after all the instructions reading the layer are done.
   * if the next value is to be reused, then, we must check that it is affected in another variable (because there will be two users: the memorize instr, and the other.
   */
  def isMacro=funs.isEmpty && tSymbVar.valuesIterator.find(_.k.notInMacro) == None
  def macroise(): ProgData2 = { 
      if (isMacro) return this
      /** one reason why we do not replace param and layer construct by read, is to be able to remove them when they are useless (in non-macro direct affectation)*/
      val (affect2s, callprocs) = instrs.partition(_.isInstanceOf[Affect[_]])
      val affects = affect2s.filter(!_.useless) //selects Affects, au passage, removes those useless instr
      readDependancy(affects, tSymbVar)
      val cc = components(affects, (_: Instr, y: Instr) => !needStored(y))
      val (cc1, cc2) = cc.partition(NeedBuiltFun(_)) //cc2 uses only concat and elt, doesn't need a macro
      val builtFuns = immutable.HashMap.empty ++ cc1.map(setInstr => newFunName() -> builtFun(setInstr))
      val newInstrs = builtFuns.map { case (k, v) ⇒ Instr(k, v) }.toList ::: cc2.toList.flatten ::: callprocs
      val defby = readDependancy(newInstrs, tSymbVar);
      val root = tSymbVar.keys.filter(tSymbVar(_).k.isMin) //.partition(tSymbVar(_).k.isLayer )
      val (sorted, _) = getGreater((root.toList).map(defby(_)));
      // writeDependency(newInstrs, tSymbVar); val is = sort(newInstrs).reverse;
      new ProgData2(sorted.reverse, builtFuns ++ funs.map { case (k, v) ⇒ k → v.macroise() }, tSymbVar, paramD, paramR);
     
  }
  /**The symbol table is not expanded while varialble are, therefore, to find out the type and number of bits of each variables, one must remove the suffixes. */
  def unfoldSpace(m: Machine): ProgData2 = {
     if (isMacro) {
      readDependancy(instrs, tSymbVar)
      val Scc = components(instrs, (x: Instr, y: Instr) => !x.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTLg].locus.isTransfer)
      for(i<-instrs) i.align
      val Tcc = components(instrs, (x: Instr, y: Instr) => x.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTLg].locus.isTransfer)
 
    }
    val muInstr = instrs.map(_.unfoldSpace(m, tSymbVar)) //faut stocquer les muInstr par affectation, et calculer d'abord quelles sont les registres qui sont repliés.

    new ProgData2(
      muInstr.flatten,
      funs.map { case (k, v) ⇒ k → v.unfoldSpace(m) }, tSymbVar, paramD, paramR)
  }
}
    //  a.exp.isInstanceOf[Layer[_,_]] 