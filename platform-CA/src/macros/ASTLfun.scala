package macros
//import compiler._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTB._
import compiler.ASTLt
import compiler.repr
import compiler.V
import compiler.Locus
import compiler.Ring
import compiler.SI
import compiler.UI
import compiler.B

/** Contains the code of locus function used as a layer of  building blocks of small bits of spatial operators, compiled with optimal perf. */
object ASTLfun {

  // @TODO we should not import compiler._, and find a way to use parameter with IntV rather than [V,SI]
  def p[L <: Locus, R <: Ring](name: String)(implicit n: repr[L], m: repr[R]) = new Param[Tuple2[L, R]](name) with ASTLt[L, R]
  /**From an IntV, computes the gradient sign, and the delta to be added to make it a distance  */

  val slopeDeltaDef = {
    //val x:IntV= p[V, SI]("dis")
    val x = p[V, SI]("dis")
    
    val tepred = transfer(e(x))
    val g=subESI(tepred)
    val grad:IntvE = sendv(List(g,-g))
  //  val grad: IntvE = tepred - sym(tepred) //TODO should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
    val slope: BoolvE = gt(grad);
    val delta: IntV = minR(transfer(sign(grad + -2)))
    val temp: BoolfV = xorR2(transfer(slope))
    val vortex: BoolF = andR(transfer(temp)); slope.bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
    grad.setName("grad"); tepred.setName("tepred"); slope.setName("slope"); delta.setName("delta"); vortex.setName("vortex")

    Fundef1("boolgrad", Coons(slope, delta), x)
  }

  /**Calls boolgrad, and separate the two results.  */
  def slopeDelta(d: IntV): (BoolvE, IntV) = { val r = Call1(slopeDeltaDef, d); (new Heead(r) with BoolvE, new Taail(r) with IntV) }

}