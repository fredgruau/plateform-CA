package compiler
/**used to compute a string encoding the locus, at compile time. */
/*class repr[L <: Locus](val name: String) 
object repr {
  implicit val nomV = new repr[V]("V");
  implicit val nomE = new repr[E]("E"); implicit val nomF = new repr[F]("F");
//  implicit val nomTVE = new repr[T[V, E]]("vE"); implicit val nomTVF = new repr[T[V, F]]("vF");
 // implicit val nomTEV = new repr[T[E, V]]("eV"); implicit val nomTEF = new repr[T[E, F]]("eF");
  //implicit val nomTFV = new repr[T[F, V]]("fV"); implicit val nomTFE = new repr[T[F, E]]("fE");
  implicit def nomT[L1<:S,L2<:S](implicit m1 : repr[L1], m2 : repr[L2]) = //compiler call it because it cannot find implicit variable
    new repr[T[L1,L2]]( m1.name.toLowerCase + m2.name);                 //with type T[X][Y] so it look for implicit fonction returning some.
}*/ 
class repr[L](val name: L)
object repr {
  implicit val nomV = new repr[V](V()); implicit val nomE = new repr[E](E()); implicit val nomF = new repr[F](F());
  implicit def nomT[L1 <: S, L2 <: S](implicit m1: repr[L1], m2: repr[L2]) = new repr[T[L1, L2]](T(m1.name, m2.name));
  implicit def nomLR[L <: Locus, R <: Ring](implicit m1: repr[L], m2: repr[R]) = new repr[Tuple2[L, R]]((m1.name, m2.name))
  implicit val nomB = new repr[B](B());
  implicit val nomR = new repr[Ring](new Ring());
  implicit val nomI = new repr[I](new I());
  implicit val nomUI = new repr[UI](UI()); implicit val nomSI = new repr[SI](SI());
}

class CentralSym[S1, S2, S3]
object CentralSym {
  implicit val vEv = new CentralSym[V, E, V]; implicit val fEf = new CentralSym[F, E, F];
  implicit val vFe = new CentralSym[V, F, E]; implicit val eFv = new CentralSym[E, F, V];
}
class Red2[S1, S2, S3]
object Red2 {
  implicit val VEF = new Red2[V, E, F];
}

