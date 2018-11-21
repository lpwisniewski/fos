package fos

object Infer {

  case class TypeScheme(params: List[TypeVar], tp: Type)

  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  object FreshTypes {
    def apply(init: Int = 0) = new FreshTypes(init)
  }

  class FreshTypes(private var init: Int) {

    private def getIncrement(): Int = {
      init = init + 1
      init
    }

    def nextTypeVar(): Type = TypeVar("T" + getIncrement())
  }

  val typeGen: FreshTypes = FreshTypes()

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    case True() => (BoolType, Nil)
    case False() => (BoolType, Nil)
    case Pred(t) =>
      val (tpe, constr) = collect(env, t)
      (NatType, (tpe, NatType) :: constr)
    case Succ(t) =>
      val (tpe, constr) = collect(env, t)
      (NatType, (tpe, NatType) :: constr)
    case IsZero(t) =>
      val (tpe, constr) = collect(env, t)
      (BoolType, (tpe, NatType) :: constr)
    case If(cond, t1, t2) =>
      val (tpecond, constrcond) = collect(env, cond)
      val (tpe1, constr1) = collect(env, t1)
      val (tpe2, constr2) = collect(env, t2)
      (tpe1, (tpecond, BoolType) :: (tpe1, tpe2) :: constr1 ++ constr2 ++ constrcond)
    case Var(str) =>
      (env.find { case (name, tpe) => name == str }
        .map(_._2.tp) // TODO Remove get on TP later
        .getOrElse(throw TypeError("No type found for " + str)),
        Nil)
    case Abs(v, EmptyTypeTree(), t) =>
      val freshTpe = typeGen.nextTypeVar()
      val (tpe, constr) = collect((v, TypeScheme(Nil, freshTpe)) :: env, t)
      (FunType(freshTpe, tpe), constr)
    case Abs(v, tptree, t) =>
      val (tpe, constr) = collect((v, TypeScheme(Nil, tptree.tpe)) :: env, t)
      (FunType(tptree.tpe, tpe), constr)
    case App(t1, t2) =>
      val (tpe1, constr1) = collect(env, t1)
      val (tpe2, constr2) = collect(env, t2)
      val freshTpe = typeGen.nextTypeVar()
      (freshTpe, (tpe1, FunType(tpe2, freshTpe)) :: constr1 ++ constr2)
  }

  def unify(c: List[Constraint]): Type => Type = ???
}
