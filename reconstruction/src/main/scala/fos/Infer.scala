package fos
import scala.collection.immutable

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
    case Zero() => (NatType, Nil)
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
      val tpe: Option[(String, TypeScheme)] = env.find { case (name, tpe) => name == str }
      tpe match {
        case Some((str, scheme)) =>
          val substs: List[(TypeVar, Type)] = scheme.params.map(p => (p, typeGen.nextTypeVar()))
          val substF: Type => Type = listSubtToSubtFunc(substs)
          (substF(scheme.tp), Nil)
        case None => throw TypeError(s"Term $str is not bounded to a type.")
      }
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
    case Let(str, EmptyTypeTree(), v, t) =>
      val (s: Type, c) = collect(env, v)
      val subst = unify(c)
      val tpeT = subst(s)
      val newEnv: Env = env.map{case (str, scheme) => (str, scheme.copy(tp = subst(scheme.tp)))} :+ (str, TypeScheme(generalize(tpeT, env), tpeT))
      collect(newEnv, t)
    case Let(str, tp, v, t) => collect(env, App(Abs(str, tp, t), v))
  }

  def listSubtToSubtFunc(list: List[(TypeVar, Type)]): Type => Type = {
    def recSubt(tpe: Type): Type = tpe match{
      case tpe: TypeVar => list.find{case (tv, nt) => tv == tpe}.map(_._2).getOrElse(tpe)
      case FunType(t1, t2) => FunType(recSubt(t1), recSubt(t2))
    }
    recSubt
  }

  def generalize(t: Type, env: Env): List[TypeVar] = t match {
    case tv: TypeVar => if(env.flatMap(_._2.params).contains(t)) Nil else tv :: Nil
    case FunType(t1, t2) => generalize(t1, env) ++ generalize(t2, env)
  }

  def unify(c: List[Constraint]): Type => Type = ???
}
