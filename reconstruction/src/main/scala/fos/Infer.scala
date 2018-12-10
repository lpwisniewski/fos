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
    case Let(str, tp, v, t) =>
      val (s: Type, c) = collect(env, v)
      val subst = unify(c)
      val tpeT = subst(s)
      val newEnv: Env = env.map{case (str, scheme) => (str, scheme.copy(tp = subst(scheme.tp)))} :+ (str, TypeScheme(generalize(tpeT, env), tpeT))
      val (tpe, constr) = collect(newEnv, t)
      tp match {
        case EmptyTypeTree() => (tpe, c ++ constr)
        case _ => (tpe, c ++ constr :+ (s, tp.tpe))
      }
  }

  def listSubtToSubtFunc(list: List[(TypeVar, Type)]): Type => Type = {
    def recSubt(tpe: Type): Type = tpe match {
      case tpe: TypeVar => list.find{case (tv, nt) => tv == tpe}.map(_._2).getOrElse(tpe)
      case FunType(t1, t2) => FunType(recSubt(t1), recSubt(t2))
      case _ => tpe
    }
    recSubt
  }

  def generalize(t: Type, env: Env): List[TypeVar] = t match {
    case tv: TypeVar =>
      if((env.flatMap(t => getTypeVars(t._2.tp)) ++ env.flatMap(_._2.params)).contains(t)) Nil
      else tv :: Nil
    case FunType(t1, t2) => generalize(t1, env) ++ generalize(t2, env)
    case _ => Nil
  }

  def getTypeVars(t: Type): List[TypeVar] = t match {
    case t: TypeVar => t :: Nil
    case FunType(t1, t2) => getTypeVars(t1) ++ getTypeVars(t2)
    case _ => Nil
  }


  def firstAppearsInSecond(sName: String, t: Type): Boolean = t match {
    case TypeVar(tName) => tName == sName
    case FunType(t1, t2) => firstAppearsInSecond(sName, t1) || firstAppearsInSecond(sName, t2)
    case NatType => false
    case BoolType => false
  }

  //[toReplace -> replacer]
  def substituteType(nameOfTypeToReplace: String, replacer: Type, currentType: Type): Type = {
    def sub(t: Type) = substituteType(nameOfTypeToReplace, replacer, t)

    currentType match {
      case TypeVar(tName) if tName == nameOfTypeToReplace => replacer
      case FunType(t1, t2) => FunType(sub(t1), sub(t2))
      case _ => currentType
    }
  }
 
 
  def treatGenericCase(typevar: TypeVar, t: Type, cPrime: List[Constraint]): Type => Type = {
    def subst: Type => Type = t1 => substituteType(typevar.name, t, t1)
    val cPrimeSubstituted = cPrime.map {
      case (t1, t2) => (subst(t1), subst(t2))
    } 
    subst.andThen(unify(cPrimeSubstituted))
  }
  
  def unify(c: List[Constraint]): Type => Type = c match {
    case Nil => (x => x)
    case (s, t) :: cPrime if s == t => unify(cPrime)
    case (x @ TypeVar(varName), t) :: cPrime if !firstAppearsInSecond(varName, t) => 
        treatGenericCase(x, t, cPrime)
    case (s, x @ TypeVar(varName)) :: cPrime if !firstAppearsInSecond(varName, s) => 
        treatGenericCase(x, s, cPrime)
    case (FunType(s1, s2), FunType(t1, t2)) :: cPrime =>
      unify((s1, t1) :: (s2, t2) :: cPrime)
    case _ => throw new TypeError("impossible to find substitution that satisfies the constraint set")
      
  }
  


}
