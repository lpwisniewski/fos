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
      case _ => tpe 
    }
    recSubt
  }

  def generalize(t: Type, env: Env): List[TypeVar] = t match {
    case tv: TypeVar => if(env.flatMap(_._2.params).contains(t)) Nil else tv :: Nil 
    case FunType(t1, t2) => generalize(t1, env) ++ generalize(t2, env)  
  }


  def sAppearsInT(sName: String, t: Type): Boolean = t match {
    case TypeVar(tName) => tName == sName
    case FunType(t1, t2) => sAppearsInT(sName, t1) || sAppearsInT(sName, t2)
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

  def unifyHelper(s: Type, t: Type): Option[Type => Type] = s match {
    case TypeVar(sName) if !sAppearsInT(sName, t) => Some((input: Type) => substituteType(sName, t, input))
    case TypeVar(_) => throw new TypeError("Unification error on " + (s, t))
    case _ => None 
  }  
  
  def unify(c: List[Constraint]): Type => Type = {

    def recursivePart(c: List[Constraint]): List[Type => Type] = {
      c match {
        case Nil => Nil
        case (s, t) :: rest if s == t => recursivePart(rest)
        case (s, t) :: rest =>
          val substOpt =
            unifyHelper(s, t)
              .orElse(unifyHelper(t, s)) 
            
            //from "A tricky detail here lies in the necessity to apply S → T to the remaining constraints in the constraint set."
            val updatedRest: List[Constraint] = 
              substOpt.map { subst => 
                rest.map { case (t1, t2) => (subst(t1), subst(t2)) }
              }.getOrElse(rest)
              
               
            val subst: Type => Type = substOpt
            .getOrElse((s, t) match { 
              case (FunType(s1, s2), FunType(t1, t2)) =>
                unify((s1, t1) :: (s2, t2) :: updatedRest)   
              case _ => throw new TypeError("impossible to find substitution that satisfies the constraint set")
            })

          subst :: recursivePart(updatedRest)
      }
    }

    val substitutions: List[Type => Type] = recursivePart(c)

    substitutions.reduceLeft((s1, s2) => s1.andThen(s2))
  }


}
