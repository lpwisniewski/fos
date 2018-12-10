package fos

import org.scalatest.FunSuite
import fos.Infer.{Constraint, TypeError}

class InferTest extends FunSuite {
  def parse(s: String): Term = Parser.phrase(Parser.Term)(new Parser.lexical.Scanner(s)) match {
    case Parser.Success(tree, _) => tree
    case _ => fail(s"Impossible to parse $s")
  }

  def parseType(s: String): Type = Parser.phrase(Parser.Type)(new Parser.lexical.Scanner(s)) match {
    case Parser.Success(tree, _) => tree.tpe
    case _ => fail(s"Impossible to parse $s")
  }

  def testTypeAndConstraints(expr: String, t: Type, cstr: List[(Type, Type)]) = {
    test(s"""testing typing of ${expr}, expected type = ${t}, expected constraints ${cstr}""") {
      val (tpe, c) = Infer.collect(Nil, parse(expr))
      assert(tpe == t)
      assert(cstr == c)
    }
  }


  val res: (Type, List[(Type, Type)]) = Infer.collect(Nil, Abs("x", BoolTypeTree(), Var("x")))

  testTypeAndConstraints("\\x: Bool. x", parseType("Bool -> Bool"), Nil)
  testTypeAndConstraints("pred 0", parseType("Nat"), List((NatType, NatType)))
  testTypeAndConstraints("pred 2", parseType("Nat"), List((NatType, NatType), (NatType, NatType), (NatType, NatType)))
  testTypeAndConstraints("iszero 0", parseType("Bool"), List((NatType, NatType)))
  testTypeAndConstraints("if iszero 0 then 0 else true", parseType("Nat"), List((BoolType, BoolType), (NatType, BoolType), (NatType, NatType)))
  testTypeAndConstraints("\\x. x", FunType(TypeVar("T1"), TypeVar("T1")), List())
  testTypeAndConstraints("\\x. if x then 0 else 0", FunType(TypeVar("T2"), NatType), List((TypeVar("T2"), BoolType), (NatType, NatType)))

  def testTyping(s: String, expected: String) = {
    test(s"""testing that after applying substitution from unify on ${s} it equals ${expected}""") {
      val (tpe, c) = Infer.collect(Nil, parse(s))
      val sub = Infer.unify(c)
      assert(sub(tpe).toString() == expected)
    }
  }

  def failTyping(s: String) = {
    test(s"""testing that after applying substitution from unify on ${s} it fails""") {
      val (tpe, c) = Infer.collect(Nil, parse(s))
      assertThrows[TypeError](Infer.unify(c))
    }
  }

  testTyping("\\x. if x then 0 else 0", "(Bool -> Nat)")
  
  testTyping("(\\x. if iszero x then succ x else pred x) (succ 10)", "Nat")
  
  testTyping("(\\x. if iszero x then succ x else pred x) (if iszero succ 10 then 1 else 0)", "Nat")

  testTyping("let func = (\\x. x) in func 0", "Nat")

  testTyping("let func = (\\x. x) in if func true then func 0 else func 0", "Nat")

  testTyping("(\\x. \\a. \\b. succ if iszero pred x then succ a else pred b)", "(Nat -> (Nat -> (Nat -> Nat)))")

   testTyping(
   s"""
     let plus3 = \\x. succ (succ (succ x)) in
     let double = \\f. \\y. f (f y) in
     double plus3 0 
   """, "Nat")
  
  failTyping(s"""
     let plus3 = \\x. succ (succ (succ x)) in
     let double = \\f. \\y. f (f y) in
     double plus3 false
   """)
   
   failTyping(s"""
     let plus3 = \\x. succ (succ (succ x)) in
     let double = \\f. \\y. f (f y) in
     double (if iszero double plus3 succ 0 
     then succ 0
     else double double)
   """)
   
  failTyping("(\\f.\\x. let g = f in g(0)) (\\x.if x then false else true) true")
  failTyping("(\\f.\\x. let g = f in if x then g(false) else x) (\\x.if x then succ x else pred x) true")
  failTyping("\\b. if b then 1 else true")

  failTyping("(\\x. x x)")

  testTyping("let double = \\f.\\x. f(f(x)) in if (double (\\x. if x then false else true) false) then double (\\x. x) 0 else 0", "Nat")

  testTyping("let f: Bool -> Bool = \\x. x in f true", "Bool")
  
  testTyping(s"""
    (\\x. let double = \\f. \\y. f (f y) in ((double double) x)) (\\y. succ y) 
    """, "(Nat -> Nat)")  
    
    failTyping(s"""
    (\\x. let double = \\f. \\y. f (f y) in ((double double) x)) (\\y. succ y) false
    """)  
     

  def testTyping(constraints: List[Constraint], inputToExpected: Map[Type, Type]) {
    test(s"""testing substitution appied on ${constraints} returns ${inputToExpected}""") {
      val sub: Type => Type = Infer.unify(constraints)
      inputToExpected.map{
        case (input, expected) =>
          val subOutput = sub(input)
          assert(subOutput == expected)
      }
    }
  }

  val constraints: List[Constraint] = List(
      (FunType(TypeVar("T2"), TypeVar("T2")),
          FunType(NatType, TypeVar("T4")))
  )

  testTyping(constraints, Map[Type, Type](TypeVar("T2") -> NatType, TypeVar("T4") -> NatType))

 val constraints2 = List[Constraint](
      (TypeVar("T4") ,BoolType),
      (TypeVar("T7"),TypeVar("T10")),
      ((FunType(TypeVar("T5"), TypeVar("T5"))), FunType(NatType, TypeVar("T7"))),
      (FunType(TypeVar("T8"), TypeVar("T8")), FunType(NatType, TypeVar("T10"))),
      ((FunType(TypeVar("T2"), TypeVar("T2"))), FunType(BoolType, TypeVar("T4"))))

val expectedResult =
  Map[Type, Type](
    TypeVar("T5") -> NatType,
    TypeVar("T7") -> NatType,
    TypeVar("T10") -> NatType,
    TypeVar("T8") -> NatType,
    TypeVar("T4") -> BoolType,
    TypeVar("T2") -> BoolType
  )
 testTyping(constraints2, expectedResult)
}
