package fos

import org.scalatest.FunSuite

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
    val (tpe, c) = Infer.collect(Nil, parse(expr))
    assert(tpe == t)
    assert(cstr == c)
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
    val (tpe, c) = Infer.collect(Nil, parse(s))
    val sub = Infer.unify(c)
    assert(sub(tpe).toString() == expected)
  }
  
  testTyping("\\x. if x then 0 else 0", "(Bool -> Nat)")
  
  testTyping("(\\x. if iszero x then succ x else pred x) (succ 10)", "Nat")
  
  testTyping("(\\x. if iszero x then succ x else pred x) (if iszero succ 10 then 1 else 0)", "Nat")
}
