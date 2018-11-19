package fos

import org.scalatest.FunSuite
import org.scalatest.compatible.Assertion

class Tests extends FunSuite {
  var i = 0
  def generalizedTestAfterParsing[T](parseMethod: String => SimplyTypedExtended.ParseResult[T])(assertionOnTerm: T => Assertion)(input: String, testTitle: String) {
    test(testTitle + " #" + i) {
      parseMethod(input) match {
        case SimplyTypedExtended.Success(trees, _) =>
          assertionOnTerm(trees)
        case other => fail("impossible to parse this" + other.toString())
      }
    }
    i += 1
  }

  def parseTest(input: String, expectedOutput: Term) {
    generalizedParseTest(SimplyTypedExtended.parse)(input, expectedOutput)
  }

  def parseTest(input: String, expectedOutput: Type) {
    generalizedParseTest(SimplyTypedExtended.parseType)(input, expectedOutput)
  }

  def generalizedParseTest[T](parseMethod: String => SimplyTypedExtended.ParseResult[T])(input: String, expectedType: T) {
    generalizedTestAfterParsing(parseMethod) { parsedType: T =>
      assert(parsedType == expectedType)
    }(input, s"""$input parsed as $expectedType""")
  }

  def parseTestWithExpectedOutputAsString[T](parser: String => SimplyTypedExtended.ParseResult[T], parseTest: (String, T) => Unit)(input: String, expectedOutput: String) {
    val expectedType = parser(expectedOutput) match {
      case SimplyTypedExtended.Success(trees, _) => trees
      case e                             => fail("impossible to parse expected output " + e)
    }
    parseTest(input, expectedType)
  }

  def parseTypeTest = parseTestWithExpectedOutputAsString[Type](SimplyTypedExtended.parseType, parseTest) _

  def parseTermTest = parseTestWithExpectedOutputAsString[Term](SimplyTypedExtended.parse, parseTest) _

  def assertTypeOfFails(input: String) {
    generalizedTestAfterParsing(SimplyTypedExtended.parse) { parsedTerm: Term =>
      assertThrows[SimplyTypedExtended.TypeError] {
        SimplyTypedExtended.typeof(Nil, parsedTerm)
      }
    }(input, s"""determining type of $input should throw a TypeError""")
  }

  // (\x:Nat->Bool. (\y:Nat.(x y)))
  val test1Abs1 = Abs("x", TypeFun(TypeNat, TypeBool), Abs("y", TypeNat, App(Var("x"), Var("y"))))
  val test1Abs2 = Abs("x", TypeNat, IsZero(Var("x")))
  parseTest(
    "(\\x:Nat-> Bool. (\\y:Nat.(x y))) (\\x:Nat.(iszero x)) 0",
    App(App(test1Abs1, test1Abs2), Zero()))

  parseTest(
    "(\\x:Nat.x) true",
    App(Abs("x", TypeNat, Var("x")), True()))

  parseTest(
    "\\x:Nat->Nat->Bool->Nat. x", Abs("x", TypeFun(TypeNat, TypeFun(TypeNat, TypeFun(TypeBool, TypeNat))), Var("x")))

  parseTest(
    "iszero (\\x: Nat. x) 3", IsZero(App(Abs("x", TypeNat, Var("x")), Succ(Succ(Succ(Zero()))))))

  def generalizedPathTest[U](transformOnParsedInput: List[Term] => U)(input: String, expected: U) { 
    test(s"""testing path of: ${input}""") {
      SimplyTypedExtended.parse(input) match {
        case SimplyTypedExtended.Success(trees, _) =>
          val transformed = transformOnParsedInput(SimplyTypedExtended.getPathStream(trees).toList)
          assert(transformed == expected)
        case e => fail("well the parsing did not even work" + e)
      }
    }
  }
  
  def pathTest(input: String, expectedPathAsStrings: List[String]) {
      val expectedPath: List[Term] = (input :: expectedPathAsStrings).map {
        SimplyTypedExtended.parse(_) match {
          case SimplyTypedExtended.Success(terms, _) => terms
          case e                             => sys.error("Fix this test expected path: " + e)
        }
      }
      
      generalizedPathTest(ls => ls)(input, expectedPath) 
  }
  
  def outputTest(input: String, expectedOutput: String) {
    SimplyTypedExtended.parse(expectedOutput) match {
      case SimplyTypedExtended.Success(expectedTrees, _) => generalizedPathTest(ls => ls.last)(input, expectedTrees)
      case e => sys.error("fix this test" + e)
    }
    
  }

  val input1 = "(let x: Bool -> Nat = (\\x: Bool. if x then 1 else 2) in x) true"
  //try to duplicate x above for another test Bool -> Nat = x x x ...
  val expectedPath = "(\\x: Bool. if x then 1 else 2 ) true" :: "if true then 1 else 2" :: "1" :: Nil
  pathTest(input1, expectedPath)

  val isZero = s"""\\x: Nat. ${bodyIsZero("x")}"""

  def bodyIsZero(x: String) = s"""if iszero ${x} then 1 else 0"""

  val parsedIsZero = Abs("x", TypeNat, If(IsZero(Var("x")), Succ(Zero()), Zero()))
  parseTest(s"""(${isZero}) ((${isZero}) 0)""", App(parsedIsZero, App(parsedIsZero, Zero())))

  assertTypeOfFails(s"""${isZero} 0""")

  val leftMostInnerBody = (0 until 4).foldRight[Term](Var("x")) { case (_, z) => App(Var("f"), z) }
  val leftMostAbs = Abs("f", TypeFun(TypeNat, TypeNat), Abs("x", TypeNat, leftMostInnerBody))
  parseTest(
    s"""(\\f: Nat -> Nat. \\x: Nat. (f (f (f (f x))))) (${isZero}) 1""",
    App(App(leftMostAbs, parsedIsZero), Succ(Zero())))

  val input2 = s"""((\\f: Nat -> Nat. \\y: Nat. f (f y)) ${isZero}) 0"""
  val expected2 =
    s"""let y: Nat = 0 in (${isZero}) (  (${isZero})  y)""" ::
      s"""(${isZero}) ((${isZero}) 0)""" ::
      s"""(${isZero}) ${bodyIsZero("0")}""" ::
      s"""(${isZero}) if true then 1 else 0""" ::
      s"""(${isZero}) 1""" ::
      bodyIsZero("1") ::
      "if false then 1 else 0" ::
      "0" :: Nil

  pathTest(input2, expected2)

  parseTest("Nat * Nat", TypePair(TypeNat, TypeNat))
  parseTypeTest("Nat * Nat -> Bool", "(Nat * Nat) -> Bool")

  val expectedType = TypeFun(TypePair(TypeNat, TypePair(TypeNat, TypeBool)), TypeFun(TypeNat, TypeBool))
  val type1 = "Nat * Nat * Bool -> Nat -> Bool"
  val type2 = "Nat * (Nat * Bool) -> (Nat -> Bool)"
  parseTest(type1, expectedType)
  parseTest(type2, expectedType)
  parseTypeTest(type1, type2)

  parseTest(s"""(\\f:${type1}. f)""", Abs("f", expectedType, Var("f")))

  val baseTypes = List("Nat", "Bool")
  for {
    t1 <- baseTypes
    t2 <- baseTypes
    t3 <- baseTypes
    t4 <- baseTypes
  } parseTypeTest(s"""$t1 -> $t2 * $t3 -> $t4""", s"""$t1 -> (($t2 * $t3) -> $t4)""")

  parseTest("\\x:Nat.\\y:Nat.{x, y}", Abs("x", TypeNat, Abs("y", TypeNat, TermPair(Var("x"), Var("y")))))
  val fType = TypeFun(TypePair(TypeNat, TypeNat), TypeNat)
  val pType = TypePair(TypeNat, TypeNat)
  val bodyPair = TermPair(First(Var("p")), Var("y"))
  val expectedParsed = Abs("f", fType, Abs("p", pType, Abs("y", TypeNat, App(Var("f"), bodyPair))))
  parseTest("\\f:Nat*Nat->Nat. \\p:Nat*Nat.\\y:Nat. f {fst p, y}", expectedParsed)

  parseTermTest("snd x y", "snd (x y)")

  pathTest(
    "(\\x:Nat.snd {10, x}) 1",
    "snd {10, 1}" :: "1" :: Nil)

  pathTest(
    "(\\f:Nat*Nat->Nat. \\p:Nat*Nat.\\y:Nat. f {fst p, y}) (\\p: Nat*Nat. succ fst p) {1, 3} 0",

    "(\\p:Nat*Nat.\\y:Nat. (\\p: Nat*Nat. succ fst p) {fst p, y}) {1, 3} 0" ::
      "(\\y:Nat. (\\p: Nat*Nat. succ fst p) {fst {1, 3}, y})  0" ::
      "(\\p: Nat*Nat. succ fst p) {fst {1, 3}, 0}" ::
      "(\\p: Nat*Nat. succ fst p) {1, 0}" ::
      "succ fst {1, 0}" ::
      "succ 1" ::
      Nil)

  assertTypeOfFails("(\\x:Nat.x) true")

  assertTypeOfFails("(\\f1:Nat*Nat->Bool.f1)(\\p:Nat*Nat. iszero fst p) true")

  def parseTest1(f: String) {
    parseTermTest(s"""${f} a b c d e""", s"""${f} (((((a b) c) d) e))""")
  }
  ("snd" :: "fst" :: Nil).foreach(parseTest1)

  val types = List("Nat", "Bool", "Nat->Nat", "Nat->Nat->Bool->Nat", "Bool* Nat -> Bool -> Nat*Nat")
  types.foreach { curType: String =>
    parseTermTest(s"""let x: ${curType} = t1 in t2""", s"""(\\x: ${curType}. t2) t1""")
  }
  
  parseTypeTest("Bool->Nat+Nat*Nat", "Bool->(Nat+(Nat*Nat))")
  for {
    t1 <- baseTypes
    t2 <- baseTypes
    t3 <- baseTypes
    t4 <- baseTypes
    t5 <- baseTypes
  } parseTypeTest(s"""${t1} * ${t2} -> ${t3} + ${t4} * ${t5}""", s"""(${t1} * ${t2}) -> (${t3} + (${t4} * ${t5}))""") 

  parseTypeTest("Nat -> Bool * Nat * Bool -> Bool", "Nat -> ((Bool * (Nat * Bool)) -> Bool)")
  
  val T1 = "Nat -> Nat"
  val t1  = s"""\\z: Nat. if iszero z then 0 else fct(pred(z))""" //recursively apply pred until the z is zero..
  
  outputTest(s"""let x: $T1 -> $T1 = fix (\\fct: $T1. ${t1}) in x 4""", 
      "0")
  
  outputTest(
      s"""let f1: Nat -> Nat = (\\z: Nat. succ(z)) in 
          let f2: Nat -> Nat = (\\z: Nat. succ(succ(z))) in
                             f1 (f2 4)""", "7")
                             
                             
  outputTest(
      s"""
        let x: Bool + Nat = inl(5) as Nat in
          case x of 
            inl x1 => (\\z: Nat. succ(z)) x1 |
            inr x2 => 
              if iszero x2  then 1 else 2
          
        """, "6")
  
  parseTest(s"""case x of 
            inl x1 => (\\z: Nat. succ(z)) x1 |
            inr x2 => if iszero x2  then 1 else 2
          """, 
          Case(Var("x"), 
                "x1", App(Abs("z", TypeNat, Succ(Var("z"))), Var("x1")),
                "x2", If(IsZero(Var("x2")), Succ(Zero()), Succ(Succ(Zero())))))
   
}