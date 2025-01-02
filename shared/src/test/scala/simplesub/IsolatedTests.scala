package simplesub

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class IsolatedTests extends TypingTestHelpers {
  
  // This test class is for isolating single tests and running them alone
  // with sbt command `~testOnly simplesub.IsolatedTests`
  
  test("isolated") {
    
    // put your test here
    
    //  doTest("{ f = 42 }", "{f: int}")
    //   doTest("{ f = 42 }.f", "int")
    // doTest("(fun x -> x.f) { f = 42 }")
    doTest("fun x -> x 42")
    
    
  }
  test{"isolated2"}{
    // doTest("fun x -> x 42")
    // doTest("fun x -> x 42", "(int -> 'a) -> 'a")
    // doTest("fun x -> not x")
    // doTest("fun f -> fun x -> f (f x)  // twice")
    // doTest("fun x -> fun y -> fun z -> if x then y else z")
    // error("succ true",
    //   "cannot constrain bool <: int")
    // error("fun x -> succ (not x)",
    //   "cannot constrain bool <: int")
    // error("fun x -> succ (not x)",
    //   "cannot constrain bool <: int")
    //   error("succ true",
    //   "cannot constrain bool <: int")
    // error("fun x -> succ (not x)",
    //   "cannot constrain bool <: int")
    // error("(fun f -> fun x -> not (f x.u)) false",
    //   "cannot constrain bool <: 'a -> 'b")
    
    
  }
  
}
