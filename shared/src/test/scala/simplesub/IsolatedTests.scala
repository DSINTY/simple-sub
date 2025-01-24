package simplesub

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class IsolatedTests extends TypingTestHelpers {
  
  // This test class is for isolating single tests and running them alone
  // with sbt command `~testOnly simplesub.IsolatedTests`
  
  test("isolated") {
    
    // put your test here
    
    // doTest("fun f -> fun x -> f (f x)")
    doTest("42", "int")
    doTest("fun x -> 42", "⊤ -> int")
    doTest("fun x -> x", "'a -> 'a")
    doTest("fun x -> x 42", "(int -> 'a) -> 'a")
    doTest("(fun x -> x) 42", "int")
    doTest("fun f -> fun x -> f (f x)  // twice", "('a ∨ 'b -> 'a) -> 'b -> 'a")
    doTest("let twice = fun f -> fun x -> f (f x) in twice", "('a ∨ 'b -> 'a) -> 'b -> 'a")
    
  }
  
}
