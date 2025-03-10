package simplesub

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class IsolatedTests extends TypingTestHelpers {
  
  // This test class is for isolating single tests and running them alone
  // with sbt command `~testOnly simplesub.IsolatedTests`
  
  test("isolated") {
    
    // put your test here
    
     doTest("let twice = fun f -> fun x -> f (f x) in twice")
    // doTest("fun f -> fun x -> f (f x)  // twice")
      
    
  }
  
}
