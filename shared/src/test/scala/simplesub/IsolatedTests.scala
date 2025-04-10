package simplesub

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class IsolatedTests extends TypingTestHelpers {
  
  // This test class is for isolating single tests and running them alone
  // with sbt command `~testOnly simplesub.IsolatedTests`
  
  test("isolated") {
    
    // put your test here
    
    doTest("(let x = (fun y -> (y 0)) in (let y = {u = x} in y))")
    
  }
  
}
