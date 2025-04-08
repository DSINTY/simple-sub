package simplesub

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class IsolatedTests extends TypingTestHelpers {
  
  // This test class is for isolating single tests and running them alone
  // with sbt command `~testOnly simplesub.IsolatedTests`

  test("simple") {
     doTest("fun i -> if ((i i) true) then true else true")
  }
  
  // test("twice") {
    
  //   // put your test here
    
  //    doTest("fun f -> fun x -> f (f x)  // twice")
  //   // doTest("fun f -> fun x -> f (f x)  // twice")
      
    
  // }


  // test("let twice") {
  //    doTest("let f = fun x -> x in {a = f 0; b = f true}")
  // }
    
  //   // put your test here
    
  //   //  doTest("fun f -> fun x -> f (f x)  // twice")
  //    doTest("let twice = fun f -> fun x -> f (f x) in twice")
  //   // doTest("fun f -> fun x -> f (f x)  // twice")
      
    
  // }

  // test("mlsub"){
  //   doTest("fun k -> let test = k (fun x -> let tmp = add x 1 in if true then x else 2) in test",
  //     "((int -> int) -> 'a) -> 'a")
  //   // MLsub: ((((int & a) -> (int | a)) -> b) -> b)
  // }

  // test("records"){
  //   doTest("fun k -> let test = (fun id -> {tmp = k id; res = id}.res) (fun x -> x) in {u=test 0; v=test true}")
  //     // "(('a -> 'a UNION bool UNION int) -> TOP) -> {u: 'a UNION int, v: 'a UNION bool}")
  // }

 
  
  
}
