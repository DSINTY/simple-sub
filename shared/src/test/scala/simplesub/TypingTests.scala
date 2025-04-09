package simplesub

import fastparse._
import Parser.expr
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class TypingTests extends TypingTestHelpers {
  
  // In the tests, leave the expected string empty so the inferred type is printed in the console
  // and you can copy and paste it after making sure it is correct.
  
  test("basic") {
    doTest("42", "int")
    doTest("fun x -> 42", "TOP -> int")
    doTest("fun x -> x", "'a -> 'a")
    doTest("fun x -> x 42", "(int -> 'a) -> 'a")
    doTest("(fun x -> x) 42", "int")
    // doTest("fun f -> fun x -> f (f x)  // twice", "('a UNION 'b -> 'a) -> 'b -> 'a")
    // doTest("let twice = fun f -> fun x -> f (f x) in twice", "('a UNION 'b -> 'a) -> 'b -> 'a")
    doTest("fun f -> fun x -> f (f x)  // twice", "('a UNION 'b -> 'b) -> 'a -> 'b")
    // doTest("let twice = fun f -> fun x -> f (f x) in twice", "('a UNION 'b -> 'b) -> 'a -> 'b")
  }
  
  test("booleans") {
    doTest("true", "bool")
    doTest("not true", "bool")
    doTest("fun x -> not x", "bool -> bool")
    doTest("(fun x -> not x) true", "bool")
    doTest("fun x -> fun y -> fun z -> if x then y else z",
      "bool -> 'a -> 'a -> 'a")
    doTest("fun x -> fun y -> if x then y else x",
      "'a INTER bool -> 'a -> 'a")
    
    error("succ true",
      "cannot constrain bool <: int")
    error("fun x -> succ (not x)",
      "cannot constrain bool <: int")
    error("(fun x -> not x.f) { f = 123 }",
      "cannot constrain int <: bool")
    // error("(fun f -> fun x -> not (f x.u)) false",
    //   "cannot constrain bool <: 'a -> 'b")
    error("(fun f -> fun x -> not (f x.u)) false",
      "cannot constrain 'a -> 'b <: bool")
  }
  
  test("records") {
    doTest("fun x -> x.f", "{f: 'a} -> 'a")
    doTest("{}", "{}") // note: MLsub returns "TOP" (equivalent)
    doTest("{ f = 42 }", "{f: int}")
    doTest("{ f = 42 }.f", "int")
    doTest("(fun x -> x.f) { f = 42 }", "int")
    doTest("fun f -> { x = f 42 }.x", "(int -> 'a) -> 'a")
    doTest("fun f -> { x = f 42; y = 123 }.y", "(int -> TOP) -> int")
    doTest("if true then { a = 1; b = true } else { b = false; c = 42 }", "{b: bool}")
    
    error("{ a = 123; b = true }.c",
      "missing field: c in {a: int, b: bool}")
    error("fun x -> { a = x }.b",
      "missing field: b in {a: 'a}")
  }
  
  test("self-app") {
    doTest("fun x -> x x", "'a INTER ('a -> 'b) -> 'b")
    
    doTest("fun x -> x x x", "'a INTER ('a -> 'a -> 'b) -> 'b")
    doTest("fun x -> fun y -> x y x", "'a INTER ('b -> 'a -> 'c) -> 'b -> 'c")
    doTest("fun x -> fun y -> x x y", "'a INTER ('a -> 'b -> 'c) -> 'b -> 'c")
    doTest("(fun x -> x x) (fun x -> x x)", "BOT")
    
    doTest("fun x -> {l = x x; r = x }",
      "'a INTER ('a -> 'b) -> {l: 'b, r: 'a}")
    
    // From https://github.com/stedolan/mlsub
    // Y combinator:
    doTest("(fun f -> (fun x -> f (x x)) (fun x -> f (x x)))",
      "('a -> 'a) -> 'a")
    // Z combinator:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))",
      "(('a -> 'b) -> 'c INTER ('a -> 'b)) -> 'c")
    // Function that takes arbitrarily many arguments:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v))) (fun f -> fun x -> f)",
      "TOP -> (TOP -> 'a) as 'a")
    
    doTest("let rec trutru = fun g -> trutru (g true) in trutru",
      "(bool -> 'a) as 'a -> BOT")
    doTest("fun i -> if ((i i) true) then true else true",
      "'a INTER ('a -> bool -> bool) -> bool")
    // ^ for: λi. if ((i i) true) then true else true,
    //    Dolan's thesis says MLsub infers: (α → ((bool → bool) ⊓ α)) → bool
    //    which does seem equivalent, despite being quite syntactically different
  }
  
  test("let-poly") {
    doTest("let f = fun x -> x in {a = f 0; b = f true}", "{a: int, b: bool}")
    doTest("fun y -> let f = fun x -> x in {a = f y; b = f true}",
      "'a -> {a: 'a, b: bool}")
    doTest("fun y -> let f = fun x -> y x in {a = f 0; b = f true}",
      "(bool UNION int -> 'a) -> {a: 'a, b: 'a}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> true)}",
      "'a -> {a: 'a, b: bool}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> succ z)}",
      "'a INTER int -> {a: 'a, b: int}")
    
    // error("(fun k -> k (fun x -> let tmp = add x 1 in x)) (fun f -> f true)",
    //   "cannot constrain bool <: int")
     error("(fun k -> k (fun x -> let tmp = add x 1 in x)) (fun f -> f true)",
      "cannot constrain int <: bool")
    // Let-binding a part in the above test:
    // error("(fun k -> let test = k (fun x -> let tmp = add x 1 in x) in test) (fun f -> f true)",
    //   "cannot constrain bool <: int")
       error("(fun k -> let test = k (fun x -> let tmp = add x 1 in x) in test) (fun f -> f true)",
      "cannot constrain int <: bool")
    
    
    // Simple example of extruding type variables constrained both ways:
    doTest("fun k -> let test = k (fun x -> let tmp = add x 1 in x) in test",
      "(('a INTER int -> 'a) -> 'b) -> 'b")
    // MLsub: ((((int & a) -> a) -> b) -> b)
    
    // Adapted to exhibit a problem if we use the old extrusion algorithm:
    doTest("fun k -> let test = k (fun x -> let tmp = add x 1 in if true then x else 2) in test",
      "((int -> int) -> 'a) -> 'a")
    // MLsub: ((((int & a) -> (int | a)) -> b) -> b)
    
    // Example loss of polymorphism due to extrusion – the identity function becomes less polymorphic:
    doTest("fun k -> let test = (fun id -> {tmp = k id; res = id}.res) (fun x -> x) in {u=test 0; v=test true}",
      "(('a -> 'a UNION bool UNION int) -> TOP) -> {u: 'a UNION int, v: 'a UNION bool}")
    // MLsub: (((a -> (bool | int | a)) -> Top) -> {u : (int | a), v : (bool | a)})
    
    // Compared with this version: (MLsub still agrees)
    doTest("fun k -> let test = {tmp = k (fun x -> x); res = (fun x -> x)}.res in {u=test 0; v=test true}",
      "(('a -> 'a) -> TOP) -> {u: int, v: bool}")
    
    doTest("fun k -> let test = (fun thefun -> {l=k thefun; r=thefun 1}) (fun x -> let tmp = add x 1 in x) in test",
      "(('a INTER int -> 'a UNION int) -> 'b) -> {l: 'b, r: int}")
    
    
    doTest("fun a -> (fun k -> let test = k (fun x -> let tmp = add x 1 in x) in test) (fun f -> f a)",
      "'a INTER int -> 'a")
    
    doTest("(fun k -> let test = k (fun x -> let tmp = (fun y -> add y 1) x in x) in test)",
      "(('a INTER int -> 'a) -> 'b) -> 'b")
    
    doTest("(fun k -> let test = k (fun x -> let tmp = let f = fun y -> add y 1 in f x in x) in test)",
      "(('a INTER int -> 'a) -> 'b) -> 'b")
    
    doTest("fun f -> let r = fun x -> fun g -> { a = f x; b = g x } in r",
      "('a -> 'b) -> 'a -> ('a -> 'c) -> {a: 'b, b: 'c}")
    
    doTest("fun f -> let r = fun x -> fun g -> { a = g x } in {u = r 0 succ; v = r true not}",
      "TOP -> {u: {a: int}, v: {a: bool}}")
    // MLsub:
    //   let res = fun f -> let r = fun x -> fun g -> { a = g x } in {u = r 0 (fun n -> n + 1); v = r {t=true} (fun y -> y.t)}
    //   val res : (Top -> {u : {a : int}, v : {a : bool}})
    
    doTest("fun f -> let r = fun x -> fun g -> { a = g x; b = f x } in {u = r 0 succ; v = r true not}",
      "(bool UNION int -> 'a) -> {u: {a: int, b: 'a}, v: {a: bool, b: 'a}}")
    
    doTest("fun f -> let r = fun x -> fun g -> { a = g x; b = f x } in {u = r 0 succ; v = r {t=true} (fun y -> y.t)}",
      "(int UNION {t: bool} -> 'a) -> {u: {a: int, b: 'a}, v: {a: bool, b: 'a}}")
    // MLsub:
    //   let res = fun f -> let r = fun x -> fun g -> { a = g x; b = f x } in {u = r 0 (fun n -> n + 1); v = r {t=true} (fun y -> y.t)}
    //   val res : (({t : bool} | int -> a) -> {u : {a : int, b : a}, v : {a : bool, b : a}})
    
    
  }
  
  test("recursion") {
    doTest("let rec f = fun x -> f x.u in f",
      "{u: 'a} as 'a -> BOT")
    
    // [test:T2]:
    doTest("let rec r = fun a -> r in if true then r else r",
      "(TOP -> 'a) as 'a")
    // ^ without canonicalization, we get the type:
    //    TOP -> (TOP -> 'a) as 'a UNION (TOP -> 'b) as 'b
    doTest("let rec l = fun a -> l in let rec r = fun a -> fun a -> r in if true then l else r",
      "(TOP -> TOP -> 'a) as 'a")
    // ^ without canonicalization, we get the type:
    //    TOP -> (TOP -> 'a) as 'a UNION (TOP -> (TOP -> TOP -> 'b) as 'b)
    doTest("let rec l = fun a -> fun a -> fun a -> l in let rec r = fun a -> fun a -> r in if true then l else r",
      "(TOP -> TOP -> TOP -> TOP -> TOP -> TOP -> 'a) as 'a") // 6 is the LCD of 3 and 2
    // ^ without canonicalization, we get the type:
    //    TOP -> TOP -> (TOP -> TOP -> 'a) as 'a UNION (TOP -> (TOP -> TOP -> TOP -> 'b) as 'b)
    
    // from https://www.cl.cam.ac.uk/~sd601/mlsub/
    doTest("let rec recursive_monster = fun x -> { thing = x; self = recursive_monster x } in recursive_monster",
      "'a -> {self: 'b, thing: 'a} as 'b")
  }
  
  test("random") {
    doTest("(let rec x = {a = x; b = x} in x)",                           "{a: 'a, b: 'a} as 'a")
    doTest("(let rec x = fun v -> {a = x v; b = x v} in x)",              "TOP -> {a: 'a, b: 'a} as 'a")
    // error("let rec x = (let rec y = {u = y; v = (x y)} in 0) in 0",       "cannot constrain int <: 'a -> 'b")
    error("let rec x = (let rec y = {u = y; v = (x y)} in 0) in 0",       "cannot constrain 'a -> 'b <: int")
    doTest("(fun x -> (let y = (x x) in 0))",                             "'a INTER ('a -> TOP) -> int")
    doTest("(let rec x = (fun y -> (y (x x))) in x)",                     "('a -> ('a INTER ('a -> 'b)) as 'b) -> 'a")
    // ^ Note: without canonicalization, we get the simpler:               ('b -> 'b INTER 'a) as 'a -> 'b
    doTest("fun next -> 0",                                               "TOP -> int")
    doTest("((fun x -> (x x)) (fun x -> x))",                             "('b UNION ('b -> 'a)) as 'a")
    doTest("(let rec x = (fun y -> (x (y y))) in x)",                     "('b INTER ('b -> 'a)) as 'a -> BOT")
    doTest("fun x -> (fun y -> (x (y y)))",                               "('a -> 'b) -> 'c INTER ('c -> 'a) -> 'b")
    doTest("(let rec x = (let y = (x x) in (fun z -> z)) in x)",          "'a -> ('a UNION ('a -> 'b)) as 'b")
    doTest("(let rec x = (fun y -> (let z = (x x) in y)) in x)",          "'a -> ('a UNION ('a -> 'b)) as 'b")
    doTest("(let rec x = (fun y -> {u = y; v = (x x)}) in x)",
      "'a -> {u: 'a UNION ('a -> 'b), v: 'c} as 'c as 'b")
    doTest("(let rec x = (fun y -> {u = (x x); v = y}) in x)",
      "'a -> {u: 'c, v: 'a UNION ('a -> 'b)} as 'c as 'b")
    doTest("(let rec x = (fun y -> (let z = (y x) in y)) in x)",          "('b INTER ('a -> TOP) -> 'b) as 'a")
    doTest("(fun x -> (let y = (x x.v) in 0))",                           "{v: 'a} INTER ('a -> TOP) -> int")
    // doTest("let rec x = (let y = (x x) in (fun z -> z)) in (x (fun y -> y.u))", // [test:T1]
    //   "'a UNION ('a INTER {u: 'b} -> ('a UNION 'b UNION ('a INTER {u: 'b} -> 'c)) as 'c)")
    doTest("let rec x = (let y = (x x) in (fun z -> z)) in (x (fun y -> y.u))", // [test:T1]
      "'a UNION ('a INTER {u: 'b} -> ('b UNION 'a UNION ('a INTER {u: 'b} -> 'c)) as 'c)")
    // ^ Note: without canonicalization, we get the simpler:
    // ('b UNION ('b INTER {u: 'c} -> 'a UNION 'c)) as 'a
  }
  
  
}
