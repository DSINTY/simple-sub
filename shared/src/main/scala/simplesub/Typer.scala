package simplesub

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import scala.math.sqrt

final case class TypeError(msg: String) extends Exception(msg)

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification (see TypeSimplifier.scala).
 *  In order to turn the resulting CompactType into a simplesub.Type, we use `coalesceCompactType`.
 */
class Typer(protected val dbg: Boolean) extends TyperDebugging {
  
  type Ctx = Map[String, TypeScheme]
  
  val BoolType: Primitive = Primitive("bool")
  val IntType: Primitive = Primitive("int")
  
  val builtins: Ctx = Map(
    "true" -> BoolType,
    "false" -> BoolType,
    "not" -> Function(BoolType, BoolType),
    "succ" -> Function(IntType, IntType),
    "add" -> Function(IntType, Function(IntType, IntType)),
    "if" -> {
      val v = freshVar(1)
      PolymorphicType(0, Function(BoolType, Function(v, Function(v, v))))
    }
  )
  
  /** The main type inference function */
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0)) catch {
          case err: TypeError => Left(err) }
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(0))))
      case Nil => Nil
    }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): (SimpleType,MutSet[Variable]) = typeTerm(term)(ctx, lvl)
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)(implicit ctx: Ctx, lvl: Int): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(lvl + 1)
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1)._1
      constrain(ty, e_ty)
      e_ty
    } else typeTerm(rhs)(ctx, lvl + 1)._1
    PolymorphicType(lvl, res)
  }

  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, lvl: Int): (SimpleType,MutSet[Variable]) = {
    lazy val res = freshVar
    // val variables = MutSet.empty[Variable]
    // println(s"typing: $term")
    term match {
      case Var(name) =>
        val variable = ctx.getOrElse(name, err("identifier not found: " + name)).instantiate
        // variables += variable.asInstanceOf[Variable]
        if (variable.isInstanceOf[Variable]) {
          (variable, MutSet(variable.asInstanceOf[Variable]))
        }
        else {
          (variable, MutSet.empty)
        }
      case Lam(name, body) =>
        val param = freshVar
        val (body_ty,functionVars) = typeTerm(body)(ctx + (name -> param), lvl)
        (Function(param, body_ty),functionVars+param)
      case App(f, a) =>
        val (f_ty,f_vars) = typeTerm(f)
        val (a_ty,a_vars) = typeTerm(a)
        // println(f_ty)
        // println(f_vars)
        // println(a_ty)
        
        // println(a_vars)
        constrain(f_ty, Function(a_ty, res))
        (res, f_vars ++ a_vars+res)
      case Lit(n) =>
        (IntType, MutSet.empty)
      case Sel(obj, name) =>
        val (obj_ty,obj_vars) = typeTerm(obj)
        constrain(obj_ty, Record((name, res) :: Nil))
        (res, obj_vars+res)
      case Rcd(fs) =>
        val variables = MutSet.empty[Variable]
        (Record(fs.map { case (n, t) => 
          val (t_ty, vars) = typeTerm(t)
          variables ++= vars
          (n, t_ty) 
        }),variables)
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl)
    }
  }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)
      // we need a cache to remember the subtyping tests in process; we also make the cache remember
      // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm)
      (implicit cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty)
  : Unit= {
    // println(s"constraining: $lhs <: $rhs")
    if (lhs is rhs) return 
    val lhs_rhs = lhs -> rhs
    lhs_rhs match {
      // There is no need to remember the subtyping tests performed that did not involve
      // type variables, as type variables will necessary be part of any possible cycles.
      // Since these types form regular trees, there will necessarily be a point where a
      // variable part of a cycle will be matched against the same type periodically.
      
      case (_: Variable, _) | (_, _: Variable) =>
        if (cache(lhs_rhs)) return
        cache += lhs_rhs
      case _ => ()
    }
    // println(s"constraining1: $lhs <: $rhs")
    lhs_rhs match {
      case (Function(l0, r0), Function(l1, r1)) =>
        constrain(l1, l0)
        constrain(r0, r1)
      // case (lhs:Function, rhs: Function) =>
      //   val l0 = lhs.lhs
      //   val r0 = lhs.rhs
      //   val l1 = rhs.lhs
      //   val r1 = rhs.rhs
      //   constrain(l1, l0)
      //   constrain(r0, r1)
      //   lhs.upperBounds ::= rhs
      //   rhs.lowerBounds ::= lhs
      case (Record(fs0), Record(fs1)) =>
        fs1.foreach { case (n1, t1) =>
          fs0.find(_._1 === n1).fold(
            err(s"missing field: $n1 in ${lhs.show}")
          ) { case (n0, t0) => constrain(t0, t1) }
        }
      case (lhs: Variable, rhs) if rhs.level <= lhs.level =>
        lhs.upperBounds ::= rhs
        // rhs.lowerBounds ::= lhs
        // if (rhs.isInstanceOf[Function]) {
        //   lhs.lowerBounds.foreach(constrain(_, rhs))
        // }
        if (rhs.isInstanceOf[Variable]) {
          rhs.asInstanceOf[Variable].lowerBounds ::= lhs
        }
        // lhs.lowerBounds.foreach(constrain(_, rhs))
      case (lhs, rhs: Variable) if lhs.level <= rhs.level =>
        rhs.lowerBounds ::= lhs
        // lhs.upperBounds ::= rhs
        // rhs.upperBounds.foreach(constrain(lhs, _))
        // if (lhs.isInstanceOf[Function]){
        //   rhs.upperBounds.foreach(constrain(lhs, _))
        // }
        if (lhs.isInstanceOf[Variable]) {
          lhs.asInstanceOf[Variable].upperBounds ::= rhs
        }
      case (_: Variable, rhs0) =>
        val rhs = extrude(rhs0, false)(lhs.level, MutMap.empty)
        constrain(lhs, rhs)
      case (lhs0, _: Variable) =>
        val lhs = extrude(lhs0, true)(rhs.level, MutMap.empty)
        constrain(lhs, rhs)
      case _ => err(s"cannot constrain ${lhs.show} <: ${rhs.show}")
    }
  }

  def matMul(A: Array[Array[Int]], B: Array[Array[Int]]): Array[Array[Int]] = {
    val m = A.length
    val n = B(0).length
    val p = B.length
    val C = Array.fill(m, n)(0)
    for (i <- 0 until m) {
      for (j <- 0 until n) {
        for (k <- 0 until p) {
          C(i)(j) = C(i)(j) | (A(i)(k) & B(k)(j))
        }
      }
    }
    C
  }

  def matAdd(A: Array[Array[Int]], B: Array[Array[Int]]): Array[Array[Int]] = {
    val m = A.length
    val n = A(0).length
    val C = Array.fill(m, n)(0)
    for (i <- 0 until m) {
      for (j <- 0 until n) {
        C(i)(j) = A(i)(j) | B(i)(j)
      }
    }
    C
  }

  def matTrans(A: Array[Array[Int]]): Array[Array[Int]] = {
    val m = A.length
    val n = A(0).length
    val C = Array.fill(n, m)(0)
    for (i <- 0 until m) {
      for (j <- 0 until n) {
        C(j)(i) = A(i)(j)
      }
    }
    C
  }

  def transitiveClosure(ty: SimpleType, vars:MutSet[Variable]): Unit = {
    // get all variables
    val types = MutSet.empty[SimpleType]
    // def collectVars(ty: SimpleType): Unit = ty match {
    //   case tv: Variable =>
    //     if (!vars(tv)) {
    //       vars += tv
    //       // tv.lowerBounds.foreach(collectVars)
    //       // tv.upperBounds.foreach(collectVars)
    //     }
    //   case Function(l, r) =>
    //     collectVars(l)
    //     collectVars(r)
    //   case Record(fs) =>
    //     fs.foreach { case (_, t) => collectVars(t) }
    //   case Primitive(_) => ()
    // }
  
    val rcdFields = MutSet.empty[String]
    // collect all the types recursively
    def collectTypes(ty: SimpleType): Unit = {
      if (!types(ty)) {
        types += ty
        // println(ty)
        ty match {
          case tv: Variable =>
            vars += tv
            // println(tv.showBounds)
            tv.lowerBounds.foreach(collectTypes)
            tv.upperBounds.foreach(collectTypes)
          case Function(l, r) =>
            collectTypes(l)
            collectTypes(r)
          case Record(fs) =>
            fs.foreach { case (n, t) => 
              rcdFields += n
              collectTypes(t) }
          case Primitive(_) => ()
        }
      }
    }
    // collectVars(ty)
    collectTypes(ty)
    vars.foreach(collectTypes)
    // types.foreach(showBounds)

    

    // construct bounds matrix M symmetrically, where M(i, j) = 1 iff i <: j
    val typeList = types.toList
    // println(typeList)
    val numNodes = typeList.length
    val typeMap = typeList.zipWithIndex.toMap
    
    val rcdFieldsList = rcdFields.toList
    val rcdFieldsMap = rcdFieldsList.zipWithIndex.toMap
    val numFields = rcdFieldsList.length

    val Mu = Array.fill(numNodes,numNodes)(0)
    val depth = Array.fill(numNodes)(0)
    
    val lhs_to_func = Array.fill(numNodes,numNodes)(0)
    val func_to_lhs = Array.fill(numNodes,numNodes)(0)
    val rhs_to_func = Array.fill(numNodes,numNodes)(0)
    val func_to_rhs = Array.fill(numNodes,numNodes)(0)

    val type_to_name = Array.fill(numNodes,numFields)(0)
    val name_to_rcd = Array.fill(numFields,numNodes)(0)
    for ((tv, i) <- typeList.zipWithIndex) {
      // Mu(i)(i) = 1
      if (tv.isInstanceOf[Variable]) {
        tv.asInstanceOf[Variable].lowerBounds.foreach { lb =>
          // if lb is not primitive type
          // if (lb.isInstanceOf[Variable]) {
            val j = typeMap(lb)
            Mu(i)(j) = 1
          // }
        }
        tv.asInstanceOf[Variable].upperBounds.foreach { ub =>
          // if (ub.isInstanceOf[Variable]) {
            val j = typeMap(ub)
            Mu(j)(i) = 1
          // }
        }
      }

      if (tv.isInstanceOf[Function]){
        val lhs = tv.asInstanceOf[Function].lhs
        val rhs = tv.asInstanceOf[Function].rhs
        val j = typeMap(lhs)
        val k = typeMap(rhs)
        // depth(j) = depth(i) + 1
        // depth(k) = depth(i) + 1
        // Mu(j)(i) = 1
        // Mu(i)(j) = 1
        lhs_to_func(j)(i) = 1
        func_to_lhs(i)(j) = 1
        rhs_to_func(k)(i) = 1
        func_to_rhs(i)(k) = 1

      }

      if (tv.isInstanceOf[Record]){
        val fs = tv.asInstanceOf[Record].fields
        for ((n, t) <- fs) {
          type_to_name(typeMap(t))(rcdFieldsMap(n)) = 1
          name_to_rcd(rcdFieldsMap(n))(i) = 1
          // Mu(j)(i) = 1
        }
      }
     
      
    }

    // for (i <- 0 until numNodes) {
    //   println(typeList(i)+" "+depth(i))
    // }
    

    // println("M")
    // for (i <- 0 until numNodes) {
    //   for (j <- 0 until numNodes) {
    //     print(Mu(i)(j) + " ")
    //   }
    //   println()
    // }

    
    // val Mupow = Array.fill(numNodes)(Mu)
    var Mupow = Array.fill(numNodes,numNodes,numNodes)(0)
    var lhs_to_func_Mu = Array.fill(numNodes,numNodes)(0)
    var rhs_to_func_A = Array.fill(numNodes,numNodes)(0)
    var Mu_new = Array.fill(numNodes,numNodes)(0)
    // for (i <- 0 until numNodes) {
    //     for (j <- 0 until numNodes) {
    //       for (l <- 0 until numNodes) {
    //               // matrix mutiplicatio
    //               lhs_to_func_Mu(i)(j) = lhs_to_func_Mu(i)(j) | (lhs_to_func(i)(l) & Mu(l)(j))
    //               rhs_to_func_A(i)(j) = rhs_to_func_A(i)(j) | (rhs_to_func(i)(l) & Mu(j)(l))
    //       }
    //     }
    //   }
    lhs_to_func_Mu = matMul(lhs_to_func, Mu)
    rhs_to_func_A = matMul(rhs_to_func, matTrans(Mu))
    
      // for (i <- 0 until numNodes) {
      //   for (j <- 0 until numNodes) {
      //     for (l <- 0 until numNodes) {
      //             Mu_new(i)(j) = Mu_new(i)(j) | (lhs_to_func_Mu(i)(l) & func_to_lhs(l)(j))
      //           }
      //           Mu_new(i)(j) = Mu_new(i)(j) | Mu(i)(j)
      //   }
        
      // }

    Mu_new = matAdd(Mu, matMul(lhs_to_func_Mu, func_to_lhs))
    

    // val Mupow = Array.fill(numNodes,numNodes,numNodes)(0)
    // Mupow(0) = Mu
    Mupow(0) = Mu_new
    // val Mlpow = Array.fill(numNodes,numNodes,numNodes)(0)
    for (k <- 1 until numNodes) {
      var Mupowk = Array.fill(numNodes,numNodes)(0)
      val A = Array.fill(numNodes,numNodes)(0)
      var lhs_to_func_A = Array.fill(numNodes,numNodes)(0)
      var A_low = Array.fill(numNodes,numNodes)(0)
      var rhs_to_func_A = Array.fill(numNodes,numNodes)(0)
      var Mlpowk = Array.fill(numNodes,numNodes)(0)
      // println("step "+k)
      for (i <- 0 until numNodes) {
        for (j <- 0 until numNodes) {
          for (l <- 0 until numNodes) {
            // matrix mutiplication
           Mupow(k)(i)(j) = Mupow(k)(i)(j)| (Mupow(k)(i)(l) & Mupow(k-1)(l)(j))
            // A_low(i)(j) = A_low(i)(j) | (Mupow(last)(j)(l) & Mupow(last)(l)(i))
            
          }
          // A_low(j)(i) = A(i)(j)
          Mupow(k)(i)(j) = Mupow(k)(i)(j) | Mupow(k-1)(i)(j)
        }
      }

      // Mupow(k) = matAdd(Mupow(k-1), matMul(Mupow(k), Mupow(k-1)))


      for (repeats <- 0 until numNodes) {
        
        
      
      // for (i <- 0 until numNodes) {
      //   for (j <- 0 until numNodes) {
      //     for (l <- 0 until numNodes) {
      //       lhs_to_func_A(i)(j) = lhs_to_func_A(i)(j) | (lhs_to_func(i)(l) & Mupow(k)(j)(l))
      //       rhs_to_func_A(i)(j) = rhs_to_func_A(i)(j) | (rhs_to_func(i)(l) & Mupow(k)(l)(j))
      //     }
      //   }
      // }

      lhs_to_func_A = matMul(lhs_to_func, matTrans(Mupow(k)))
      rhs_to_func_A = matMul(rhs_to_func, Mupow(k))

      Mupowk = matAdd(matAdd(matMul(rhs_to_func_A,func_to_rhs), matMul(lhs_to_func_A, func_to_lhs)), Mupow(k))
      for (i <- 0 until numNodes) {
        for (j <- 0 until numNodes) {
          // for (l <- 0 until numNodes) {
          //   Mupowk(i)(j) = Mupowk(i)(j) | (lhs_to_func_A(i)(l) & func_to_lhs(l)(j))
          //   Mupowk(i)(j) = Mupowk(i)(j) | (rhs_to_func_A(i)(l) & func_to_rhs(l)(j))
          //   Mupowk(i)(j) = Mupowk(i)(j) | A(i)(j)

          //   // Mlpowk(i)(j) = Mlpowk(i)(j) | (rhs_to_func_A(i)(l) & func_to_rhs(l)(j))
          //   // Mlpowk(i)(j) = Mlpowk(i)(j) | A_low(i)(j)

          //   Mupowk(i)(j) = Mupowk(i)(j) | Mupow(k)(i)(j)
            
            
          // }
          if (Mupowk(i)(j) == 1) {
            if (typeList(i).isInstanceOf[Record] && typeList(j).isInstanceOf[Record]) {
              val fs0 = typeList(i).asInstanceOf[Record].fields
              val fs1 = typeList(j).asInstanceOf[Record].fields
              
             fs0.foreach { case (n0, t0) =>
          fs1.find(_._1 === n0).fold(
            err(s"missing field: $n0 in ${typeList(j).show}")
          ) { case (n1, t1) => Mupowk(typeMap(t0))(typeMap(t1))=1 }
        }
            }
          }
          
        

        }
      }
      // for (i <- 0 until numNodes) {
      //   for (j <- 0 until numNodes) {
      //     for (l <- 0 until numNodes) {
      //       lhs_to_func_A(i)(j) = lhs_to_func_A(i)(j) | (lhs_to_func(i)(l) & Mupow(k)(j)(l))
      //       rhs_to_func_A(i)(j) = rhs_to_func_A(i)(j) | (rhs_to_func(i)(l) & Mupow(k)(l)(j))
      //     }
      //   }
      // }
           Mupow(k) = Mupowk
        }
       
      
      // for (i <- 0 until numNodes) {
      //   for (j <- 0 until numNodes) {
      //     for (l <- 0 until numNodes) {
      //       Mupowk(i)(j) = Mupowk(i)(j) | (Mupow(k-1)(i)(l) & Mupow(k-1)(l)(j))
      //     }
      //   }
      // }
        
      


      
      // println("M"+k)
      // for (i <- 0 until numNodes) {
      //   for (j <- 0 until numNodes) {
      //     print(Mupowk(i)(j) + " ")
      //   }
      //   println()
      // }
    }


    // Compute M^* = M + M^2 + M^3 + ... +M^n, where n = numNodes
    // val Mstar = Array.fill(numNodes,numNodes)(0)
    // for (k <- 0 until numNodes) {
    //   for (i <- 0 until numNodes) {
    //     for (j <- 0 until numNodes) {
    //       Mstar(i)(j) = Mstar(i)(j) | Mupow(k)(i)(j)
    //     }
    //   }
    // }

    val Mstar = Mupow(numNodes-1)

    // println("M*")
    // for (k <- 1 to numNodes) {
    //   for (i <- 0 until numNodes) {
    //     for (j <- 0 until numNodes) {
    //       Mstar(i)(j) = Mstar(i)(j) | Mupow(k-1)(i)(j)
    //     }
    //   }
    // }
    // for ((tv, i) <- typeList.zipWithIndex) {
    //   if (tv.isInstanceOf[Variable]) {
    //     tv.asInstanceOf[Variable].lowerBounds.foreach { lb =>
          
    //         val j = typeMap(lb)
    //         M(i)(j) = 1
          
    //     }
    //     tv.asInstanceOf[Variable].upperBounds.foreach { ub =>
    //       val j = typeMap(ub)
    //       M(j)(i) = 1
          
    //     }
    //   }
      
    // }
    


    

    //Compute M^2 M^3 , ... , M^n, maintain them in a list
    // print M


    // println("M*")

    // for (i <- 0 until numNodes) {
    //   for (j <- 0 until numNodes) {
    //     print(Mstar(i)(j) + " ")
    //   }
    //   println()
    // }

    // empty the bounds of all variables
    // for (tv <- typeList) {
    //   if (tv.isInstanceOf[Variable]) {
    //     tv.asInstanceOf[Variable].lowerBounds = Nil
    //     tv.asInstanceOf[Variable].upperBounds = Nil
    //   }
    //   tv.lowerBounds = Nil
    //   tv.upperBounds = Nil
    // }
    // from Mstar back to variables upperbounds and lowerbounds
    // for ((tv, i) <- typeList.zipWithIndex) {
    //   if (tv.isInstanceOf[Variable]){
    //     for (j <- 0 until (numNodes-i)) {
    //       if (Mlstar(i)(j) == 1) {
    //         tv.asInstanceOf[Variable].lowerBounds ::= typeList(j)
    //         // tv.upperBounds ::= varList(j)
    //         // if (typeList(j).isInstanceOf[Variable]) {
    //         //   typeList(j).asInstanceOf[Variable].upperBounds ::= tv
    //         // }
    //         // typeList(j).lowerBounds ::= tv
    //       }
    //       if (Mustar(i)(j) == 1) {
    //         tv.asInstanceOf[Variable].upperBounds ::= typeList(j)
    //         // tv.lowerBounds ::= varList(j)
    //         // if (typeList(j).isInstanceOf[Variable]) {
    //         //   typeList(j).asInstanceOf[Variable].lowerBounds ::= tv
    //         // }
    //         // typeList(j).upperBounds ::= tv
    //       }
    //     }
    // }
    // }

    for ((tv, i) <- typeList.zipWithIndex) {
      if (tv.isInstanceOf[Variable]){
        for (j <- 0 until numNodes) {
          if (i != j ) {
            if (Mstar(i)(j) == 1) {
            tv.asInstanceOf[Variable].lowerBounds ::= typeList(j)
            if (typeList(j).isInstanceOf[Variable]) {
              
              typeList(j).asInstanceOf[Variable].upperBounds ::= tv
            }
            
          }
            
          } 
          
        }
      }
      else if (tv.isInstanceOf[Function]){
        for (j <- 0 until numNodes) {
          if (i != j ) {
            if (Mstar(i)(j) == 1) {
              if (!(typeList(j).isInstanceOf[Variable] |typeList(j).isInstanceOf[Function]) )  err(s"cannot constrain ${typeList(j).show} <: ${tv.show}")
            }

            
          }
        }
      }
      else if (tv.isInstanceOf[Record]){
        for (j <- 0 until numNodes) {
          if (i != j ) {
            if (Mstar(i)(j) == 1) {
              if (!(typeList(j).isInstanceOf[Variable] |typeList(j).isInstanceOf[Record]) )  err(s"cannot constrain ${typeList(j).show} <: ${tv.show}")
            }

            
          }
        }
      }

      else if (tv.isInstanceOf[Primitive]){
        for (j <- 0 until numNodes) {
          if (i != j ) {
            if (Mstar(i)(j) == 1) {
              if (!typeList(j).isInstanceOf[Variable]  )  err(s"cannot constrain ${typeList(j).show} <: ${tv.show}")
            }

            
          }
        }
      }
      // if (tv.isInstanceOf[Function]) {
      //   for (j <- 0 until numNodes) {
      //     if (i!=j){
      //       if (Mstar(i)(j) == 1) {
      //         if (typeList(j).isInstanceOf[Function]) {
      //           val f = tv.asInstanceOf[Function]
      //           val g = typeList(j).asInstanceOf[Function]
      //           val l0 = f.lhs
      //           val r0 = f.rhs
      //           val l1 = g.lhs
      //           val r1 = g.rhs
      //           if (l0.isInstanceOf[Variable] && l1.isInstanceOf[Variable]) {
      //             l0.asInstanceOf[Variable].upperBounds ::= l1
      //             l1.asInstanceOf[Variable].lowerBounds ::= l0
      //           }
      //           if (r0.isInstanceOf[Variable] && r1.isInstanceOf[Variable]) {
      //             r0.asInstanceOf[Variable].lowerBounds ::= r1
      //             r1.asInstanceOf[Variable].upperBounds ::= r0
      //           }
      //         }
              
              

      //       }
      //   }
      //   }
      // }
    }
    // println(ty.showBounds)

    

  }
  
  type PolarVariable = (Variable, Boolean)
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  def extrude(ty: SimpleType, pol: Boolean)
      (implicit lvl: Int, cache: MutMap[PolarVariable, Variable]): SimpleType =
      // Note that we need to keep a cache of _polar_ type variables, the idea being that if a
      // variable v is extruded, two new variables should be created, one for each of v's bounds
      // (unless of course the variable occurs strictly positively or negatively, in which case
      // one of the two bounds can be discarded). This way, we essentially create a conservative
      // approximation of v in the result of the extrusion, and any later instantiation of v
      // (created at every point the nested let binding is used) will be able to receive
      // additional constraints independently as long as it is within these approximating bounds.
    if (ty.level <= lvl) ty else ty match {
      case Function(l, r) => Function(extrude(l, !pol), extrude(r, pol))
      case Record(fs) => Record(fs.map(nt => nt._1 -> extrude(nt._2, pol)))
      case tv: Variable => cache.getOrElse(tv -> pol, {
        val nvs = freshVar
        cache += tv -> pol -> nvs
        if (pol) {
          tv.upperBounds ::= nvs
          nvs.lowerBounds = tv.lowerBounds.map(extrude(_, pol))
        } else {
          tv.lowerBounds ::= nvs
          nvs.upperBounds = tv.upperBounds.map(extrude(_, pol))
        }
        nvs
      })
      case Primitive(_) => ty
    }
  
  def err(msg: String): Nothing = throw TypeError(msg)
  
  private var freshCount = 0
  def freshVar(implicit lvl: Int): Variable = new Variable(lvl, Nil, Nil)
  
  def freshenAbove(lim: Int, ty: SimpleType)(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[Variable, Variable]
    def freshen(ty: SimpleType): SimpleType = if (ty.level <= lim) ty else ty match {
      case tv: Variable =>
        freshened.get(tv) match {
          case Some(tv) => tv
          case None =>
            val v = freshVar
            freshened += tv -> v
            // v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
            // v.upperBounds = tv.upperBounds.mapConserve(freshen)
            //  ^ the above are more efficient, but they lead to a different order
            //    of fresh variable creations, which leads to some types not being
            //    simplified the same when put into the RHS of a let binding...
            v.lowerBounds = tv.lowerBounds.reverse.map(freshen).reverse
            v.upperBounds = tv.upperBounds.reverse.map(freshen).reverse
            v
        }
      case Function(l, r) => Function(freshen(l), freshen(r))
      case Record(fs) => Record(fs.map(ft => ft._1 -> freshen(ft._2)))
      case Primitive(_) => ty
    }
    freshen(ty)
  }
  
  
  // The data types used for type inference:
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int): SimpleType
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    def instantiate(implicit lvl: Int) = freshenAbove(level, body)
  }
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  case class Function(lhs: SimpleType, rhs: SimpleType) extends SimpleType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
    // var lowerBounds: List[SimpleType] = Nil
    //   var upperBounds: List[SimpleType] = Nil
  }
  case class Record(fields: List[(String, SimpleType)]) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  case class Primitive(name: String) extends SimpleType {
    def level: Int = 0
    override def toString = name
  }
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class Variable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
  ) extends SimpleType with CompactTypeOrVariable {
    private[simplesub] val uid: Int = { freshCount += 1; freshCount - 1 }
    private[simplesub] var recursiveFlag = false // used temporarily by `compactType`
    lazy val asTypeVar = new TypeVariable("α", uid)
    override def toString: String = "α" + uid + "'" * level
    override def hashCode: Int = uid
  }
  
  trait CompactTypeOrVariable
  
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def coalesceType(st: SimpleType): Type = {
    val recursive = mutable.Map.empty[PolarVariable, TypeVariable]
    def go(st: SimpleType, polarity: Boolean)(inProcess: Set[PolarVariable]): Type = st match {
      case tv: Variable =>
        val tv_pol = tv -> polarity
        if (inProcess.contains(tv_pol))
          recursive.getOrElseUpdate(tv_pol, freshVar(0).asTypeVar)
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + tv_pol))
          val mrg = if (polarity) Union else Inter
          val res = boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
          recursive.get(tv_pol).fold(res)(RecursiveType(_, res))
        }
      case Function(l, r) => FunctionType(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case Record(fs) => RecordType(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case Primitive(n) => PrimitiveType(n)
    }
    go(st, true)(Set.empty)
  }
  
  
}
