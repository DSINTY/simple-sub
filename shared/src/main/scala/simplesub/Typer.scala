package simplesub

import scala.collection.mutable
import scala.collection.mutable.Stack
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import javax.management.openmbean.SimpleType
import scala.collection.mutable.ArrayBuffer
import scala.annotation.elidable

class FastSet(n: Int) {
  // Word size is fixed at 64 bits using Long
  private val WORD_SIZE = 64
  // Number of words needed: ceil(n / WORD_SIZE)
  private val numWords = (n + WORD_SIZE - 1) / WORD_SIZE
  // Bit vector initialized with all bits set to 0
  private val bits = Array.fill(numWords)(0L)

  /** Inserts an element x into the set. */
  def insert(x: Int): Unit = {
    if (x < 0 || x >= n) throw new IndexOutOfBoundsException(s"Element $x out of bounds [0, $n)")
    val wordIndex = x / WORD_SIZE
    val bitPos = x % WORD_SIZE
    bits(wordIndex) |= (1L << bitPos)  // Set the bit at position bitPos in the word
  }

  /** Updates this set to be the union of this set and other. */
  def assignUnion(other: FastSet): Unit = {
    require(other.numWords == numWords, "Sets must have the same universe size")
    for (i <- 0 until numWords) {
      bits(i) |= other.getBits(i)  // Use getBits to access other's bits
    }
  }

  /** Returns a list of elements in this set but not in other (X \ Y). */
  def diff(other: FastSet): List[Int] = {
    require(other.numWords == numWords, "Sets must have the same universe size")
    val result = ArrayBuffer[Int]()
    for (i <- 0 until numWords) {
      // Compute Z = X & ~Y for the current word
      var z = bits(i) & ~other.getBits(i)  // Use getBits to access other's bits
      while (z != 0) {
        val pos = java.lang.Long.numberOfTrailingZeros(z)  // Find least significant 1 bit
        val elem = i * WORD_SIZE + pos  // Calculate element index
        if (elem < n) {  // Ensure we don’t include unused bits beyond n
          result += elem
        }
        z &= z - 1  // Turn off the least significant 1 bit
      }
    }
    result.toList  // Convert to immutable List as required
  }

  // Renamed method to avoid ambiguity with the bits field
  private def getBits(i: Int): Long = bits(i)
}

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
      PolymorphicType(0, Function(BoolType, Function(v, Function(v, v))), Set.empty[(SimpleType)])
    }
  )

  val symbolMap: MutMap[String, Int]= MutMap(
    "R" -> 0,
    "S" -> 1,
    "empty" -> 2,
    "f_in(" -> 3,
    "f_in)" -> 4,
    "f_out(" -> 5,
    "f_out)" -> 6,
    "rev" -> 7,
  )

  val fieldSet: MutSet[String] = MutSet.empty[String]
  
  /** The main type inference function */
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0, MutSet.empty[(SimpleType, Int, SimpleType)], MutSet.empty[(SimpleType)], MutSet.empty[(SimpleType, SimpleType)])) catch {
          case err: TypeError => Left(err) }
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(0))))
      case Nil => Nil
    }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): (SimpleType, MutSet[(SimpleType, Int, SimpleType)], MutSet[(SimpleType)], MutSet[(SimpleType, SimpleType)]) = typeTerm(term)(ctx, lvl)
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)(implicit ctx: Ctx, lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)],polyRels: MutSet[(SimpleType,SimpleType)]): PolymorphicType = {
    var mono_types = types.toSet[(SimpleType)]
    val res = if (isrec) {
      val e_ty = freshVar(lvl + 1)
      types += e_ty
      // mono_types += e_ty
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1, rels, types, polyRels)._1
      // constrain(ty, e_ty)
      rels += ((ty, symbolMap("empty"), e_ty))
      rels += ((e_ty, symbolMap("rev"), ty))
      
      types += ty
      e_ty
    } else typeTerm(rhs)(ctx, lvl + 1, rels, types)._1
  
    types += res

    PolymorphicType(lvl, res, mono_types)
  }

 
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, lvl: Int, rels: MutSet[(SimpleType, Int, SimpleType)] = MutSet.empty[(SimpleType,Int,SimpleType)], types: MutSet[(SimpleType)]=MutSet[SimpleType](BoolType, IntType), polyRels: MutSet[(SimpleType,SimpleType)]=MutSet.empty[(SimpleType,SimpleType)]): (SimpleType, MutSet[(SimpleType, Int, SimpleType)], MutSet[(SimpleType)], MutSet[(SimpleType, SimpleType)]) = {
    lazy val res = freshVar
    
    
    val tyv = term match {
      case Var(name) =>{
        if (name == "if") {
          val v = freshVar(1)
          // val ty = Function(BoolType, Function(v, Function(v, v)))
          types += v
          // types += ty
          rels += ((v, symbolMap("f_in("), Function(v, v)))
          rels += ((v, symbolMap("f_out("), Function(v, v)))
          rels += ((Function(v, v), symbolMap("f_in)"), v))
          rels += ((Function(v, v), symbolMap("f_out)"), v))
          types += Function(v, v)
          rels += ((v, symbolMap("f_in("), Function(v, Function(v, v))))
          rels += ((Function(v, v), symbolMap("f_out("), Function(v, Function(v, v))))
          rels += ((Function(v, Function(v, v)), symbolMap("f_in)"), v))
          rels += ((Function(v, Function(v, v)), symbolMap("f_out)"), Function(v, v)))
          types += Function(v, Function(v, v))

          rels += ((BoolType, symbolMap("f_in("), Function(BoolType, Function(v, Function(v, v)))))
          rels += ((Function(BoolType, Function(v, Function(v, v))), symbolMap("f_in)"), BoolType))
          rels += ((Function(BoolType, Function(v, Function(v, v))), symbolMap("f_out)"), Function(v, Function(v, v))))
          rels += (( Function(v, Function(v, v)), symbolMap("f_out("), Function(BoolType, Function(v, Function(v, v)))))
          types += Function(BoolType, Function(v, Function(v, v)))

          PolymorphicType(0, Function(BoolType, Function(v, Function(v, v))), Set.empty[(SimpleType)]).instantiate
      }
      else
        ctx.getOrElse(name, err("identifier not found: " + name)).instantiate
    }
      case Lam(name, body) =>
        val param = freshVar
         types += param
        val body_ty = typeTerm(body)(ctx + (name -> param), lvl, rels, types, polyRels)._1
        rels += ((param, symbolMap("f_in("), Function(param, body_ty)))
        rels += ((body_ty, symbolMap("f_out("), Function(param, body_ty)))
        rels += ((Function(param, body_ty), symbolMap("f_in)"), param))
        rels += ((Function(param, body_ty), symbolMap("f_out)"), body_ty))
       
        types += body_ty
        Function(param, body_ty)
      case App(f, a) =>
        val f_ty = typeTerm(f)._1
        types += f_ty
        val a_ty = typeTerm(a)._1
        types += a_ty
        types += Function(a_ty, res)
        
       
        rels += ((a_ty, symbolMap("f_in("), Function(a_ty, res)))
        rels += ((Function(a_ty, res), symbolMap("f_in)"), a_ty))
        rels += ((Function(a_ty, res), symbolMap("f_out)"), res))
        rels += ((res, symbolMap("f_out("), Function(a_ty, res)))
        rels += ((f_ty, symbolMap("empty"), Function(a_ty, res)))
        rels += ((Function(a_ty, res), symbolMap("rev"), f_ty))

        res
      case Lit(n) =>
        IntType
      case Sel(obj, name) =>
        val obj_ty = typeTerm(obj)._1
        val ty = Record(List(name -> res))
        types+=ty
        rels += ((obj_ty, symbolMap("empty"), ty ))
        rels += ((ty, symbolMap("rev"), obj_ty ))
        types += obj_ty
        var openSym = 0
          var closeSym = 0
          if (symbolMap.contains("rec_" + name + "(")) 
          {
            openSym = symbolMap("rec_" + name + "(")
            closeSym = symbolMap("rec_" + name + ")")
          }
          else
          {
            openSym = symbolMap.size
            symbolMap += ("rec_"+name+"(" -> openSym)
            closeSym = symbolMap.size
            symbolMap += ("rec_"+name+")" -> closeSym)
          }
          
          rels += ((res, openSym, ty))
          rels += ((ty, closeSym, res))
          types += res
          
          fieldSet += name 
        res
      case Rcd(fs) =>
        val fs_ty = fs.map { case (n, t) => (n, typeTerm(t)._1) }
        val ty = Record(fs_ty)
        fs_ty.foreach { case (n, t) => 
          var openSym = 0
          var closeSym = 0
          if (symbolMap.contains("rec_" + n + "(")) 
          {
            openSym = symbolMap("rec_" + n + "(")
            closeSym = symbolMap("rec_" + n + ")")
          }
          else
          {
            openSym = symbolMap.size
            symbolMap += ("rec_"+n+"(" -> openSym)
            closeSym = symbolMap.size
            symbolMap += ("rec_"+n+")" -> closeSym)
          }
          
          rels += ((t, openSym, ty))
          rels += ((ty, closeSym, t))
          types += t
          
          fieldSet += n 
        }
        ty
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)(ctx, lvl, rels, types, polyRels)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl, rels, types, polyRels)._1
        // typeTerm(bod)(ctx + (nme -> n_ty), lvl, rels, types)._1

    }
    types += tyv


    (tyv, rels, types, polyRels)
  }

  def opp(sym: String): String = {
    if (sym=="R") "S"
    else "R"
  }
  
  def termSym(sym: String): String = {
    if (sym=="R") "rev"
    else "empty"
  }
  
  def cflReach(ty: SimpleType, rels: MutSet[(SimpleType, Int, SimpleType)], types: MutSet[(SimpleType)], polyRels:  MutSet[(SimpleType, SimpleType)]): SimpleType = {
    val rules_1 = MutSet.empty[(Int, Int)]
    val rules_2 = MutSet.empty[(Int, Int, Int)]
    val rules_3 = MutSet.empty[(Int, Int, Int, Int)]
    // println("PolyRels: ", polyRels)

    for (primType <- Seq(BoolType, IntType)){
    rels += ((primType, symbolMap("f_in("), Function(primType, primType)))
    rels += ((Function(primType, primType), symbolMap("f_in)"), primType))
    rels += ((Function(primType, primType), symbolMap("f_out)"), primType))
    rels += ((primType, symbolMap("f_out("), Function(primType, primType)))
    types += Function(primType, primType)
    types += primType
   }

    rels += ((IntType, symbolMap("f_in("), Function(IntType, Function(IntType, IntType))))
    rels += ((Function(IntType, Function(IntType, IntType)), symbolMap("f_in)"), IntType))
    rels += ((Function(IntType, Function(IntType, IntType)), symbolMap("f_out)"), Function(IntType, IntType)))
    rels += ((Function(IntType, IntType), symbolMap("f_out("), Function(IntType, Function(IntType, IntType))))
    types += Function(IntType, Function(IntType, IntType))

   

    val typesArray = types.to(ArrayBuffer)
    val reverseTypesMap: MutMap[SimpleType, Int] = typesArray.zipWithIndex.to(MutMap)


    

    for (N <- Seq("R","S")){
      val N_sym = symbolMap(N)
      val N_sym_opp = symbolMap(opp(N))
      rules_2 += ((N_sym,N_sym, N_sym))
      rules_1 += ((N_sym,symbolMap(termSym(N))))
      rules_3 += ((N_sym,symbolMap("f_out("), N_sym, symbolMap("f_out)")))
      // val f_outN = symbolMap.size
      // symbolMap += ("f_out("+N -> f_outN)
      // rules_2 += ((f_outN, symbolMap("f_out("), N_sym))
      // rules_2 += ((N_sym, f_outN, symbolMap("f_out)")))
      rules_3 += ((N_sym,symbolMap("f_in("), N_sym_opp, symbolMap("f_in)")))
      // val f_inN = symbolMap.size
      // symbolMap += (opp(N)+"f_in)" -> f_inN)
      // rules_2 += ((f_inN, N_sym_opp,symbolMap("f_in)")))
      // rules_2 += ((N_sym, symbolMap("f_in("), f_inN))
      // symbolMap += ("f_in("+N -> f_inN)
      // rules_2 += ((f_inN, symbolMap("f_in("), N_sym_opp))
      // rules_2 += ((N_sym, f_inN, symbolMap("f_in)")))

      for (n<-fieldSet){
        rules_3 += ((N_sym,symbolMap("rec_"+n+"("), N_sym, symbolMap("rec_"+n+")")))
        // val rec_N = symbolMap.size
        // symbolMap += ("rec_"+n+"("+N -> rec_N)
        // rules_2 += ((rec_N, symbolMap("rec_"+n+"("), N_sym))
        // rules_2 += ((N_sym, rec_N, symbolMap("rec_"+n+")")))

      }
    }

    // convert rules_3 into rules_2
    val NonTermSyms = MutSet[String]("S","R")
    for (rule_3<- rules_3){
      val (sym_A, sym_B1, sym_B2, sym_B3) = rule_3
      val current_N = symbolMap.size
      val sym_B1_name = symbolMap.find(_._2 == sym_B1).map(_._1).getOrElse(s"unknown_symbol_$sym_B1")
      val sym_B2_name = symbolMap.find(_._2 == sym_B2).map(_._1).getOrElse(s"unknown_symbol_$sym_B2")
      symbolMap += ( (sym_B1_name+sym_B2_name) -> current_N)
      NonTermSyms += (sym_B1_name+sym_B2_name)
      rules_2 += ((current_N, sym_B1, sym_B2))
      rules_2 += ((sym_A, current_N, sym_B3))


    }

    // for each rule, add the corresponding polymorphic rule
    val poly_symbolMap = MutMap.empty[String,Int]
    var i = 0
    val original_rules_2 = rules_2.clone()
    val original_rules_3 = rules_3.clone()
    val original_symbolMap = symbolMap.clone()
    for (polyRel<-polyRels){
      val symMapSize = symbolMap.size
      symbolMap += ("poly_epsilon_"+i)->symMapSize
      symbolMap += ("poly_delta_"+i)->(symMapSize+1)
      rels += ((polyRel._1,symMapSize,polyRel._2 ))
      
      rels += ((polyRel._2,symMapSize+1,polyRel._1 ))

      val current_symMap_size = symbolMap.size
      for ((symName,j)<- original_symbolMap){
      
        poly_symbolMap += (symName+"_poly_open_"+i)->(current_symMap_size+j*2)
        poly_symbolMap += (symName+"_poly_close_"+i)->(current_symMap_size+j*2+1)
        rules_2 += ((current_symMap_size+j*2, j, symMapSize), (current_symMap_size+j*2, symMapSize, j))
        rules_2 += ((current_symMap_size+j*2+1, j, symMapSize+1), (current_symMap_size+j*2+1, symMapSize+1, j))
        // rules_1 += ((j,current_symMap_size+j*2))


      }
      
      
      symbolMap ++= poly_symbolMap
      // rels += ((polyRel._1,symbolMap(("S_poly_open_"+i)),polyRel._2 ))
      // rels += ((polyRel._2,symbolMap(("S_poly_close_"+i)),polyRel._1 ))
      rels += ((polyRel._1,symbolMap(("R_poly_open_"+i)),polyRel._2 ))
      rels += ((polyRel._2,symbolMap(("R_poly_close_"+i)),polyRel._1 ))
      for ((sym_A,sym_B1,sym_B2)<-original_rules_2){
        
         val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
         val sym_B1_name = symbolMap.find(_._2 == sym_B1).map(_._1).getOrElse(s"unknown_symbol_$sym_B1")
         val sym_B2_name = symbolMap.find(_._2 == sym_B2).map(_._1).getOrElse(s"unknown_symbol_$sym_B2")
         
        //  rules_2 += ((symbolMap(sym_A_name+"_poly_open_"+i),sym_B1, symbolMap(sym_B2_name+"_poly_open_"+i)))
         rules_2 += ((sym_A,symbolMap(sym_B1_name+"_poly_open_"+i), symbolMap(sym_B2_name+"_poly_close_"+i)))
        //  rules_2 += ((symbolMap(sym_A_name+"_poly_open_"+i),symbolMap(sym_B1_name+"_poly_open_"+i), sym_B2))
      }
      
     

      // for ((sym_A, sym_B1, sym_B2, sym_B3) <- original_rules_3){
      //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
      //   val sym_B1_name = symbolMap.find(_._2 == sym_B1).map(_._1).getOrElse(s"unknown_symbol_$sym_B1")
      //   val sym_B2_name = symbolMap.find(_._2 == sym_B2).map(_._1).getOrElse(s"unknown_symbol_$sym_B2")
      //   val sym_B3_name = symbolMap.find(_._2 == sym_B3).map(_._1).getOrElse(s"unknown_symbol_$sym_B3")
      //   // rules_3 += ((symbolMap(sym_A_name+"_poly_open_"+i),symbolMap(sym_B1_name+"_poly_open_"+i), sym_B2, sym_B3))
      //   // rules_3 += ((sym_A,symbolMap(sym_B1_name+"_poly_open_"+i), symbolMap(sym_B2_name+"_poly_close_"+i), sym_B3))
      //   // rules_3 += ((symbolMap(sym_A_name+"_poly_open_"+i),symbolMap(sym_B1_name+"_poly_open_"+i), symbolMap(sym_B2_name+"_poly_open_"+i), symbolMap(sym_B3_name+"_poly_close_"+i)))
      //   // rules_3 += ((sym_A,symbolMap(sym_B1_name+"_poly_open_"+i),sym_B2 , symbolMap(sym_B3_name+"_poly_close_"+i)))
      //   // rules_3 += ((symbolMap(sym_A_name+"_poly_open_"+i),sym_B1, symbolMap(sym_B2_name+"_poly_open_"+i),sym_B3))
      //   rules_3 += ((sym_A, sym_B1, symbolMap(sym_B2_name+"_poly_open_"+i), symbolMap(sym_B3_name+"_poly_close_"+i)))
      //   rules_3 += ((symbolMap(sym_A_name+"_poly_open_"+i),sym_B1,sym_B2, symbolMap(sym_B3_name+"_poly_open_"+i)))
      // }

     
      i += 1

    }

    val num_inst = i
    // generate all possible permutations of num_inst
    val numbers = (0 until num_inst).toList
    
    // Get all possible lengths (from 1 to n)
    val perms = (1 to num_inst).flatMap { length =>
      // Get all combinations of given length
      numbers.combinations(length).flatMap { combo =>
        // Get all permutations of each combination
        combo.permutations.toList
      }.toList
    }.toList

    val num_perms = perms.size
    var curMapSize = symbolMap.size
    for (nonTermSym <- NonTermSyms){
      for (i <- 0 until num_perms){
        val perm = perms(i)
        if (perm.size!=1) {
          
          symbolMap+= (nonTermSym + "_poly_open_path_" +i)-> curMapSize
          curMapSize += 1
        }

      }
    }

    for  ((sym_A,sym_B1,sym_B2)<-original_rules_2){
         val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
         val sym_B1_name = symbolMap.find(_._2 == sym_B1).map(_._1).getOrElse(s"unknown_symbol_$sym_B1")
         val sym_B2_name = symbolMap.find(_._2 == sym_B2).map(_._1).getOrElse(s"unknown_symbol_$sym_B2")
          var num_pos_perms = 0
         if (NonTermSyms.contains(sym_A_name))  num_pos_perms = num_perms
         else num_pos_perms = num_inst

          for (i <- 0 until num_pos_perms){

            val perm = perms(i)
            val perm_size = perm.size
            // if (perm.size!=1) {
              for (cut<-0 to perm_size){
                val afterCut = perm.slice(cut, perm_size)
                val afterCutSize = perm_size - cut
                var lhs_name=""
                var rhs_name=""
                var valid = true
                if (cut == 0) lhs_name = sym_B1_name
                else if (cut == 1) lhs_name = sym_B1_name + "_poly_open_"+perm(0)
                else{
                  val beforeCut = perm.slice(0, cut)
                  val beforeCutIndex = perms.indexOf(beforeCut)
                  lhs_name = sym_B1_name + "_poly_open_path_"+beforeCutIndex
                  if (!NonTermSyms.contains(sym_B1_name)) valid = false
                }

                if (afterCutSize == 0) rhs_name = sym_B2_name
                else if (afterCutSize == 1) rhs_name = sym_B2_name + "_poly_open_"+perm.last
                else {
                  val afterCutIndex = perms.indexOf(afterCut)
                  rhs_name = sym_B2_name + "_poly_open_path_"+afterCutIndex
                  if (!NonTermSyms.contains(sym_B2_name)) valid = false
                }
                if (valid)
                {
                  var sym_A_poly_name = ""
                  if (perm_size==1) sym_A_poly_name = sym_A_name+"_poly_open_"+perm(0)
                  else sym_A_poly_name = sym_A_name+"_poly_open_path_"+i
                  rules_2 += ((symbolMap(sym_A_poly_name),symbolMap(lhs_name), symbolMap(rhs_name)))
                }

              }
              for (j <- 0 until num_inst){
                if (!perm.contains(j)){
                  val newPerm = perm :+ j
                  val index = perms.indexOf(newPerm)
                  var sym_A_poly_name = ""
                  if (perm_size==1) sym_A_poly_name = sym_A_name+"_poly_open_"+perm(0)
                  else sym_A_poly_name = sym_A_name+"_poly_open_path_"+i

                  if (NonTermSyms.contains(sym_B1_name))rules_2 += ((symbolMap(sym_A_poly_name),symbolMap(sym_B1_name+"_poly_open_path_"+index), symbolMap(sym_B2_name+"_poly_close_"+j)))
                }
              }
            // }

          }
         
         
        //  rules_2 += ((symbolMap(sym_A_name+"_poly_open_"+i),symbolMap(sym_B1_name+"_poly_open_"+i), sym_B2))
      }
  
    var num_syms = symbolMap.size
    val num_types = types.size


    
    // initialize  a stack
    val W = Stack[(Int, Int, Int)]()
    val H_s = MutSet[(Int, Int, Int)]()
    val cols = ArrayBuffer.fill(num_types, num_syms*3)(new FastSet(num_types))
    val rows = ArrayBuffer.fill(num_types, num_syms*3)(new FastSet(num_types))
    // construct the adjacency matrix
    
    // println("typesArray: %s\n", typesArray)
    /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  

    def cflConstrain(i:Int, j: Int, sub: Boolean, poly: Boolean) = {
    
    if (i!=j){
          // if i is variable
          // if (typesArray(i).isInstanceOf[Variable]&& !typesArray(j).isInstanceOf[Variable]){
          if (!typesArray(i).isInstanceOf[Variable] && !typesArray(j).isInstanceOf[Variable]){
            if (!(typesArray(i).isInstanceOf[Function] && typesArray(j).isInstanceOf[Function])){
              if (!(typesArray(i).isInstanceOf[Record] && typesArray(j).isInstanceOf[Record])){
                err(s"cannot constrain ${typesArray(i).show} <: ${typesArray(j).show}")
              }
            }
          }

          // Check for missing field for record types
          if (typesArray(i).isInstanceOf[Record] && typesArray(j).isInstanceOf[Record]){
            val i_fields = typesArray(i).asInstanceOf[Record].fields
            val j_fields = typesArray(j).asInstanceOf[Record].fields
            for (j_field <- j_fields){
              // if not second entry of i_fields contains j_field._1
              if (!i_fields.exists(_._1 == j_field._1)){
                err(s"missing field: ${j_field._1} in ${typesArray(i).show}")
              }
            }
          }

          if (typesArray(i).isInstanceOf[Variable]){
            // val v = typesArray(i).asInstanceOf[Variable]
            // val ty = typesArray(j)
            if (sub)
            typesArray(i).asInstanceOf[Variable].upperBounds ::= typesArray(j)
            else{
              if (poly || !typesArray(j).isInstanceOf[Variable]){
                typesArray(i).asInstanceOf[Variable].lowerBounds ::= typesArray(j)
              }
              // if (typesArray(j).isInstanceOf[Variable]){
              //   if (!typesArray(j).asInstanceOf[Variable].upperBounds.contains(typesArray(i))){
              //     typesArray(i).asInstanceOf[Variable].lowerBounds ::= typesArray(j)
              //   }

              // }
            }
            
          }
          // if j is variable
          // if (typesArray(j).isInstanceOf[Variable] && !typesArray(i).isInstanceOf[Variable]){
          //   // val v = typesArray(j).asInstanceOf[Variable]
          //   // val ty = typesArray(i)
          //   if (sub)
          //   typesArray(j).asInstanceOf[Variable].lowerBounds ::= typesArray(i)
          //   else 
          //     typesArray(j).asInstanceOf[Variable].upperBounds ::= typesArray(i)
          //   // W.push((j, symbolMap("rev"), i))
          //   //   H_s += ((j, symbolMap("rev"), i))
          //   //   cols(i)(symbolMap("rev")).insert(j)
          //   //   rows(j)(symbolMap("rev")).insert(i)
            
          // }
        }

      
  }

   
    rels.foreach{case (lhs, sym, rhs) =>
      val i = reverseTypesMap(lhs)
      // println("lhs: %s\n", lhs)
      // println("sym: ", symbolMap.find(_._2 == sym).map(_._1).getOrElse(s"unknown_symbol_$sym"))
      // println("rhs: %s\n", rhs)
      val j = reverseTypesMap(rhs)
      if (i==(-1)){
        println("not found i", lhs)
      }
      if (j==(-1)){
        println("not found j", lhs)

      }
      
        W.push((i, sym, j))
        cols(j)(sym).insert(i)
        rows(i)(sym).insert(j)
      // }
      
    }
   

    // typesArray.zipWithIndex.foreach{case (ty, i) =>
    //   W.push((i, symbolMap("S"), i))
    //   cols(i)(symbolMap("S")).insert(i)
    //   rows(i)(symbolMap("S")).insert(i)
    // }

    H_s ++= W


    

    

    // println(W)
    // for ((i, sym, j) <- W){
    //   val sym_name = symbolMap.find(_._2 == sym).map(_._1).getOrElse(s"unknown_symbol_$sym")
    //   println("sym_name: ", sym_name, "i: ", "j:", j)
    // }

    while (W.nonEmpty){
      val (u,sym_B,v) = W.pop()
      val sym_B_name = symbolMap.find(_._2 == sym_B).map(_._1).getOrElse(s"unknown_symbol_$sym_B")
      // println( sym_B_name,  u,  v)

      rules_1.foreach{case (sym_A, sym_B1) =>
        if (sym_B1==sym_B) {
          if (sym_A==symbolMap("S")) cflConstrain(u, v, true, false)
          W.push((u, sym_A, v))
          val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
          H_s += ((u, sym_A, v))
          cols(v)(sym_A).insert(u)
          rows(u)(sym_A).insert(v)
            
        }

      }

      rules_2.foreach{case (sym_A, sym_B1, sym_B2) =>
        if (sym_B2==sym_B) {
          for (w <- cols(u)(sym_B1).diff(cols(v)(sym_A))){
            if (sym_A==symbolMap("S"))  cflConstrain(w, v, true, false)
            // else{
            //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
            //   if (sym_A_name.startsWith("S_poly_open")){
            //     cflConstrain(w, v, true,true)
            //   }
            // }
            if (sym_A==symbolMap("R")) cflConstrain(w, v, false,false)
            // else{
            //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
            //   if (sym_A_name.startsWith("R_poly_open")){
            //     cflConstrain(w, v, false,true)
            //   }
            // }
                

            W.push((w, sym_A, v))
            H_s += ((w, sym_A, v))
            cols(v)(sym_A).insert(w)
            rows(w)(sym_A).insert(v)
              
            
            

          }
        }

      }

      rules_2.foreach{case (sym_A, sym_B1, sym_B2) =>
        if (sym_B1==sym_B) {
          for (w <- rows(v)(sym_B2).diff(rows(u)(sym_A))){
            if (sym_A==symbolMap("S")) cflConstrain(u, w, true,false)
            // else{
            //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
            //   // if (sym_A_name.startsWith("S_poly_open")){
            //   //   cflConstrain(u, w, true, true)
            //   // }
            // }
            if (sym_A==symbolMap("R")) cflConstrain(u, w, false, false)
            // else{
            //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
            //   // if (sym_A_name.startsWith("R_poly_open")){
            //   //   cflConstrain(u, w, false,true)
            //   // }
            // }
            
            W.push((u, sym_A, w))
            H_s += ((u, sym_A, w))
            cols(w)(sym_A).insert(u)
            rows(u)(sym_A).insert(w)
              
            
            
          }
        }

      }

      
    }

    // for ((u,sym_A,v) <- H_s){
    //   val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
    //   println(typesArray(u), sym_A_name, typesArray(v))
    // }



    // handle polymorphic types
    // loop through SymbolMap
    // val PolySymMap = MutMap.empty[String, Int]
    // // val num_syms = symbolMap.size
    // val originalNumSyms = symbolMap.size
    
    // for ((sym, i) <- symbolMap){
    //   PolySymMap += (sym+"_poly" -> (i+num_syms))
    // }
    // num_syms += num_syms
    // symbolMap ++= PolySymMap
    // symbolMap+= ("inst_to_poly" -> (num_syms+1))
    // symbolMap+= ("poly_to_inst" -> (num_syms+2))
    // num_syms += 2

    // for ((sym, i) <- symbolMap){
    //   if (i<originalNumSyms){
    //     rules_2 += ((i, symbolMap("inst_to_poly"), i+originalNumSyms))
    //     rules_2 += ((symbolMap("inst_to_poly"), i , i+originalNumSyms))
    //     rules_2 += ((i, symbolMap("inst_to_poly"), i))
    //     rules_2 += ((symbolMap("inst_to_poly"), i, i))
    //     rules_2 += ((i+originalNumSyms, symbolMap("poly_to_inst"), i))

    //   }
      
    // }




    ty
    
  }

  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  // def constrain(lhs: SimpleType, rhs: SimpleType)
  //     // we need a cache to remember the subtyping tests in process; we also make the cache remember
  //     // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm)
  //     (implicit cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty)
  // : Unit = {
  //   if (lhs is rhs) return
  //   val lhs_rhs = lhs -> rhs
  //   lhs_rhs match {
  //     // There is no need to remember the subtyping tests performed that did not involve
  //     // type variables, as type variables will necessary be part of any possible cycles.
  //     // Since these types form regular trees, there will necessarily be a point where a
  //     // variable part of a cycle will be matched against the same type periodically.
  //     case (_: Variable, _) | (_, _: Variable) =>
  //       if (cache(lhs_rhs)) return
  //       cache += lhs_rhs
  //     case _ => ()
  //   }
  //   lhs_rhs match {
  //     case (Function(l0, r0), Function(l1, r1)) =>
  //       constrain(l1, l0)
  //       constrain(r0, r1)
  //     case (Record(fs0), Record(fs1)) =>
  //       fs1.foreach { case (n1, t1) =>
  //         fs0.find(_._1 === n1).fold(
  //           err(s"missing field: $n1 in ${lhs.show}")
  //         ) { case (n0, t0) => constrain(t0, t1) }
  //       }
  //     case (lhs: Variable, rhs) if rhs.level <= lhs.level =>
  //       lhs.upperBounds ::= rhs
  //       lhs.lowerBounds.foreach(constrain(_, rhs))
  //     case (lhs, rhs: Variable) if lhs.level <= rhs.level =>
  //       rhs.lowerBounds ::= lhs
  //       rhs.upperBounds.foreach(constrain(lhs, _))
  //     case (_: Variable, rhs0) =>
  //       val rhs = extrude(rhs0, false)(lhs.level, MutMap.empty)
  //       constrain(lhs, rhs)
  //     case (lhs0, _: Variable) =>
  //       val lhs = extrude(lhs0, true)(rhs.level, MutMap.empty)
  //       constrain(lhs, rhs)
  //     case _ => err(s"cannot constrain ${lhs.show} <: ${rhs.show}")
  //   }
  // }
  
  type PolarVariable = (Variable, Boolean)
  
  
  
  def err(msg: String): Nothing = throw TypeError(msg)
  
  private var freshCount = 0
  def freshVar(implicit lvl: Int=0): Variable = new Variable(lvl, Nil, Nil)
  
  def freshenAbove(lim: Int, ty: SimpleType,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)])(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[Variable, Variable]
    val freshened_fun = MutMap.empty[Function, Function]
    def freshen(ty: SimpleType,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)]): SimpleType = if (ty.level <= lim) ty else ty match {
      case tv: Variable =>
        freshened.get(tv) match {
          case Some(tv) => tv
          case None =>
            val v = freshVar
            freshened += tv -> v
            types += v

            // v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
            // v.upperBounds = tv.upperBounds.mapConserve(freshen)
            //  ^ the above are more efficient, but they lead to a different order
            //    of fresh variable creations, which leads to some types not being
            //    simplified the same when put into the RHS of a let binding...
            // v.lowerBounds = tv.lowerBounds.reverse.map(freshen(_, rels, types)).reverse
            // v.upperBounds = tv.upperBounds.reverse.map(freshen(_, rels, types)).reverse
            // v.lowerBounds.foreach(lb => {
            //   rels += ((v, symbolMap("rev"), lb))
            // })
            // v.upperBounds.foreach(ub => {
            //   rels += ((v, symbolMap("empty"), ub))
            // })

            val relsSeq = rels.toSeq
            val relsToAdd = MutSet[(SimpleType, Int, SimpleType)]()
            for (rel <- relsSeq.reverse){
              
              if (rel._1==tv){
                relsToAdd += ((v, rel._2, freshen(rel._3, rels, types)))
              }
              if (rel._3==tv){
                relsToAdd += (( freshen(rel._1, rels, types), rel._2, v))
              }
            }
            rels ++= relsToAdd.toSeq.reverse
            v
        }
      case Function(l, r) => {
        freshened_fun.get(Function(l, r)) match {
          case Some(fun_ty) => fun_ty
          case None =>
            val freshend_l = freshen(l,rels, types)
            val freshend_r = freshen(r,rels, types)
            val fun_ty = Function(freshend_l,freshend_r)
            freshened_fun += Function(l, r) -> fun_ty
            types += fun_ty
            for (rel <- rels){
              if (rel._1==Function(l, r)){
                rels += ((fun_ty, rel._2, freshen(rel._3, rels, types)))
              }
              if (rel._3==ty){
                rels += (( freshen(rel._1, rels, types), rel._2, fun_ty))
              }
            }
            fun_ty
          }
        
      }
      case Record(fs) =>{
        val fs_ty = fs.map(ft => ft._1 -> freshen(ft._2,rels, types))
        val rec_ty = Record(fs_ty)
        fs_ty.foreach { case (n, t) => 
          var openSym = 0
          var closeSym = 0
          if (symbolMap.contains("rec_" + n + "(")) 
          {
            openSym = symbolMap("rec_" + n + "(")
            closeSym = symbolMap("rec_" + n + ")")
          }
          else
          {
            openSym = symbolMap.size
            symbolMap += ("rec_"+n+"(" -> openSym)
            closeSym = symbolMap.size
            symbolMap += ("rec_"+n+")" -> closeSym)
          }
          
          rels += ((t, openSym, rec_ty))
          rels += ((rec_ty, closeSym, t))
          types += t
          
          fieldSet += n 
        }


        types += rec_ty
        rec_ty
      } 
      case Primitive(_) => ty
    }
    freshen(ty,rels, types)
  }
  
  def polyInstantiate( poly_body: SimpleType, mono_types: Set[(SimpleType)])(implicit rels: MutSet[(SimpleType, Int, SimpleType)], types: MutSet[(SimpleType)], polyRels:MutSet[(SimpleType,SimpleType)]) : SimpleType={
    val copied = MutMap.empty[Variable, Variable]
    val copied_fun = MutMap.empty[Function, Function]
    val copied_recs = MutMap.empty[Record, Record]
    // val copiedFunc = MutMap.empty[Function, Function]
    // for (ty <- types) {
    //   if (ty.isInstanceOf[Variable]) {
    //     val v = ty.asInstanceOf[Variable]
    //     copied += v -> v
    //   }
    // }
    def copyBody(ty: SimpleType): SimpleType = {
      println("copying body", ty)
      var copy = false
    val inst_ty =ty match {
      case tv: Variable =>
        copied.get(tv) match {
          case Some(tv) => {
            // copy = false
            tv
          }
          case None =>
            if (mono_types.contains(ty)) return ty
            else{
              val v = freshVar
              copied += tv -> v
              types += v
              copy = true
              v
            }
        }

      case Function(l, r) =>

        copied_fun.get(Function(l, r)) match {
          case Some(fun_ty) => fun_ty
          case None =>
            val l1 = copyBody(l)
            val r1 = copyBody(r)
            types += l1
            types += r1
            val inst_body = Function(l1,r1)
            rels += ((l1, symbolMap("f_in("), inst_body))
            rels += ((inst_body, symbolMap("f_in)"), l1))
            rels += ((r1, symbolMap("f_out("), inst_body))
            rels += ((inst_body, symbolMap("f_out)"), r1))
            if (l1!= l || r1 != r) {
              copy = true
              copied_fun += Function(l, r) -> inst_body
              types += inst_body
            }
            
            inst_body
          }
      case Record(fs) =>
        copied_recs.get(Record(fs)) match {
          case Some(rec_ty) => rec_ty
          case None =>
            val fs_ty = fs.map { case (n, t) =>{
            val copyBody_t= copyBody(t)
            if (copyBody_t != t) copy = true
            n -> copyBody_t
          } }
          val inst_body = Record(fs_ty)
          fs_ty.foreach { case (n, t) => 
            var openSym = 0
            var closeSym = 0
            if (symbolMap.contains("rec_" + n + "(")) 
            {
              openSym = symbolMap("rec_" + n + "(")
              closeSym = symbolMap("rec_" + n + ")")
            }
            else
            {
              openSym = symbolMap.size
              symbolMap += ("rec_"+n+"(" -> openSym)
              closeSym = symbolMap.size
              symbolMap += ("rec_"+n+")" -> closeSym)
            }
            
            rels += ((t, openSym, inst_body))
            rels += ((inst_body, closeSym, t))
            types += t
            
            fieldSet += n 
          }
          types += inst_body
          if (copy) {
            copied_recs += Record(fs) -> inst_body
          }
          inst_body
        }
      case Primitive(_) => ty
    }
    if (copy){
      for ((u,sym,v) <- rels){
        // if (u==ty && mono_types.contains(v)){
        //   rels += ((inst_ty, sym, v))
        // }
        // if (v==ty && mono_types.contains(u)){
        //   rels += ((u, sym, inst_ty))
        // }
        if (u==ty ){
          rels += ((inst_ty, sym, copyBody(v)))
        }
        if (v==ty ){
          rels += ((copyBody(u), sym, inst_ty))
        }


      }
    }

    inst_ty
  }
    val tyv = copyBody(poly_body)
    polyRels+= ((tyv, poly_body))

    tyv

  }
  
  // The data types used for type inference:
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)] = MutSet.empty,types: MutSet[(SimpleType)]=MutSet.empty, polyRels: MutSet[(SimpleType,SimpleType)]=MutSet.empty[(SimpleType,SimpleType)]): SimpleType
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType, mono_types: Set[(SimpleType)]) extends TypeScheme {
    // def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)]) = freshenAbove(level, body, rels, types)
    def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)], polyRels: MutSet[(SimpleType,SimpleType)]) = polyInstantiate(body, mono_types)
    // def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)],  polyRels: MutSet[(SimpleType,SimpleType)]) = body
  }
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    def level: Int
    def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)],polyRels: MutSet[(SimpleType,SimpleType)]) = this
  }
  case class Function(lhs: SimpleType, rhs: SimpleType) extends SimpleType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
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
