package simplesub

import scala.collection.mutable
import scala.collection.mutable.Stack
import scala.collection.mutable.{Map => MutMap, Set => MutSet, BitSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import javax.management.openmbean.SimpleType
import scala.collection.mutable.ArrayBuffer
import scala.annotation.elidable

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
      PolymorphicType(0, Function(BoolType, Function(v, Function(v, v))), Set.empty[(SimpleType)], Set.empty[(SimpleType)], false)
    }
  )

  var symbolMap: MutMap[String, Int]= MutMap(
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
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins)(implicit rels: MutSet[(SimpleType, Int, SimpleType)] = MutSet.empty[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)] = MutSet.empty[(SimpleType)], polyRels: MutSet[(SimpleType, SimpleType)] = MutSet.empty[(SimpleType, SimpleType)] ): List[Either[TypeError, PolymorphicType]] ={
     
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try {
         
          val tyi = typeLetRhs(isrec, nme, rhs)(ctx, 0,rels, types, polyRels)
          val rels_clone = rels.clone()
          val constrainedType = cflReach(tyi.body, rels_clone, types, polyRels)
          val constrainedSchema = PolymorphicType(
            tyi.level, 
            constrainedType, 
            tyi.mono_types, 
            tyi.poly_vars, 
            tyi.isRec
          )
          Right(constrainedSchema)
          
        } catch {
          case err: TypeError => Left(err) }
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(0))))(rels, types, polyRels)
      case Nil => Nil
    }
  }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): (SimpleType) = {
    val (tyi, rels, types, polyRels) = typeTerm(term)(ctx, lvl)
    cflReach(tyi, rels, types, polyRels)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)(implicit ctx: Ctx, lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)],polyRels: MutSet[(SimpleType,SimpleType)]): PolymorphicType = {
    val mono_types = types.toSet[(SimpleType)]
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
    } else {
      val (rhsType, rhsRels, rhsTypes, rhsPolyRels) = typeTerm(rhs)(ctx, lvl + 1, rels, types, polyRels)
      rels ++= rhsRels
      types ++= rhsTypes
      polyRels ++= rhsPolyRels
      rhsType
    }
  
    types += res

    val poly_vars = MutSet.empty[SimpleType]

    for (poly_type <- types){
      if (! mono_types.contains(poly_type)){
        if (poly_type.isInstanceOf[Variable]) poly_vars += poly_type
        
      }
    }

    PolymorphicType(lvl, res, mono_types, poly_vars.toSet, isrec)
  }

 
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, lvl: Int, rels: MutSet[(SimpleType, Int, SimpleType)] = MutSet.empty[(SimpleType,Int,SimpleType)], types: MutSet[(SimpleType)]=MutSet[SimpleType](BoolType, IntType), polyRels: MutSet[(SimpleType,SimpleType)]=MutSet.empty[(SimpleType,SimpleType)]): (SimpleType, MutSet[(SimpleType, Int, SimpleType)], MutSet[(SimpleType)], MutSet[(SimpleType, SimpleType)]) = {
    lazy val res = freshVar
    
    
    val tyv = term match {
      case Var(name) =>{
        if (name == "if") {
          val mono_types = types.toSet[(SimpleType)] 
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

          PolymorphicType(0, Function(BoolType, Function(v, Function(v, v))), mono_types, Set.empty[(SimpleType)], false).instantiate
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
        val fs_ty = fs.map { case (n, t) => 
          val (fieldType, fieldRels, fieldTypes, fieldPolyRels) = typeTerm(t)
          rels ++= fieldRels
          types ++= fieldTypes
          polyRels ++= fieldPolyRels
          (n, fieldType)
        }
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
        // Make sure to use the result of typeTerm properly and merge all relations
        val (bodyType, bodyRels, bodyTypes, bodyPolyRels) = typeTerm(bod)(ctx + (nme -> n_ty), lvl, rels, types, polyRels)
        rels ++= bodyRels
        types ++= bodyTypes
        polyRels ++= bodyPolyRels
        bodyType

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
      rules_3 += ((N_sym,symbolMap("f_in("), N_sym_opp, symbolMap("f_in)")))
      for (n<-fieldSet){
        rules_3 += ((N_sym,symbolMap("rec_"+n+"("), N_sym, symbolMap("rec_"+n+")")))

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
    val symbolMap_backup = symbolMap.clone()
    val rels_backup = rels.clone()
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
      }
      symbolMap ++= poly_symbolMap
      rels += ((polyRel._1,symbolMap(("R_poly_open_"+i)),polyRel._2 ))
      rels += ((polyRel._2,symbolMap(("R_poly_close_"+i)),polyRel._1 ))
      for ((sym_A,sym_B1,sym_B2)<-original_rules_2){
         val sym_A_name = symbolMap.find(_._2 == sym_A).map(_._1).getOrElse(s"unknown_symbol_$sym_A")
         val sym_B1_name = symbolMap.find(_._2 == sym_B1).map(_._1).getOrElse(s"unknown_symbol_$sym_B1")
         val sym_B2_name = symbolMap.find(_._2 == sym_B2).map(_._1).getOrElse(s"unknown_symbol_$sym_B2")
         rules_2 += ((sym_A,symbolMap(sym_B1_name+"_poly_open_"+i), symbolMap(sym_B2_name+"_poly_close_"+i)))
      }     
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
          }
      }

    var num_syms = symbolMap.size
    val num_types = types.size

    val W = Stack[(Int, Int, Int)]()
    val H_s = MutSet[(Int, Int, Int)]()
    val cols = ArrayBuffer.fill(num_types, num_syms*3)(new BitSet(num_types))
    val rows = ArrayBuffer.fill(num_types, num_syms*3)(new BitSet(num_types))
   
    def cflConstrain(i:Int, j: Int, sub: Boolean, poly: Boolean) = {
    
    if (i!=j){
          (typesArray(i), typesArray(j)) match {
          case (r1: Record, r2: Record) =>
            val i_fields = r1.fields
            val j_fields = r2.fields
            if (sub) {
              for (j_field <- j_fields) {
                if (!i_fields.exists(_._1 == j_field._1)) {
                  err(s"missing field: ${j_field._1} in ${r1.show}")
                }
              }
            } else {
              for (i_field <- i_fields) {
                if (!j_fields.exists(_._1 == i_field._1)) {
                  err(s"missing field: ${i_field._1} in ${r2.show}")
                }
              }
            }
          // Case where i is a Variable
          case (v: Variable, tj) =>
            if (sub) {
              v.upperBounds ::= tj
            } else {
              tj match {
                case _: Variable => // Do nothing
                case _ => v.lowerBounds ::= tj
              }
            }
          case (ti, v: Variable) => // do nothing, valid case
          case  (f1: Function, v: Function) =>  //do nothing, valid case
          case (ti,tj) => err(s"cannot constrain ${ti.show} <: ${tj.show}")
        }
        }
  }

    rels.foreach{case (lhs, sym, rhs) =>
      val i = typesArray.indexOf(lhs)
      val j = typesArray.indexOf(rhs)
      if (i==(-1)){
        println("not found i", lhs)
      }
      if (j==(-1)){
        println("not found j", lhs)
      }
      
        W.push((i, sym, j))
        cols(j)(sym) += i
        rows(i)(sym) += j
    }
   
    H_s ++= W

    while (W.nonEmpty){
      val (u,sym_B,v) = W.pop()
      val sym_B_name = symbolMap.find(_._2 == sym_B).map(_._1).getOrElse(s"unknown_symbol_$sym_B")

      rules_1.foreach{case (sym_A, sym_B1) =>
        if (sym_B1==sym_B) {
          if (sym_A==symbolMap("S")) cflConstrain(u, v, true, false)
          if (sym_A==symbolMap("R")) cflConstrain(u, v, false, false)
          W.push((u, sym_A, v))
          H_s += ((u, sym_A, v))
          cols(v)(sym_A) += u
          rows(u)(sym_A) += v
        }
      }

      rules_2.foreach{case (sym_A, sym_B1, sym_B2) =>
        if (sym_B2==sym_B) {
          for (w <- cols(u)(sym_B1).diff(cols(v)(sym_A))){
            if (sym_A==symbolMap("S"))  cflConstrain(w, v, true, false)
            if (sym_A==symbolMap("R")) cflConstrain(w, v, false,false)
            W.push((w, sym_A, v))
            H_s += ((w, sym_A, v))
            cols(v)(sym_A) += w
            rows(w)(sym_A) += v
          }
        }
        if (sym_B1==sym_B) {
          for (w <- rows(v)(sym_B2).diff(rows(u)(sym_A))){
            if (sym_A==symbolMap("S")) cflConstrain(u, w, true,false)
            if (sym_A==symbolMap("R")) cflConstrain(u, w, false, false)
            
            W.push((u, sym_A, w))
            H_s += ((u, sym_A, w))
            cols(w)(sym_A) += u
            rows(u)(sym_A) += w
          }
        }
      }
      }
    ty
  }
  
  type PolarVariable = (Variable, Boolean)
  
  
  
  def err(msg: String): Nothing = throw TypeError(msg)
  
  private var freshCount = 0
  def freshVar(implicit lvl: Int=0): Variable = new Variable(lvl, Nil, Nil)
  
  
  def polyInstantiate( poly_body: SimpleType, mono_types: Set[(SimpleType)], poly_vars: Set[(SimpleType)], isrec: Boolean)(implicit rels: MutSet[(SimpleType, Int, SimpleType)], types: MutSet[(SimpleType)], polyRels: MutSet[(SimpleType,SimpleType)]) : SimpleType={
    val copied_poly_vars = MutMap.empty[Variable, Variable]
    val copied = MutMap.empty[Variable, Variable]
    val copied_fun = MutMap.empty[Function, Function]
    val copied_recs = MutMap.empty[Record, Record]
    
    var caller = poly_body
    val new_rels = MutSet.empty[(SimpleType, Int, SimpleType)]
    def copyBody(ty: SimpleType): SimpleType = {
      var copy = false
      val prev_caller = caller
      caller = ty
    val inst_ty = ty match {
      case tv: Variable =>
        copied.get(tv) match {
          case Some(tv) => {
            tv
          }
          case None =>
            if (mono_types.contains(ty)) return ty
            else{
              copied_poly_vars.get(tv) match {
                case Some(tv1) => {
                  copied += tv -> tv1
                  copy = true
                  tv1
                }
                case None =>
                  val v = freshVar
                  copied += tv -> v
                  types += v
                  copy = true
                  v
              }
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
        if (u==ty ){
          val copied_v = copyBody(v)
          new_rels += ((inst_ty, sym, copied_v))
        }
        if (v==ty ){
          val copied_u = copyBody(u)
          if (copied_u == u){
            new_rels += ((copied_u, sym, inst_ty))
          }
        }


      }
      
    }

    inst_ty
  }
    
    val tyv = copyBody(poly_body)

    polyRels+= ((tyv, poly_body))
    

    rels ++= new_rels
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
  case class PolymorphicType(level: Int, body: SimpleType, mono_types: Set[(SimpleType)], poly_vars: Set[(SimpleType)], isrec: Boolean) extends TypeScheme {
    // def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)]) = freshenAbove(level, body, rels, types)

    def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)], polyRels: MutSet[(SimpleType,SimpleType)]) = polyInstantiate(body, mono_types, poly_vars, isrec)
    // def instantiate(implicit lvl: Int,rels: MutSet[(SimpleType, Int, SimpleType)],types: MutSet[(SimpleType)],  polyRels: MutSet[(SimpleType,SimpleType)]) = body

    def isRec = isrec
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