structure botworld_quoteLib = struct

open preamble botworldTheory botworld_dataTheory
open basicReflectionLib holSyntaxSyntax listSyntax

val _ = Parse.temp_bring_to_front_overload","{Name=",",Thy="pair"}

(* TODO: move to preamble *)
fun term_rewrite eqs tm =
  let
    fun match_and_subst tm eq =
      let val (s1,s2) = match_term (lhs eq) tm in mk_thm([],subst s1 (inst s2 eq)) end
    fun rw1 tm = tryfind (match_and_subst tm) eqs
  in tm |> QCONV (DEPTH_CONV rw1) |> concl |> rhs end
(* -- *)

(* TODO: move? *)
fun assoc [] k = NONE
  | assoc ((k',v)::ls) k = if k = k' then SOME v else assoc ls k
(* -- *)

val _ = Parse.temp_overload_on("Num", ``Tyapp(strlit"num")[]``)
val _ = Parse.temp_overload_on("Level", ``Tyapp(strlit"level")[]``)
val _ = Parse.temp_overload_on("Pair", ``λt1 t2. Tyapp(strlit"prod")[t1;t2]``)

(*
quote_foo : (('a -> term) # type) -> (('a foo -> term) # type)
quote_bar : ((('a -> term) # type), (('b -> term) # type)) -> ((('a, 'b) bar -> term) # type)
*)

fun quoter table (current_quote_ty,current_ty) ty =
  let
    val (tyop,argl) = dest_type ty
    fun get_qt a =
      if is_vartype a then mk_pair (valOf (assoc table a))
      else if a = current_ty then current_quote_ty
      else rand(quoter table (current_quote_ty,current_ty) a)
    val qts = map get_qt argl
    val args = list_mk_pair qts handle HOL_ERR _ => T
    val quote_ty = "quote_"^(fst(dest_type ty))
    val q = if null argl then [QUOTE("FST "^quote_ty)]
            else [QUOTE("FST ("^quote_ty),ANTIQUOTE args,QUOTE")"]
  in
    Term q
  end

fun quote_type_to_deep table ty =
  case type_view ty of
    Tyvar name =>
      (case assoc table ty of
         SOME (_,t) => t
       | NONE => mk_Tyvar (string_to_inner (tyvar_to_deep name)))
  | Tyapp (thy,name,args) =>
      mk_Tyapp(string_to_inner name, mk_list(List.map (quote_type_to_deep table) args, type_ty))

(*
val (type_being_defined,quote_ty_aux) = (ty,quote_ty_aux_applied)
*)

fun quote_term_to_deep table current_quote (type_being_defined,quote_ty_aux) =
  let
    val type_to_deep = quote_type_to_deep table
    fun ttd tm =
      case dest_term tm of
        VAR(x,ty) =>
        if ty = type_being_defined then mk_comb(quote_ty_aux,tm)
        else
          (case assoc table ty of
             SOME (q,_) => mk_comb(q,tm)
           | NONE => mk_comb(quoter table (current_quote,type_being_defined) ty, tm))
      | CONST {Name,Thy,Ty} => mk_Const(string_to_inner Name, type_to_deep Ty)
      | COMB (f,x) => mk_Comb(ttd f, ttd x)
      | LAMB (x,b) =>
          let
            val (x,ty) = dest_var x
          in
            mk_Abs(mk_Var(string_to_inner x, type_to_deep ty), ttd b)
          end
  in ttd end

val aux_rws = ref ([]:term list)

val mk_quote_tac = ref(NO_TAC)

(* val vnames = NONE
val ty = ``:exp`` *)

fun mk_quote vnames ty =
  let
    val tyvs = type_vars ty
    val ax = TypeBase.axiom_of ty
    val (tyname,_) = dest_type ty

    (* val branches = ax |> SPEC_ALL |> concl |> strip_exists |> #2 |> strip_conj *)
    (* val branch_eqns = map (#2 o strip_forall) branches *)
    (* val lhs_br = map lhs branch_eqns *)
    (* val rhs_br = map rhs branch_eqns *)
    (* (* next part does the wrong thing with n-ary constructors, but works fine for unary *) *)
    (* (* sometimes I miss lisp *) *)
    (* val to_quote = map (map type_of o #2 o strip_comb) lhs_br |> flatten |> mk_set *)
    (* (* figuring out what the nonidentical recursive arguments are *) *)
    (* val nonstandard = to_quote |> filter (fn t => not ((t |> dest_type |> #1) = tyname)) *)
    (* (* problems: this gives /what/ the nonstandard (first) arguments are, but not what to do with them *) *)
    (* (* TODO: *) *)
    (* (*    1) Figure out if we already have quoters for the things in nonstandard *) *)
    (* (*    2) If not, /make/ quoters for the things in nonstandard *) *)
    (* (*    3) If so, use them *) *)
    (* (*    4) If it's a variable then take an argument *) *)
    (* (*    5) Somehow unify the clauses of ax to not do this whole thing twice *) *)

    val target_ty = ax |> concl |> dest_forall |> fst |> type_of |> strip_fun |> snd
    val quote_ty_name = "quote_"^tyname
    val quote_ty_aux_name = quote_ty_name^"_aux"
    val (v,b0) = ax |> SPEC_ALL |> concl |> inst [target_ty|->holSyntaxSyntax.term_ty]
                    |> boolSyntax.dest_exists
    val b = b0 |> strip_exists |> #2 |> strip_conj |> filter (fn s => v = rator (lhs (#2 (strip_forall s))))
    val (argts,argqs) =
      case vnames of NONE =>
        (map (fn _ => genvar type_ty) tyvs,
         map (fn ty => genvar(ty --> term_ty)) tyvs)
      | SOME (qnames,tnames) =>
        (map (fn n => mk_var(n,type_ty)) tnames,
         map2 (fn n => fn ty => mk_var(n,ty --> term_ty)) qnames tyvs)
    val qts = zip argqs argts
    val argslist = map mk_pair qts
    val args = list_mk_pair argslist handle HOL_ERR _ => T
    val table = zip tyvs qts
    val quote_ty_aux = mk_var(quote_ty_aux_name,
                              if null tyvs then type_of v
                              else type_of args --> ty --> term_ty)
    val quote_ty_aux_applied = if null tyvs then quote_ty_aux else mk_comb(quote_ty_aux,args)
    val lhses = b |> map (lhs o snd o strip_forall)
                  |> map (subst [v|->quote_ty_aux_applied])
    val inner_ty = quote_type_to_deep table ty
    fun mk_rhs l =
    (*
      val l = el 3 lhses
      val tm = rand l
    *)
      quote_term_to_deep table (mk_pair(quote_ty_aux_applied, inner_ty)) (ty,quote_ty_aux_applied) (rand l)
    val eqs = map (fn l => mk_eq(l,mk_rhs l |> term_rewrite (!aux_rws))) lhses
    val aux_def = Define [ANTIQUOTE(list_mk_conj eqs)]
                  handle HOL_ERR _ => tDefine (quote_ty_name^"_def") [ANTIQUOTE(list_mk_conj eqs)] (!mk_quote_tac)
                                      before ignore (proofManagerLib.drop())
    val quote_ty = mk_var(quote_ty_name,
                              if null tyvs then
                                mk_prod(type_of quote_ty_aux,type_ty)
                              else
                              type_of args -->
                              mk_prod(type_of quote_ty_aux_applied,type_ty))
    val quote_ty_applied = if null tyvs then quote_ty else mk_comb(quote_ty,args)
    val defined_quote_ty_aux =
      aux_def |> SPEC_ALL |> CONJUNCTS |> hd |> concl |> strip_forall |> snd |> lhs |> strip_comb |> fst
    val defined_quote_ty_aux_applied =
      if null tyvs then defined_quote_ty_aux else mk_comb(defined_quote_ty_aux,args)
    val quote_ty_rhs = mk_pair(defined_quote_ty_aux_applied,
                               inner_ty)
    val q_def = Define[ANTIQUOTE(mk_eq(quote_ty_applied,quote_ty_rhs))]
  in
   (aux_def,q_def)
  end

end
