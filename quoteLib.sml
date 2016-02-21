open preamble botworldTheory botworld_dataTheory
open basicReflectionLib holSyntaxSyntax listSyntax


val _ = bring_to_front_overload","{Name=",",Thy="pair"}

val _ = Parse.overload_on("Num", ``Tyapp(strlit"num")[]``)
val _ = Parse.overload_on("Level", ``Tyapp(strlit"level")[]``)
val _ = Parse.overload_on("Pair", ``λt1 t2. Tyapp(strlit"prod")[t1;t2]``)

fun assoc [] k = NONE
  | assoc ((k',v)::ls) k = if k = k' then SOME v else assoc ls k


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

fun term_rewrite eqs tm = 
  let 
    fun match_and_subst tm eq =
      let val (s1,s2) = match_term (lhs eq) tm in mk_thm([],subst s1 (inst s2 eq)) end
    fun rw1 tm = tryfind (match_and_subst tm) eqs
  in tm |> QCONV (DEPTH_CONV rw1) |> concl |> rhs end

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
                  handle HOL_ERR _ => tDefine (quote_ty_name^"_def") [ANTIQUOTE(list_mk_conj eqs)] (!mk_quote_tac) before ignore (drop())
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

val (quote_num_aux_def,quote_num_def) = mk_quote NONE ``:num``
val (quote_level_aux_def,quote_level_def) = mk_quote NONE ``:level``
val (quote_prod_aux_def,quote_prod_def) = mk_quote (SOME(["q1","q2"],["t1","t2"])) ``:'a # 'b``
val (quote_list_aux_def,quote_list_def) = mk_quote (SOME(["q"],["t"])) ``:'a list``

val quote_list_aux_cong = Q.store_thm("quote_list_aux_cong",`!l1 l2 t1 t2 q1 q2.
l1 = l2 /\
t1 = t2 /\
(!a. MEM a l1 ==> q1 a = q2 a)
==> quote_list_aux (q1,t1) l1 = quote_list_aux (q2,t2) l2`,
Induct \\ rw[quote_list_aux_def] \\ rw[quote_list_aux_def]
)

val quote_list_is_aux = Q.prove(`FST (quote_list (x,y)) z = quote_list_aux (x,y) z`, rw[quote_list_def])

val _ = DefnBase.export_cong "quote_list_aux_cong"
val _ = aux_rws := concl quote_list_is_aux :: !aux_rws

val quote_char_aux_def = Define `quote_char_aux c = Comb ^(term_to_deep ``CHR``) (quote_num_aux (ORD c))`
val quote_char_def = Define `quote_char = (quote_char_aux , ^(type_to_deep ``:char``))`

val (quote_id_aux_def,quote_id_def) = mk_quote (SOME(["q"],["t"])) ``:'a id``
val (quote_tctor_aux_def,quote_tctor_def) = mk_quote NONE ``:tctor``

val _ = mk_quote_tac := (wf_rel_tac `measure t_size` \\ gen_tac \\ Induct \\ rw[astTheory.t_size_def]
                                   \\ simp[] \\ res_tac \\ simp[])

val (quote_t_aux_def,quote_t_def) = mk_quote NONE ``:t`` 
val quote_t_aux_def = save_thm("quote_t_aux_def",quote_t_aux_def |> REWRITE_RULE[GSYM quote_list_is_aux,ETA_AX])

val (quote_spec_aux_def,quote_spec_def) = mk_quote NONE ``:spec``
val (quote_option_aux_def,quote_option_def) = mk_quote (SOME(["q"],["t"])) ``:'a option``
val _ = overload_on("quote_specs",``quote_list quote_spec``)

val quote_int_aux_def = Define `quote_int_aux i = if i < 0i
                                                  then Comb ^(term_to_deep ``int_neg``)
                                                      (Comb ^(term_to_deep ``int_of_num``) (FST quote_num (Num (-i))))
                                                  else Comb ^(term_to_deep ``int_of_num``) (FST quote_num (Num i))`
val quote_int_def = Define `quote_int = (quote_int_aux, ^(type_to_deep ``:int``))`

val quote_lit = Define `quote_lit = (ARB:lit->term,ARB:type) (* TODO *)`

(* val quote_word_aux_def = Define `quote_word_aux ((q:'a -> term),t) (w:'a word) = Comb (Const (strlit "n2w") *)
(*     (Fun Num (Tyapp (strlit "cart") [Bool; t]))) (FST quote_num (w2n w))` *)
(* val quote_word_def = Define `quote_word (q,t) = (quote_word_aux (q,t) , type)` *)
(* val _ = overload_on("quote_word8",``) *)

val _ = mk_quote_tac := (wf_rel_tac `measure pat_size` \\ gen_tac \\ Induct \\ rw[astTheory.pat_size_def]
                                   \\ simp[] \\ res_tac \\ simp[])
val (quote_pat_aux_def,quote_pat_def) = mk_quote NONE ``:pat``
val quote_pat_aux_def = save_thm("quote_t_aux_def",quote_pat_aux_def |> REWRITE_RULE[GSYM quote_list_is_aux,ETA_AX])

val (quote_opn_aux_def,quote_opn_def) = mk_quote NONE ``:opn``
val (quote_opb_aux_def,quote_opb_def) = mk_quote NONE ``:opb``
val (quote_op_aux_def,quote_op_def) = mk_quote NONE ``:op``
val (quote_lop_aux_def,quote_lop_def) = mk_quote NONE ``:lop``

val _ = mk_quote_tac := (wf_rel_tac `measure exp_size` \\ rpt conj_tac \\ simp[] \\ (* TODO *)

val (quote_exp_aux_def,quote_exp_def) = mk_quote NONE ``:exp``
val (quote_dec_aux_def,quote_dec_def) = mk_quote NONE ``:dec``
val _ = overload_on("quote_decs",``quote_list quote_dec``)

val (quote_top_aux_def,quote_top_def) = mk_quote NONE ``:top``

val (quote_command_aux_def,quote_command_def) = mk_quote NONE ``:command``

val quote_top_def = Define`
  quote_top = (ARB:top->term,ARB:type) (* TODO *)`;

Val _ = overload_on("quote_prog",``quote_list quote_top``);

val (quote_privateData_aux_def,quote_privateData_def) = mk_quote NONE ``:privateData``

val quote_event_def = Define`
  quote_event = (ARB:event->term,ARB:type) (* TODO *)`;

val _ = overload_on("quote_observation",
    ``quote_prod (quote_num,(quote_prod (quote_event,quote_privateData)))``);

(*
quote_foo : (('a -> term) # type) -> (('a foo -> term) # type)
quote_bar : ((('a -> term) # type), (('b -> term) # type)) -> ((('a, 'b) bar -> term) # type)
*)
