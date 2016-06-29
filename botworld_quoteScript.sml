open preamble botworld_quoteLib
     reflectionLib holSemanticsTheory
     setSpecTheory reflectionTheory
     local open dep_rewrite in end

val _ = new_theory"botworld_quote";

val ty = ``:num``
val (quote_num_aux_def,quote_num_def) = mk_quote NONE ty

val constrs =
  quote_num_aux_def |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> map (subst[tmass |-> ``tmaof (i:'U interpretation)``])

val num_assums = assums

val quote_num_thm = Q.store_thm("quote_num_thm",
  `is_set_theory ^mem ⇒
   ∀tmsig i v.
    ^(list_mk_conj assums) ⇒
    ∀n. termsem tmsig i v (FST quote_num n) = to_inner (SND quote_num) n`,
  ntac 5 strip_tac
  \\ simp[quote_num_def]
  \\ Induct
  \\ rw[quote_num_aux_def]
  \\ rw[termsem_def]
  >- (
    qhdtm_x_assum`FLOOKUP`kall_tac
    \\ drule instance_def
    \\ simp[]
    \\ disch_then(qspecl_then[`i`,`[]`]mp_tac)
    \\ rw[]
    \\ CONV_TAC(LAND_CONV(RAND_CONV EVAL))
    \\ simp[] )
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[]`]mp_tac)
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ simp[]
  \\ simp[fun_to_inner_def]
  \\ match_mp_tac apply_abstract_matchable
  \\ simp[wf_to_inner_range_thm]
  \\ metis_tac[wf_to_inner_finv_left]);

val ty = ``:level``
val (quote_level_aux_def,quote_level_def) = mk_quote NONE ty

val constrs =
  quote_level_aux_def |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> map (subst[tmass |-> ``tmaof (i:'U interpretation)``])

val quote_level_thm = Q.store_thm("quote_level_thm",
  `is_set_theory ^mem ⇒
   ∀tmsig i v.
    ^(list_mk_conj (assums@num_assums)) ⇒
    ∀n. termsem tmsig i v (FST quote_level n) = to_inner (SND quote_level) n`,
  ntac 5 strip_tac
  \\ simp[quote_level_def]
  \\ Induct
  \\ rw[quote_level_aux_def]
  \\ rw[termsem_def]
  >- (
    qpat_assum`FLOOKUP _ (strlit "MP") = _`assume_tac
    \\ drule instance_def
    \\ simp[]
    \\ disch_then(qspecl_then[`i`,`[]`]mp_tac)
    \\ rw[]
    \\ CONV_TAC(LAND_CONV(RAND_CONV EVAL))
    \\ simp[] )
  \\ qpat_assum`FLOOKUP _ (strlit "Trust") = _`assume_tac
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[]`]mp_tac)
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ simp[]
  \\ simp[fun_to_inner_def]
  \\ match_mp_tac apply_abstract_matchable
  \\ dep_rewrite.DEP_REWRITE_TAC[quote_num_thm]
  \\ simp[wf_to_inner_range_thm,quote_num_def]
  \\ metis_tac[wf_to_inner_finv_left]);

val ty = ``:'a # 'b``

val (quote_prod_aux_def,quote_prod_def) = mk_quote (SOME(["q1","q2"],["t1","t2"])) ty

val quote_prod_aux_cong = Q.store_thm("quote_prod_aux_cong",
  `∀xy1 xy2 qta1 qtb1 qta2 qtb2.
   xy1 = xy2 ∧
   (∀q1 t1 q2 t2 x1. qta1 = (q1,t1) ∧ qta2 = (q2,t2) ∧ x1 = FST xy1 ⇒ t1 = t2 ∧ q1 x1 = q2 x1) ∧
   (∀q1 t1 q2 t2 y1. qtb1 = (q1,t1) ∧ qtb2 = (q2,t2) ∧ y1 = SND xy1 ⇒ t1 = t2 ∧ q1 y1 = q2 y1)
   ⇒
   quote_prod_aux (qta1,qtb1) xy1 = quote_prod_aux (qta2,qtb2) xy2 `,
  rpt Cases \\ rw[quote_prod_aux_def]);
val _ = DefnBase.export_cong "quote_prod_aux_cong";

val constrs =
  quote_prod_aux_def |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val [q1,t1,q2,t2] = quote_prod_def |> concl |> strip_forall |> #1

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> mapi (fn i => if i mod 2 = 0 then
       subst[tmass |-> ``tmaof (i:'U interpretation)``,
             ``Tyvar (strlit "A")`` |-> t1,
             ``Tyvar (strlit "B")`` |-> t2] else I)

val _ = Parse.bring_to_front_overload"tyvars"{Name="tyvars",Thy="holSyntax"};

val to_inner_t1 = ``(to_inner ^t1):'a -> 'U``
val to_inner_t2 = ``(to_inner ^t2):'b -> 'U``

val quote_prod_thm = Q.store_thm("quote_prod_thm",
  `is_set_theory ^mem ⇒
   ∀^q1 ^t1 ^q2 ^t2 tmsig i v.
     (*tyvars t1 = [] ∧ tyvars t2 = [] ∧*)
     wf_to_inner ^to_inner_t1 ∧
     typesem (tyaof i) (tyvof v) t1 = range ^to_inner_t1 ∧
     (∀a. termsem tmsig i v (q1 a) = to_inner t1 a) ∧
     wf_to_inner ^to_inner_t2 ∧
     typesem (tyaof i) (tyvof v) t2 = range ^to_inner_t2 ∧
     (∀b. termsem tmsig i v (q2 b) = to_inner t2 b) ∧
     ^(list_mk_conj assums) ⇒
     ∀p. termsem tmsig i v (FST (quote_prod ((q1,t1),(q2,t2))) p) =
       to_inner (SND (quote_prod ((q1,t1),(q2,t2)))) p`,
  ntac 9 strip_tac
  \\ Cases
  \\ rw[quote_prod_def,quote_prod_aux_def,termsem_def]
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[(t1,Tyvar(strlit"A"));(t2,Tyvar(strlit"B"))]`]mp_tac)
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL))))
  \\ rw[fun_to_inner_def]
  \\ dep_rewrite.DEP_REWRITE_TAC[apply_abstract]
  \\ rw[wf_to_inner_range_thm,range_fun_to_inner]
  \\ TRY (
    match_mp_tac (UNDISCH abstract_in_funspace)
    \\ rw[wf_to_inner_range_thm] )
  \\ metis_tac[wf_to_inner_finv_left]);

val ty = ``:'a list``;

val (quote_list_aux_def,quote_list_def) = mk_quote (SOME(["q"],["t"])) ty;

val quote_list_aux_cong = Q.store_thm("quote_list_aux_cong",
  `!l1 l2 t1 t2 q1 q2.
      l1 = l2 /\
      t1 = t2 /\
      (!a. MEM a l1 ==> q1 a = q2 a)
      ==> quote_list_aux (q1,t1) l1 = quote_list_aux (q2,t2) l2`,
  Induct \\ rw[quote_list_aux_def] \\ rw[quote_list_aux_def]);
val _ = DefnBase.export_cong "quote_list_aux_cong";

val constrs =
  quote_list_aux_def |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val [q,t] = quote_list_def |> concl |> strip_forall |> #1

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> mapi (fn i => if i mod 2 = 0 then
       subst[tmass |-> ``tmaof (i:'U interpretation)``,
             ``Tyvar (strlit "A")`` |-> t] else I)
val list_assums = assums

val to_inner_t = ``(to_inner ^t):'a -> 'U``

val quote_list_thm = Q.store_thm("quote_list_thm",
  `is_set_theory ^mem ⇒
   ∀^q ^t tmsig i v.
     wf_to_inner ^to_inner_t ∧
     typesem (tyaof i) (tyvof v) t = range ^to_inner_t ∧
     (∀a. termsem tmsig i v (q a) = to_inner t a) ∧
     ^(list_mk_conj assums) ⇒
     ∀l. termsem tmsig i v (FST (quote_list (q,t)) l) =
       to_inner (SND (quote_list (q,t))) l`,
  ntac 7 strip_tac
  \\ Induct
  \\ rw[quote_list_def,quote_list_aux_def,termsem_def]
  >- (
    qpat_assum`FLOOKUP _ (strlit"NIL") = _`assume_tac
    \\ drule instance_def
    \\ simp[]
    \\ disch_then(qspecl_then[`i`,`[(t,Tyvar(strlit"A"))]`]mp_tac)
    \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
    \\ rw[]
    \\ CONV_TAC(LAND_CONV(RAND_CONV EVAL))
    \\ rw[] )
  \\ qpat_assum`FLOOKUP _ (strlit"CONS") = _`assume_tac
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[(t,Tyvar(strlit"A"))]`]mp_tac)
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL))))
  \\ rw[fun_to_inner_def]
  \\ fs[quote_list_def]
  \\ dep_rewrite.DEP_REWRITE_TAC[apply_abstract]
  \\ rw[wf_to_inner_range_thm,range_fun_to_inner]
  \\ TRY (
    match_mp_tac (UNDISCH abstract_in_funspace)
    \\ rw[wf_to_inner_range_thm] )
  \\ metis_tac[wf_to_inner_finv_left]);

val quote_list_is_aux = Q.prove(
  `FST (quote_list (x,y)) z = quote_list_aux (x,y) z`,
  rw[quote_list_def]);

val num_list_assums =
  (list_mk_conj list_assums)
  |> subst[t |-> ``SND quote_num``]
  |> inst[alpha |-> ``:num``]

val num_ty_assums =
  base_type_assums ``:num``
  |> map (subst [tyass |-> ``tyaof (i:'U interpretation)``])

val quote_num_list_example = Q.store_thm("quote_num_list_example",
  `is_set_theory ^mem ⇒
   ∀tysig tmsig i v.
     ^(list_mk_conj num_ty_assums) ∧
     ^(list_mk_conj (tl num_assums)) ∧
     ^num_list_assums ⇒
   ∀l. termsem tmsig i v (FST (quote_list quote_num) l) = to_inner (SND (quote_list quote_num)) l`,
  ntac 6 strip_tac
  \\ fs[quote_num_def]
  \\ match_mp_tac (UNDISCH quote_list_thm)
  \\ simp[]
  \\ conj_tac >- ( rw[typesem_def] )
  \\ match_mp_tac (UNDISCH quote_num_thm |> SIMP_RULE std_ss [quote_num_def])
  \\ simp[]);

val _ = aux_rws := concl quote_list_is_aux :: !aux_rws

val ty = ``:char``;

val quote_char_aux_def = Define `quote_char_aux c = Comb ^(term_to_deep ``CHR``) (quote_num_aux (ORD c))`
val quote_char_def = Define `quote_char = (quote_char_aux , ^(type_to_deep ty))`

val constrs = [``CHR``]

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> map (subst[tmass |-> ``tmaof (i:'U interpretation)``])
val char_assums = assums

val quote_char_thm = Q.store_thm("quote_char_thm",
  `is_set_theory ^mem ⇒
   ∀tmsig i v.
     ^(list_mk_conj num_assums) ∧
     ^(list_mk_conj assums)
     ⇒
     ∀c. termsem tmsig i v (FST quote_char c) = to_inner (SND quote_char) c`,
  ntac 5 strip_tac
  \\ Cases
  \\ fs[quote_char_def,quote_char_aux_def]
  \\ rw[termsem_def]
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[]`]mp_tac)
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ simp[]
  \\ simp[fun_to_inner_def]
  \\ match_mp_tac apply_abstract_matchable
  \\ simp[wf_to_inner_range_thm]
  \\ dep_rewrite.DEP_REWRITE_TAC[UNDISCH quote_num_thm |> SIMP_RULE std_ss [quote_num_def]]
  \\ simp[wf_to_inner_range_thm]
  \\ metis_tac[wf_to_inner_finv_left]);

val char_list_assums =
  (list_mk_conj list_assums)
  |> subst[t |-> ``SND quote_char``]
  |> inst[alpha |-> ``:char``]

val char_ty_assums =
  base_type_assums ``:char``
  |> map (subst [tyass |-> ``tyaof (i:'U interpretation)``])

val quote_char_list_thm = Q.store_thm("quote_char_list_thm",
  `is_set_theory ^mem ⇒
   ∀tysig tmsig i v.
    ^(list_mk_conj char_ty_assums) ∧
    ^(list_mk_conj (tl char_assums)) ∧
    ^(list_mk_conj num_assums) ∧
    ^char_list_assums ⇒
    ∀l. termsem tmsig i v (FST (quote_list quote_char) l) = to_inner (SND (quote_list quote_char)) l`,
  ntac 6 strip_tac
  \\ fs[quote_char_def]
  \\ match_mp_tac (UNDISCH quote_list_thm)
  \\ simp[]
  \\ conj_tac >- ( rw[typesem_def] )
  \\ match_mp_tac (UNDISCH quote_char_thm |> SIMP_RULE std_ss [quote_char_def])
  \\ simp[]);

val ty = ``:'a id``;

val (quote_id_aux_def,quote_id_def) = mk_quote (SOME(["q"],["t"])) ty;

val constrs =
  quote_id_aux_def |> SPEC_ALL |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val [q,t] = quote_id_def |> concl |> strip_forall |> #1

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> mapi (fn i => if i mod 2 = 0 then
       subst[tmass |-> ``tmaof (i:'U interpretation)``,
             ``Tyvar (strlit "A")`` |-> t] else I)
val id_assums = assums

val to_inner_t = ``(to_inner ^t):'a -> 'U``

val quote_id_thm = Q.store_thm("quote_id_thm",
  `is_set_theory ^mem ⇒
   ∀^q ^t tysig tmsig i v.
     wf_to_inner ^to_inner_t ∧
     typesem (tyaof i) (tyvof v) t = range ^to_inner_t ∧
     (∀a. termsem tmsig i v (q a) = to_inner t a) ∧
     ^(list_mk_conj assums) ∧
     ^(list_mk_conj char_ty_assums) ∧
     ^(list_mk_conj (tl char_assums)) ∧
     ^(list_mk_conj num_assums) ∧
     ^char_list_assums
     ⇒
     ∀l. termsem tmsig i v (FST (quote_id (q,t)) l) =
       to_inner (SND (quote_id (q,t))) l`,
  ntac 8 strip_tac
  \\ Induct
  \\ rw[quote_id_def,quote_id_aux_def,termsem_def]
  >- (
    qpat_assum`FLOOKUP _ (strlit"Short") = _`assume_tac
    \\ drule instance_def
    \\ simp[]
    \\ disch_then(qspecl_then[`i`,`[(t,Tyvar(strlit"A"))]`]mp_tac)
    \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
    \\ rw[]
    \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
    \\ rw[fun_to_inner_def]
    \\ dep_rewrite.DEP_REWRITE_TAC[apply_abstract]
    \\ rw[wf_to_inner_range_thm]
    \\ metis_tac[wf_to_inner_finv_left])
  \\ qpat_assum`FLOOKUP _ (strlit"Long") = _`assume_tac
  \\ drule instance_def
  \\ simp[]
  \\ disch_then(qspecl_then[`i`,`[(t,Tyvar(strlit"A"))]`]mp_tac)
  \\ CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))
  \\ rw[]
  \\ CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL))))
  \\ rw[fun_to_inner_def]
  \\ dep_rewrite.DEP_REWRITE_TAC[UNDISCH quote_char_list_thm]
  \\ simp[] \\ conj_tac >- metis_tac[]
  \\ dep_rewrite.DEP_REWRITE_TAC[apply_abstract]
  \\ rw[wf_to_inner_range_thm,range_fun_to_inner]
  \\ TRY (
    match_mp_tac (UNDISCH abstract_in_funspace)
    \\ rw[wf_to_inner_range_thm] )
  \\ fs[quote_char_def,quote_list_def,wf_to_inner_range_thm]
  \\ metis_tac[wf_to_inner_finv_left]);

val char_list_id_assums =
  list_mk_conj id_assums
  |> subst[t |-> ``SND (quote_list quote_char)``]
  |> inst[alpha |-> ``:char list``]

val char_list_ty_assums =
  base_type_assums ``:char list``
  |> map (subst [tyass |-> ``tyaof (i:'U interpretation)``])

val quote_char_list_id_thm = Q.store_thm("quote_char_list_id_thm",
  `is_set_theory ^mem ⇒
   ∀tysig tmsig i v.
     ^(list_mk_conj char_ty_assums) ∧
     ^(list_mk_conj (tl char_assums)) ∧
     ^(list_mk_conj num_assums) ∧
     ^char_list_assums ∧
     ^(list_mk_conj char_list_ty_assums) ∧
     ^char_list_id_assums ⇒
   ∀x. termsem tmsig i v (FST (quote_id (quote_list quote_char)) x) = to_inner (SND (quote_id (quote_list quote_char))) x`,
  ntac 6 strip_tac
  \\ fs[quote_list_def,quote_char_def]
  \\ match_mp_tac (UNDISCH quote_id_thm)
  \\ simp[]
  \\ qexists_tac`tysig`
  \\ simp[]
  \\ conj_tac >- ( rw[typesem_def] )
  \\ fs[quote_char_def]
  \\ match_mp_tac (UNDISCH quote_char_list_thm |> SIMP_RULE std_ss [quote_list_def,quote_char_def])
  \\ qexists_tac`tysig`
  \\ simp[]);

val ty = ``:tctor``;

val (quote_tctor_aux_def,quote_tctor_def) = mk_quote NONE ty;

val constrs =
  quote_tctor_aux_def |> SPEC_ALL |> CONJUNCTS
  |> map (#1 o strip_comb o rand o lhs o concl o SPEC_ALL)

val assums = map base_term_assums constrs
  |> List.concat |> cons (to_inner_prop [] ty)
  |> map (subst[tmass |-> ``tmaof (i:'U interpretation)``])

val tctor_assums = assums

val quote_tctor_thm = Q.store_thm("quote_tctor_thm",
  `is_set_theory ^mem ⇒
   ∀tmsig i v.
     ^(list_mk_conj assums)
     ⇒
     ∀t. termsem tmsig i v (FST quote_tctor t) = to_inner (SND quote_tctor) t`,
  ntac 5 strip_tac
  \\ simp[quote_tctor_def]
  \\ Induct
  \\ rw[quote_tctor_aux_def]

val _ = mk_quote_tac := (wf_rel_tac `measure t_size` \\ gen_tac \\ Induct \\ rw[astTheory.t_size_def]
                                   \\ simp[] \\ res_tac \\ simp[])

val (quote_t_aux_def,quote_t_def) = mk_quote NONE ``:t``
val quote_t_aux_def = save_thm("quote_t_aux_def",
    quote_t_aux_def |> REWRITE_RULE[GSYM quote_list_is_aux,ETA_AX])

val (quote_spec_aux_def,quote_spec_def) = mk_quote NONE ``:spec``
val _ = overload_on("quote_specs",``quote_list quote_spec``)

val (quote_option_aux_def,quote_option_def) = mk_quote (SOME(["q"],["t"])) ``:'a option``

val quote_option_aux_cong = Q.store_thm("quote_option_aux_cong",
  `∀o1 o2 q1 q2 t1 t2.
   o1 = o2 ∧ t1 = t2 ∧ (∀x. o1 = SOME x ⇒ q1 x = q2 x)
   ⇒ quote_option_aux (q1,t1) o1 = quote_option_aux (q2,t2) o2`,
  Cases \\ simp[quote_option_aux_def]);
val _ = DefnBase.export_cong"quote_option_aux_cong";

val quote_int_aux_def = Define `quote_int_aux i = if i < 0i
                                                  then Comb ^(term_to_deep ``int_neg``)
                                                      (Comb ^(term_to_deep ``int_of_num``) (FST quote_num (Num (-i))))
                                                  else Comb ^(term_to_deep ``int_of_num``) (FST quote_num (Num i))`
val quote_int_def = Define `quote_int = (quote_int_aux, ^(type_to_deep ``:int``))`

val quote_word8_aux_def = Define`quote_word8_aux (w:word8) =
  Comb ^(term_to_deep``w2n:word8->num``) (FST quote_num (w2n w))`;
val quote_word8_def = Define`quote_word8 = (quote_word8_aux,^(type_to_deep``:word8``))`;

val _ = special_quoters := (``:word8``,``FST quote_word8``) :: !special_quoters;

val quote_word64_aux_def = Define`quote_word64_aux (w:word64) =
  Comb ^(term_to_deep``w2n:word64->num``) (FST quote_num (w2n w))`;
val quote_word64_def = Define`quote_word64 = (quote_word64_aux,^(type_to_deep``:word64``))`;

val _ = special_quoters := (``:word64``,``FST quote_word64``) :: !special_quoters;

val (quote_lit_aux_def,quote_lit_def) = mk_quote NONE ``:lit``

val _ = mk_quote_tac := (wf_rel_tac `measure pat_size` \\ gen_tac \\ Induct \\ rw[astTheory.pat_size_def]
                                   \\ simp[] \\ res_tac \\ simp[])
val (quote_pat_aux_def,quote_pat_def) = mk_quote NONE ``:pat``
val quote_pat_aux_def = save_thm("quote_pat_aux_def",quote_pat_aux_def |> REWRITE_RULE[GSYM quote_list_is_aux,ETA_AX])

val (quote_word_size_aux_def,quote_word_size_def) = mk_quote NONE ``:word_size``
val (quote_shift_aux_def,quote_shift_def) = mk_quote NONE ``:shift``

val (quote_opn_aux_def,quote_opn_def) = mk_quote NONE ``:opn``
val (quote_opb_aux_def,quote_opb_def) = mk_quote NONE ``:opb``
val (quote_opw_aux_def,quote_opw_def) = mk_quote NONE ``:opw``
val (quote_lop_aux_def,quote_lop_def) = mk_quote NONE ``:lop``
val (quote_op_aux_def,quote_op_def) = mk_quote NONE ``:op``

val quote_option_is_aux = Q.prove(
  `FST (quote_option qt) z = quote_option_aux qt z`,
  Cases_on`qt`\\rw[quote_option_def]);

val _ = aux_rws := concl quote_option_is_aux :: !aux_rws

(*
val _ = aux_rws := tl (!aux_rws)
*)

(*
val FST_cong = Q.store_thm("FST_cong",
  `x1 = x2 ⇒
   FST (x1,y1) = FST (x2,y2)`,rw[])
val _ = DefnBase.export_cong"FST_cong";

val SND_cong = Q.store_thm("SND_cong",
  `y1 = y2 ⇒
   SND (x1,y1) = SND (x2,y2)`,rw[])
val _ = DefnBase.export_cong"SND_cong";
*)

val quote_prod_split1 = Q.prove(
  `quote_prod x = (quote_prod_aux x, Pair (SND(FST x)) (SND(SND x)))`,
  PairCases_on`x`\\rw[quote_prod_def]);

val quote_prod_split2 = Q.prove(
  `quote_prod (x,y) = (quote_prod_aux (x,y), Pair (SND x) (SND y))`,
  PairCases_on`x`\\PairCases_on`y`\\rw[quote_prod_def]);

val quote_prod_split3 = Q.prove(
  `quote_prod (x,(y,z)) = (quote_prod_aux (x,(y,z)), Pair (SND x) z)`,
  PairCases_on`x`\\rw[quote_prod_def]);

val quote_prod_split4 = Q.prove(
  `quote_prod ((x,y),z) = (quote_prod_aux ((x,y),z), Pair y (SND z))`,
  PairCases_on`z`\\rw[quote_prod_def]);

val _ = aux_rws :=
  concl quote_prod_split4 ::
  concl quote_prod_split3 ::
  concl quote_prod_split2 ::
  concl quote_prod_split1 ::
  !aux_rws

val _ = mk_quote_tac := (
  wf_rel_tac `measure exp_size` \\ rpt conj_tac \\ simp[]
  \\ gen_tac \\ Induct \\ rw[] \\ simp[astTheory.exp_size_def] \\ res_tac \\ simp[astTheory.exp_size_def]);

val (quote_exp_aux_def,quote_exp_def) = mk_quote NONE ``:exp``
val quote_exp_aux_def = save_thm("quote_exp_aux_def",
    quote_exp_aux_def |>
    REWRITE_RULE[ETA_AX,
         GSYM quote_list_is_aux,
         GSYM quote_option_is_aux,
         GSYM quote_prod_split4,
         GSYM quote_prod_split3,
         GSYM quote_prod_split2,
         GSYM quote_prod_split1]); (* TODO: remove RESTRICT *)

val (quote_dec_aux_def,quote_dec_def) = mk_quote NONE ``:dec``
val _ = overload_on("quote_decs",``quote_list quote_dec``)

val (quote_top_aux_def,quote_top_def) = mk_quote NONE ``:top``

val (quote_name_aux_def,quote_name_def) = mk_quote NONE ``:name``

val (quote_command_aux_def,quote_command_def) = mk_quote NONE ``:command``

val _ = overload_on("quote_prog",``quote_list quote_top``);

val (quote_privateData_aux_def,quote_privateData_def) = mk_quote NONE ``:privateData``

val (quote_frame_aux_def,quote_frame_def) = mk_quote NONE ``:frame``;
val (quote_cargo_aux_def,quote_cargo_def) = mk_quote NONE ``:cargo``;
val (quote_item_aux_def,quote_item_def) = mk_quote NONE ``:item``;
val (quote_itemCache_aux_def,quote_itemCache_def) = mk_quote NONE ``:itemCache``;

val (quote_bool_aux_def,quote_bool_def) = mk_quote NONE ``:bool``;

val (quote_robot_aux_def,quote_robot_def) = mk_quote NONE ``:robot``;

val (quote_action_aux_def,quote_action_def) = mk_quote NONE ``:action``;

val (quote_event_aux_def,quote_event_def) = mk_quote NONE ``:event``;

val _ = overload_on("quote_observation",
    ``quote_prod (quote_name,(quote_prod (quote_event,quote_privateData)))``);

val _ = export_theory();
