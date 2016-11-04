open preamble
     seqTheory
     botworldTheory botworld_quoteTheory
     basicReflectionLib
     holKernelTheory

val _ = new_theory"botworld_sv"

val _ = Parse.bring_to_front_overload","{Name=",",Thy="pair"};
val _ = Parse.hide"S";

(* utility *)

val _ = Parse.type_abbrev("utilityfn",``:history -> real``);

val utilityfn_def = Define`
  utilityfn (u:utilityfn) ⇔
    (∀x. 0 ≤ u x ∧ u x ≤ 1) ∧
    ∀s h h'. u h ≤ u h' ⇒ u (s ::: h) ≤ u (s ::: h')`;

val exp_disc_fn_def = Define`
  exp_disc_fn v γ h n =
    γ pow n * v (THE (LNTH n h))`;

val exp_disc_def = Define`
  exp_disc (v:state->real,γ) h = suminf (exp_disc_fn v γ h)`;

val _ = overload_on("values",``λ(u:(state -> real) # real). FST u``);
val _ = overload_on("discount",``λ(u:(state -> real) # real). SND u``);

val wf_exp_disc_def = Define`
  wf_exp_disc (v,γ) ⇔
    (∀s. 0 ≤ v s ∧ v s ≤ 1) ∧
    0 < γ ∧ γ < 1`;

(* TODO: does this already exist? *)
val REAL_SUB_RAT1 = Q.store_thm("REAL_SUB_RAT1",
  `c ≠ 0 ⇒ a / c - b / c = (a - b) / c`,
  strip_tac
  \\ qspecl_then[`a`,`c`,`b`,`c`]mp_tac realTheory.REAL_SUB_RAT
  \\ rw[]
  \\ `a * c - c * b = (a - b) * c` by
     metis_tac[realTheory.REAL_MUL_COMM,realTheory.REAL_SUB_LDISTRIB]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[realTheory.REAL_DIV_RMUL_CANCEL]);

val exp_disc_fn_eta = Q.store_thm("exp_disc_fn_eta",
  `exp_disc_fn v γ h = λn. γ pow n * v (THE (LNTH n h))`,
  simp[FUN_EQ_THM,exp_disc_fn_def]);

val exp_disc_fn_non_neg = Q.store_thm("exp_disc_fn_non_neg",
  `(∀s. 0 ≤ v s) ∧ 0 < γ ⇒
   ∀n. 0 ≤ exp_disc_fn v γ h n`,
  strip_tac \\
  simp[exp_disc_fn_eta] \\
  gen_tac \\
  match_mp_tac realTheory.REAL_LE_MUL \\ simp[] \\
  match_mp_tac realTheory.POW_POS \\
  simp[realTheory.REAL_LT_IMP_LE] )

val exp_disc_fn_bound_gp = Q.store_thm("exp_disc_fn_bound_gp",
  `(∀s. 0 ≤ v s ∧ v s ≤ 1) ∧ 0 < γ ∧ γ < 1 ⇒
    ∀n. sum (0,n) (exp_disc_fn v γ h) ≤ sum (0,n) (λn. γ pow n)`,
  strip_tac \\
  gen_tac \\
  match_mp_tac realTheory.SUM_LE \\
  rw[exp_disc_fn_eta] \\
  ONCE_REWRITE_TAC[realTheory.REAL_MUL_COMM] \\
  `0 < γ pow r`
  by ( simp[realTheory.REAL_POW_LT] ) \\
  simp[GSYM realTheory.REAL_LE_RDIV_EQ] \\
  `γ pow r ≠ 0` by (CCONTR_TAC \\ fs[]) \\
  simp[realTheory.REAL_DIV_REFL] )

val exp_disc_fn_bound_lim = Q.store_thm("exp_disc_fn_bound_lim",
  `(∀s. 0 ≤ v s ∧ v s ≤ 1) ∧ 0 < γ ∧ γ < 1 ⇒
   ∀n. sum (0,n) (exp_disc_fn v γ h) < 1 / (1 - γ)`,
  strip_tac \\
  gen_tac \\
  match_mp_tac realTheory.REAL_LET_TRANS \\
  qexists_tac`sum (0,n) (λn. γ pow n)` \\
  simp[exp_disc_fn_bound_gp]
  \\ qspec_then`γ`mp_tac seqTheory.GP_FINITE \\
  impl_tac >- (CCONTR_TAC \\ fs[]) \\
  simp[] \\ disch_then kall_tac \\
  `γ - 1 = -(1 - γ)` by simp[realTheory.REAL_NEG_SUB] \\
  `γ pow n - 1 = -(1 - γ pow n)` by simp[realTheory.REAL_NEG_SUB] \\
  pop_assum SUBST_ALL_TAC \\
  pop_assum SUBST_ALL_TAC \\
  simp[realTheory.neg_rat] \\
  IF_CASES_TAC \\ fs[] \\
  `1 - γ ≠ 0` by simp[] \\
  simp[GSYM REAL_SUB_RAT1] \\
  simp[realTheory.REAL_LT_SUB_RADD] \\
  simp[realTheory.REAL_LT_ADDR] \\
  match_mp_tac realTheory.REAL_LT_DIV \\
  simp[realTheory.REAL_SUB_LT,realTheory.REAL_POW_LT] );

val exp_disc_fn_summable = Q.store_thm("exp_disc_fn_summable",
  `(∀s. 0 ≤ v s ∧ v s ≤ 1) ∧ 0 < γ ∧ γ < 1 ⇒
   summable (exp_disc_fn v γ h)`,
  rw[seqTheory.summable,seqTheory.sums,GSYM seqTheory.convergent] \\
  match_mp_tac seqTheory.SEQ_ICONV \\
  mp_tac exp_disc_fn_non_neg \\
  impl_tac >- fs[] \\ strip_tac \\
  SUBST_ALL_TAC exp_disc_fn_eta \\
  qho_match_abbrev_tac`bounded _ (λn. sum (0,n) f) ∧ _` \\
  imp_res_tac realTheory.SUM_POS \\
  conj_tac >- (
    simp[seqTheory.SEQ_BOUNDED] \\
    qexists_tac`1 / (1 - γ)` \\
    simp[realTheory.abs] \\
    simp[Abbr`f`,GSYM exp_disc_fn_eta] \\
    simp[exp_disc_fn_bound_lim]) \\
  rw[] \\
  fs[realTheory.real_ge,GREATER_EQ] \\
  fs[LESS_EQ_EXISTS] \\
  ONCE_REWRITE_TAC[GSYM realTheory.REAL_SUB_LE] \\
  simp[GSYM realTheory.SUM_DIFF]);

val exp_disc_fn_sums =
  exp_disc_fn_summable
  |> UNDISCH
  |> MATCH_MP seqTheory.SUMMABLE_SUM
  |> REWRITE_RULE[GSYM exp_disc_def]
  |> DISCH_ALL

val exp_disc_fn_cons_suc = Q.store_thm("exp_disc_fn_cons_suc",
  `exp_disc_fn v γ (s:::h) (SUC n) = γ * exp_disc_fn v γ h n`,
  rw[exp_disc_fn_def,realTheory.pow,realTheory.REAL_MUL_ASSOC]);

val sum_1_exp_disc_fn_cons = Q.store_thm("sum_1_exp_disc_fn_cons",
  `sum (0,1) (exp_disc_fn v γ (s:::h)) = v s`,
  REWRITE_TAC[ONE] \\ rw[realTheory.sum,exp_disc_fn_def,realTheory.pow]);

val exp_disc_thm = Q.store_thm("exp_disc_thm",
  `wf_exp_disc u ⇒
   exp_disc u (s:::h) =
       (values u) s + (discount u) * exp_disc u h`,
  Cases_on`u` \\
  qmatch_goalsub_rename_tac`wf_exp_disc (v,γ)` \\
  simp[wf_exp_disc_def] \\
  disch_then assume_tac \\
  mp_tac (MATCH_MP  seqTheory.SER_OFFSET
    (Q.ISPEC`(s:state):::h`(Q.GEN`h`(UNDISCH exp_disc_fn_summable)))) \\
  disch_then(qspec_then`1`mp_tac) \\
  simp[GSYM ADD1,exp_disc_fn_cons_suc,sum_1_exp_disc_fn_cons] \\
  rw[exp_disc_def] \\
  drule seqTheory.SER_CDIV \\
  disch_then(qspec_then`γ`mp_tac) \\
  simp[] \\
  Cases_on`γ = 0` \\ fs[] \\
  `(λn. γ * exp_disc_fn v γ h n / γ) = exp_disc_fn v γ h`
  by (
    rw[FUN_EQ_THM] \\
    drule realTheory.REAL_DIV_RMUL_CANCEL \\
    disch_then(qspecl_then[`exp_disc_fn v γ h n`,`1`]mp_tac) \\
    simp[realTheory.REAL_MUL_COMM] ) \\
  simp[] \\
  disch_then (mp_tac o MATCH_MP seqTheory.SUM_UNIQ)
  \\ disch_then (SUBST_ALL_TAC o SYM) \\
  simp[realTheory.REAL_DIV_LMUL] \\
  simp[realTheory.REAL_SUB_ADD2]);

val exp_disc_imp_utilityfn = Q.store_thm("exp_disc_imp_utilityfn",
  `wf_exp_disc u ∧
   (∀h. exp_disc u h ≤ 1)
    ⇒ utilityfn (exp_disc u)`,
  Cases_on`u` \\
  qmatch_goalsub_rename_tac`wf_exp_disc (v,γ)` \\
  simp[utilityfn_def,exp_disc_thm] \\
  rw[wf_exp_disc_def,utilityfn_def]
  >- (
    rw[exp_disc_def] \\
    `0 = sum (0,0) (exp_disc_fn v γ x)`
    by ( simp[realTheory.sum] ) \\
    pop_assum SUBST1_TAC \\
    match_mp_tac seqTheory.SER_POS_LE \\
    conj_tac >- (
      match_mp_tac exp_disc_fn_summable
      \\ simp[] ) \\
    simp[exp_disc_fn_non_neg] )
  \\ match_mp_tac realTheory.REAL_LE_LMUL_IMP
  \\ simp[realTheory.REAL_LT_IMP_LE]);

val with_policy_def = Define`
  with_policy (c,p) = robot_memory_fupd (K p) o robot_command_fupd (K c)`;

val weaklyExtensional_def = Define`
  weaklyExtensional (u:utilityfn) ⇔
    ∀s cp1 cp2 h. u (fill (with_policy cp1) s ::: h) = u (fill (with_policy cp2) s ::: h)`;

val discount_def = Define`
  discount (u:utilityfn) = sup { (u (s ::: h) - u (s ::: h')) / (u h - u h') | (s,h,h') | u h ≠ u h' }`

val discount_exists_def = Define`
  discount_exists (u:utilityfn) ⇔
    (∃h1 h2. u h1 ≠ u h2) ∧
    (∃z. ∀s h1 h2. u h1 ≠ u h2 ⇒ (u (s:::h2) − u (s:::h1)) / (u h2 − u h1) < z)`;

val discount_not_negative = Q.store_thm("discount_not_negative",
  `utilityfn u ∧ discount_exists u ⇒ 0 ≤ discount u`,
  rw[utilityfn_def,discount_def,discount_exists_def]
  \\ qmatch_goalsub_abbrev_tac`sup P`
  \\ `∃x. P x` by ( simp[Abbr`P`,UNCURRY] \\ simp[EXISTS_PROD] \\ metis_tac[])
  \\ `∃z. ∀x. P x ⇒ x < z`
  by (
    simp[Abbr`P`,UNCURRY] \\ simp[EXISTS_PROD]
    \\ simp[PULL_EXISTS] \\ metis_tac[] )
  \\ `∃x. P x ∧ 0 ≤ x` suffices_by metis_tac[realTheory.REAL_SUP_UBOUND,realTheory.REAL_LE_TRANS]
  \\ simp[Abbr`P`,UNCURRY,EXISTS_PROD]
  \\ simp[PULL_EXISTS]
  \\ asm_exists_tac \\ simp[]
  \\ Cases_on`u h2 ≤ u h1`
  >- (
    last_x_assum drule
    \\ disch_then(qspec_then`s`strip_assume_tac)
    \\ qexists_tac`s`
    \\ match_mp_tac realTheory.REAL_LE_DIV
    \\ simp[realTheory.REAL_SUB_LE] )
  \\ pop_assum mp_tac
  \\ simp[realTheory.REAL_NOT_LE,realTheory.REAL_LT_LE]
  \\ strip_tac
  \\ last_x_assum drule
  \\ disch_then(qspec_then`s`strip_assume_tac)
  \\ qexists_tac`s`
  \\ ONCE_REWRITE_TAC [GSYM realTheory.REAL_NEG_LE0]
  \\ ONCE_REWRITE_TAC [realTheory.neg_rat]
  \\ IF_CASES_TAC >- metis_tac[realTheory.REAL_SUB_0]
  \\ simp[realTheory.REAL_NEG_SUB]
  \\ qmatch_abbrev_tac`a / b ≤ 0`
  \\ `0 ≤ a / -b`
  suffices_by (
    REWRITE_TAC[realTheory.neg_rat]
    \\ IF_CASES_TAC >- metis_tac[realTheory.REAL_SUB_0]
    \\ ONCE_REWRITE_TAC[GSYM realTheory.REAL_NEG_LE0]
    \\ REWRITE_TAC[realTheory.neg_rat]
    \\ IF_CASES_TAC >- metis_tac[realTheory.REAL_SUB_0]
    \\ simp[] )
  \\ simp[realTheory.REAL_NEG_SUB,Abbr`a`,Abbr`b`]
  \\ match_mp_tac realTheory.REAL_LE_DIV
  \\ simp[realTheory.REAL_SUB_LE] );

(* suggester/verifier *)

val dominates_def = Define`
  (dominates (:α) (Trust k) (u,S) cp cp' ⇔
     LCA k (UNIV:α set) ⇒
     ∀s. s ∈ S ⇒
       u (hist (fill (with_policy cp') s)) ≤
       u (hist (fill (with_policy cp) s))) ∧
  (dominates (:α) MP (u,S) cp cp' ⇔
   ∀k. LCA k (UNIV:α set) ⇒
       ∀s. s ∈ S ⇒
         u (hist (fill (with_policy cp') s)) ≤
         u (hist (fill (with_policy cp) s))
           + ((discount u) pow k))`;

val dominates_refl = Q.store_thm("dominates_refl",
  `utilityfn u ∧ discount_exists u ⇒ dominates a l (u,S) cp cp`,
  Cases_on`a`\\Cases_on`l`\\simp[dominates_def]
  \\ simp[realTheory.REAL_LE_ADDR]
  \\ metis_tac[discount_not_negative,realTheory.POW_POS]);

val dominates'_def = Define`
  (dominates' a (Trust k) g cp cp' = dominates a (Trust (SUC k)) g cp cp') ∧
  (dominates' (:α) MP (u,S) cp cp' =
   ∀k. LCA (SUC k) 𝕌(:α) ⇒ ∀s. s ∈ S ⇒
     u (hist (fill (with_policy cp') s)) ≤ u (hist (fill (with_policy cp) s)) + (discount u) pow k)`;

val dominates'_refl = Q.store_thm("dominates'_refl",
  `utilityfn u ∧ discount_exists u ⇒ dominates' a l (u,S) cp cp`,
  Cases_on`a`\\reverse(Cases_on`l`)\\simp[dominates'_def]
  >- metis_tac[dominates_refl]
  \\ simp[realTheory.REAL_LE_ADDR]
  \\ metis_tac[discount_not_negative,realTheory.POW_POS]);

val level_to_ml_def = Define`
  level_to_ml (l:level) = (ARB:exp) (* TODO *)`;

val term_to_ml_def = Define`
  (* term_to_ml (Var s ty) = App Opapp [Var(Long"Botworld""mk_var"); Con NONE [Lit (StrLit (explode s)); type_to_ml ty]] ∧ *)
  term_to_ml (t:term) = (ARB:exp) (* TODO *)`;

(* -- *)

val _ = overload_on("state_with_hole_ty",type_to_deep``:state_with_hole``);
val _ = overload_on("observation_ty",type_to_deep``:observation``);
val _ = overload_on("utilityfn_ty",type_to_deep``:utilityfn``);
val _ = overload_on("command_ty",type_to_deep``:command``);
val _ = overload_on("dominates_tm",term_to_deep``dominates (:α)``);
val _ = overload_on("updateh_tm",term_to_deep``updateh``);

val mk_target_concl_def = Define`
  mk_target_concl l utm Stm ctm obs m1 m2 =
  Comb
  (Comb
   (Comb
    (Comb dominates_tm (FST quote_level l))
    (FST (quote_prod
          ((I, utilityfn_ty),
           (I, Fun state_with_hole_ty Bool)))
     (utm, Comb (Comb (Comb updateh_tm Stm) ctm) (FST quote_observation obs))))
   (FST (quote_prod (quote_command, quote_list (quote_list quote_word8))) m1))
  (FST (quote_prod (quote_command, quote_list (quote_list quote_word8))) m2)`;

val check_theorem_def = Define`
  check_theorem thm l utm Stm ctm obs m1 m2 =
    aconv (concl thm) (mk_target_concl l utm Stm ctm obs m1 m2)`;

(* TODO: translate mk_target_concl *)

(*
val sv_body_def = Define`
  sv_body l Stm utm σ obs cp1 =
   case σ obs cp1 of
   | NONE => NONE
   | SOME (cp2,th) =>
       if aconv (concl th) (mk_target_concl obs cp1 cp2 l Stm utm)
*)

(* Two preambles.
   1. Botworld preamble, at the end of which we have preamble_env, which is
      called by run_policy.
   2. sv_preamble, which is all the rest of the preamble stuff and only sv has
      access to it.

  Botworld preamble:
    - Pure library functions:
      - Pure cores of I/O functions
      - Botworld datatype
      - CakeML datatypes
    - Candle kernel functions:
      - the monadic functions in holKernelTheory
    - Impure I/O wrappers
      - read/write functions that call FFI

  sv_preamble:
    - Candle definitions of botworld, up to dominates
      - i.e., build the inner_ctxt
      - N.B.: this includes defining preamble_env
    - definition of check_theorem
*)

val sv_preamble_decs_def = Define`
  sv_preamble_decs = ARB:prog`; (* TODO *)

val sv_def = Define`
  sv l utm Stm ctm π σ =
    (* N.B. this requires there to be enough leftover space in register 0 *)
    encode_register 0 (listsexp o MAP topsexp) (
    (* assumes Botworld preamble gets run by botworld *)
    (* Botworld preamble includes helper functions:
       Botworld.read_observation : unit -> observation
       Botworld.read_output : unit -> command * prog
       Botworld.write_output : command * prog -> unit
    *)
    (*
       sv_preamble includes:
       check_theorem
    *)
    (*
      N.B. The only functions in either preamble that call any FFI are
           Botworld.read_observation,
           Botworld.read_output,
           Botworld.write_output
    *)
    (*
      Assume σ is an expression that is closed by the definitions of the both
      preambles, not including the FFI-calling functions, and two variables
      "observation" and "default", and it returns a (memory * thm) option
    *)
    (read_code π) (* this will read the observation and write the default *) ++
    [Tdec(Dlet(Pvar"default")(App Opapp [Var(Long"Botworld""read_output");Con NONE []]));
     Tdec(Dlet(Pvar"observation")(App Opapp [Var(Long"Botworld""read_observation");Con NONE []]))] ++
    sv_preamble_decs ++
    [Tdec(Dlet(Pvar"result")
           (Mat σ (* n.b. σ refers to the observation and default variables *)
              [(Pcon(SOME(Short"NONE"))[],Con NONE [])
              ;(Pcon(SOME(Short"SOME"))[Pcon NONE [Pvar"policy";Pvar"thm"]],
               If (App Opapp
                   [Var(Long"SV""check_theorem");
                    Con NONE
                      [Var(Short"thm")
                      ;level_to_ml l
                      ;term_to_ml utm
                      ;term_to_ml Stm
                      ;term_to_ml ctm
                      ;Var(Short"observation")
                      ;Var(Short"policy")
                      ;Var(Short"default")
                      ]])
                   (App Opapp [Var(Long"Botworld""write_output");Var(Short"policy")])
                   (Con NONE []))]))])
     π`;

val _ = export_theory()
