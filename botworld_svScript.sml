open preamble
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

val discount_def = Define`
  discount (u:utilityfn) = sup { (u (s ::: h) - u (s ::: h')) / (u h - u h') | (s,h,h') | u h ≠ u h' }`

val weaklyExtensional_def = Define`
  weaklyExtensional (u:utilityfn) ⇔
    ∀s p1 p2 h. u (fill p1 s ::: h) = u (fill p2 s ::: h)`;

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
  (dominates (:α) (Trust k) (S,u) m m' ⇔
     LCA k (UNIV:α set) ⇒
     ∀s. s ∈ S ⇒
       u (hist (fill m' s)) ≤
       u (hist (fill m s))) ∧
  (dominates (:α) MP (S,u) m m' ⇔
   ∀k. LCA k (UNIV:α set) ⇒
       ∀s. s ∈ S ⇒
         u (hist (fill m' s)) ≤
         u (hist (fill m s))
           + ((discount u) pow k))`;

val dominates_refl = Q.store_thm("dominates_refl",
  `utilityfn u ∧ discount_exists u ⇒ dominates a l (S,u) m m`,
  Cases_on`a`\\Cases_on`l`\\simp[dominates_def]
  \\ simp[realTheory.REAL_LE_ADDR]
  \\ metis_tac[discount_not_negative,realTheory.POW_POS]);

val dominates'_def = Define`
  (dominates' a (Trust k) g m m' = dominates a (Trust (SUC k)) g m m') ∧
  (dominates' (:α) MP (S,u) m m' =
   ∀k. LCA (SUC k) 𝕌(:α) ⇒ ∀s. s ∈ S ⇒
     u (hist (fill m' s)) ≤ u (hist (fill m s)) + (discount u) pow k)`;

val dominates'_refl = Q.store_thm("dominates'_refl",
  `utilityfn u ∧ discount_exists u ⇒ dominates' a l (S,u) m m`,
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
val _ = overload_on("dominates_tm",term_to_deep``dominates (:α)``);

val mk_target_concl_def = Define`
  mk_target_concl obs m1 m2 l Stm utm =
  Comb
  (Comb
   (Comb
    (Comb dominates_tm (FST quote_level l))
    (FST (quote_prod
          ((I, Fun state_with_hole_ty Bool), (I, utilityfn_ty)))
     (Comb Stm (FST quote_observation obs), utm)))
   (FST (quote_prod (quote_command, quote_prog)) m1)) (* TODO: these need to quote_memory instead *)
  (FST (quote_prod (quote_command, quote_prog)) m2)`;

val check_theorem_def = Define`
  check_theorem thm l Stm obs utm m1 m2 =
    aconv (concl thm) (mk_target_concl obs m1 m2 l Stm utm)`;

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

val sv_def = Define`
  sv l Stm utm π σ =
    (* assumes Botworld preamble gets run by botworld *)
    (* Botworld preamble includes helper functions:
       Botworld.read_observation : unit -> observation
       Botworld.read_output : unit -> command * prog
       Botworld.write_output : command * prog -> unit
    *)
    (*
       sv_preamble includes:
       check_theorem : thm * level * term * observation * term * (command * prog) * (command * prog) -> bool
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
      "observation" and "fallback", and it returns a (command * prog * thm) option
    *)
    π (* this will read the observation and write the fallback *) ++
    (* TODO: insert sv_preamble here *)
    [Tdec(Dlet(Pvar"observation")(App Opapp [Var(Long"Botworld""read_observation");Con NONE []]));
     Tdec(Dlet(Pvar"fallback")(App Opapp [Var(Long"Botworld""read_output");Con NONE []]));
     Tdec(Dlet(Pvar"result")
           (Mat σ (* n.b. σ refers to the observation and fallback variables *)
              [(Pcon(SOME(Short"NONE"))[],Con NONE [])
              ;(Pcon(SOME(Short"SOME"))[Pcon NONE [Pvar"policy";Pvar"thm"]],
               If (App Opapp
                   [Var(Long"Botworld""check_theorem");
                    Con NONE
                      [Var(Short"thm")
                      ;level_to_ml l
                      ;term_to_ml Stm
                      ;Var(Short"observation")
                      ;term_to_ml utm
                      ;Var(Short"policy")
                      ;Var(Short"fallback")
                      ]])
                   (App Opapp [Var(Long"Botworld""write_output");Var(Short"policy")])
                   (Con NONE []))]))]`;

val _ = export_theory()
