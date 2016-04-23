open preamble
     botworld_preambleTheory
     botworld_serialiseTheory
     astTheory semanticPrimitivesTheory
     evalPropsTheory funBigStepTheory
     ml_translatorTheory
open terminationTheory

val _ = new_theory"botworld_io"

val _ = Globals.max_print_depth := 0;
val evals = [evaluate_def, do_app_def, lookup_var_id_def, build_rec_env_merge,
             find_recfun_ALOOKUP, store_alloc_def, store_lookup_def, store_assign_def,
             libTheory.opt_bind_def, rich_listTheory.EL_LENGTH_APPEND, pat_bindings_def,
             pmatch_def];
val _ = Globals.max_print_depth := 20;

(* TODO: move? *)

val Eval_Var_Long = Q.store_thm("Eval_Var_Long",
  `Eval env (Var (Long x y)) (P r) ⇔
   (∃v. lookup_var_id (Long x y) env = SOME v ∧ P r v)`,
  rw[Eval_def,Once bigStepTheory.evaluate_cases]);

val Arrow_imp_do_opapp = Q.store_thm("Arrow_imp_do_opapp",
  `(a --> b) f c ∧ a x v ⇒
   ∃env e u ck.
     do_opapp [c; v] = SOME (env,e) ∧
     evaluate (empty_state with clock := ck) env [e] = (empty_state,Rval [u]) ∧
     b (f x) u`,
  rw[Arrow_def,AppReturns_def,evaluate_closure_def,PULL_EXISTS]
  \\ res_tac
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ simp[]
  \\ fs[funBigStepEquivTheory.functional_evaluate_list]
  \\ fs[bigClockTheory.big_clocked_unclocked_equiv]
  \\ `empty_state with clock := 0 = empty_state`
  by simp[empty_state_def,semanticPrimitivesTheory.state_component_equality]
  \\ rw[Once bigStepTheory.evaluate_cases,PULL_EXISTS]
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ simp[]
  \\ rw[Once bigStepTheory.evaluate_cases]);

(* -- *)

val get_input_length_rec_thm = Q.store_thm("get_input_length_rec_thm",
  `∀ m n s st env.
   s.ffi.oracle = botworld_oracle ∧
   s.ffi.ffi_state = st ∧
   s.ffi.final_event = NONE ∧
   m = LENGTH (encode_observation st.bot_input) ∧
   lookup_var_id (Short "n") env = SOME(Litv(IntLit &n)) ∧
   lookup_var_id (Short "f") env = SOME(Recclosure env0 [("f","n",get_input_length_loop_body)] "f") ∧
   Eval env (Var (Long "Botworld""length_rec")) ((LIST_TYPE WORD8 --> NUM --> SUM_TYPE NUM (OPTION_TYPE NUM)) length_rec)
   ⇒
   ∃ bs ck s'.
   evaluate (s with clock := ck) env [get_input_length_loop_body] = (s',Rval[Litv(IntLit (&m))]) ∧
   s' = s with <| refs := MAP W8array bs ++ s.refs |>`,
  gen_tac \\ completeInduct_on `m` \\ rw[]
  \\ rw[get_input_length_loop_body_def]
  \\ rw (store_v_same_type_def::evals)
  \\ rw[ffiTheory.call_FFI_def]
  \\ rw[botworld_oracle_def]
  \\ rw[botworld_get_input_length_def]
  >- (
    fs[Eval_Var_Long]
    \\ fs evals
    \\ drule (GEN_ALL Arrow_imp_do_opapp)
    \\ qmatch_goalsub_abbrev_tac`W8array ws`
    \\ cheat (* broken *))
  \\ cheat)

val get_input_length_thm = Q.store_thm("get_input_length_thm",
  `lookup_var_id (Long"Botworld""get_input_length") env = SOME (Closure env0 "x" get_input_length_body) ∧
   s.ffi.oracle = botworld_oracle ∧
   evaluate s env [u] = (s,Rval[Conv NONE []]) ∧
   evaluate s env [App Opapp [Var(Long"Botworld""get_input_length"); u]] = (s', res) ∧
   Eval env (Var (Long "Botworld""length_rec")) ((LIST_TYPE WORD8 --> NUM --> SUM_TYPE NUM (OPTION_TYPE NUM)) length_rec) ∧
   res ≠ Rerr(Rabort Rtimeout_error)
   ⇒
   ∃ck bs.
     s' = s with <| refs := MAP W8array bs ++ s.refs;
                    clock := s.clock - ck |>
     ∧ res = Rval[Litv(IntLit (&(LENGTH (encode_observation st.bot_input))))]`,
  rw[evaluate_def] \\ rfs[]
  \\ fs[do_opapp_def]
  \\ every_case_tac \\ fs[]
  \\ qhdtm_x_assum `funBigStep$evaluate` mp_tac
  \\ simp[get_input_length_body_def, evaluate_def, lookup_var_id_def, evalPropsTheory.build_rec_env_merge]
  \\ simp[do_opapp_def, evalPropsTheory.find_recfun_ALOOKUP]
  \\ rw[] \\ fs[] \\ pop_assum mp_tac
  \\ simp[evalPropsTheory.build_rec_env_merge]
  \\ cheat);

val _ = export_theory()
