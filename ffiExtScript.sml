open preamble match_goal terminationTheory

val _ = new_theory"ffiExt";

(* TODO: move the contents of this theory back to CakeML? *)

val ffi_state_rel_def = Define`
  ffi_state_rel oracle R s1 s2 ⇔
    s1.oracle = oracle ∧ s2.oracle = oracle ∧
    R s1.ffi_state s2.ffi_state ∧
    s2 = s1 with ffi_state := s2.ffi_state`;

val ffi_rel_def = Define`
  ffi_rel oracle R s1 s2 ⇔
    ffi_state_rel oracle R s1.ffi s2.ffi ∧
    s2 = s1 with ffi := s2.ffi`;

val ffi_rel_dec_clock = Q.store_thm("ffi_rel_dec_clock",
  `ffi_rel or R s1 s2 ⇒
   ffi_rel or R (dec_clock s1) (dec_clock s2)`,
  EVAL_TAC \\ rw[semanticPrimitivesTheory.state_component_equality]);

val ffi_rel_same_clock = Q.store_thm("ffi_rel_same_clock",
  `ffi_rel or R s1 s2 ⇒ s1.clock = s2.clock`,
  EVAL_TAC \\ rw[semanticPrimitivesTheory.state_component_equality]);

val ffi_rel_same_refs = Q.store_thm("ffi_rel_same_refs",
  `ffi_rel or R s1 s2 ⇒ s1.refs = s2.refs`,
  EVAL_TAC \\ rw[semanticPrimitivesTheory.state_component_equality]);

val ffi_rel_same_defined_mods = Q.store_thm("ffi_rel_same_defined_mods",
  `ffi_rel or R s1 s2 ⇒ s1.defined_mods = s2.defined_mods`,
  EVAL_TAC \\ rw[semanticPrimitivesTheory.state_component_equality]);

val ffi_rel_same_defined_types = Q.store_thm("ffi_rel_same_defined_types",
  `ffi_rel or R s1 s2 ⇒ s1.defined_types = s2.defined_types`,
  EVAL_TAC \\ rw[semanticPrimitivesTheory.state_component_equality]);

fun extends_tac (tac:tactic) ((g as (asl,w)):goal) =
  let
    val asms1 = HOLset.fromList Term.compare asl
    val (gs,v) = tac g
    fun extends asl =
      let
        val asms2 = HOLset.fromList Term.compare asl
      in not (HOLset.isEmpty (HOLset.difference(asms2,asms1))) end
  in
    (assert(List.all (extends o #1)) gs,v)
  end

val call_FFI_invariant_def = Define`
  call_FFI_invariant oracle R ⇔
  ∀ffi ffi'.
    ffi.oracle = oracle ∧
    ffi' = ffi with ffi_state := ffi'.ffi_state ∧
    R ffi.ffi_state ffi'.ffi_state ⇒
    ∀i ws.
      let (ffj,vs) = call_FFI ffi i ws in
      let (ffj',vs') = call_FFI ffi' i ws in
        R ffj.ffi_state ffj'.ffi_state
        ∧ ffj' = ffj with ffi_state := ffj'.ffi_state
        ∧ vs = vs'`;

val do_app_ffi_extensional = Q.store_thm("do_app_ffi_extensional",
  `call_FFI_invariant oracle R ∧
   ffi_state_rel oracle R ffi1 ffi2 ⇒
   OPTION_REL
    (λ((refs1,ffi1),res1) ((refs2,ffi2),res2).
       refs1 = refs2 ∧ res1 = res2 ∧
       ffi2 = ffi1 with ffi_state := ffi2.ffi_state ∧
       ffi1.oracle = oracle ∧ ffi2.oracle = oracle ∧
       R ffi1.ffi_state ffi2.ffi_state)
    (do_app (refs,ffi1) op es)
    (do_app (refs,ffi2) op es)`,
  (match1_tac(mg.acb`o_ : 'a option`,(fn(a,t)=>extends_tac(Cases_on`^(t("o"))` \\fs[]\\rveq))))
  \\ fs[OPTREL_def]
  \\ rpt (match1_tac(mg.acb`o_ : 'a # 'b`,(fn(a,t)=>extends_tac(Cases_on`^(t("o"))` \\fs[]\\rveq))))
  >- (
    reverse(Cases_on`op`)\\fs[semanticPrimitivesTheory.do_app_def]
    \\ every_case_tac \\ fs[UNCURRY]
    \\ spose_not_then strip_assume_tac
    \\ fs[call_FFI_invariant_def,ffi_state_rel_def]
    \\ match_tac([mg.a"1"`_`,mg.a"2"`_`,mg.a"3"`_`], fn(a,t)=>
                 first_x_assum(drule_thm(LIST_CONJ (map a ["1","2","3"]))))
    \\ simp[]
    \\ qmatch_assum_rename_tac`call_FFI _ i ws = _`
    \\ map_every qexists_tac[`i`,`ws`]
    \\ simp[]
    \\ spose_not_then strip_assume_tac
    \\ fs[] )
  \\ rw[ffi_state_rel_def,ffiTheory.ffi_state_component_equality]
  \\ fs[semanticPrimitivesPropsTheory.do_app_cases,semanticPrimitivesTheory.do_app_def] \\ rw[]
  \\ every_case_tac \\ fs[]
  \\ spose_not_then strip_assume_tac
  \\ fs[call_FFI_invariant_def,ffiTheory.ffi_state_component_equality,GSYM CONJ_ASSOC]
  \\ match_tac([mg.a"1"`_`,mg.a"2"`_`,mg.a"3"`_`,mg.a"4"`_`], fn(a,t)=>
               first_x_assum(drule_thm(LIST_CONJ [REFL(rhs(concl(a"1"))),a"1",a"2",a"3",a"4"])))
  \\ simp[]
  \\ qmatch_assum_rename_tac`call_FFI _ i ws = _`
  \\ map_every qexists_tac[`i`,`ws`]
  \\ simp[]
  \\ spose_not_then strip_assume_tac
  \\ fs[]
  \\ fs[ffiTheory.ffi_state_component_equality]
  \\ rveq \\ fs[]
  \\ fs[ffiTheory.call_FFI_def]
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]);

val evaluate_ffi_extensional = Q.store_thm("evaluate_ffi_extensional",
  `call_FFI_invariant oracle R ⇒
   (∀st env es st' res res' st2 st2'.
      ffi_rel oracle R st st' ∧
      evaluate st env es = (st2,res) ∧
      evaluate st' env es = (st2',res')
      ⇒ res = res' ∧ ffi_rel oracle R st2 st2') ∧
   (∀st env v pes err_v st' res res' st2 st2'.
       ffi_rel oracle R st st' ∧
       evaluate_match st env v pes err_v = (st2,res) ∧
       evaluate_match st' env v pes err_v = (st2',res')
       ⇒ res = res' ∧ ffi_rel oracle R st2 st2')`,
  strip_tac
  \\ ho_match_mp_tac evaluate_ind
  \\ rpt conj_tac
  \\ rpt gen_tac \\ simp[evaluate_def] \\ strip_tac
  \\ rveq \\ rpt gen_tac \\ fs[] \\ strip_tac
  \\ TRY (
    every_case_tac
  \\ rpt (qpat_x_assum`_ ∧ _`strip_assume_tac) \\ rveq
  \\ fs[] \\ rfs[] \\ rveq
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ first_x_assum drule \\ fs[]
  \\ rpt( strip_tac \\ rveq)
  \\ spose_not_then strip_assume_tac \\ fs[] \\ rveq
  \\ first_x_assum drule \\ fs[])
  (* App case *)
  \\ every_case_tac
  \\ rpt (qpat_x_assum`_ ∧ _`strip_assume_tac) \\ rveq
  \\ fs[] \\ rfs[] \\ rveq
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ first_x_assum drule \\ fs[]
  \\ rpt( strip_tac \\ rveq)
  \\ spose_not_then strip_assume_tac \\ fs[] \\ rveq
  \\ imp_res_tac ffi_rel_dec_clock
  \\ imp_res_tac ffi_rel_same_clock \\ fs[]
  \\ TRY(first_x_assum drule \\ fs[])
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ imp_res_tac do_app_ffi_extensional
  \\ fs[ffi_rel_def,
        semanticPrimitivesTheory.state_component_equality,
        evaluateTheory.dec_clock_def]
  \\ match_tac(
       [mg.a"h"`ffi_state_rel _ R ffi_ _`,
        mg.bau`do_app (refs_,ffi_) op_ es_`
       ],
       fn(a,t)=>first_x_assum(drule_thm(a"h")) \\ simp[]
                \\ map_every (exists_tac o t) ["refs","op","es"])
  \\ simp[OPTREL_def]
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ fs[ffi_state_rel_def]);

val evaluate_decs_ffi_extensional = Q.store_thm("evaluate_decs_ffi_extensional",
  `call_FFI_invariant oracle R ⇒
   ∀mn st env decs st' res res' st2 st2'.
   ffi_rel oracle R st st' ∧
   evaluate_decs mn st env decs = (st2,res) ∧
   evaluate_decs mn st' env decs = (st2',res')
   ⇒
   res = res' ∧ ffi_rel oracle R st2 st2'`,
  strip_tac
  \\ ho_match_mp_tac evaluateTheory.evaluate_decs_ind
  \\ rw[evaluateTheory.evaluate_decs_def] \\ rw[]
  \\ imp_res_tac ffi_rel_same_defined_types \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[] \\ fs[]
  \\ TRY (
    first_x_assum drule \\ disch_then drule \\ rw[]
    \\ first_x_assum drule \\ disch_then drule \\ rw[])
  \\ imp_res_tac (CONJUNCT1 (UNDISCH evaluate_ffi_extensional)) \\ fs[]
  \\ rveq \\ fs[]
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ fs[ffi_rel_def,semanticPrimitivesTheory.state_component_equality]);

val evaluate_tops_ffi_extensional = Q.store_thm("evaluate_tops_ffi_extensional",
  `call_FFI_invariant oracle R ⇒
   ∀st env tops st' res res' st2 st2'.
   ffi_rel oracle R st st' ∧
   evaluate_tops st env tops = (st2,res) ∧
   evaluate_tops st' env tops = (st2',res')
   ⇒
   res = res' ∧ ffi_rel oracle R st2 st2'`,
  strip_tac
  \\ ho_match_mp_tac evaluateTheory.evaluate_tops_ind
  \\ rw[evaluateTheory.evaluate_tops_def] \\ rw[]
  \\ imp_res_tac ffi_rel_same_defined_mods \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[] \\ fs[]
  \\ TRY (
    first_x_assum drule \\ disch_then drule \\ rw[]
    \\ first_x_assum drule \\ disch_then drule \\ rw[])
  \\ imp_res_tac (UNDISCH evaluate_decs_ffi_extensional) \\ fs[]
  \\ rveq \\ fs[]
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ fs[ffi_rel_def,semanticPrimitivesTheory.state_component_equality]);

val evaluate_prog_ffi_extensional = Q.store_thm("evaluate_prog_ffi_extensional",
  `call_FFI_invariant oracle R ⇒
   ffi_rel oracle R st st' ∧
   evaluate_prog st env prog = (st2,res) ∧
   evaluate_prog st' env prog = (st2',res')
   ⇒
   res = res' ∧ ffi_rel oracle R st2 st2'`,
  simp[evaluateTheory.evaluate_prog_def]
  \\ ntac 2 strip_tac
  \\ imp_res_tac ffi_rel_same_defined_mods
  \\ imp_res_tac ffi_rel_same_defined_types
  \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ metis_tac[evaluate_tops_ffi_extensional]);

val _ = export_theory();
