open preamble botworld_quoteLib

val _ = new_theory"botworld_quote";

val (quote_num_aux_def,quote_num_def) = mk_quote NONE ``:num``
val (quote_level_aux_def,quote_level_def) = mk_quote NONE ``:level``

val (quote_prod_aux_def,quote_prod_def) = mk_quote (SOME(["q1","q2"],["t1","t2"])) ``:'a # 'b``

val quote_prod_aux_cong = Q.store_thm("quote_prod_aux_cong",
  `∀xy1 xy2 qta1 qtb1 qta2 qtb2.
   xy1 = xy2 ∧
   (∀q1 t1 q2 t2 x1. qta1 = (q1,t1) ∧ qta2 = (q2,t2) ∧ x1 = FST xy1 ⇒ t1 = t2 ∧ q1 x1 = q2 x1) ∧
   (∀q1 t1 q2 t2 y1. qtb1 = (q1,t1) ∧ qtb2 = (q2,t2) ∧ y1 = SND xy1 ⇒ t1 = t2 ∧ q1 y1 = q2 y1)
   ⇒
   quote_prod_aux (qta1,qtb1) xy1 = quote_prod_aux (qta2,qtb2) xy2 `,
  rpt Cases \\ rw[quote_prod_aux_def]);
val _ = DefnBase.export_cong "quote_prod_aux_cong";

val (quote_list_aux_def,quote_list_def) = mk_quote (SOME(["q"],["t"])) ``:'a list``

val quote_list_aux_cong = Q.store_thm("quote_list_aux_cong",
  `!l1 l2 t1 t2 q1 q2.
      l1 = l2 /\
      t1 = t2 /\
      (!a. MEM a l1 ==> q1 a = q2 a)
      ==> quote_list_aux (q1,t1) l1 = quote_list_aux (q2,t2) l2`,
  Induct \\ rw[quote_list_aux_def] \\ rw[quote_list_aux_def]);
val _ = DefnBase.export_cong "quote_list_aux_cong";

val quote_list_is_aux = Q.prove(
  `FST (quote_list (x,y)) z = quote_list_aux (x,y) z`,
  rw[quote_list_def]);

val _ = aux_rws := concl quote_list_is_aux :: !aux_rws

val quote_char_aux_def = Define `quote_char_aux c = Comb ^(term_to_deep ``CHR``) (quote_num_aux (ORD c))`
val quote_char_def = Define `quote_char = (quote_char_aux , ^(type_to_deep ``:char``))`

val (quote_id_aux_def,quote_id_def) = mk_quote (SOME(["q"],["t"])) ``:'a id``
val (quote_tctor_aux_def,quote_tctor_def) = mk_quote NONE ``:tctor``

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

val (quote_lit_aux_def,quote_lit_def) = mk_quote NONE ``:lit``

val _ = mk_quote_tac := (wf_rel_tac `measure pat_size` \\ gen_tac \\ Induct \\ rw[astTheory.pat_size_def]
                                   \\ simp[] \\ res_tac \\ simp[])
val (quote_pat_aux_def,quote_pat_def) = mk_quote NONE ``:pat``
val quote_pat_aux_def = save_thm("quote_pat_aux_def",quote_pat_aux_def |> REWRITE_RULE[GSYM quote_list_is_aux,ETA_AX])

val (quote_opn_aux_def,quote_opn_def) = mk_quote NONE ``:opn``
val (quote_opb_aux_def,quote_opb_def) = mk_quote NONE ``:opb``
val (quote_op_aux_def,quote_op_def) = mk_quote NONE ``:op``
val (quote_lop_aux_def,quote_lop_def) = mk_quote NONE ``:lop``

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

val (quote_command_aux_def,quote_command_def) = mk_quote NONE ``:command``

val _ = overload_on("quote_prog",``quote_list quote_top``);

val (quote_privateData_aux_def,quote_privateData_def) = mk_quote NONE ``:privateData``

val quote_event_def = Define`
  quote_event = (ARB:event->term,ARB:type) (* TODO *)`;

val _ = overload_on("quote_observation",
    ``quote_prod (quote_num,(quote_prod (quote_event,quote_privateData)))``);

val _ = export_theory();
