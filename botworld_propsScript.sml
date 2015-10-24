open preamble botworldTheory botworld_dataTheory

val _ = new_theory"botworld_props";

val get_focal_robot_def = Define`
  get_focal_robot s =
    EL s.focal_index (s.state ' s.focal_coordinate).robots`;

val policy_fun_def = Define`
  policy_fun p speed obs =
   let r = runMachine (ffi_from_observation obs, <| memory := p; processor := <| speed := speed |> |>) in
   (r.command,r.memory)`;

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val set_policies_def = Define`
  (set_policies [] _ = []) ∧
  (set_policies rs [] = rs) ∧
  (set_policies (r::rs) (p::ps) = (r with memory := p)::(set_policies rs ps))`;

val LENGTH_set_policies = Q.store_thm("LENGTH_set_policies[simp]",
  `LENGTH (set_policies rs ps) = LENGTH rs`,
  qid_spec_tac`ps`>>
  Induct_on`rs`>>simp[set_policies_def]>>
  Cases_on`ps`>>simp[set_policies_def]);

val EL_set_policies = Q.store_thm("EL_set_policies",
  `i < LENGTH rs ⇒
     EL i (set_policies rs ps) =
     (EL i rs with memory := if i < LENGTH ps then EL i ps else (EL i rs).memory)`,
  map_every qid_spec_tac[`i`,`ps`] >>
  Induct_on`rs` >> simp[] >>
  Cases_on`ps`>>simp[set_policies_def] >- (
    rw[robot_component_equality] ) >>
  gen_tac >> Cases >> simp[])

val square_set_policies_def = Define`
  square_set_policies sq ps = sq with <| robots := set_policies sq.robots ps |>`;

val LENGTH_square_set_policies_robots = Q.store_thm("LENGTH_square_set_policies_robots[simp]",
  `LENGTH (square_set_policies sq ps).robots = LENGTH sq.robots`,
  rw[square_set_policies_def]);

val LENGTH_FILTER_set_policies_ignore = Q.prove(
  `(∀r p. P r ⇔ P (r with memory := p)) ⇒
   ∀ls ps. LENGTH (FILTER P (set_policies ls ps)) = LENGTH (FILTER P ls)`,
   strip_tac >>
   Induct >> simp[set_policies_def] >>
   Cases_on`ps`>>simp[set_policies_def] >>
   rw[] >> metis_tac[])

val contested_ignores_policy = Q.store_thm("contested_ignores_policy[simp]",
  `contested (square_set_policies sq ps) n ⇔ contested sq n`,
  rw[contested_def,square_set_policies_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  match_mp_tac LENGTH_FILTER_set_policies_ignore >>
  simp[canLift_def])

val MAP_robot_command_set_policies = Q.store_thm("MAP_robot_command_set_policies[simp]",
  `MAP robot_command (set_policies rs ps) = MAP robot_command rs`,
  qid_spec_tac`ps`>>
  Induct_on`rs` >>
  simp[set_policies_def] >>
  Cases_on`ps`>>simp[set_policies_def])

val inspectShielded_ignores_policy = Q.store_thm("inspectShielded_ignores_policy[simp]",
  `n < LENGTH ls ⇒
    (inspectShielded (set_policies ls ps) n ⇔ inspectShielded ls n)`,
  simp[inspectShielded_def] >> simp[EL_set_policies]);

val destroyShielded_ignores_policy = Q.store_thm("destroyShielded_ignores_policy[simp]",
  `n < LENGTH ls ⇒
    (destroyShielded (set_policies ls ps) n ⇔ destroyShielded ls n)`,
  simp[destroyShielded_def] >> simp[EL_set_policies]);

val fix_inspected_def = Define`
  (fix_inspected ps (Inspected j r) =
     Inspected j (r with memory := if j < LENGTH ps then EL j ps else r.memory)) ∧
  (fix_inspected _ a = a)`;

val act_ignores_policy = Q.store_thm("act_ignores_policy[simp]",
  `act (square_set_policies sq ps) nb i = fix_inspected ps (act sq nb i)`,
  rw[act_def,square_set_policies_def,fix_inspected_def] >>
  rfs[EL_set_policies] >> fs[] >>
  `r'.command = r.command` by simp[Abbr`r`] >>
  simp[] >>
  BasicProvers.CASE_TAC >> fs[LET_THM] >>
  TRY (rw[fix_inspected_def]>>NO_TAC)
  >- (
    simp[Abbr`r`,canLift_def] >>
    rw[fix_inspected_def])
  >- (
    rw[Abbr`r`,fix_inspected_def] )
  >- (
    simp[o_DEF,GSYM square_set_policies_def] >>
    rw[fix_inspected_def] >>
    BasicProvers.CASE_TAC >> rw[fix_inspected_def]))

(*
val localActions_ignores_policy = Q.store_thm("localActions_ignores_policy",
  `localActions (square_set_policies sq ps) nb = localActions sq nb`,
  rw[localActions_def]

val event_ignores_policy = Q.store_thm("event_ignores_policy",
  `event (square_set_policies sq ps) nb =
   event sq nb with robotActions updated_by
     (λls. ZIP (set_policies (MAP FST ls) ps, MAP SND ls))`,
  rw[event_def]

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s')
   ⇒
   step (fill (c,p) s) = fill (policy_fun p (get_focal_robot s).processor.speed obs) s'`,
  rw[wf_state_with_hole_def,fill_def,get_focal_robot_def,step_def,steph_def] >>
  `Abbrev(sq = s.state ' s.focal_coordinate)` by (
    fs[FLOOKUP_DEF,markerTheory.Abbrev_def] ) >> simp[] >>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  qpat_assum`_ = s'`(assume_tac o Abbrev_intro o SYM) >>
  computeEvents_def
  event_def
  EQ_MP
  var_eq_tac >> simp[]
  qpat_assum
*)

val _ = export_theory();
