open preamble botworldTheory botworld_dataTheory

val _ = new_theory"botworld_props";

val get_focal_robot_def = Define`
  get_focal_robot s =
    EL s.focal_index (s.state ' s.focal_coordinate).robots`;

val policy_fun_def = Define`
  policy_fun p speed obs =
   let r = runMachine (ffi_from_observation obs, <| memory := p; processor := speed |>) in
   (r.command,r.memory)`;

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val set_policy_def = Define`
  set_policy r i ps =
    r with memory updated_by (λm. if i < LENGTH ps then EL i ps else m)`;

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
     set_policy (EL i rs) i ps`,
  map_every qid_spec_tac[`i`,`ps`] >>
  Induct_on`rs` >> simp[] >>
  Cases_on`ps`>>simp[set_policies_def] >- (
    rw[robot_component_equality,set_policy_def] ) >>
  gen_tac >> Cases >> simp[set_policy_def] >>
  simp[robot_component_equality])

val set_policies_thm = Q.store_thm("set_policies_thm",
  `set_policies rs ps = GENLIST (λi. set_policy (EL i rs) i ps) (LENGTH rs)`,
  rw[LIST_EQ_REWRITE,EL_set_policies]);

(*
val set_policies_append = Q.store_thm("set_policies_append",
  `set_policies (a ++ b) ps =
   set_policies a ps ++
   GENLIST (λi. set_policy (EL (LENGTH a + i) b) (LENGTH a + i) ps) (LENGTH b)`,
  rw[set_policies_thm, GENLIST_APPEND] >>
*)

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
  simp[inspectShielded_def] >> simp[EL_set_policies,set_policy_def]);

val destroyShielded_ignores_policy = Q.store_thm("destroyShielded_ignores_policy[simp]",
  `n < LENGTH ls ⇒
    (destroyShielded (set_policies ls ps) n ⇔ destroyShielded ls n)`,
  simp[destroyShielded_def] >> simp[EL_set_policies,set_policy_def]);

val fix_inspected_def = Define`
  (fix_inspected ps (Inspected j r) = Inspected j (set_policy r j ps)) ∧
  (fix_inspected _ a = a)`;

val act_ignores_policy = Q.store_thm("act_ignores_policy[simp]",
  `act (square_set_policies sq ps) nb i = fix_inspected ps (act sq nb i)`,
  rw[act_def,square_set_policies_def,fix_inspected_def] >>
  rfs[EL_set_policies] >> fs[] >>
  `r'.command = r.command` by simp[Abbr`r`]
  >- simp[set_policy_def] >>
  simp[] >>
  BasicProvers.CASE_TAC >> fs[LET_THM] >>
  TRY (rw[fix_inspected_def]>>fs[set_policy_def]>>NO_TAC)
  >- (
    simp[Abbr`r`,canLift_def] >>
    rw[fix_inspected_def] >> fs[set_policy_def])
  >- (
    rw[Abbr`r`,fix_inspected_def] >> fs[set_policy_def])
  >- (
    simp[o_DEF,GSYM square_set_policies_def] >>
    rw[fix_inspected_def] >>
    BasicProvers.CASE_TAC >> rw[fix_inspected_def]))

val localActions_ignores_policy = Q.store_thm("localActions_ignores_policy[simp]",
  `localActions (square_set_policies sq ps) nb = MAP (fix_inspected ps) (localActions sq nb)`,
  rw[localActions_def,MAP_GENLIST] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM])

val updateInventory_ignores_policy = Q.store_thm("updateInventory_ignores_policy",
  `i < LENGTH sq.robots ⇒
   (updateInventory (square_set_policies sq ps) i a =
    set_policy (updateInventory sq i a) i ps)`,
  rw[updateInventory_def,square_set_policies_def] >>
  rfs[EL_set_policies] >>
  simp[Abbr`r`] >>
  BasicProvers.CASE_TAC >> simp[set_policy_def]);

val GENLIST_updateInventory_ignores_policy = Q.store_thm("GENLIST_updateInventory_ignores_policy[simp]",
  `GENLIST (λi. updateInventory (square_set_policies sq ps) i (f i)) (LENGTH sq.robots) =
   GENLIST (λi. set_policy (updateInventory sq i (f i)) i ps) (LENGTH sq.robots)`,
  rw[LIST_EQ_REWRITE,updateInventory_ignores_policy])

(*
val event_ignores_policy = Q.store_thm("event_ignores_policy",
  `event (square_set_policies sq ps) nb =
   event sq nb with robotActions updated_by
     (λls. ZIP (set_policies (MAP FST ls) ps, MAP (fix_inspected ps) (MAP SND ls)))`,
  rw[event_def,event_component_equality] >> rw[] >>
  `LENGTH actions = LENGTH actions' ∧
   LENGTH veterans = LENGTH veterans' ∧
   children = children' ∧
   LENGTH fallen = LENGTH fallen'` by (
     unabbrev_all_tac >> simp[] >>
     simp[LENGTH_FLAT,MAP_GENLIST,MAP_MAP_o] >>
     rw[] >> AP_TERM_TAC >>
     simp[LIST_EQ_REWRITE,EL_MAP] >>
     rw[] >- (
       match_mp_tac EQ_SYM >>
       BasicProvers.CASE_TAC >>
       simp[fix_inspected_def] ) >>
     >- (
       match_mp_tac EQ_SYM >>
       BasicProvers.CASE_TAC >>
       simp[fix_inspected_def] ) >>
     fs[MEM_MAP] >- (
       Cases_on`y`>>fs[fix_inspected_def]>>
       rw[] >> fs[] ) >>
     first_x_assum(qspec_then`Destroyed x`mp_tac) >>
     simp[fix_inspected_def] ) >>
  `LENGTH veterans = LENGTH actions` by (
    unabbrev_all_tac >> simp[localActions_def] )
  >- (
    simp[GSYM ZIP_APPEND,MAP_MAP_o] >>
    simp[MAP_ZIP,LENGTH_REPLICATE] >>
    simp[REPLICATE_GENLIST,MAP_GENLIST,fix_inspected_def] >>
    simp[GSYM ZIP_APPEND]
    simp[set_policies_thm] >>
    simp[fix_inspected_def] >>
    ZIP_APPEND
    ZIP_GENLIST
    simp[ZIP_MAP]
    simp[APPEND_LENGTH_EQ,LENGTH_ZIP,MAP_ZIP]
    match_mp_tac APPEND_EQ
    f"append_eq"
    m``l1:'a list ++ l2 = l3 ++ l4``


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
