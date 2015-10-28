open preamble botworldTheory botworld_dataTheory

val _ = new_theory"botworld_props";

(* TODO: move *)
val FLOOKUP_FMAP_MAP2 = Q.store_thm("FLOOKUP_FMAP_MAP2",
  `FLOOKUP (FMAP_MAP2 f m) x =
   OPTION_MAP (CURRY f x) (FLOOKUP m x) `,
  rw[FLOOKUP_DEF,FMAP_MAP2_THM])
(* -- *)

val LENGTH_localActions = Q.store_thm("LENGTH_localActions[simp]",
  `LENGTH (localActions sq nb) = LENGTH sq.robots`,
  EVAL_TAC >> simp[])

val get_focal_robot_def = Define`
  get_focal_robot s =
    EL s.focal_index (s.state ' s.focal_coordinate).robots`;

val policy_fun_def = Define`
  policy_fun p speed obs =
   let r = runMachine (ffi_from_observation obs, <| memory := p; processor := speed |>) in
   (r.command,r.memory)`;

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val square_update_robot_o = Q.store_thm("square_update_robot_o",
  `square_update_robot (f o g) i = square_update_robot f i o square_update_robot g i`,
  rw[square_update_robot_def,FUN_EQ_THM,square_component_equality] >>
  simp[LIST_EQ_REWRITE,EL_LUPDATE])

val set_policy_def = Define`
  set_policy r i ps =
    r with memory updated_by (λm. if i < LENGTH ps then EL i ps else m)`;

val set_policy_const = Q.store_thm("set_policy_const[simp]",
  `(set_policy r x ps).inventory = r.inventory`,
  EVAL_TAC)

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

val set_policy_less = Q.store_thm("set_policy_less",
  `LENGTH ps ≤ i ⇒ set_policy r i ps = r`,
   simp[set_policy_def] >> rw[robot_component_equality])

val set_policies_APPEND1 = Q.store_thm("set_policies_APPEND1",
  `LENGTH ps ≤ LENGTH ls ⇒
    set_policies (ls ++ ex) ps = set_policies ls ps ++ ex`,
  rw[set_policies_thm,ONCE_REWRITE_RULE[ADD_COMM]GENLIST_APPEND] >>
  rw[APPEND_EQ_APPEND] >> disj1_tac >> qexists_tac`[]` >>
  rw[LIST_EQ_REWRITE,EL_APPEND1,EL_APPEND2] >>
  simp[set_policy_less])

val shatter_ignores_policy = Q.store_thm("shatter_ignores_policy[simp]",
  `shatter (set_policy r i ps) = shatter r`,
  EVAL_TAC)

val square_set_policies_def = Define`
  square_set_policies ps sq = sq with <| robots := set_policies sq.robots ps |>`;

val square_set_policies_const = Q.store_thm("square_set_policies_const[simp]",
  `(square_set_policies ps sq).items = sq.items ∧
   (square_set_policies ps sq).robots = set_policies sq.robots ps`,
  EVAL_TAC)

val LENGTH_square_set_policies_robots = Q.store_thm("LENGTH_square_set_policies_robots[simp]",
  `LENGTH (square_set_policies ps sq).robots = LENGTH sq.robots`,
  rw[square_set_policies_def]);

val LENGTH_FILTER_set_policies_ignore = Q.prove(
  `(∀r p. P r ⇔ P (r with memory := p)) ⇒
   ∀ls ps. LENGTH (FILTER P (set_policies ls ps)) = LENGTH (FILTER P ls)`,
   strip_tac >>
   Induct >> simp[set_policies_def] >>
   Cases_on`ps`>>simp[set_policies_def] >>
   rw[] >> metis_tac[])

val contested_ignores_policy = Q.store_thm("contested_ignores_policy[simp]",
  `contested (square_set_policies ps sq) n ⇔ contested sq n`,
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
  `act (square_set_policies ps sq) nb i = fix_inspected ps (act sq nb i)`,
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
  `localActions (square_set_policies ps sq) nb = MAP (fix_inspected ps) (localActions sq nb)`,
  rw[localActions_def,MAP_GENLIST] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM])

val updateInventory_ignores_policy = Q.store_thm("updateInventory_ignores_policy",
  `i < LENGTH sq.robots ⇒
   (updateInventory (square_set_policies ps sq) i a =
    set_policy (updateInventory sq i a) i ps)`,
  rw[updateInventory_def,square_set_policies_def] >>
  rfs[EL_set_policies] >>
  simp[Abbr`r`] >>
  BasicProvers.CASE_TAC >> simp[set_policy_def]);

val GENLIST_updateInventory_ignores_policy = Q.store_thm("GENLIST_updateInventory_ignores_policy[simp]",
  `GENLIST (λi. updateInventory (square_set_policies ps sq) i (f i)) (LENGTH sq.robots) =
   GENLIST (λi. set_policy (updateInventory sq i (f i)) i ps) (LENGTH sq.robots)`,
  rw[LIST_EQ_REWRITE,updateInventory_ignores_policy])

val updateInventory_fix_inspected = Q.store_thm("updateInventory_fix_inspected[simp]",
  `updateInventory sq x (fix_inspected ps y) = updateInventory sq x y`,
  Cases_on`y`>>simp[fix_inspected_def] >> EVAL_TAC)

val incomingFrom_MovedIn = Q.store_thm("incomingFrom_MovedIn",
  `MEM x (incomingFrom y z) ⇒ ∃i. SND x = MovedIn i`,
  Cases_on`z`>>rw[incomingFrom_def]>>
  fs[MEM_FLAT,MEM_MAP] >>
  every_case_tac >> fs[] >> rw[] >> fs[]);

val event_set_policies_def = Define`
  event_set_policies ps ev =
    ev with robotActions updated_by
      (λls. ZIP (set_policies (MAP FST ls) ps, MAP (fix_inspected ps) (MAP SND ls)))`;

val event_ignores_policy = Q.store_thm("event_ignores_policy",
  `LENGTH ps ≤ LENGTH sq.robots ⇒
   event (square_set_policies ps sq) nb =
   event_set_policies ps (event sq nb)`,
  rw[event_set_policies_def,event_def,event_component_equality] >> rw[] >>
  `LENGTH actions = LENGTH actions' ∧
   LENGTH veterans = LENGTH veterans' ∧
   children = children' ∧
   fallen = fallen'` by (
     unabbrev_all_tac >> simp[] >>
     simp[LENGTH_FLAT,MAP_GENLIST,MAP_MAP_o] >>
     rw[] >> AP_TERM_TAC >>
     simp[LIST_EQ_REWRITE,EL_MAP] >>
     rw[] >- (
       match_mp_tac EQ_SYM >>
       BasicProvers.CASE_TAC >>
       simp[fix_inspected_def] )
     >- (
       match_mp_tac EQ_SYM >>
       BasicProvers.CASE_TAC >>
       simp[fix_inspected_def] ) >>
     fs[MEM_MAP,EL_MAP] >- (
       Cases_on`y`>>fs[fix_inspected_def]>>
       rw[] >> fs[] ) >>
     first_x_assum(qspec_then`Destroyed x`mp_tac) >>
     simp[fix_inspected_def] ) >>
  `LENGTH veterans = LENGTH actions` by (
    unabbrev_all_tac >> simp[localActions_def] ) >>
  `LENGTH actions' = LENGTH sq.robots` by simp[Abbr`actions'`]
  >- (
    simp[GSYM ZIP_APPEND,MAP_MAP_o] >>
    simp[MAP_ZIP,LENGTH_REPLICATE] >>
    simp[REPLICATE_GENLIST,MAP_GENLIST,fix_inspected_def] >>
    simp[set_policies_APPEND1] >>
    simp[GSYM ZIP_APPEND] >>
    `MAP (fix_inspected ps o SND) immigrations = MAP SND immigrations` by (
      simp[Abbr`immigrations`,MAP_FLAT] >> AP_TERM_TAC >>
      simp[MAP_GENLIST] >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
      imp_res_tac incomingFrom_MovedIn >>
      rw[fix_inspected_def] ) >>
    simp[] >>
    simp[ZIP_MAP,MAP_MAP_o,o_DEF] >>
    AP_TERM_TAC >> simp[] >>
    simp[Abbr`veterans'`,Abbr`veterans`] >>
    simp[set_policies_thm,LIST_EQ_REWRITE] >>
    simp[Abbr`actions`] >>
    simp[EL_MAP] )
  >- (
    simp[Abbr`actions`] >>
    simp[EXISTS_MAP] >>
    rpt AP_THM_TAC >> AP_TERM_TAC >>
    rw[FUN_EQ_THM] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[FUN_EQ_THM] >>
    Cases >> simp[fix_inspected_def] )
  >- (
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,LENGTH_ZIP,EL_MAP] >>
    simp[EL_ZIP] >>
    simp[EL_set_policies] >>
    simp[Abbr`actions`,EL_MAP] >>
    rw[] >>
    Cases_on`EL x actions'` >> fs[fix_inspected_def]))

val neighbours_ignores_policy = Q.store_thm("neighbours_ignores_policy[simp]",
  `neighbours (square_set_policies ps o_f g) c =
   MAP (OPTION_MAP (square_set_policies ps)) (neighbours g c)`,
  Cases_on`c`>>rw[neighbours_def,FLOOKUP_o_f] >>
  BasicProvers.CASE_TAC >> rw[])

(*
val computeEvents_ignores_policy = Q.store_thm("computeEvents_ignores_policy",
  `computeEvents (square_set_policies ps o_f g) =
     event_set_policies ps o_f computeEvents g`,
  rw[computeEvents_def,fmap_eq_flookup,FLOOKUP_FMAP_MAP2,fmap_rel_OPTREL_FLOOKUP,FLOOKUP_o_f] >>
  Cases_on`FLOOKUP g k`>>simp[] >>
  event_ignores_policy
  neighbours_def
  OPTION_MAP (robot_command o robots) over the neighbours in event, since that's all that matters about them

val fill_square_set_policies = Q.store_thm("fill_square_set_policies",
  `i < LENGTH sq.robots ⇒
     fill_square (c,p) sq i =
     square_set_policies
       (GENLIST (λj. if i = j then p else (EL j sq.robots).memory) (LENGTH sq.robots))
       (fill_square (c,[]) sq i)`,
  rw[fill_square_def,square_component_equality,set_policies_thm] >>
  simp[LIST_EQ_REWRITE,EL_LUPDATE] >>
  ONCE_REWRITE_TAC[set_policy_def] >>
  simp[] >>
  ONCE_REWRITE_TAC[robot_component_equality] >>
  simp[] >> gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[])
*)

val updated_policies_def = Define`
  updated_policies i f sq =
    GENLIST (λj. (if i = j then f else I) (EL j sq.robots).memory) (LENGTH sq.robots)`;

val square_update_robot_set_policies = Q.store_thm("square_update_robot_set_policies",
  `i < LENGTH sq.robots ⇒
   square_update_robot (memory_fupd f) i sq =
   square_set_policies (updated_policies i f sq) sq`,
  rw[square_component_equality,square_update_robot_def,set_policies_thm,updated_policies_def] >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE] >> rw[] >>
  rw[set_policy_def,robot_component_equality])

val event_ignores_policy1 = Q.prove(
  `i < LENGTH sq.robots ⇒
     event (square_update_robot (memory_fupd f) i sq) nb =
     event_set_policies (updated_policies i f sq) (event sq nb)`,
  rw[square_update_robot_set_policies] >>
  match_mp_tac event_ignores_policy >>
  rw[updated_policies_def] );

(*
val computeEvents_ignores_policy = Q.store_thm("computeEvents_ignores_policy",
  `i < LENGTH sq.robots ⇒
   computeEvents (g |+ (c,square_update_robot (memory_fupd f) i sq)) =
   computeEvents (g |+ (c,sq))`,
  rw[computeEvents_def,fmap_eq_flookup,FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> simp[] >- (
    rw[event_ignores_policy1]

    ... )
  Cases_on`FLOOKUP g k`>>simp[]

  simp[OPTION_MAP_def]
  Ca
  f"option_map"

val _ = overload_on("with_policy",``λc p.  robot_memory_fupd (K p) o robot_command_fupd (K c)``);

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ∧
   policy_fun p (get_focal_robot s).processor obs = (c',p')
   ⇒
   step (fill (with_policy c p) s) = fill (with_policy c' p') s'`,
  rw[wf_state_with_hole_def,fill_def,get_focal_robot_def,step_def,steph_def] >>
  simp[square_update_robot_o] >>
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
