open preamble botworldTheory botworld_dataTheory

val _ = new_theory"botworld_props";

(* TODO: move *)

val FLOOKUP_FMAP_MAP2 = Q.store_thm("FLOOKUP_FMAP_MAP2",
  `FLOOKUP (FMAP_MAP2 f m) x =
   OPTION_MAP (CURRY f x) (FLOOKUP m x) `,
  rw[FLOOKUP_DEF,FMAP_MAP2_THM])

val FILTER_INDICES = Q.store_thm("FILTER_INDICES",
  `∃f.
     (∀i. i < LENGTH (FILTER P ls) ⇒ EL i (FILTER P ls) = EL (f i) ls) ∧
     (INJ f (count (LENGTH (FILTER P ls))) (count (LENGTH ls))) ∧
     (∀x y. x < LENGTH (FILTER P ls) ∧ y < LENGTH (FILTER P ls) ∧ x < y ⇒ f x < f y)`,
  Induct_on`ls` >> simp[] >>
  gen_tac >>
  IF_CASES_TAC >> fs[] >- (
    qexists_tac`λi. if i = 0 then 0 else SUC (f (PRE i))` >>
    simp[] >>
    conj_tac >- ( Cases >> simp[EL_CONS] ) >>
    conj_tac >- (
      fs[INJ_DEF] >>
      conj_tac >> Cases >> simp[] >>
      Cases >> simp[] ) >>
    Cases >> simp[] ) >>
  qexists_tac`SUC o f` >> simp[] >> fs[INJ_DEF]);

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val ZIP_MAP_PAIR = Q.store_thm("ZIP_MAP_PAIR",
  `LENGTH l1 = LENGTH l2 ⇒
   ZIP (MAP f1 l1,MAP f2 l2) = MAP (f1 ## f2) (ZIP(l1,l2))`,
  rw[ZIP_MAP,MAP_MAP_o] >> simp[o_DEF] >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM,FORALL_PROD]);

val MEM_EL_P = Q.store_thm("MEM_EL_P",
  `∀l. (∃n. n < LENGTH l ∧ P (EL n l)) ⇔ (∃x. MEM x l ∧ P x)`,
  rw[MEM_EL] >> metis_tac[]);

(* -- *)

val incomingFrom_MovedIn = Q.store_thm("incomingFrom_MovedIn",
  `MEM x (incomingFrom y z) ⇒ ∃i. SND x = MovedIn i`,
  Cases_on`z`>>rw[incomingFrom_def]>>
  fs[MEM_FLAT,MEM_MAP] >>
  every_case_tac >> fs[] >> rw[] >> fs[]);

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

val square_update_robot_o = Q.store_thm("square_update_robot_o",
  `square_update_robot (f o g) i = square_update_robot f i o square_update_robot g i`,
  rw[square_update_robot_def,FUN_EQ_THM,square_component_equality] >>
  simp[LIST_EQ_REWRITE,EL_LUPDATE])

val wf_state_with_hole_find_focal = Q.store_thm("wf_state_with_hole_find_focal",
  `wf_state_with_hole s ⇒
    find_focal s.state = (s.focal_coordinate,s.focal_index)`,
  rw[wf_state_with_hole_def,find_focal_def] >>
  SELECT_ELIM_TAC >> metis_tac[])

val map_robotActions_def = Define
  `map_robotActions f (ra:(robot#action) list) = ZIP(MAP (f o FST) ra,MAP SND ra)`;

val if_focal_def = Define`
  if_focal f r = if r.focal then f r else r`;

val map_inspected_def = Define`
  (map_inspected f (Inspected j r) = Inspected j (f r)) ∧
  (map_inspected _ a = a)`;
val _ = export_rewrites["map_inspected_def"];

val LENGTH_square_update_robot = Q.store_thm("LENGTH_square_update_robot[simp]",
  `LENGTH (square_update_robot f i sq).robots = LENGTH sq.robots`,
  rw[square_update_robot_def]);

val LENGTH_FILTER_memory = Q.prove(
  `(∀r p. P r ⇔ P (r with memory := p)) ⇒
   ∀ls ps i. i < LENGTH ls ⇒
     LENGTH (FILTER P (LUPDATE (EL i ls with memory := p) i ls)) = LENGTH (FILTER P ls)`,
   strip_tac >>
   Induct >> simp[] >>
   gen_tac >> Cases >> simp[] >>
   simp[LUPDATE_def] >>
   rw[] >> rfs[] >>
   metis_tac[]);

val contested_ignores_policy = Q.store_thm("contested_ignores_policy[simp]",
  `i < LENGTH sq.robots ⇒
   (contested (sq with robots updated_by LUPDATE (EL i sq.robots with memory := p) i) n ⇔ contested sq n)`,
  rw[contested_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  match_mp_tac (MP_CANON LENGTH_FILTER_memory) >>
  simp[canLift_def])

val inspectShielded_ignores_policy = Q.store_thm("inspectShielded_ignores_policy[simp]",
  `i < LENGTH ls ∧ n < LENGTH ls ⇒
   (inspectShielded (LUPDATE (EL i ls with memory := p) i ls) n ⇔
    inspectShielded ls n)`,
  rw[inspectShielded_def] >>
  simp[EL_LUPDATE] >>
  simp[inspectAttempts_def,FILTER_MAP] >>
  simp[LENGTH_FILTER_memory] >> rw[])

val destroyShielded_ignores_policy = Q.store_thm("destroyShielded_ignores_policy[simp]",
  `i < LENGTH ls ∧ n < LENGTH ls ⇒
   (destroyShielded (LUPDATE (EL i ls with memory := p) i ls) n ⇔
    destroyShielded ls n)`,
  rw[destroyShielded_def] >>
  simp[EL_LUPDATE] >>
  simp[destroyAttempts_def,FILTER_MAP] >>
  simp[LENGTH_FILTER_memory] >> rw[])

val MAP_robot_command_square_update_robot_memory_fupd = Q.store_thm("MAP_robot_command_square_update_robot_memory_fupd[simp]",
  `MAP robot_command (square_update_robot (memory_fupd f) x sq).robots =
   MAP robot_command sq.robots`,
  rw[square_update_robot_def] >>
  rw[LIST_EQ_REWRITE,EL_MAP,EL_LUPDATE] >>
  rw[]);

val updateInventory_ignores_policy = Q.store_thm("updateInventory_ignores_policy",
  `i < LENGTH sq.robots ∧
   (∀z. (z < LENGTH sq.robots ∧ (EL z sq.robots).focal) ⇔ z = fi)
   ⇒
   updateInventory (square_update_robot (memory_fupd (K p)) fi sq) i a =
   if_focal (memory_fupd (K p)) (updateInventory sq i a)`,
  rw[] >>
  `fi < LENGTH sq.robots` by metis_tac[] >>
  rw[updateInventory_def] >>
  Cases_on`a`>>simp[if_focal_def] >>
  unabbrev_all_tac >> fs[] >>
  fs[square_update_robot_def,EL_LUPDATE] >>
  (Cases_on`(EL i sq.robots).focal` >|[
     `i = fi` by metis_tac[],
     `i ≠ fi` by metis_tac[]
     ]) >>
  simp[]);

val updateInventory_const = Q.store_thm("updateInventory_const[simp]",
  `(updateInventory sq i a).memory = (EL i sq.robots).memory ∧
   (updateInventory sq i a).focal = (EL i sq.robots).focal`,
  rw[updateInventory_def] >>
  BasicProvers.CASE_TAC >> rw[])

val updateInventory_map_inspected = Q.store_thm("updateInventory_map_inspected[simp]",
  `updateInventory sq i (map_inspected f a) = updateInventory sq i a`,
  Cases_on`a`>>simp[updateInventory_def]);

val MEM_Built_localActions_not_focal = Q.store_thm("MEM_Built_localActions_not_focal",
  `MEM (Built x r) (localActions a b) ⇒ ¬r.focal`,
  rw[localActions_def,MEM_GENLIST,act_def,LET_THM] >>
  pop_assum mp_tac >> CASE_TAC >> fs[] >>
  every_case_tac >> fs[] >>
  fs[construct_def] >>
  every_case_tac >> fs[] >> rw[]);

val Destroyed_eq_map_inspected = Q.store_thm("Destroyed_eq_map_inspected[simp]",
  `Destroyed x = map_inspected f a ⇔ Destroyed x = a`,
  Cases_on`a`>>simp[]);

val shatter_if_focal_memory_fupd = Q.store_thm("shatter_if_focal_memory_fupd[simp]",
  `shatter (if_focal (memory_fupd x) r) = shatter r`,
  rw[if_focal_def,shatter_def]);

val if_focal_memory_fupd_inventory = Q.store_thm("if_focal_memory_fupd_inventory[simp]",
  `(if_focal (memory_fupd x) r).inventory = r.inventory`,
  rw[if_focal_def]);

val less8 = Q.prove(
  `x < 8n ⇔ (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7)`,
  rw[EQ_IMP_THM] >> simp[])

val updateInventory_ignores_policy2 = Q.store_thm("updateInventory_ignores_policy2",
  `¬(EL i sq.robots).focal ⇒
   if_focal (memory_fupd x) (updateInventory sq i a) = updateInventory sq i a`,
  rw[updateInventory_def] >>
  rw[if_focal_def] >>
  CASE_TAC >> fs[]);

val computeEvents_with_focal_policy = Q.store_thm("computeEvents_with_focal_policy",
  `wf_state_with_hole s
   ⇒
   computeEvents (fill (memory_fupd (K p)) s) =
   (λev. ev with robotActions updated_by MAP (if_focal (memory_fupd (K p)) ## map_inspected (if_focal (memory_fupd (K p)))))
     o_f computeEvents s.state`,
  rw[fmap_eq_flookup,FLOOKUP_o_f,computeEvents_def,FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE,fill_def] >>
  qpat_abbrev_tac`f = memory_fupd _` >>
  rw[] >- (
    fs[wf_state_with_hole_def] >>
    `Abbrev(sq = s.state ' s.focal_coordinate)` by (
      metis_tac[flookup_thm,markerTheory.Abbrev_def] ) >>
    fs[] >>
    Cases_on`s.focal_coordinate` >>
    simp[neighbours_def,FLOOKUP_UPDATE] >>
    rpt(IF_CASES_TAC >- (`F` suffices_by rw[] >> intLib.COOPER_TAC)) >>
    simp[] >>
    ntac 7 (pop_assum kall_tac) >>
    qpat_abbrev_tac`nb = _::_` >>
    `∀sq. MEM (SOME sq) nb ⇒ EVERY ($~ o robot_focal) sq.robots` by (
      simp[Abbr`nb`,EVERY_MEM,MEM_EL,PULL_EXISTS] >> rw[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      qpat_assum`SOME _ = _`(assume_tac o SYM) >>
      asm_exists_tac >> simp[] >>
      intLib.COOPER_TAC ) >>
    qpat_assum`Abbrev (nb = _)` kall_tac >>
    rw[event_def] >>
    `∀f g. MAP (if_focal f ## map_inspected g) immigrations = immigrations` by (
      unabbrev_all_tac >> simp[MAP_EQ_ID] >>
      simp[MEM_FLAT,MEM_GENLIST,PULL_EXISTS] >> rw[] >>
      imp_res_tac incomingFrom_MovedIn >>
      Cases_on`x`>>fs[]>>
      rw[if_focal_def] >>
      Cases_on`EL i nb`>>
      fs[incomingFrom_def] >>
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      every_case_tac >> fs[] >>
      fs[MEM_EL,EVERY_MEM,PULL_EXISTS] >>
      metis_tac[] ) >>
    `actions = MAP (map_inspected (if_focal f)) actions'` by (
      unabbrev_all_tac >>
      simp[localActions_def,MAP_GENLIST] >>
      rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[FUN_EQ_THM,act_def] >>
      rw[square_update_robot_def] >>
      simp[EL_LUPDATE] >> rw[] >>
      CASE_TAC >> fs[] >>
      simp[EVERY_MEM,EXISTS_MEM] >>
      simp[canLift_def] >> rw[] >>
      rw[if_focal_def] >>
      BasicProvers.FULL_CASE_TAC >> fs[] >>
      metis_tac[] ) >>
    map_every qunabbrev_tac[`actions`,`actions'`] >> fs[] >>
    pop_assum kall_tac >>
    `children = children'` by (
      match_mp_tac EQ_SYM >>
      unabbrev_all_tac >> simp[] >>
      AP_TERM_TAC >>
      simp[MAP_MAP_o,MAP_EQ_f] >>
      rw[] >>
      CASE_TAC >> simp[] ) >>
    map_every qunabbrev_tac[`children`] >> fs[] >>
    pop_assum kall_tac >>
    `veterans = MAP (if_focal f) veterans'` by (
      unabbrev_all_tac >>
      simp[MAP_GENLIST] >>
      simp[GENLIST_FUN_EQ,EL_MAP] >>
      gen_tac >> strip_tac >>
      qmatch_assum_abbrev_tac`i < LENGTH sq.robots` >>
      `∀z. z < LENGTH sq.robots ∧ (EL z sq.robots).focal ⇔ z = s.focal_index` by (
        metis_tac[] ) >>
      simp[updateInventory_ignores_policy] ) >>
    qunabbrev_tac`veterans`>>fs[] >>
    pop_assum kall_tac >>
    conj_tac >- (
      `LENGTH veterans' = LENGTH sq.robots` by simp[Abbr`veterans'`] >>
      simp[ZIP_MAP_PAIR] >>
      simp[GSYM ZIP_MAP_PAIR,LENGTH_REPLICATE] >>
      AP_TERM_TAC >> simp[] >>
      simp[REPLICATE_GENLIST,MAP_GENLIST] >>
      simp[Abbr`children'`] >>
      simp[MAP_FLAT,MAP_MAP_o,o_DEF] >>
      AP_TERM_TAC >>
      simp[MAP_EQ_f] >>
      rw[] >> Cases_on`a`>>simp[] >>
      imp_res_tac MEM_Built_localActions_not_focal >>
      simp[if_focal_def] ) >>
    conj_tac >- (
      `(square_update_robot f s.focal_index sq).items = sq.items` by (
        simp[Abbr`f`,square_update_robot_def] ) >> simp[] >>
      rpt AP_THM_TAC >> AP_TERM_TAC >>
      simp[FUN_EQ_THM] >>
      simp[EXISTS_MAP] >>
      simp[EXISTS_MEM] >> rw[] >>
      EQ_TAC >> rw[] >>
      asm_exists_tac >>
      (Cases_on`x` ORELSE Cases_on`a`) >> fs[] ) >>
    conj_tac >- (
      AP_TERM_TAC >>
      simp[LIST_EQ_REWRITE,EL_MAP,EL_ZIP] >>
      qx_gen_tac`n` >>
      Cases_on`EL n (localActions sq nb)`>>simp[] >>
      simp[square_update_robot_def,EL_LUPDATE] >>
      simp[Abbr`f`] >> rw[] ) >>
    unabbrev_all_tac >>
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_GENLIST,MEM_MAP,PULL_EXISTS,MAP_GENLIST]) >>
  Cases_on`FLOOKUP s.state k`>>fs[]>>
  qpat_abbrev_tac`nb = neighbours (_ |+ _) _` >>
  `LENGTH nb = LENGTH (neighbours s.state k)` by (
    simp[Abbr`nb`] >>
    Cases_on`k`>>simp[neighbours_def] ) >>
  `∀n. n < LENGTH nb ⇒ (IS_SOME (EL n nb) ⇔ IS_SOME (EL n (neighbours s.state k)))` by (
    simp[Abbr`nb`] >>
    Cases_on`k`>>simp[neighbours_def] >>
    simp[less8] >>
    gen_tac >> strip_tac >> simp[FLOOKUP_UPDATE] >>
    rw[] >> fs[wf_state_with_hole_def] ) >>
  `∀g. ∀n. n < LENGTH nb ⇒ (incomingFrom n (EL n nb)) = MAP (if_focal f ## map_inspected g) (incomingFrom n (EL n (neighbours s.state k)))` by (
    rpt gen_tac >> strip_tac >>
    Cases_on`EL n nb` >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[incomingFrom_def]>>
    simp[IS_SOME_EXISTS] >> strip_tac >>
    simp[incomingFrom_def] >>
    simp[MAP_FLAT,MAP_MAP_o] >>
    simp[o_DEF] >>
    AP_TERM_TAC >>
    simp[Once LIST_EQ_REWRITE] >>
    conj_asm1_tac >- (
      fs[Abbr`nb`] >>
      Cases_on`k`>>fs[neighbours_def] >>
      fs[less8,FLOOKUP_UPDATE] >> rfs[] >>
      every_case_tac >> fs[] >> rveq >>
      simp[square_update_robot_def] >>
      fs[FLOOKUP_DEF] ) >>
    simp[EL_MAP] >>
    gen_tac >> strip_tac >>
    fs[Abbr`nb`] >>
    Cases_on`k`>>fs[neighbours_def,if_focal_def] >>
    fs[less8,FLOOKUP_UPDATE] >> rfs[if_focal_def] >>
    every_case_tac >> fs[] >> rveq >>
    fs[square_update_robot_def,EL_LUPDATE,Abbr`f`] >>
    rw[] >> rfs[] >> fs[FLOOKUP_DEF,if_focal_def] >> rveq >> fs[] >>
    every_case_tac >> fs[] >>
    fs[wf_state_with_hole_def,FLOOKUP_DEF] >>
    metis_tac[]) >>
  rw[event_def] >>
  `∀g. MAP (if_focal f ## map_inspected g) immigrations' = immigrations` by (
    gen_tac >>
    map_every qunabbrev_tac[`immigrations'`,`immigrations`] >>
    simp[MAP_FLAT] >>
    AP_TERM_TAC >>
    simp[MAP_GENLIST] >>
    simp[LIST_EQ_REWRITE,EL_MAP] >>
    first_x_assum(qspec_then`g`mp_tac) >>
    simp[] >> rw[] >> simp[EL_MAP]) >>
  `actions = MAP (map_inspected (if_focal f)) actions'` by (
    unabbrev_all_tac >>
    simp[localActions_def,MAP_GENLIST] >>
    rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
    simp[FUN_EQ_THM,act_def] >>
    qpat_abbrev_tac`f1 = fled (_ _)` >>
    qpat_abbrev_tac`f2 = fled _` >>
    `∀m. f1 m ⇔ f2 m` by (
      unabbrev_all_tac >>
      Cases >> simp[fled_def] >> rfs[] >>
      metis_tac[] ) >>
    rw[square_update_robot_def] >>
    simp[EL_LUPDATE] >> rw[] >>
    CASE_TAC >> fs[] >>
    simp[EVERY_MEM,EXISTS_MEM] >>
    simp[canLift_def] >> rw[] >>
    rw[if_focal_def] >>
    TRY BasicProvers.FULL_CASE_TAC >> fs[] >>
    fs[wf_state_with_hole_def] >>
    metis_tac[] ) >>
  map_every qunabbrev_tac[`actions`,`actions'`] >> fs[] >>
  pop_assum kall_tac >>
  `veterans = MAP (if_focal f) veterans'` by (
    unabbrev_all_tac >>
    simp[MAP_GENLIST] >>
    simp[GENLIST_FUN_EQ,EL_MAP] >>
    gen_tac >> strip_tac >>
    qmatch_assum_abbrev_tac`i < LENGTH sq.robots` >>
    `¬(EL i sq.robots).focal` by (
      fs[wf_state_with_hole_def] >> metis_tac[] ) >>
    simp[updateInventory_ignores_policy2] ) >>
  qunabbrev_tac`veterans`>>fs[] >>
  pop_assum kall_tac >>
  conj_tac >- (
    `LENGTH veterans' = LENGTH x.robots` by simp[Abbr`veterans'`] >>
    simp[ZIP_MAP_PAIR] >>
    simp[GSYM ZIP_MAP_PAIR,LENGTH_REPLICATE] >>
    AP_TERM_TAC >> simp[] >>
    simp[REPLICATE_GENLIST,MAP_GENLIST] >>
    simp[Abbr`children'`] >>
    simp[MAP_FLAT,MAP_MAP_o,o_DEF] >>
    conj_asm1_tac >- (
      simp[Abbr`children`] >>
      AP_TERM_TAC >>
      simp[LIST_EQ_REWRITE,EL_MAP] >>
      qx_gen_tac`n` >>
      Cases_on`EL n (localActions x (neighbours s.state k))`>>simp[] >>
      simp[if_focal_def] >> rw[] >>
      metis_tac[MEM_Built_localActions_not_focal,LENGTH_localActions,MEM_EL]) >>
    simp[] >>
    AP_TERM_TAC >>
    simp[LENGTH_FLAT] >>
    AP_TERM_TAC >>
    simp[MAP_MAP_o,MAP_EQ_f] ) >>
  conj_tac >- (
    AP_THM_TAC >>
    simp[EXISTS_MAP] >>
    rpt AP_THM_TAC >> AP_TERM_TAC >>
    simp[FUN_EQ_THM] >>
    simp[EXISTS_MEM] >> rw[] >>
    EQ_TAC >> rw[] >> asm_exists_tac >>
    (Cases_on`x'` ORELSE Cases_on`a`) >> fs[] ) >>
  conj_tac >- (
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_MAP,EL_ZIP] >>
    qx_gen_tac`n` >>
    Cases_on`EL n (localActions x (neighbours s.state k))`>>simp[]) >>
  unabbrev_all_tac >>
  AP_TERM_TAC >>
  simp[LIST_EQ_REWRITE,EL_GENLIST,MEM_MAP,PULL_EXISTS,MAP_GENLIST]);

val focal_preserved = Q.store_thm("focal_preserved",
  `wf_state_with_hole s ∧
   events = computeEvents s.state ∧
   ev = events ' s.focal_coordinate ∧
   ¬EXISTS(λa. a = Destroyed s.focal_index ∨ ∃r. a = Inspected s.focal_index r)(MAP SND ev.robotActions) ∧
   s' = computeSquare o_f events
   ⇒
   ∃c' i'. wf_state_with_hole <| state := s'; focal_coordinate := c'; focal_index := i' |>`,
  rw[wf_state_with_hole_def,FLOOKUP_o_f] >>
  fs[EVERY_MAP] >>
  fs[computeEvents_def] >>
  fs[FLOOKUP_FMAP_MAP2] >>
  `s.focal_coordinate ∈ FDOM s.state` by fs[FLOOKUP_DEF] >>
  fs[FMAP_MAP2_THM] >>
  rator_x_assum`EVERY`mp_tac >>
  qpat_abbrev_tac`nb = neighbours _ _` >>
  `s.state ' s.focal_coordinate = sq` by fs[FLOOKUP_DEF] >>
  pop_assum SUBST_ALL_TAC >>
  strip_tac >>
  reverse(Cases_on`isMovedOut (SND (EL s.focal_index (event sq nb).robotActions))`) >- (
    qexists_tac`s.focal_coordinate` >> fs[] >>
    simp[computeSquare_def] >>
    qho_match_abbrev_tac`∃i. (i < LENGTH l ∧ (EL i (MAP f l)).focal) ∧ R i` >>
    cheat ) >>
  cheat);

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ∧
   policy_fun p (get_focal_robot s).processor obs = (c',p')
   ⇒
   step (fill (with_policy c p) s) = fill (with_policy c' p') s'`,
  rw[wf_state_with_hole_def,fill_def,get_focal_robot_def,step_def,steph_def] >>
  `Abbrev(sq = s.state ' s.focal_coordinate)` by (
    fs[FLOOKUP_DEF,markerTheory.Abbrev_def] ) >> simp[] >>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  qpat_assum`_ = s'`(assume_tac o Abbrev_intro o SYM) >>
  qmatch_assum_abbrev_tac`Abbrev(s' = _ with state := state')` >>
  fs[Abbr`s'`] >>
  simp[Once square_update_robot_o] >>
  qpat_abbrev_tac`sq' = square_update_robot (command_fupd _) _ _` >>
  `wf_state_with_hole (s with state := s.state |+ (s.focal_coordinate,sq'))` by (
    fs[wf_state_with_hole_def] >>
    simp[FLOOKUP_UPDATE] >>
    simp[Abbr`sq'`,square_update_robot_def,EL_LUPDATE] >>
    rw[] >> simp[EL_LUPDATE] >> fs[] >>
    metis_tac[] ) >>
  drule computeEvents_with_focal_policy >>
  simp[fill_def] >> disch_then kall_tac >>
  simp[o_DEF] >>
  simp[Abbr`state'`] >>
  qpat_abbrev_tac`events = computeEvents _` >>
  simp[fmap_eq_flookup] >> gen_tac >>
  simp[FLOOKUP_UPDATE,FLOOKUP_o_f] >>
  CASE_TAC >> simp[] >- (
    strip_tac >> var_eq_tac >>
    drule(GEN_ALL focal_preserved) >> simp[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac wf_state_with_hole_find_focal >> fs[] >>
    fs[wf_state_with_hole_def,FLOOKUP_o_f] >>
    rveq >> rfs[] ) >>
  `(computeSquare o_f events) ' k = computeSquare x` by (
    fs[FLOOKUP_DEF,o_f_FAPPLY] ) >>
  pop_assum SUBST_ALL_TAC >>
  IF_CASES_TAC >> fs[] >- (
    rveq >>
    simp[computeSquare_def,square_update_robot_def] >>
    (* probably want information hiding to happen earlier than encoding *)
    cheat ) >>
  cheat);

(*
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

val neighbours_FUPDATE_same = Q.store_thm("neighbours_FUPDATE_same[simp]",
  `neighbours (g |+ (c,sq)) c = neighbours g c`,
  Cases_on`c`>>simp[neighbours_def,FLOOKUP_UPDATE] >>
  simp_tac(srw_ss()++intLib.INT_ARITH_ss)[]);

val shift4_def = Define`
  shift4 x = if 4i < x then x-1 else x`;

val neighbour_coord_def = Define`
  neighbour_coord c k ⇔
    (Num (ABS (FST c - FST k))) ≤ 1 ∧
    (Num (ABS (SND c - SND k))) ≤ 1`;

val lesseq1 = Q.prove(
  `x ≤ 1n ⇔ (x = 0 ∨ x = 1)`,
  rw[EQ_IMP_THM] >> simp[])

val lesseq2 = Q.prove(
  `x ≤ 2n ⇔ (x = 0 ∨ x = 1 ∨ x = 2)`,
  rw[EQ_IMP_THM] >> simp[])

val plus_less_eq_1 = Q.prove(
  `x + y ≤ 1n ⇔ (x = 0 ∧ y ≤ 1) ∨
                (x = 1 ∧ y ≤ 0)`,
  rw[EQ_IMP_THM] >> simp[])

val NUM_ABS_eq_0 = Q.prove(
  `Num (ABS x) = 0 ⇔ x = 0`,
  rw[EQ_IMP_THM] >> intLib.COOPER_TAC)

val NUM_ABS_eq_1 = Q.prove(
  `Num (ABS x) = 1 ⇔ x = 1 ∨ x = -1`,
  rw[EQ_IMP_THM] >> intLib.COOPER_TAC)

val neighbours_FUPDATE = Q.store_thm("neighbours_FUPDATE",
  `neighbours (g |+ (c,sq)) k =
   if c ≠ k ∧ neighbour_coord c k then
     LUPDATE (SOME sq)
       (Num(shift4((((FST c - FST k)+1)*3)+((SND c - SND k)+1))))
       (neighbours g k)
   else neighbours g k`,
  Cases_on`k`>>Cases_on`c`>>simp[neighbours_def,FLOOKUP_UPDATE,neighbour_coord_def] >>
  simp[plus_less_eq_1,NUM_ABS_eq_0,NUM_ABS_eq_1,lesseq1,lesseq2] >>
  match_mp_tac EQ_SYM >>
  IF_CASES_TAC >- (
    fs[integerTheory.INT_EQ_SUB_RADD] >> rpt var_eq_tac >>
    simp_tac(srw_ss()++intLib.INT_ARITH_ss)[] >> fs[] >>
    fsrw_tac[intLib.INT_ARITH_ss][AC integerTheory.INT_ADD_ASSOC integerTheory.INT_ADD_COMM] >>
    simp[LIST_EQ_REWRITE,EL_LUPDATE,shift4_def] >>
    simp[less8] >> rw[] >> simp[] >> simp[FLOOKUP_DEF]) >>
  rw[] >> fsrw_tac[intLib.INT_ARITH_ss][] >> rw[FLOOKUP_DEF])

val update_focal_robot_def = Define`
  update_focal_robot f i sq =
    if i < LENGTH sq.robots ∧ (EL i sq.robots).focal then
      square_update_robot f i sq
    else sq`;

val updated_policies_def = Define`
  updated_policies i f ls =
    GENLIST (λj. (if i = j ∧ (EL i ls).focal then f else I) (EL j ls).memory) (LENGTH ls)`;

val updated_policies_APPEND = Q.store_thm("updated_policies_APPEND",
  `updated_policies i f (l1 ++ l2) =
   if i < LENGTH l1 then
     updated_policies i f l1 ++ MAP robot_memory l2
   else MAP robot_memory l1 ++ updated_policies (i - LENGTH l1) f l2`,
  rw[updated_policies_def,LIST_EQ_REWRITE] >>
  Cases_on`x < LENGTH l1`>>simp[EL_APPEND1,EL_APPEND2]>>
  rw[]>>fsrw_tac[ARITH_ss][]>>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[EL_APPEND2,EL_APPEND1,EL_MAP]);

val updated_policies_APPEND2_nonfocal = Q.store_thm("updated_policies_APPEND2_nonfocal",
  `EVERY ($~ o robot_focal) ls ⇒
   updated_policies i f (l1 ++ ls) = updated_policies i f l1 ++ MAP robot_memory ls`,
  rw[updated_policies_def] >>
  simp[LIST_EQ_REWRITE] >>
  gen_tac >> strip_tac >>
  Cases_on`x < LENGTH l1`>>
  simp[EL_APPEND1,EL_APPEND2] >>
  fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  rw[] >> fs[] >>
  rfs[EL_APPEND1] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[EL_APPEND2,EL_MAP])

val updated_policies_nonfocal = save_thm("updated_policies_nonfocal",
  updated_policies_APPEND2_nonfocal
  |> Q.GEN`l1` |> Q.SPEC`[]`
  |> SIMP_RULE (srw_ss())[updated_policies_def,SimpRHS])

val LENGTH_updated_policies = Q.store_thm("LENGTH_updated_policies[simp]",
  `LENGTH (updated_policies i f ls) = LENGTH ls`,
  EVAL_TAC >> simp[]);

val update_focal_robot_set_policies = Q.store_thm("update_focal_robot_set_policies",
  `i < LENGTH sq.robots ⇒
   update_focal_robot (memory_fupd f) i sq =
   square_set_policies (updated_policies i f sq.robots) sq`,
  rw[square_component_equality,update_focal_robot_def,square_update_robot_def,set_policies_thm,updated_policies_def] >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE] >> rw[] >>
  rw[set_policy_def,robot_component_equality])

val event_ignores_policy1 = Q.prove(
  `i < LENGTH sq.robots ⇒
     event (update_focal_robot (memory_fupd f) i sq) nb =
     event_set_policies (updated_policies i f sq.robots) (event sq nb)`,
  rw[update_focal_robot_set_policies] >>
  match_mp_tac event_ignores_policy >>
  rw[updated_policies_def] );

val focal_at_def = Define`
  focal_at g c sq i ⇔
  (∀c' sq' i'. FLOOKUP g c' = SOME sq' ∧ i' < LENGTH sq'.robots ∧ (EL i' sq'.robots).focal ⇒
     i' = i ∧ c' = c ∧ sq' = sq)`;

val event_update_policies_def = Define`
  event_update_policies i f ev =
    event_set_policies (updated_policies i f (MAP FST (ev.robotActions))) ev`;

val set_policies_updated_policies_nonfocal = Q.store_thm("set_policies_updated_policies_nonfocal",
  `EVERY ($~ o robot_focal) l2 ⇒
   rs ≼ l1 ++ l2 ⇒
   set_policies rs (updated_policies i f (l1 ++ l2)) =
   set_policies rs (updated_policies i f l1)`,
  strip_tac >>
  simp[set_policies_thm,LIST_EQ_REWRITE] >>
  rw[updated_policies_def] >>
  simp[set_policy_def] >>
  Cases_on`x < LENGTH l1`>>simp[EL_APPEND1] >- (
    IF_CASES_TAC >> simp[] >> fs[] >> rfs[EL_APPEND1] >>
    IF_CASES_TAC >> fs[] >> rfs[] >> rfs[EL_APPEND1] ) >>
  simp[robot_component_equality] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >- (
    fs[] >> rw[] >> pop_assum mp_tac >>
    simp[EL_APPEND2] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    strip_tac >>
    `F` suffices_by rw[] >>
    pop_assum mp_tac >> simp[] ) >>
  pop_assum mp_tac >> simp[] >>
  fs[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1] );

val set_policies_append1_same = Q.store_thm("set_policies_append1_same",
  `set_policies (l1 ++ l2) (MAP robot_memory l1 ++ p2) =
   l1 ++ set_policies l2 p2`,
  rw[set_policies_thm] >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < LENGTH l1`>>
  simp[EL_APPEND1,EL_APPEND2] >>
  simp[set_policy_def] >>
  rw[robot_component_equality] >>
  simp[EL_APPEND1,EL_APPEND2] >>
  simp[EL_MAP] >> fs[])

val set_policies_append2_same = Q.store_thm("set_policies_append2_same",
  `LENGTH l1 = LENGTH p1 ⇒
   set_policies (l1 ++ l2) (p1 ++ MAP robot_memory l2) =
   set_policies l1 p1 ++ l2`,
  rw[set_policies_thm] >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < LENGTH l1`>>
  simp[EL_APPEND1,EL_APPEND2] >>
  simp[set_policy_def] >>
  rw[robot_component_equality] >>
  simp[EL_APPEND1,EL_APPEND2] >>
  simp[EL_MAP])

val set_policies_same = save_thm("set_policies_same",
  set_policies_append2_same
  |> Q.GEN`l1` |> Q.SPEC`[]`
  |> Q.GEN`p1` |> Q.SPEC`[]`
  |> SIMP_RULE (srw_ss())[]
  |> SIMP_RULE (srw_ss())[set_policies_thm,SimpRHS])

val act_Inspected_less = Q.store_thm("act_Inspected_less",
  `act sq nb m = Inspected n r ⇒ n < LENGTH sq.robots`,
  simp[act_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[])

val MEM_Inspected_localActions_less = Q.store_thm("MEM_Inspected_localActions_less",
  `MEM (Inspected n r) (localActions sq nb) ⇒ n < LENGTH sq.robots`,
  rw[localActions_def,MEM_GENLIST] >>
  metis_tac[act_Inspected_less])

val event_set_policies_update_policies_no_move = Q.store_thm("event_set_policies_update_policies_no_move",
  `LENGTH (FILTER robot_focal sq.robots) ≤ 1 ∧
   FILTER robot_focal (FLAT (MAP (square_robots o THE) (FILTER IS_SOME nb))) = [] ⇒
   event_set_policies (updated_policies i f sq.robots) (event sq nb) =
   event_update_policies i f (event sq nb)`,
  rw[event_update_policies_def] >>
  rw[event_set_policies_def,event_component_equality] >>
  rw[event_def] >> rw[] >>
  rfs[Abbr`fallen'`,Abbr`children'`,Abbr`veterans'`] >>
  `LENGTH veterans = LENGTH actions` by (
    unabbrev_all_tac >> simp[localActions_def] ) >>
  `LENGTH actions = LENGTH sq.robots` by simp[Abbr`actions`] >>
  simp[MAP_ZIP,LENGTH_REPLICATE] >>
  simp[REPLICATE_GENLIST,MAP_GENLIST,fix_inspected_def] >>
  AP_TERM_TAC >> simp[] >>
  `∀ps. MAP (fix_inspected ps) (MAP SND immigrations) = MAP SND immigrations` by (
    simp[Abbr`immigrations`,MAP_MAP_o,MAP_FLAT,MAP_GENLIST,o_DEF] >>
    gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    rw[FUN_EQ_THM,LIST_EQ_REWRITE,EL_MAP] >>
    imp_res_tac(SIMP_RULE std_ss [MEM_EL,PULL_EXISTS] incomingFrom_MovedIn) >>
    fs[fix_inspected_def] ) >>
  rfs[] >>
  simp[set_policies_APPEND1] >>
  simp[Abbr`actions`] >>
  REWRITE_TAC[GSYM localActions_ignores_policy] >>
  `EVERY ($~ o robot_focal) children` by (
    simp[Abbr`children`,localActions_def,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MAP_GENLIST,MEM_GENLIST] >>
    rw[act_def,LET_THM] >>
    every_case_tac >> fs[] >>
    fs[construct_def] >>
    every_case_tac >> fs[] >> rw[] ) >>
  first_assum(strip_assume_tac o MATCH_MP (GEN_ALL set_policies_updated_policies_nonfocal)) >>
  simp[set_policies_APPEND1] >>
  simp[updated_policies_APPEND2_nonfocal] >>
  `updated_policies i f veterans = updated_policies i f sq.robots` by (
    simp[updated_policies_def] >>
    simp[LIST_EQ_REWRITE] >>
    rw[Abbr`veterans`] >> rfs[] ) >>
  reverse conj_tac >- (
    simp[MAP_EQ_f] >>
    Cases >> simp[fix_inspected_def] >>
    strip_tac >>
    imp_res_tac MEM_Inspected_localActions_less >>
    simp[set_policy_def,EL_APPEND1] >>
    rw[updated_policies_APPEND,EL_APPEND1,robot_component_equality,EL_MAP] >>
    simp[updated_policies_def,Abbr`veterans`]) >>
  Cases_on`EVERY ($~ o robot_focal) (MAP FST immigrations)` >- (
    first_assum(strip_assume_tac o MATCH_MP (GEN_ALL set_policies_updated_policies_nonfocal)) >>
    simp[set_policies_APPEND1] ) >>
  `F` suffices_by rw[] >>
  pop_assum mp_tac >> simp[] >>
  fs[FILTER_EQ_NIL] >>
  fs[Abbr`immigrations`,EVERY_MAP] >>
  fs[EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_GENLIST,MEM_MAP,MEM_FILTER,IS_SOME_EXISTS] >>
  rw[] >>
  qcase_tac`EL k nb` >>
  Cases_on`EL k nb`>> fs[incomingFrom_def] >>
  fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
  every_case_tac >> fs[] >>
  metis_tac[MEM_EL]);

val focal_at_FILTER_1 = Q.store_thm("focal_at_FILTER_1",
  `focal_at g c sq i ∧ sq ∈ FRANGE g ⇒
   LENGTH (FILTER robot_focal sq.robots) ≤ 1`,
  Cases_on`FILTER robot_focal sq.robots` >> simp[] >>
  Cases_on`t`>>simp[] >>
  Q.ISPECL_THEN[`sq.robots`,`robot_focal`]strip_assume_tac(GEN_ALL FILTER_INDICES) >>
  rfs[] >>
  rw[focal_at_def,IN_FRANGE_FLOOKUP] >>
  first_x_assum(qspecl_then[`0`,`1`]mp_tac) >> simp[] >>
  strip_tac >>
  first_assum(qspec_then`0`mp_tac) >>
  first_x_assum(qspec_then`1`mp_tac) >>
  simp[] >> rw[] >>
  `f 0 < LENGTH sq.robots ∧ f 1 < LENGTH sq.robots` by (
    fs[INJ_DEF] >> first_x_assum match_mp_tac >> simp[] ) >>
  metis_tac[MEM,MEM_FILTER,prim_recTheory.LESS_REFL]);

val computeEvents_ignores_policy = Q.store_thm("computeEvents_ignores_policy",
  `i < LENGTH sq.robots ∧ focal_at g c sq i ∧ sq ∈ FRANGE g ⇒
   computeEvents (g |+ (c,update_focal_robot (memory_fupd f) i sq)) =
   event_update_policies i f o_f computeEvents (g |+ (c,sq))`,
  rw[computeEvents_def,fmap_eq_flookup,FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE,FLOOKUP_o_f] >>
  IF_CASES_TAC >> simp[] >- (
    rw[event_ignores_policy1,update_focal_robot_set_policies] >>
    match_mp_tac event_set_policies_update_policies_no_move >>
      simp[FILTER_EQ_NIL] >>
      conj_tac >- metis_tac[focal_at_FILTER_1] >>
      simp[EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_FILTER,IS_SOME_EXISTS] >>
      rw[] >>
      fs[focal_at_def] >>
      pop_assum mp_tac >> simp_tac std_ss [MEM_EL] >> strip_tac >>
      qpat_assum`MEM _ _`mp_tac >>
      Cases_on`c`>> simp_tac(srw_ss())[neighbours_def] >>
      metis_tac[PAIR_EQ,intLib.ARITH_PROVE``(∀x. x ≠ x + 1 ∧ x ≠ x -1)``] ) >>
  Cases_on`FLOOKUP g k`>>simp[]>>
  match_mp_tac EQ_SYM >>
  (fn g =>
     match_mp_tac EQ_TRANS >>
     match_exists_tac(
       event_set_policies_update_policies_no_move
       |> GSYM |>
       |> PAR

     concl
       (DISCH_ALL (PART_MATCH lhs (GSYM event_set_policies_update_policies_no_move)
  match_exists_tac(concl PART_MATCH

(*
val event_set_policies_update_policies = Q.store_thm("event_set_policies_update_policies",
  `LENGTH (FILTER robot_focal (sq.robots ++ (FLAT (MAP (square_robots o THE) (FILTER IS_SOME nb))))) ≤ 1 ⇒
   event_set_policies (updated_policies i f sq.robots) (event sq nb) =
   event_update_policies i f (event sq nb)`,
  rw[event_update_policies_def] >>
  rw[event_set_policies_def,event_component_equality] >>
  rw[event_def] >> rw[] >>
  rfs[Abbr`fallen'`,Abbr`children'`,Abbr`veterans'`] >>
  `LENGTH veterans = LENGTH actions` by (
    unabbrev_all_tac >> simp[localActions_def] ) >>
  `LENGTH actions = LENGTH sq.robots` by simp[Abbr`actions`] >>
  simp[MAP_ZIP,LENGTH_REPLICATE] >>
  simp[REPLICATE_GENLIST,MAP_GENLIST,fix_inspected_def] >>
  AP_TERM_TAC >> simp[] >>
  `∀ps. MAP (fix_inspected ps) (MAP SND immigrations) = MAP SND immigrations` by (
    simp[Abbr`immigrations`,MAP_MAP_o,MAP_FLAT,MAP_GENLIST,o_DEF] >>
    gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    rw[FUN_EQ_THM,LIST_EQ_REWRITE,EL_MAP] >>
    imp_res_tac(SIMP_RULE std_ss [MEM_EL,PULL_EXISTS] incomingFrom_MovedIn) >>
    fs[fix_inspected_def] ) >>
  rfs[] >>
  simp[set_policies_APPEND1] >>
  simp[Abbr`actions`] >>
  REWRITE_TAC[GSYM localActions_ignores_policy] >>
  `EVERY ($~ o robot_focal) children` by (
    simp[Abbr`children`,localActions_def,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MAP_GENLIST,MEM_GENLIST] >>
    rw[act_def,LET_THM] >>
    every_case_tac >> fs[] >>
    fs[construct_def] >>
    every_case_tac >> fs[] >> rw[] ) >>
  first_assum(strip_assume_tac o MATCH_MP (GEN_ALL set_policies_updated_policies_nonfocal)) >>
  simp[set_policies_APPEND1] >>
  simp[updated_policies_APPEND2_nonfocal] >>
  `updated_policies i f veterans = updated_policies i f sq.robots` by (
    simp[updated_policies_def] >>
    simp[LIST_EQ_REWRITE] >>
    rw[Abbr`veterans`] >> rfs[] ) >>
  reverse conj_tac >- (
    simp[MAP_EQ_f] >>
    Cases >> simp[fix_inspected_def] >>
    strip_tac >>
    imp_res_tac MEM_Inspected_localActions_less >>
    simp[set_policy_def,EL_APPEND1] >>
    rw[updated_policies_APPEND,EL_APPEND1,robot_component_equality,EL_MAP] >>
    simp[updated_policies_def,Abbr`veterans`]) >>
  Cases_on`EVERY ($~ o robot_focal) (MAP FST immigrations)` >- (
    first_assum(strip_assume_tac o MATCH_MP (GEN_ALL set_policies_updated_policies_nonfocal)) >>
    simp[set_policies_APPEND1] ) >>
  `EVERY ($~ o robot_focal) sq.robots` by (
    fs[FILTER_APPEND] >>
    qmatch_assum_abbrev_tac`a + b ≤ 1n` >>
    `b ≠ 0` by (
      simp[Abbr`b`,LENGTH_NIL] >>
      simp[FILTER_EQ_NIL] >>
      fs[EXISTS_MEM,Abbr`immigrations`] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      fs[MEM_FLAT,MEM_MAP,MEM_GENLIST,PULL_EXISTS,MEM_FILTER] >>
      qcase_tac`EL k nb` >>
      Cases_on`EL k nb`>> fs[incomingFrom_def] >>
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      qexists_tac`EL k nb` >> simp[] >>
      every_case_tac >> fs[] >>
      simp[MEM_EL] >> metis_tac[] ) >>
    `a = 0` by decide_tac >>
    fs[Abbr`a`,LENGTH_NIL,FILTER_EQ_NIL,EVERY_MEM] ) >>
  simp[updated_policies_nonfocal] >>
  simp[updated_policies_APPEND] >>
  IF_CASES_TAC >> simp[] >- (
    simp[set_policies_append2_same] >>
    simp[updated_policies_nonfocal] ) >>
  simp[set_policies_append1_same] >>
  `MAP robot_memory veterans = MAP robot_memory sq.robots` by (
    simp[Abbr`veterans`,MAP_GENLIST] >>
    simp[LIST_EQ_REWRITE,EL_MAP] ) >>
  qspec_then`veterans`mp_tac(Q.GEN`l2`set_policies_same) >>
  simp[] >> disch_then kall_tac >>
  simp[set_policies_thm]
  incomingFrom_def
*)

*)

val _ = export_theory();
