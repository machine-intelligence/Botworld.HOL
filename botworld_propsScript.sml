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

val less8 = Q.prove(
  `x < 8n ⇔ (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7)`,
  rw[EQ_IMP_THM] >> simp[])

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

val updateInventory_const = Q.store_thm("updateInventory_const[simp]",
  `(updateInventory sq i a).memory = (EL i sq.robots).memory ∧
   (updateInventory sq i a).focal = (EL i sq.robots).focal`,
  rw[updateInventory_def] >>
  BasicProvers.CASE_TAC >> rw[])

val act_Inspected_less = Q.store_thm("act_Inspected_less",
  `act sq nb m = Inspected n r ⇒ n < LENGTH sq.robots`,
  simp[act_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[])

val MEM_Inspected_localActions_less = Q.store_thm("MEM_Inspected_localActions_less",
  `MEM (Inspected n r) (localActions sq nb) ⇒ n < LENGTH sq.robots`,
  rw[localActions_def,MEM_GENLIST] >>
  metis_tac[act_Inspected_less])

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

val computeEvents_ignores_policy = Q.store_thm("computeEvents_ignores_policy",
  `i < LENGTH sq.robots ∧ focal_at g c sq i ⇒
   computeEvents (g |+ (c,update_focal_robot (memory_fupd f) i sq)) =
   event_update_policies i f o_f computeEvents (g |+ (c,sq))`,
  rw[computeEvents_def,fmap_eq_flookup,FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE,FLOOKUP_o_f] >>
  IF_CASES_TAC >> simp[] >- (
    rw[event_ignores_policy1,update_focal_robot_set_policies] ) >>
  Cases_on`FLOOKUP g k`>>simp[]>>
  reverse (Cases_on`neighbour_coord c k`) >- (
    simp[neighbours_FUPDATE] >>
    updated_policies_def

    CONV_TAC(LAND_CONV(RAND_CONV(REWR_CONV (INST_TYPE[alpha|->``:square``]neighbours_FUPDATE))))
    match_term(top_goal() |> snd |> rator |> rand |> rand)(lhs(concl neighbours_FUPDATE))
    REWRITE_TAC[neighbours_FUPDATE]

    neighbours_ignores_policy

    ... )
  Cases_on`FLOOKUP g k`>>simp[]

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
  qmatch_assum_abbrev_tac`Abbrev(s' = _ with state := state')` >>
  fs[Abbr`s'`] >>
  reverse(Cases_on`∃dir. a = MovedOut dir`)>>fs[]>-(
    `(c'',i) = (s.focal_coordinate,s.focal_index)` by (
      every_case_tac >> fs[] ) >> fs[] >>
    rpt var_eq_tac >>
*)

val _ = export_theory();
