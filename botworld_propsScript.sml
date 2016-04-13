open preamble botworldTheory botworld_dataTheory
local open realSimps in end

val _ = new_theory"botworld_props";

(* TODO: move *)

val CHOICE_IMAGE_SING = Q.store_thm("CHOICE_IMAGE_SING",
  `f (CHOICE {x}) = CHOICE (IMAGE f {x})`,
  rw[]);

val ALL_DISTINCT_MAP_MEM = Q.store_thm("ALL_DISTINCT_MAP_MEM",
  `∀ls x1 x2. ALL_DISTINCT (MAP f ls) ∧
   MEM x1 ls ∧ MEM x2 ls ∧ f x1 = f x2 ⇒ x1 = x2`,
  Induct \\ rw[MEM_MAP] \\ metis_tac[]);

val ALL_DISTINCT_MAP_FST =
  ALL_DISTINCT_MAP_MEM |> Q.GEN`f` |> Q.ISPEC`FST`
  |> SIMP_RULE(srw_ss())[FORALL_PROD]

val ALL_DISTINCT_MAP_FILTER = Q.store_thm("ALL_DISTINCT_MAP_FILTER",
  `∀ls. ALL_DISTINCT (MAP f ls) ⇒ ALL_DISTINCT (MAP f (FILTER P ls))`,
  Induct \\ rw[] \\ fs[MEM_MAP,MEM_FILTER] \\ metis_tac[]);

val ALL_DISTINCT_FILTER_GENLIST = Q.store_thm("ALL_DISTINCT_FILTER_GENLIST",
  `ALL_DISTINCT (FILTER P (GENLIST f n)) ⇔
   ∀m1 m2. m1 < n ∧ m2 < n ∧ f m1 = f m2 ∧ P (f m1) ⇒ m1 = m2`,
  Induct_on`n` \\ rw[GENLIST,FILTER_SNOC,ALL_DISTINCT_SNOC,MEM_FILTER,MEM_GENLIST]
  \\ metis_tac[LESS_ANTISYM,LESS_CASES,LESS_OR_EQ,NOT_LESS,prim_recTheory.LESS_THM]);

val MAP2_MAP = Q.store_thm("MAP2_MAP",
  `(∀l1 l2. LENGTH l1 = LENGTH l2 ⇒
            MAP2 f (MAP g l1) l2 = MAP2 (CURRY (UNCURRY f o (g ## I))) l1 l2) ∧
   (∀l1 l2. LENGTH l1 = LENGTH l2 ⇒
            MAP2 f l1 (MAP h l2) = MAP2 (CURRY (UNCURRY f o (I ## h))) l1 l2)`,
  conj_tac
  \\ Induct \\ simp[]
  \\ Cases_on`l2` \\ simp[]);

val MAP2_same = Q.store_thm("MAP2_same",
  `∀l. MAP2 f l l = MAP (W f) l`,
  Induct \\ simp[]);

val PAIR_MAP_COMPOSE = Q.store_thm("PAIR_MAP_COMPOSE",
  `(a ## b) o (c ## d) = (a o c ## b o d)`,
  rw[FUN_EQ_THM,FORALL_PROD]);

val MAP_FILTER_remove = Q.store_thm("MAP_FILTER_remove",
  `∀l1 l2. MAP f l1 = MAP f l2 ∧ (∀n. n < LENGTH l1 ⇒ (P (EL n l1) ⇔ P (EL n l2)))
    ⇒ MAP f (FILTER P l1) = MAP f (FILTER P l2)`,
  Induct \\ rw[]
  \\ Cases_on`l2` \\ fs[]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac(srw_ss())[] \\ strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[]);

val PERM_FLAT = Q.store_thm("PERM_FLAT",
  `∀l1 l2. PERM l1 l2 ⇒ PERM (FLAT l1) (FLAT l2)`,
  ho_match_mp_tac PERM_IND
  \\ simp[]
  \\ conj_tac >- ( simp[PERM_APPEND_IFF] )
  \\ conj_tac >- ( simp[PERM_SWAP_L_AT_FRONT] )
  \\ metis_tac[PERM_TRANS]);

val PERM_SNOC = Q.store_thm("PERM_SNOC",
  `∀l1 x l2. PERM (SNOC x l1) l2 ⇔ PERM (x::l1) l2`,
  Induct \\ rw[]
  \\ rw[PERM_FUN_SWAP_AT_FRONT]
  \\ metis_tac[PERM_CONS_IFF,PERM_TRANS,PERM_SYM]);

val ALL_DISTINCT_FLAT = Q.store_thm("ALL_DISTINCT_FLAT",
  `∀lss. ALL_DISTINCT (FLAT lss) ⇔
         ALL_DISTINCT (FILTER ($<> []) lss) ∧
         (∀ls. MEM ls lss ⇒ ALL_DISTINCT ls) ∧
         (∀l1 l2. MEM l1 lss ∧ MEM l2 lss ∧ l1 ≠ l2 ⇒ DISJOINT (set l1) (set l2))`,
  Induct \\ rw[]
  \\ rw[ALL_DISTINCT_APPEND]
  \\ rw[EQ_IMP_THM] \\ fs[]
  >- (
    fs[MEM_FILTER,MEM_FLAT]
    \\ Cases_on`h`\\fs[]
    \\ metis_tac[MEM] )
  >- (
    fs[IN_DISJOINT,MEM_FLAT]
    \\ metis_tac[] )
  >- (
    fs[IN_DISJOINT,MEM_FLAT]
    \\ metis_tac[] )
  \\ fs[MEM_FILTER] \\ rw[] \\ fs[]
  \\ fs[IN_DISJOINT,MEM_FLAT]
  \\ metis_tac[]);

val PERM_FILTER_SPLIT = Q.store_thm("PERM_FILTER_SPLIT",
  `∀P ls. PERM ls (FILTER P ls ++ FILTER ($~ o P) ls)`,
  gen_tac \\ Induct \\ simp[] \\ rw[]
  \\ rw[PERM_CONS_EQ_APPEND]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ asm_exists_tac \\ rw[]);

(*
val QSORT_any_pivot = Q.store_thm("QSORT_any_pivot",
  `∀R ls x. MEM x ls ⇒
   (QSORT R ls =
    QSORT R (FILTER (λy. y ≠ x ∧ R x y) ls) ++ (FILTER ($= x) ls) ++
    QSORT R (FILTER (λy. y ≠ x ∧ R y x) ls))`,
  ho_match_mp_tac QSORT_IND
  \\ simp[]
  \\ rpt gen_tac
  \\ strip_tac
  \\ gen_tac
  \\ strip_tac
  >- (
    rveq \\ fs[]
    \\ simp[Once QSORT_DEF]
    \\ pairarg_tac \\ fs[]

val QSORT_SET_TO_LIST_INSERT = Q.store_thm("QSORT_SET_TO_LIST_INSERT",
  `∀s. FINITE s ⇒
   ∀x. x ∈ s ⇒
     QSORT R (SET_TO_LIST s) =
     QSORT R (SET_TO_LIST { y | y ∈ s ∧ y ≠ x ∧ R y x } ) ++ [x] ++
     QSORT R (SET_TO_LIST { y | y ∈ s ∧ y ≠ x ∧ R x y } )`,
  \\ ho_match_mp_tac SET_TO_LIST_IND
  \\ rw[] \\ fs[]
  \\ Cases_on`s = ∅` \\ fs[]
  \\ simp[Once SET_TO_LIST_THM]
  \\ simp[Once QSORT_DEF]
  \\ pairarg_tac \\ fs[]

*)

val ALL_DISTINCT_QSORT = Q.store_thm("ALL_DISTINCT_QSORT",
  `ALL_DISTINCT (QSORT R ls) ⇔ ALL_DISTINCT ls`,
  metis_tac[QSORT_PERM,ALL_DISTINCT_PERM])

val FLOOKUP_FMAP_MAP2 = Q.store_thm("FLOOKUP_FMAP_MAP2",
  `FLOOKUP (FMAP_MAP2 f m) x =
   OPTION_MAP (CURRY f x) (FLOOKUP m x) `,
  rw[FLOOKUP_DEF,FMAP_MAP2_THM])

val FMAP_MAP2_o_f = Q.store_thm("FMAP_MAP2_o_f",
  `FMAP_MAP2 f (g o_f h) = FMAP_MAP2 (f o (I ## g)) h`,
  rw[fmap_eq_flookup,FLOOKUP_FMAP_MAP2,FLOOKUP_o_f]
  \\ CASE_TAC \\ fs[]);

val o_f_FMAP_MAP2 = Q.store_thm("o_f_FMAP_MAP2",
  `f o_f (FMAP_MAP2 g h) = FMAP_MAP2 (f o g) h`,
  rw[fmap_eq_flookup,FLOOKUP_FMAP_MAP2,FLOOKUP_o_f]
  \\ CASE_TAC \\ fs[]);

val FMAP_MAP2_SND_compose = Q.store_thm("FMAP_MAP2_SND_compose",
  `FMAP_MAP2 (f o SND) (FMAP_MAP2 (g o SND) x) = FMAP_MAP2 (f o g o SND) x`,
  rw[fmap_eq_flookup,FLOOKUP_FMAP_MAP2]
  \\ Cases_on`FLOOKUP x k` \\ simp[])

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

val unique_index_filter = Q.store_thm("unique_index_filter",
  `∀ls i. i < LENGTH ls ∧
   (∀j. j < LENGTH ls ⇒ (R (EL j ls) ⇔ j = i)) ∧
   P (EL i ls) ⇒
   ∃k. k < LENGTH (FILTER P ls) ∧ (∀j. j < LENGTH (FILTER P ls) ⇒ (R (EL j (FILTER P ls)) ⇔ j = k))`,
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> fs[] >- (
    Cases_on`i`>>fs[]>-(
      qexists_tac`0`>>simp[]>>rw[]>>
      Cases_on`j`>>fs[]>-(
        first_x_assum(qspec_then`0`mp_tac)>>simp[])>>
      `MEM (EL n (FILTER P ls)) ls` by (
        metis_tac[MEM_FILTER,MEM_EL] ) >>
      fs[MEM_EL] >>
      first_x_assum(qspec_then`SUC n'`mp_tac)>>simp[]) >>
    last_x_assum(qspec_then`n`mp_tac)>>simp[]>>
    impl_tac >- (
      rw[] >>
      first_x_assum(qspec_then`SUC j`mp_tac)>>simp[])>>
    rw[] >>
    qexists_tac`SUC k`>>simp[]>>rw[]>>
    Cases_on`j`>>fs[]>>
    last_x_assum(qspec_then`0`mp_tac)>>simp[]) >>
  Cases_on`i`>>fs[]>>
  last_x_assum drule >>
  impl_tac >- (
    rw[] >>
    first_x_assum(qspec_then`SUC j`mp_tac)>>simp[])>>
  rw[]);

val LENGTH_FILTER_EQ = Q.store_thm("LENGTH_FILTER_EQ",
  `∀l1 l2.
   LENGTH l1 = LENGTH l2 ∧ (∀i. i < LENGTH l1 ⇒ (P (EL i l1) ⇔ P (EL i l2)))
   ⇒ LENGTH (FILTER P l1) = LENGTH (FILTER P l2)`,
  Induct \\ simp[LENGTH_NIL_SYM]
  \\ gen_tac \\ Cases \\ simp[]
  \\ metis_tac[LESS_MONO_EQ,EL_restricted,HD,prim_recTheory.LESS_0,LENGTH]);

val APPEND_EQ_suff =
  DISCH_ALL(#2(EQ_IMP_RULE(UNDISCH(SPEC_ALL(CONJUNCT1 (SPEC_ALL APPEND_11_LENGTH))))))
  |> SIMP_RULE(pure_ss)[AND_IMP_INTRO,CONJ_ASSOC]
  |> SIMP_RULE(pure_ss)[PROVE[]``LENGTH a = LENGTH b ∧ a = b ⇔ a = b``]

(* -- *)

val grid_injective = Q.store_thm("grid_injective",
  `wf_state s ⇒
   ∀c1 c2 sq.
     (FLOOKUP s.grid c1 = SOME sq) ∧
     (FLOOKUP s.grid c2 = SOME sq) ∧
     ¬ NULL sq.robots
     ⇒
     (c1 = c2)`,
  rw[wf_state_def,listTheory.NULL_EQ,pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP]
  \\ metis_tac[listTheory.MEM,listTheory.list_CASES])

val same_name_same_square = Q.store_thm("same_name_same_square",
  `wf_state s ⇒
   ∀s1 s2 nm.
     s1 ∈ FRANGE s.grid ∧
     s2 ∈ FRANGE s.grid ∧
     MEM nm (MAP FST s1.robots) ∧
     MEM nm (MAP FST s2.robots)
     ⇒ s1 = s2`,
  rw[wf_state_def,finite_mapTheory.IN_FRANGE_FLOOKUP,pred_setTheory.IN_DISJOINT]
  \\ metis_tac[optionTheory.SOME_11]);

val focal_robot_unique = Q.store_thm("focal_robot_unique",
  `wf_state_with_hole s ⇒
   ∀s1 s2.
     s1 ∈ FRANGE s.state.grid ∧ s2 ∈ FRANGE s.state.grid ∧
     MEM s.focal_name (MAP FST s1.robots) ∧
     MEM s.focal_name (MAP FST s2.robots)
     ⇒
     s1 = s2`,
  metis_tac[wf_state_with_hole_def,same_name_same_square]);

val FST_updateInventory = Q.store_thm("FST_updateInventory[simp]",
  `FST (updateInventory sq x y) = x`,
  Cases_on`y`\\rw[updateInventory_def]);

val SND_updateInventory_const = Q.store_thm("SND_updateInventory_const[simp]",
  `(SND (updateInventory sq nm y)).command = (FST y).command ∧
   (SND (updateInventory sq nm y)).processor = (FST y).processor ∧
   (SND (updateInventory sq nm y)).frame = (FST y).frame`,
  Cases_on`y` \\ rw[updateInventory_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]);

val FST_runMachine = Q.store_thm("FST_runMachine[simp]",
  `FST (runMachine obsr) = FST(FST obsr)`,
  Cases_on`obsr`\\rw[runMachine_def,UNCURRY]);

val FST_FST_prepare = Q.store_thm("FST_FST_prepare[simp]",
  `FST (FST (prepare z x)) = FST x`,
  PairCases_on`x` \\ simp[prepare_def]);

val FST_o_if_focal = Q.store_thm("FST_o_if_focal[simp]",
  `FST o if_focal x y = FST`,
  rw[if_focal_def,FUN_EQ_THM,FORALL_PROD]);

val NOT_isMovedIn_act = Q.store_thm("NOT_isMovedIn_act[simp]",
  `¬isMovedIn (act sq nb a)`,
  rw[act_def]
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]);

val less8 = Q.prove(
  `x < 8n ⇔ (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7)`,
  rw[EQ_IMP_THM] >> simp[])

val LENGTH_neighbour_coords = Q.store_thm("LENGTH_neighbour_coords",
  `LENGTH (neighbour_coords x) = 8`,
  Cases_on`x`>>simp[neighbour_coords_def]);

val LENGTH_neighbours = Q.store_thm("LENGTH_neighbours",
  `LENGTH (neighbours x y) = 8`,
  simp[neighbours_def,LENGTH_neighbour_coords]);

val opposite_less8 = Q.store_thm("opposite_less8[simp]",
  `opposite dir < 8`, rw[opposite_def])

val opposite_inj = Q.store_thm("opposite_inj",
  `i < 8 ∧ j < 8 ∧ opposite i = opposite j ⇒ i = j`,
  EVAL_TAC \\ rw[less8] \\ fs[]);

val opposite_opposite = Q.store_thm("opposite_opposite[simp]",
  `dir < 8 ⇒ opposite (opposite dir) = dir`,
  EVAL_TAC >> rw[less8] >> simp[]);

val neighbours_EL_neighbour_coords = Q.store_thm("neighbours_EL_neighbour_coords",
  `dir < 8 ∧ FLOOKUP s i = SOME sq ⇒
   EL (opposite dir) (neighbours s (EL dir (neighbour_coords i))) = SOME sq`,
  simp[neighbours_def] >>
  Cases_on`EL dir (neighbour_coords i)` >>
  Cases_on`i` >>
  fs[neighbour_coords_def] >>
  simp[less8] >>
  strip_tac >> fs[opposite_def] >> rveq
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ rpt AP_TERM_TAC
  \\ simp[]
  \\ intLib.COOPER_TAC);

val ALL_DISTINCT_neighbour_coords = Q.store_thm("ALL_DISTINCT_neighbour_coords[simp]",
  `ALL_DISTINCT (neighbour_coords k)`,
  Cases_on`k` \\ rw[neighbour_coords_def]
  \\ intLib.COOPER_TAC)

val NOT_MEM_neighbour_coords = Q.store_thm("NOT_MEM_neighbour_coords",
  `¬MEM k (neighbour_coords k)`,
  Cases_on`k`\\rw[neighbour_coords_def]
  \\ intLib.COOPER_TAC);

val neighbour_coords_opposite_imp = Q.store_thm("neighbour_coords_opposite_imp",
  `d < 8 ⇒
   EL (opposite d) (neighbour_coords (EL d (neighbour_coords c))) = c`,
  Cases_on`c`>>
  rw[less8] >> simp[neighbour_coords_def,opposite_def] >>
  intLib.COOPER_TAC);

val event_name_in_grid = Q.store_thm("event_name_in_grid",
  `FLOOKUP g c = SOME sq ∧
   MEM nra (event sq (neighbours g c)).robotActions ⇒
   if ¬isMovedIn (SND(SND nra)) then
     MEM (FST nra) (MAP FST sq.robots)
   else
   ∃c' sq'.
     FLOOKUP g c' = SOME sq' ∧ c ≠ c' ∧
     MEM (FST nra) (MAP FST sq'.robots)`,
  simp[event_def]
  \\  strip_tac
  >- (
    fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MEM_MAP,UNCURRY]
    \\ fs[localActions_def,MEM_MAP,UNCURRY]
    \\ metis_tac[] )
  \\ fs[MEM_FLAT,MEM_GENLIST]
  \\ rveq
  \\ Cases_on`EL dir (neighbours g c)` \\ fs[incomingFrom_def]
  \\ fs[MEM_MAP,MEM_FILTER]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ fs[neighbours_def]
  \\ rfs[EL_MAP]
  \\ asm_exists_tac
  \\ simp[EXISTS_PROD]
  \\ reverse conj_tac >- metis_tac[]
  \\ Cases_on`c` \\ fs[neighbour_coords_def]
  \\ fs[less8] \\ rw[]
  \\ intLib.COOPER_TAC);

val incomingFrom_MovedIn = Q.store_thm("incomingFrom_MovedIn",
  `MEM x (incomingFrom y z) ⇒ ∃i. SND (SND x) = MovedIn i`,
  Cases_on`z`>>rw[incomingFrom_def]>>
  fs[MEM_FLAT,MEM_MAP,MEM_FILTER,EXISTS_PROD]);

val wf_state_event_same_name = Q.store_thm("wf_state_event_same_name",
  `wf_state s ∧
   MEM (nm,ra1) ev1.robotActions ∧
   MEM (nm,ra2) ev2.robotActions ∧
   FLOOKUP (computeEvents s.grid) c1 = SOME ev1 ∧
   FLOOKUP (computeEvents s.grid) c2 = SOME ev2 ∧
   c1 ≠ c2
   ⇒
   ∃dir. dir < 8 ∧ {SND ra1; SND ra2} = {MovedIn dir; MovedOut (opposite dir)}`,
  rw[computeEvents_def,FLOOKUP_FMAP_MAP2,wf_state_def]
  \\ fs[event_def,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MEM_MAP,UNCURRY,MEM_FLAT,MEM_GENLIST]
  \\ rw[]
  \\ rpt (
    qmatch_asmsub_abbrev_tac`incomingFrom _ nb`
    \\ Cases_on`nb`
    \\ qpat_assum`Abbrev _`(strip_assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
    \\ fs[incomingFrom_def])
  \\ fs[MEM_MAP,MEM_FILTER]
  \\ fs[localActions_def,MEM_MAP] \\ rw[]
  \\ TRY pairarg_tac \\ fs[] \\ rw[]
  \\ TRY pairarg_tac \\ fs[] \\ rw[]
  \\ fs[IN_DISJOINT,MEM_MAP,EXISTS_PROD]
  >- metis_tac[]
  >- (
    rfs[neighbours_def,EL_MAP]
    \\ reverse(Cases_on`EL dir (neighbour_coords c2) = c1`)
    >- metis_tac[]
    \\ rw[] \\ fs[] \\ rw[]
    \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ `r = r'` by metis_tac[ALL_DISTINCT_MAP_FST]
    \\ simp[act_def]
    \\ fs[LENGTH_neighbour_coords,GSYM neighbours_def]
    \\ imp_res_tac neighbours_EL_neighbour_coords \\ fs[]
    \\ qexists_tac`dir` \\ rw[EXTENSION,EQ_IMP_THM] )
  >- (
    rfs[neighbours_def,EL_MAP]
    \\ reverse(Cases_on`EL dir (neighbour_coords c1) = c2`)
    >- metis_tac[]
    \\ rw[] \\ fs[] \\ rw[]
    \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ `r = r'` by metis_tac[ALL_DISTINCT_MAP_FST]
    \\ simp[act_def]
    \\ fs[LENGTH_neighbour_coords,GSYM neighbours_def]
    \\ imp_res_tac neighbours_EL_neighbour_coords \\ fs[]
    \\ qexists_tac`dir` \\ rw[EXTENSION,EQ_IMP_THM] )
  \\ rfs[neighbours_def,EL_MAP]
  \\ qmatch_assum_rename_tac`d1 < LENGTH (_ c1)`
  \\ qmatch_assum_rename_tac`d2 < LENGTH (_ c2)`
  \\ reverse(Cases_on`EL d1 (neighbour_coords c1) = EL d2 (neighbour_coords c2)`)
  >- metis_tac[]
  \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ `r = r'` by metis_tac[ALL_DISTINCT_MAP_FST]
  \\ rw[] \\ fs[] \\ rw[]
  \\ fs[LENGTH_neighbour_coords]
  \\ `d1 = d2` by metis_tac[opposite_inj]
  \\ fs[] \\ rw[]
  \\ Cases_on`c1` \\ Cases_on`c2`
  \\ `F` suffices_by rw[]
  \\ pop_assum mp_tac
  \\ simp[neighbour_coords_def]
  \\ fs[less8]
  \\ intLib.COOPER_TAC);

val MEM_MovedOut_localActions = Q.store_thm("MEM_MovedOut_localActions",
  `MEM nra (localActions sq nb) ∧
   SND(SND nra) = MovedOut dir
   ⇒
   dir < LENGTH nb ∧
   (FST(SND nra)).command = Move dir ∧
   IS_SOME (EL dir nb)`,
  simp[localActions_def,MEM_MAP]
  \\ strip_tac
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[act_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[] \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[] \\ fs[]);

val NOT_MEM_MovedIn_localActions = Q.store_thm("NOT_MEM_MovedIn_localActions",
  `MEM nra (localActions sq nb) ⇒ ¬isMovedIn(SND(SND nra))`,
  simp[localActions_def,MEM_MAP] \\ strip_tac
  \\ pairarg_tac \\ fs[]);

val same_name_same_action = Q.store_thm("same_name_same_action",
  `wf_state s ∧
   FLOOKUP (computeEvents s.grid) c1 = SOME ev1 ∧
   FLOOKUP (computeEvents s.grid) c2 = SOME ev2 ∧
   MEM (nm,ra1) ev1.robotActions ∧
   MEM (nm,ra2) ev2.robotActions ⇒
   ((c1 = c2 ∧ ra1 = ra2) ∨
    ∃dir. dir < 8 ∧ {SND ra1; SND ra2} = {MovedIn dir; MovedOut (opposite dir)})`,
  rw[IN_FRANGE_FLOOKUP,computeEvents_def,FLOOKUP_FMAP_MAP2]
  \\ reverse(Cases_on`c1=c2`\\fs[])
  >- (
    drule (GEN_ALL wf_state_event_same_name)
    \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
    \\ metis_tac[] )
  \\ fs[] \\ rveq \\ fs[]
  \\ disj1_tac
  \\ drule (GEN_ALL event_name_in_grid)
  \\ disch_then drule
  \\ drule (GEN_ALL event_name_in_grid)
  \\ qpat_assum`MEM (nm,ra1) _`assume_tac
  \\ disch_then drule
  \\ rw[]
  >- (
    rpt(qpat_assum`MEM _ _.robotActions`mp_tac)
    \\ simp[event_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,UNCURRY,o_DEF,MEM_MAP,EXISTS_PROD]
    \\ reverse strip_tac
    >- ( imp_res_tac incomingFrom_MovedIn \\ fs[] )
    \\ reverse strip_tac
    >- ( imp_res_tac incomingFrom_MovedIn \\ fs[] )
    \\ rveq \\ simp[]
    \\ `ALL_DISTINCT (MAP FST (localActions sq (neighbours s.grid c1)))`
    by (
      simp[localActions_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
      \\ metis_tac[] )
    \\ metis_tac[PAIR_EQ,ALL_DISTINCT_MAP_FST] )
  >- ( fs[wf_state_def,IN_DISJOINT] \\ metis_tac[] )
  >- ( fs[wf_state_def,IN_DISJOINT] \\ metis_tac[] )
  \\ rpt(qpat_assum`MEM _ _.robotActions`mp_tac)
  \\ simp[event_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,UNCURRY,o_DEF,MEM_MAP,EXISTS_PROD]
  \\ strip_tac
  >- ( metis_tac[NOT_MEM_MovedIn_localActions,SND] )
  \\ strip_tac
  >- ( metis_tac[NOT_MEM_MovedIn_localActions,SND] )
  \\ Cases_on`EL dir (neighbours s.grid c1)`\\fs[incomingFrom_def]
  \\ Cases_on`EL dir' (neighbours s.grid c1)`\\fs[incomingFrom_def]
  \\ rfs[neighbours_def,EL_MAP]
  \\ fs[MEM_MAP,MEM_FILTER,UNCURRY]
  \\ rveq
  \\ reverse conj_asm2_tac
  >- (
    fs[wf_state_def,IN_DISJOINT,MEM_MAP,PULL_EXISTS]
    \\ metis_tac[ALL_DISTINCT_neighbour_coords,EL_ALL_DISTINCT_EL_EQ] )
  \\ rveq \\ fs[] \\ rw[]
  \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ metis_tac[ALL_DISTINCT_MAP_FST,PAIR,SND]);

val event_MovedOut_MovedIn = Q.store_thm("event_MovedOut_MovedIn",
  `FLOOKUP (computeEvents g) c = SOME ev ∧
   MEM (nm,r,MovedOut dir) ev.robotActions
   ⇒
   ∃ev' r0.
   dir < LENGTH (neighbour_coords c) ∧
   FLOOKUP (computeEvents g) (EL dir (neighbour_coords c)) = SOME ev' ∧
   MEM (nm,r0,MovedIn (opposite dir)) ev'.robotActions`,
  rw[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
  \\ reverse(fs[event_def])
  >- (
    fs[MEM_FLAT,MEM_GENLIST] \\ rw[]
    \\ Cases_on`EL dir' (neighbours g c)` \\ fs[incomingFrom_def]
    \\ fs[MEM_MAP,MEM_FILTER,UNCURRY] )
  \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MEM_MAP,UNCURRY]
  \\ drule MEM_MovedOut_localActions
  \\ simp[] \\ strip_tac
  \\ fs[Once neighbours_def]
  \\ rfs[EL_MAP,IS_SOME_EXISTS]
  \\ simp[EXISTS_OR_THM]
  \\ disj2_tac
  \\ simp[MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`opposite dir`
  \\ simp[Once LENGTH_neighbours]
  \\ simp[Once neighbours_def,EL_MAP,Once LENGTH_neighbour_coords]
  \\ fs[Once LENGTH_neighbour_coords]
  \\ simp[neighbour_coords_opposite_imp]
  \\ simp[incomingFrom_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ rveq
  \\ fs[localActions_def,MEM_MAP,UNCURRY]
  \\ rw[]
  \\ qexists_tac`SND y'` \\ fs[]);

val event_MovedIn_MovedOut = Q.store_thm("event_MovedIn_MovedOut",
  `MEM (nm,r,MovedIn dir) ev.robotActions ∧
  FLOOKUP (computeEvents g) c = SOME ev
  ⇒
  ∃ev'.
  dir < LENGTH (neighbour_coords c) ∧
  FLOOKUP (computeEvents g) (EL dir (neighbour_coords c)) = SOME ev' ∧
  MEM (nm,r,MovedOut (opposite dir)) ev'.robotActions`,
  rw[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
  \\ fs[event_def]
  >- (
    fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MEM_MAP,UNCURRY]
    \\ imp_res_tac NOT_MEM_MovedIn_localActions
    \\ qpat_assum`MovedIn _ = _`(assume_tac o SYM)
    \\ fs[] )
  \\ fs[MEM_FLAT,MEM_GENLIST] \\ rw[]
  \\ simp[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MEM_MAP,UNCURRY]
  \\ Cases_on`EL dir' (neighbours g c)` \\ fs[incomingFrom_def]
  \\ fs[MEM_MAP,MEM_FILTER,UNCURRY] \\ rw[]
  \\ fs[Once neighbours_def]
  \\ rfs[EL_MAP]
  \\ simp[EXISTS_OR_THM]
  \\ disj1_tac
  \\ simp[localActions_def,MEM_MAP,PULL_EXISTS,UNCURRY]
  \\ qexists_tac`y`
  \\ simp[act_def,EL_MAP]
  \\ fs[Once LENGTH_neighbour_coords,neighbour_coords_opposite_imp]
  \\ simp[LENGTH_neighbour_coords]
  \\ simp[updateInventory_def]);

val wf_state_step = Q.store_thm("wf_state_step",
  `wf_state s ⇒ wf_state (step s)`,
  strip_tac
  \\ first_assum mp_tac
  \\ simp_tac(srw_ss())[wf_state_def]
  \\ reverse(rpt strip_tac)
  >- (
    fs[step_def,IN_FRANGE_FLOOKUP,FLOOKUP_FMAP_MAP2]
    \\ rw[]
    \\ pop_assum mp_tac
    \\ simp[computeSquare_def,MEM_MAP,PULL_EXISTS,MEM_GENLIST,MEM_FILTER]
    \\ reverse(rw[])
    \\ TRY pairarg_tac \\ fs[]
    \\ rw[runMachine_def,prepare_def,UNCURRY]
    \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
    \\ simp[GSYM ADD1]
    \\ match_mp_tac prim_recTheory.LESS_SUC
    \\ first_x_assum match_mp_tac
    \\ rw[]
    \\ fs[event_def]
    >- (
      asm_exists_tac
      \\ fs[MAP2_MAP,MAP2_same]
      \\ fs[PAIR_MAP_COMPOSE]
      \\ fs[MEM_MAP,UNCURRY,EXISTS_PROD]
      \\ rw[]
      \\ fs[localActions_def,MEM_MAP,UNCURRY]
      \\ metis_tac[PAIR])
    \\ fs[MEM_FLAT,MEM_GENLIST]
    \\ rw[]
    \\ Cases_on`EL dir (neighbours s.grid k)` \\ fs[incomingFrom_def]
    \\ fs[MEM_MAP,MEM_FILTER,UNCURRY]
    \\ rw[]
    \\ fs[neighbours_def]
    \\ rfs[EL_MAP]
    \\ asm_exists_tac \\ rw[]
    \\ metis_tac[] )
  >- (
    fs[IN_FRANGE_FLOOKUP,step_def,FLOOKUP_FMAP_MAP2]
    \\ simp[computeSquare_def,MAP_MAP_o,MAP_GENLIST]
    \\ simp[ALL_DISTINCT_APPEND,MEM_GENLIST,ALL_DISTINCT_GENLIST,MEM_MAP,MEM_FILTER,PULL_EXISTS]
    \\ simp[combinTheory.o_DEF,ETA_AX]
    \\ conj_tac
    >- (
      match_mp_tac ALL_DISTINCT_MAP_FILTER
      \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
      \\ simp[event_def,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[localActions_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ fs[PULL_EXISTS]
      \\ simp[ALL_DISTINCT_APPEND]
      \\ conj_tac >- metis_tac[]
      \\ simp[MEM_MAP,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
      \\ simp[MAP_FLAT,MAP_GENLIST,o_DEF]
      \\ conj_tac
      >- (
        simp[ALL_DISTINCT_FLAT,MEM_GENLIST,PULL_EXISTS]
        \\ conj_tac
        >- (
          simp[ALL_DISTINCT_FILTER_GENLIST]
          \\ qx_genl_tac[`d1`,`d2`]
          \\ qmatch_goalsub_abbrev_tac`incomingFrom _ n1`
          \\ qmatch_goalsub_abbrev_tac`_ = _ _ (incomingFrom _ n2)`
          \\ Cases_on`n1` \\ simp[incomingFrom_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
          \\ Cases_on`n2` \\ simp[incomingFrom_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
          \\ rw[]
          \\ fs[markerTheory.Abbrev_def]
          \\ rpt(qpat_assum`SOME _ = _`(assume_tac o SYM))
          \\ rfs[neighbours_def,EL_MAP]
          \\ Q.ISPEC_THEN`neighbour_coords k`match_mp_tac
               (Q.GEN`l` (MP_CANON (DISCH_ALL (#1 (EQ_IMP_RULE (UNDISCH_ALL (SPEC_ALL ALL_DISTINCT_EL_IMP)))))))
          \\ simp[]
          \\ spose_not_then strip_assume_tac
          \\ last_x_assum drule
          \\ rator_x_assum`FLOOKUP`kall_tac
          \\ disch_then drule
          \\ disch_then drule
          \\ simp[IN_DISJOINT]
          \\ fs[GSYM NULL_EQ,NOT_NULL_MEM]
          \\ fs[MEM_FILTER]
          \\ qmatch_assum_abbrev_tac`(l1:'a list) = l2`
          \\ `MEM (FST e) l1` by (simp[Abbr`l1`,MEM_MAP,MEM_FILTER] \\ metis_tac[])
          \\ `MEM (FST e) l2` by metis_tac[]
          \\ fs[Abbr`l1`,Abbr`l2`,MEM_MAP,MEM_FILTER]
          \\ metis_tac[] )
        \\ conj_tac
        >- (
          rw[]
          \\ qmatch_goalsub_abbrev_tac`incomingFrom _ nb`
          \\ Cases_on`nb` \\ simp[incomingFrom_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
          \\ match_mp_tac ALL_DISTINCT_MAP_FILTER
          \\ fs[markerTheory.Abbrev_def]
          \\ rpt(qpat_assum`SOME _ = _`(assume_tac o SYM))
          \\ rfs[neighbours_def,EL_MAP]
          \\ metis_tac[] )
        \\ qx_genl_tac[`d1`,`d2`]
        \\ qpat_abbrev_tac`nb = neighbours _ _`
        \\ Cases_on`EL d1 nb` \\ simp[incomingFrom_def]
        \\ Cases_on`EL d2 nb` \\ simp[incomingFrom_def]
        \\ simp[MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
        \\ rw[]
        \\ fs[Abbr`nb`,neighbours_def,EL_MAP]
        \\ simp[IN_DISJOINT,MEM_MAP,MEM_FILTER,UNCURRY]
        \\ spose_not_then strip_assume_tac
        \\ drule same_name_same_square
        \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS,MEM_MAP]
        \\ asm_exists_tac \\ simp[]
        \\ qpat_assum`FLOOKUP _ (EL d1 _) = _`assume_tac
        \\ asm_exists_tac \\ simp[]
        \\ asm_exists_tac \\ simp[]
        \\ rveq
        \\ asm_exists_tac \\ simp[]
        \\ spose_not_then strip_assume_tac \\ rveq
        \\ last_x_assum drule
        \\ qpat_assum`FLOOKUP _ (EL d2 _) = _`assume_tac
        \\ disch_then drule
        \\ simp[GSYM NULL_EQ, NOT_NULL_MEM]
        \\ reverse conj_tac >- metis_tac[]
        \\ `d1 ≠ d2` suffices_by metis_tac[ALL_DISTINCT_neighbour_coords,EL_ALL_DISTINCT_EL_EQ]
        \\ spose_not_then strip_assume_tac \\ fs[])
      \\ rw[]
      \\ spose_not_then strip_assume_tac
      \\ Cases_on`EL dir (neighbours s.grid k)`\\fs[incomingFrom_def]
      \\ rfs[neighbours_def,EL_MAP]
      \\ fs[MEM_MAP,MEM_FILTER,UNCURRY]
      \\ rveq \\ fs[]
      \\ last_x_assum drule
      \\ qpat_assum`FLOOKUP _ k = _`assume_tac
      \\ disch_then drule
      \\ simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS]
      \\ metis_tac[NOT_MEM_neighbour_coords,MEM_EL])
    \\ rw[]
    \\ spose_not_then strip_assume_tac
    \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
    \\ rw[]
    \\ drule (GEN_ALL event_name_in_grid)
    \\ disch_then drule
    \\ simp[]
    \\ fs[PULL_EXISTS]
    \\ rw[]
    \\ spose_not_then strip_assume_tac
    \\ first_x_assum drule \\ simp[]
    \\ asm_exists_tac \\ simp[])
  \\ fs[step_def,FLOOKUP_FMAP_MAP2]
  \\ simp[computeSquare_def,MAP_MAP_o,MAP_GENLIST,o_DEF,ETA_AX]
  \\ REWRITE_TAC[CONJ_ASSOC]
  \\ reverse conj_tac
  >- (
    simp[IN_DISJOINT,MEM_GENLIST]
    \\ spose_not_then strip_assume_tac
    \\ rw[] \\ fs[name_component_equality] )
  \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
  \\ rveq
  \\ simp[IN_DISJOINT,MEM_GENLIST,MEM_MAP,MEM_FILTER,UNCURRY,PULL_EXISTS]
  \\ fs[IN_DISJOINT]
  \\ rw[]
  \\ spose_not_then strip_assume_tac
  >- (
    rw[]
    \\ drule (GEN_ALL event_name_in_grid)
    \\ disch_then drule
    \\ rator_x_assum`FLOOKUP`mp_tac
    \\ drule (GEN_ALL event_name_in_grid)
    \\ disch_then drule
    \\ rw[]
    >- metis_tac[]
    >- (
      spose_not_then strip_assume_tac
      \\ qmatch_assum_rename_tac`c2 ≠ c3`
      \\ reverse(Cases_on`c3=c1`) >- metis_tac[]
      \\ rveq \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`FST ra1 = FST ra2`
      \\ Cases_on`ra1` \\ Cases_on`ra2` \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`MEM (nm,a1) _`
      \\ qpat_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ disch_then drule
      \\ simp[]
      \\ qpat_assum`FLOOKUP _ c2 = _`assume_tac
      \\ asm_exists_tac
      \\ rw[EXTENSION]
      \\ disj2_tac
      \\ qexists_tac`SND a1`
      \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[])
    >- (
      spose_not_then strip_assume_tac
      \\ qmatch_assum_rename_tac`c1 ≠ c3`
      \\ reverse(Cases_on`c3=c2`) >- metis_tac[]
      \\ rveq \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`FST ra1 = FST ra2`
      \\ Cases_on`ra1` \\ Cases_on`ra2` \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`MEM (nm,a1) _`
      \\ qpat_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ qpat_assum`FLOOKUP _ c1 = _`assume_tac
      \\ disch_then drule
      \\ simp[]
      \\ qpat_assum`FLOOKUP _ c2 = _`assume_tac
      \\ asm_exists_tac
      \\ rw[EXTENSION]
      \\ disj2_tac
      \\ qexists_tac`SND a2`
      \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[])
    >- (
      spose_not_then strip_assume_tac
      \\ qmatch_assum_rename_tac`c2 ≠ c3`
      \\ qmatch_assum_rename_tac`c1 ≠ c4`
      \\ reverse(Cases_on`c3=c4`) >- metis_tac[]
      \\ rveq \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`FST ra1 = FST ra2`
      \\ Cases_on`ra1` \\ Cases_on`ra2` \\ fs[] \\ rveq
      \\ qmatch_assum_rename_tac`MEM (nm,a1) _`
      \\ qpat_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ qpat_assum`FLOOKUP _ c1 = _`assume_tac
      \\ disch_then drule
      \\ simp[]
      \\ qpat_assum`FLOOKUP _ c2 = _`assume_tac
      \\ asm_exists_tac
      \\ rw[EXTENSION]
      \\ disj2_tac
      \\ qexists_tac`MovedOut (opposite dir)`
      \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ pop_assum(assume_tac o SYM)
      \\ fs[]))
  >- (
    rw[]
    \\ qpat_assum`FLOOKUP _ c1 = _`assume_tac
    \\ drule (GEN_ALL event_name_in_grid)
    \\ disch_then drule
    \\ rw[]
    >- (
      rw[MEM_MAP]
      \\ spose_not_then strip_assume_tac
      \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,MEM_MAP]
      \\ qpat_assum`_ = FST _`(assume_tac o SYM)
      \\ res_tac \\ rfs[] )
    >- (
      rw[MEM_MAP]
      \\ spose_not_then strip_assume_tac
      \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,MEM_MAP]
      \\ qpat_assum`_ = FST _`(assume_tac o SYM)
      \\ res_tac \\ rfs[] ))
  \\ rw[]
  \\ drule (GEN_ALL event_name_in_grid)
  \\ disch_then drule
  \\ qpat_assum`_ = FST _`(assume_tac o SYM)
  \\ rw[MEM_MAP]
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ fs[IN_FRANGE_FLOOKUP,MEM_MAP,PULL_EXISTS]
  \\ qpat_assum`_ = FST _`(assume_tac o SYM)
  \\ res_tac \\ rfs[]);

val wf_state_fill = Q.store_thm("wf_state_fill",
  `wf_state s.state ⇒ wf_state (fill f s)`,
  simp[wf_state_def,fill_def,FLOOKUP_o_f,IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ strip_tac
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ BasicProvers.TOP_CASE_TAC
    \\ BasicProvers.TOP_CASE_TAC
    \\ strip_tac \\ rveq
    \\ simp[MAP_MAP_o]
    \\ metis_tac[] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ BasicProvers.TOP_CASE_TAC
    \\ strip_tac \\ rveq
    \\ simp[MAP_MAP_o]
    \\ metis_tac[] )
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ strip_tac \\ rveq
  \\ fs[MAP_MAP_o]
  \\ metis_tac[]);

val focal_event_sing = Q.store_thm("focal_event_sing",
  `wf_state s ∧
   sq ∈ FRANGE s.grid ∧
   MEM nm (MAP FST sq.robots)
   ⇒
    ∃x.
     {(c,ev,a) | ∃r. MEM (nm,r,a) ev.robotActions ∧
                   ¬isMovedOut a ∧
                   FLOOKUP (computeEvents s.grid) c = SOME ev }
     = {x}`,
  rw[computeEvents_def,IN_FRANGE_FLOOKUP,FLOOKUP_FMAP_MAP2,EXTENSION,PULL_EXISTS]
  \\ `MEM nm (MAP FST (event sq (neighbours s.grid k)).robotActions)`
  by (
    rw[event_def,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
    \\ rw[localActions_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX] )
  \\ qmatch_asmsub_abbrev_tac`MEM nm (MAP FST ev.robotActions)`
  \\ `FLOOKUP (computeEvents s.grid) k = SOME ev`
  by simp[computeEvents_def,FLOOKUP_FMAP_MAP2]
  \\ fs[MEM_MAP] \\ rw[]
  \\ qmatch_assum_rename_tac`MEM nra ev.robotActions`
  \\ Cases_on`isMovedIn (SND(SND nra))`
  >- (
    qexists_tac`(k,ev,SND(SND nra))`
    \\ rw[EQ_IMP_THM,Abbr`ev`]
    \\ PairCases_on`nra` \\ fs[]
    \\ rveq
    >- (
      drule (GEN_ALL same_name_same_action)
      \\ disch_then drule
      \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
      \\ disch_then drule
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac \\ rveq \\ fs[]
      \\ Cases_on`nra2` \\ fs[]
      \\ fs[EXTENSION]
      \\ first_assum(qspec_then`a`mp_tac)
      \\ simp_tac(srw_ss())[]
      \\ strip_tac \\ fs[]
      \\ first_x_assum(qspec_then`MovedOut(opposite dir)`mp_tac)
      \\ simp[] )
    \\ asm_exists_tac \\ simp[]
    \\ Cases_on`nra2` \\ fs[])
  \\ Cases_on`isMovedOut (SND(SND nra))`
  >- (
    PairCases_on`nra`\\fs[]
    \\ Cases_on`nra2`\\fs[]
    \\ rw[]
    \\ drule (GEN_ALL event_MovedOut_MovedIn)
    \\ disch_then drule
    \\ rw[]
    \\ qexists_tac`(EL n (neighbour_coords k), ev', MovedIn(opposite n))`
    \\ rw[EQ_IMP_THM]
    >- (
      fs[computeEvents_def,FLOOKUP_FMAP_MAP2,Abbr`ev`]
      \\ rveq \\ fs[] \\ rveq
      \\ `c = EL n (neighbour_coords k) ∧ (r,a) = (r0,MovedIn (opposite n))`
      by (
        drule (GEN_ALL same_name_same_action)
        \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
        \\ disch_then drule
        \\ qpat_assum`FLOOKUP _ (_ _) = _`assume_tac
        \\ disch_then drule
        \\ disch_then drule
        \\ disch_then drule
        \\ strip_tac \\ fs[]
        \\ fs[EXTENSION]
        \\ first_assum(qspec_then`a`mp_tac)
        \\ simp_tac(srw_ss())[]
        \\ strip_tac \\ fs[]
        \\ first_x_assum(qspec_then`MovedOut(opposite dir)`mp_tac)
        \\ simp[] )
      \\ fs[] )
    \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
    \\ rw[]
    \\ metis_tac[] )
  \\ qexists_tac`(k,ev,SND(SND nra))`
  \\ rw[EQ_IMP_THM]
  >- (
    fs[computeEvents_def,FLOOKUP_FMAP_MAP2,Abbr`ev`]
    \\ PairCases_on`nra` \\ rfs[] \\ rveq
    \\ drule (GEN_ALL same_name_same_action)
    \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
    \\ disch_then drule
    \\ qpat_assum`FLOOKUP _ k = _`assume_tac
    \\ disch_then drule
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac \\ fs[]
    \\ fs[EXTENSION]
    \\ first_x_assum(qspec_then`nra2`mp_tac)
    \\ rw[] \\ fs[] )
  \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2,Abbr`ev`]
  \\ PairCases_on`nra` \\ rfs[] \\ rveq
  \\ metis_tac[]);

val FRANGE_fill = Q.store_thm("FRANGE_fill",
  `FRANGE (fill f s).grid =
   IMAGE (square_robots_fupd (MAP (if_focal s.focal_name f)))
     (FRANGE s.state.grid)`,
  rw[EXTENSION,IN_FRANGE_FLOOKUP,EQ_IMP_THM,fill_def,FLOOKUP_o_f]
  \\ pop_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[]
  \\ TRY(qexists_tac`k`\\simp[])
  \\ metis_tac[]);

val wf_state_with_hole_steph = Q.store_thm("wf_state_with_hole_steph",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s')
   ⇒
   wf_state_with_hole s'`,
  rw[steph_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[wf_state_with_hole_def]
  \\ rveq \\ fs[]
  \\ `wf_state (fill (with_command c) s)` by metis_tac[wf_state_fill]
  \\ conj_tac >- ( match_mp_tac wf_state_step \\ simp[] )
  \\ drule (GEN_ALL focal_event_sing)
  \\ simp[FRANGE_fill,PULL_EXISTS]
  \\ disch_then drule
  \\ simp[MAP_MAP_o]
  \\ disch_then drule
  \\ disch_then(qx_choose_then`ceva`strip_assume_tac)
  \\ fs[] \\ rveq
  \\ qexists_tac`computeSquare s.state.time_step (c',ev)`
  \\ simp[step_def,IN_FRANGE_FLOOKUP,FLOOKUP_FMAP_MAP2]
  \\ fs[EXTENSION]
  \\ first_x_assum(qspec_then`(c',ev,a)`mp_tac)
  \\ simp[] \\ strip_tac
  \\ conj_tac >- ( asm_exists_tac \\ simp[fill_def] )
  \\ simp[computeSquare_def]
  \\ disj1_tac
  \\ simp[MEM_MAP,MAP_MAP_o,MEM_FILTER,PULL_EXISTS]
  \\ CONV_TAC(STRIP_QUANT_CONV(move_conj_left(can(match_term``MEM _ _``))))
  \\ asm_exists_tac
  \\ simp[]
  \\ fs[FEVERY_ALL_FLOOKUP]
  \\ first_x_assum drule
  \\ simp[EVERY_MEM,MEM_MAP]
  \\ metis_tac[]);

val robots_by_name_def = Define`
  robots_by_name s nm = { r | ∃sq. ALOOKUP sq.robots nm = SOME r ∧ sq ∈ FRANGE s.grid }`;

val get_robot_by_name_def = Define`
  get_robot_by_name s nm = CHOICE (robots_by_name s nm)`

val robots_by_name_sing = Q.store_thm("robots_by_name_sing",
  `wf_state s ⇒
   robots_by_name s nm = {} ∨
   ∃r. robots_by_name s nm = {r}`,
  rw[wf_state_def,robots_by_name_def]
  \\ rw[EXTENSION]
  \\ reverse(Cases_on`∃sq. sq ∈ FRANGE s.grid ∧ IS_SOME (ALOOKUP sq.robots nm)`)
  >- (
    disj1_tac \\ rw[]
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ metis_tac[NOT_SOME_NONE] )
  \\ disj2_tac
  \\ fs[IS_SOME_EXISTS]
  \\ qexists_tac`x`
  \\ reverse(rw[EQ_IMP_THM])
  >- metis_tac[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[IN_DISJOINT,MEM_MAP,EXISTS_PROD]
  \\ fs[IN_FRANGE_FLOOKUP]
  \\ Cases_on`k=k'`\\fs[] \\ rveq \\ fs[]
  \\ metis_tac[]);

val get_focal_robot_def = Define`
  get_focal_robot s = get_robot_by_name s.state s.focal_name`;

val get_focal_robot_sing = Q.store_thm("get_focal_robot_sing",
  `wf_state_with_hole s ⇒
    robots_by_name s.state s.focal_name  = {get_focal_robot s}`,
  rw[wf_state_with_hole_def]
  \\ drule (GEN_ALL robots_by_name_sing)
  \\ disch_then(qspec_then`s.focal_name`strip_assume_tac)
  >- (
    fs[robots_by_name_def,EXTENSION]
    \\ fs[MEM_MAP,EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,NOT_SOME_NONE,option_CASES] )
  \\ rw[get_focal_robot_def]
  \\ rw[get_robot_by_name_def]);

val get_focal_robot_unique = Q.store_thm("get_focal_robot_unique",
  `wf_state_with_hole s ∧
   sq ∈ FRANGE s.state.grid ∧
   MEM (s.focal_name,r) sq.robots
   ⇒ r = get_focal_robot s`,
  rw[]
  \\ drule get_focal_robot_sing
  \\ rw[get_focal_robot_def]
  \\ fs[robots_by_name_def,EXTENSION]
  \\ first_x_assum(qspec_then`r`(match_mp_tac o #1 o EQ_IMP_RULE))
  \\ metis_tac[wf_state_def,ALOOKUP_ALL_DISTINCT_MEM,wf_state_with_hole_def]);

val clock_preserved = Q.store_thm("clock_preserved",
  `wf_state s ⇒
   IMAGE robot_processor (robots_by_name (step s) nm) =
   IMAGE robot_processor (robots_by_name s nm) ∨
   robots_by_name s nm = {} ∨
   robots_by_name (step s) nm = {}`,
  rw[]
  \\ drule (GEN_ALL robots_by_name_sing)
  \\ disch_then(qspec_then`nm`strip_assume_tac)
  \\ fs[]
  \\ imp_res_tac wf_state_step
  \\ drule (GEN_ALL robots_by_name_sing)
  \\ disch_then(qspec_then`nm`strip_assume_tac)
  \\ fs[]
  \\ fs[robots_by_name_def]
  \\ fs[EXTENSION]
  \\ last_x_assum(qspec_then`r`strip_assume_tac) \\ fs[]
  \\ last_x_assum(qspec_then`r'`strip_assume_tac) \\ fs[]
  \\ fs[IN_FRANGE_FLOOKUP]
  \\ rator_x_assum`wf_state`kall_tac
  \\ fs[step_def,FLOOKUP_FMAP_MAP2]
  \\ rw[]
  \\ fs[computeSquare_def,ALOOKUP_APPEND]
  \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
  \\ rw[]
  \\ every_case_tac \\ fs[]
  >- (
    imp_res_tac ALOOKUP_MEM
    \\ fs[MEM_MAP,MEM_GENLIST]
    \\ rw[]
    \\ fs[prepare_def,runMachine_def]
    \\ pairarg_tac \\ fs[]
    \\ rw[]
    \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ qmatch_assum_abbrev_tac`MEM (nm,r) sq.robots`
    \\ `nm.built_step = s.time_step` by simp[Abbr`nm`]
    \\ metis_tac[prim_recTheory.LESS_REFL,MEM_MAP,FST] )
  \\ rw[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,MEM_FILTER]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ fs[prepare_def,runMachine_def]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ rator_x_assum`ALOOKUP`kall_tac
  \\ rator_x_assum`run_policy`kall_tac
  \\ drule (GEN_ALL event_name_in_grid)
  \\ disch_then drule
  \\ rw[] >- (
    drule same_name_same_square
    \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ disch_then drule
    \\ qpat_assum`_ = SOME sq`assume_tac
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ impl_tac >- metis_tac[]
    \\ strip_tac \\ rveq
    \\ drule grid_injective
    \\ disch_then drule
    \\ qpat_assum`_ _ k' = _`assume_tac
    \\ disch_then drule
    \\ simp[NOT_NULL_MEM]
    \\ impl_tac >- metis_tac[]
    \\ strip_tac \\ rveq
    \\ fs[]
    \\ reverse(fs[event_def])
    >- (
      fs[MEM_FLAT,MEM_GENLIST] \\ rw[]
      \\ imp_res_tac incomingFrom_MovedIn
      \\ fs[] )
    \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,o_DEF,UNCURRY,MEM_MAP]
    \\ rw[]
    \\ fs[localActions_def,MEM_MAP,UNCURRY]
    \\ rw[] \\ fs[]
    \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ metis_tac[ALL_DISTINCT_MAP_FST,PAIR,PAIR_EQ] )
  \\ Cases_on`a` \\ fs[]
  \\ drule (GEN_ALL event_MovedIn_MovedOut)
  \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
  \\ qpat_assum`_ = SOME sq'`assume_tac
  \\ disch_then drule \\ simp[]
  \\ strip_tac
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ qpat_assum`MEM (_,_,MovedIn _) _`kall_tac
  \\ reverse(fs[event_def])
  >- (
    fs[MEM_FLAT,MEM_GENLIST] \\ rw[]
    \\ imp_res_tac incomingFrom_MovedIn
    \\ fs[] )
  \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,o_DEF,UNCURRY,MEM_MAP]
  \\ rw[]
  \\ fs[localActions_def,MEM_MAP,UNCURRY]
  \\ rw[] \\ fs[]
  \\ drule same_name_same_square
  \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ disch_then drule
  \\ qpat_assum`_ = SOME sq`assume_tac
  \\ disch_then drule
  \\ simp[MEM_MAP,PULL_EXISTS]
  \\ disch_then drule
  \\ simp[AND_IMP_INTRO]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ disch_then drule
  \\ rw[] \\ fs[]
  \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ metis_tac[ALL_DISTINCT_MAP_FST,PAIR,PAIR_EQ] );

val if_focal_eta  = Q.store_thm("if_focal_eta",
  `if_focal fnm f = λ(nm,r). (nm, if nm = fnm then f r else r)`,
  rw[FUN_EQ_THM,if_focal_def,FORALL_PROD])

val fill_robots_by_name = Q.store_thm("fill_robots_by_name",
  `robots_by_name (fill f s) s.focal_name = IMAGE f (robots_by_name s.state s.focal_name)`,
  rw[fill_def,robots_by_name_def,IN_FRANGE_FLOOKUP,FLOOKUP_o_f,EXTENSION,EQ_IMP_THM,PULL_EXISTS]
  >- (
    every_case_tac \\ fs[] \\ rw[] \\ fs[]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs[MEM_MAP,EXISTS_PROD,if_focal_def]
    \\ rw[]
    \\ fs[if_focal_eta,ALOOKUP_MAP_gen]
    \\ metis_tac[PAIR] )
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`k` \\ simp[]
  \\ simp[if_focal_eta,ALOOKUP_MAP_gen]);

val steph_focal_clock = Q.store_thm("steph_focal_clock",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ⇒
   (get_focal_robot s).processor = (get_focal_robot s').processor`,
  rw[]
  \\ drule get_focal_robot_sing
  \\ imp_res_tac wf_state_with_hole_steph
  \\ drule get_focal_robot_sing
  \\ rw[]
  \\ simp_tac(srw_ss())[get_focal_robot_def,get_robot_by_name_def]
  \\ ASM_REWRITE_TAC[CHOICE_IMAGE_SING]
  \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
  \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ qho_match_abbrev_tac`P s = P s'`
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac`P <| state := (fill (with_command c) s); focal_name := s.focal_name |>`
  \\ simp[Abbr`P`]
  \\ conj_tac
  >- (
    simp[fill_robots_by_name,GSYM IMAGE_COMPOSE]
    \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ simp[FUN_EQ_THM] )
  \\ fs[steph_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ `wf_state (fill (with_command c) s)` by metis_tac[wf_state_fill,wf_state_with_hole_def]
  \\ drule (GEN_ALL clock_preserved)
  \\ disch_then(qspec_then`s.focal_name`strip_assume_tac)
  >- simp[]
  \\ imp_res_tac get_focal_robot_sing
  \\ fs[fill_robots_by_name]);

val fill_with_policy_split = Q.store_thm("fill_with_policy_split",
  `fill (with_policy c p) s =
   fill (memory_fupd (K p))
   (s with state := fill (command_fupd (K c)) s)`,
  rw[fill_def,state_with_hole_component_equality,state_component_equality]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[square_component_equality,MAP_MAP_o,o_DEF]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM,FORALL_PROD,if_focal_def]);

val step_time_step = Q.store_thm("step_time_step[simp]",
  `(step s).time_step = s.time_step + 1`,
  rw[step_def]);

val fill_time_step = Q.store_thm("fill_time_step[simp]",
  `(fill f s).time_step = s.state.time_step `,
  EVAL_TAC);

val update_robots_def = Define`
  update_robots nm f = (square_robots_fupd (MAP (if_focal nm f)))`

val update_robots_items = Q.store_thm("update_robots_items[simp]",
  `(update_robots nm f sq).items = sq.items`,
  EVAL_TAC);

val update_robots_intro =
  Q.ISPEC`update_robots nm f`ETA_AX
  |> CONV_RULE(LAND_CONV(REWRITE_CONV[update_robots_def]))

val update_robots_split = Q.store_thm("update_robots_split",
  `update_robots nm (with_policy c p) =
   update_robots nm (with_memory p) o
   update_robots nm (with_command c)`,
  rw[FUN_EQ_THM,update_robots_def,square_component_equality]
  \\ rw[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,if_focal_def]);

val event_update_robots_def = Define`
  event_update_robots nm f =
    event_robotActions_fupd
      (MAP (if_focal nm (f ## I)))`;

val SND_if_focal_with_memory_command = Q.store_thm("SND_if_focal_with_memory_command[simp]",
  `(SND (if_focal nm (with_memory p) r)).command = (SND r).command`,
  Cases_on`r` \\ rw[if_focal_def]);

val SND_if_focal_with_memory_inventory = Q.store_thm("SND_if_focal_with_memory_inventory[simp]",
  `(SND (if_focal nm (with_memory p) r)).inventory = (SND r).inventory`,
  Cases_on`r` \\ rw[if_focal_def]);

val SND_if_focal_with_memory_canLift = Q.store_thm("SND_if_focal_with_memory_canLift[simp]",
  `canLift (SND (if_focal nm (with_memory p) x)) = canLift (SND x)`,
  Cases_on`x` \\ rw[if_focal_def,FUN_EQ_THM,canLift_def]);

val LENGTH_FILTER_requests_with_memory = Q.store_thm("LENGTH_FILTER_requests_with_memory",
  `LENGTH (FILTER (requests x y o SND o if_focal nm (with_memory p)) ls) =
   LENGTH (FILTER (requests x y o SND) ls)`,
  Induct_on`ls` \\ rw[requests_def]);

val contested_with_memory = Q.store_thm("contested_with_memory[simp]",
  `contested (update_robots nm (with_memory p) sq) = contested sq`,
  rw[FUN_EQ_THM,contested_def,update_robots_def,MAP_MAP_o]
  \\ simp[FILTER_MAP,LENGTH_FILTER_requests_with_memory]);

val usedItem_with_memory = Q.store_thm("usedItem_with_memory",
  `usedItem
    (MAP (SND o SND)
      (localActions (update_robots nm (with_memory p) sq)
        (neighbours (update_robots nm (with_memory p) o_f g) k))) =
   usedItem
     (MAP (SND o SND)
       (localActions sq (neighbours g k)))`,
  rw[localActions_def,MAP_MAP_o,o_DEF,UNCURRY]
  \\ rw[FUN_EQ_THM,usedItem_def,EXISTS_MAP]
  \\ rw[update_robots_def,EXISTS_MAP]
  \\ match_mp_tac EXISTS_CONG \\ simp[]
  \\ Cases \\ simp[]
  \\ simp[act_def]
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[GSYM update_robots_def,Once EXISTS_NOT_EVERY]
  \\ fs[EVERY_MEM,EXISTS_MEM]
  \\ metis_tac[]);

val dropItem_with_memory = Q.store_thm("dropItem_with_memory",
  `MAP (dropItem o SND)
     (localActions (update_robots nm (with_memory p) x)
       (neighbours (update_robots nm (with_memory p) o_f g) k)) =
   MAP (dropItem o SND) (localActions x (neighbours g k))`,
  rw[localActions_def,MAP_MAP_o,o_DEF,UNCURRY]
  \\ rw[update_robots_def,MAP_MAP_o,o_DEF,MAP_EQ_f]
  \\ rw[dropItem_def]
  \\ simp[act_def]
  \\ every_case_tac \\ fs[]);

val fled_with_memory = Q.store_thm("fled_with_memory",
  `fled (neighbours (robots_fupd (MAP (if_focal nm (with_memory p))) o_f g) k) =
   fled (neighbours g k)`,
  simp[FUN_EQ_THM] \\ Cases \\ rw[fled_def]
  \\ simp[neighbours_def]
  \\ rw[EQ_IMP_THM]
  \\ rfs[EL_MAP,IS_SOME_EXISTS]
  \\ fs[FLOOKUP_o_f]
  \\ every_case_tac \\ fs[]);

val MEM_Destroyed_localActions_with_memory = Q.store_thm("MEM_Destroyed_localActions_with_memory",
  `MEM (Destroyed nm')
     (MAP (SND o SND)
        (localActions (update_robots nm (with_memory p) x)
          (neighbours (update_robots nm (with_memory p) o_f g) k))) ⇔
   MEM (Destroyed nm')
     (MAP (SND o SND)
        (localActions x (neighbours g k)))`,
  rw[MEM_MAP,localActions_def,PULL_EXISTS,update_robots_def,UNCURRY]
  \\ rw[EQ_IMP_THM]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ asm_exists_tac \\ simp[]
  \\ qpat_assum`_ = _`(mp_tac o SYM)
  \\ simp[act_def]
  \\ every_case_tac \\ fs[]
  \\ fs[MAP_MAP_o,o_DEF,fled_with_memory]
  \\ fs[ALOOKUP_MAP_gen,if_focal_eta] \\ rveq \\ fs[]
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ every_case_tac \\ fs[]);

val MAP_robot_command_o_SND_update_robots_with_memory = Q.store_thm("MAP_robot_command_o_SND_update_robots_with_memory[simp]",
  `MAP (robot_command o SND) (update_robots nm (with_memory p) sq).robots =
   MAP (robot_command o SND) sq.robots`,
  rw[update_robots_def,MAP_MAP_o,o_DEF,MAP_EQ_f]);

val FILTER_isBuilt_localActions_with_memory = Q.store_thm("FILTER_isBuilt_localActions_with_memory",
  `FILTER isBuilt
     (MAP (SND o SND)
        (localActions (update_robots nm (with_memory p) x)
          (neighbours (update_robots nm (with_memory p) o_f g) k))) =
   FILTER isBuilt
     (MAP (SND o SND)
        (localActions x (neighbours g k)))`,
  rw[localActions_def,MAP_MAP_o,update_robots_def]
  \\ qspec_tac(`x.robots`,`ls`)
  \\ Induct \\ simp[UNCURRY]
  \\ Cases
  \\ simp[act_def]
  \\ every_case_tac \\ fs[]
  \\ fs[EVERY_MEM,EXISTS_MEM,GSYM update_robots_def]
  \\ metis_tac[]);

val SND_SND_if_focal_I = Q.store_thm("SND_SND_if_focal_I[simp]",
  `SND (SND (if_focal nm (f ## I) x)) = SND (SND x)`,
  PairCases_on`x` \\ EVAL_TAC \\ rw[]);

val FST_if_focal = Q.store_thm("FST_if_focal[simp]",
  `FST (if_focal nm f x) = FST x`,
  PairCases_on`x` \\ EVAL_TAC);

val canLift_with_memory = Q.store_thm("canLift_with_memory[simp]",
  `canLift (r with memory := p) = canLift r`,
  rw[canLift_def,FUN_EQ_THM]);

val fled_with_memory = Q.store_thm("fled_with_memory[simp]",
  `fled (neighbours (update_robots n (with_memory p) o_f g) k) c =
   fled (neighbours g k) c`,
  Cases_on`c` \\ rw[fled_def]
  \\ rw[neighbours_def,EQ_IMP_THM]
  \\ rfs[EL_MAP,FLOOKUP_o_f]
  \\ every_case_tac \\ fs[]);

val ALOOKUP_update_robots = Q.store_thm("ALOOKUP_update_robots[simp]",
  `ALOOKUP (update_robots nm f sq).robots n =
   OPTION_MAP (if n = nm then f else I) (ALOOKUP sq.robots n)`,
  rw[update_robots_def,if_focal_eta,ALOOKUP_MAP_gen,ETA_AX]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM]);

val act_with_memory = Q.store_thm("act_with_memory",
  `(∀r'. act sq (neighbours g k) r ≠ Inspected nm r')
   ⇒
   act (update_robots nm (with_memory p) sq)
       (neighbours (update_robots nm (with_memory p) o_f g) k)
       (if x = nm then r with memory := p else r) =
   act sq (neighbours g k) r`,
  rw[act_def]
  \\ every_case_tac \\ fs[]
  \\ TRY (fs[LENGTH_neighbours] \\  NO_TAC)
  \\ rveq \\ fs[]
  \\ fs[neighbours_def,update_robots_def,EL_MAP,FLOOKUP_o_f]
  \\ every_case_tac \\ fs[]);

val computeEvents_update_robots_with_memory = Q.store_thm("computeEvents_update_robots_with_memory",
  `wf_state s ∧
   FEVERY
    (λ(_,ev). EVERY (λa. ∀r. a ≠ Inspected nm r) (MAP (SND o SND) ev.robotActions))
    (computeEvents s.grid)
   ⇒
   computeEvents (update_robots nm (with_memory p) o_f s.grid) =
   event_update_robots nm (with_memory p) o_f (computeEvents s.grid)`,
  rw[fmap_eq_flookup,FLOOKUP_o_f,computeEvents_def,FLOOKUP_FMAP_MAP2]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ fs[FEVERY_ALL_FLOOKUP,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
  \\ first_x_assum drule
  \\ rw[event_def,event_update_robots_def]
  \\ simp[usedItem_with_memory,dropItem_with_memory,
          MEM_Destroyed_localActions_with_memory,
          FILTER_isBuilt_localActions_with_memory]
  \\ TRY (
    match_mp_tac APPEND_EQ_suff
    \\ conj_tac
    >- (
      simp[localActions_def,update_robots_def,MAP2_MAP,MAP2_same,MAP_MAP_o,PAIR_MAP_COMPOSE,
           o_DEF,UNCURRY,MAP_EQ_f,FORALL_PROD]
      \\ rpt gen_tac \\ strip_tac
      \\ CONV_TAC(RAND_CONV(REWR_CONV(GSYM PAIR))) \\ simp[]
      \\ simp[if_focal_def]
      \\ qpat_abbrev_tac`a1 = act _ _ _`
      \\ qpat_abbrev_tac`a2 = act _ _ _`
      \\ `a1 = a2`
      by (
        unabbrev_all_tac
        \\ simp[GSYM update_robots_def]
        \\ match_mp_tac act_with_memory
        \\ fs[localActions_def,update_robots_def,MAP2_MAP,MAP2_same,MAP_MAP_o,PAIR_MAP_COMPOSE,
              o_DEF,UNCURRY,EVERY_MAP]
        \\ fs[EVERY_MEM,FORALL_PROD]
        \\ metis_tac[])
      \\ fs[update_robots_intro,GSYM update_robots_def]
      \\ rw[updateInventory_def]
      \\ every_case_tac \\ fs[MAP_MAP_o])
    \\ simp[MAP_FLAT,MAP_GENLIST]
    \\ AP_TERM_TAC
    \\ REWRITE_TAC[LENGTH_neighbours]
    \\ REWRITE_TAC[GENLIST_FUN_EQ]
    \\ simp[]
    \\ simp[neighbours_def,EL_MAP,LENGTH_neighbour_coords]
    \\ simp[FLOOKUP_o_f]
    \\ rw[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[incomingFrom_def]
    \\ simp[MAP_MAP_o,o_DEF,if_focal_def,UNCURRY,update_robots_def]
    \\ simp[FILTER_MAP,o_DEF,UNCURRY,if_focal_def,LAMBDA_PROD]
    \\ simp[MAP_MAP_o,MAP_EQ_f,UNCURRY,FORALL_PROD,if_focal_def]
    \\ rw[] )
  \\ match_mp_tac MAP_FILTER_remove
  \\ reverse conj_tac
  >- (
    simp[EL_MAP,localActions_def,update_robots_def,MAP_MAP_o]
    \\ simp[UNCURRY,o_DEF,if_focal_eta] )
  \\ simp[MAP_MAP_o,localActions_def,UNCURRY,o_DEF,update_robots_def,MAP_EQ_f]
  \\ simp[shatter_def,FORALL_PROD]
  \\ simp[]
  \\ rpt gen_tac \\ strip_tac
  \\ conj_tac >- (EVAL_TAC \\ rw[])
  \\ simp[GSYM update_robots_def]
  \\ qpat_abbrev_tac`a1 = act _ _ _`
  \\ qpat_abbrev_tac`a2 = act _ _ _`
  \\ `a1 = a2`
  by (
    unabbrev_all_tac
    \\ simp[if_focal_def]
    \\ match_mp_tac act_with_memory
    \\ fs[localActions_def,update_robots_def,MAP2_MAP,MAP2_same,MAP_MAP_o,PAIR_MAP_COMPOSE,
          o_DEF,UNCURRY,EVERY_MAP]
    \\ fs[EVERY_MEM,FORALL_PROD]
    \\ metis_tac[])
  \\ simp[updateInventory_def]
  \\ every_case_tac \\ fs[]);

open match_goal

(* TODO: move *)

open terminationTheory

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
  \\ fs[evalPropsTheory.do_app_cases,semanticPrimitivesTheory.do_app_def] \\ rw[]
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
  \\ rpt (qpat_assum`_ ∧ _`strip_assume_tac) \\ rveq
  \\ fs[] \\ rfs[] \\ rveq
  \\ imp_res_tac ffi_rel_same_refs \\ fs[]
  \\ first_x_assum drule \\ fs[]
  \\ rpt( strip_tac \\ rveq)
  \\ spose_not_then strip_assume_tac \\ fs[] \\ rveq
  \\ first_x_assum drule \\ fs[])
  (* App case *)
  \\ every_case_tac
  \\ rpt (qpat_assum`_ ∧ _`strip_assume_tac) \\ rveq
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
        funBigStepTheory.dec_clock_def]
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

val encoded_ffi_def = Define`
  encoded_ffi ffi1 ffi2 ⇔
    encode_observation ffi1.bot_input =
    encode_observation ffi2.bot_input ∧
    encode_output ffi1.bot_output =
    encode_output ffi2.bot_output`;

val evaluate_decs_ffi_extensional = Q.store_thm("evaluate_decs_ffi_extensional",
  `call_FFI_invariant oracle R ⇒
   ∀mn st env decs st' res res' st2 st2'.
   ffi_rel oracle R st st' ∧
   evaluate_decs mn st env decs = (st2,res) ∧
   evaluate_decs mn st' env decs = (st2',res')
   ⇒
   res = res' ∧ ffi_rel oracle R st2 st2'`,
  strip_tac
  \\ ho_match_mp_tac funBigStepTheory.evaluate_decs_ind
  \\ rw[funBigStepTheory.evaluate_decs_def] \\ rw[]
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
  \\ ho_match_mp_tac funBigStepTheory.evaluate_tops_ind
  \\ rw[funBigStepTheory.evaluate_tops_def] \\ rw[]
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
  simp[funBigStepTheory.evaluate_prog_def]
  \\ ntac 2 strip_tac
  \\ imp_res_tac ffi_rel_same_defined_mods
  \\ imp_res_tac ffi_rel_same_defined_types
  \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ metis_tac[evaluate_tops_ffi_extensional]);

(* -- *)

val botworld_call_FFI_invariant = Q.store_thm("botworld_call_FFI_invariant",
  `call_FFI_invariant botworld_oracle encoded_ffi`,
  rw[call_FFI_invariant_def,ffiTheory.call_FFI_def,encoded_ffi_def]
  \\ pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
  \\ fs[ffiTheory.ffi_state_component_equality]
  \\ rfs[]
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[botworld_serialiseTheory.botworld_oracle_def]
  \\ every_case_tac
  \\ fs[botworld_serialiseTheory.botworld_read_def,
        botworld_serialiseTheory.botworld_write_def,
        botworld_serialiseTheory.botworld_get_output_length_def,
        botworld_serialiseTheory.botworld_get_input_length_def,
        botworld_serialiseTheory.botworld_read_output_def]
  \\ every_case_tac \\ fs[] \\ rfs[] \\ rveq \\ fs[]);

val ffi_from_observation_with_memory = Q.store_thm("ffi_from_observation_with_memory",
  `obs1 = FST (prepare x y) ∧ obs2 = FST (prepare x' y) ∧
   x' = x with robotActions updated_by (MAP (if_focal nm (with_memory p ## I)))
   ⇒
   ffi_state_rel botworld_oracle encoded_ffi
    (ffi_from_observation obs1)
    (ffi_from_observation obs2)`,
  rw[ffi_state_rel_def,ffi_from_observation_def,
     ffiTheory.initial_ffi_state_def]
  \\ rw[botworld_serialiseTheory.botworld_initial_state_def]
  \\ simp[encoded_ffi_def]
  \\ simp[botworld_serialiseTheory.encode_observation_def]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ PairCases_on`y` \\ simp[prepare_def]
  \\ simp[botworld_serialiseTheory.observationsexp_def]
  \\ simp[botworld_serialiseTheory.eventsexp_def]
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,if_focal_def]
  \\ rw[]
  \\ simp[botworld_serialiseTheory.robotsexp_def]);

val evaluate_botworld_prog_ffi =
  MATCH_MP evaluate_prog_ffi_extensional botworld_call_FFI_invariant

val preamble_env_ffi = Q.store_thm("preamble_env_ffi",
  `preamble_env (ffi_from_observation obs) = (st,env) ⇒
    st.ffi = (ffi_from_observation obs)`,
  cheat);

val preamble_env_ignores_ffi = Q.store_thm("preamble_env_ignores_ffi",
  `preamble_env ffi1 = (st,env1) ∧
   preamble_env ffi2 = (st',env2)
   ⇒
   st' = st with ffi := st'.ffi ∧ env1 = env2`,
  cheat);

val print_sexp_11 = Q.store_thm("print_sexp_11[simp]",
  `print_sexp x = print_sexp y ⇔ x = y`,
  cheat);

val outputsexp_11 = Q.store_thm("outputsexp_11[simp]",
  `outputsexp x = outputsexp y ⇔ x = y`,
  Cases_on`x` \\ Cases_on`y`
  \\ simp[botworld_serialiseTheory.outputsexp_def]
  \\ cheat);

val encode_output_inj = Q.store_thm("encode_output_inj",
  `encode_output x = encode_output y ⇒ x = y`,
  rw[botworld_serialiseTheory.encode_output_def]
  \\ (holSyntaxLibTheory.MAP_EQ_MAP_IMP
      |> ONCE_REWRITE_RULE[IMP_ANTISYM_RULE SWAP_IMP (Q.SPECL[`P`,`Q`](Q.GENL[`P`,`Q`]SWAP_IMP))]
      |> drule)
  \\ impl_tac
  >- ( simp[] \\ metis_tac[ORD_11,LESS_MOD,ORD_BOUND] )
  \\ simp[]);

val run_policy_ffi_with_memory = Q.store_thm("run_policy_ffi_with_memory",
  `x' = x with robotActions updated_by (MAP (if_focal nm' (with_memory p' ## I))) ⇒
   run_policy p ck (nm,x',private a) = run_policy p ck (nm,x,private a)`,
  fs[run_policy_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac preamble_env_ffi
  \\ match_tac([mg.a"1"`_`,mg.a"2"`_`],fn(a,t)=>
       preamble_env_ignores_ffi
       |> REWRITE_RULE[GSYM AND_IMP_INTRO]
       |> GEN_ALL
       |> INST_TYPE[beta|->``:botworld_ffi_state``]
       |> drule_thm(a"1")
       \\ disch_then(drule_thm(a"2")))
  \\ rw[] \\ fs[]
  \\ match_tac([mg.a"1"`_`,mg.a"2"`_`],fn(a,t)=>
       evaluate_botworld_prog_ffi
       |> ONCE_REWRITE_RULE[CONJ_COMM]
       |> REWRITE_RULE[GSYM AND_IMP_INTRO]
       |> GEN_ALL
       |> drule_thm (a"1")
       \\ disch_then (drule_thm(a"2")))
  \\ simp[ffi_rel_def]
  \\ impl_tac
  >- (
    match_mp_tac (GEN_ALL ffi_from_observation_with_memory)
    \\ simp[prepare_def,EXISTS_PROD]
    \\ metis_tac[])
  \\ simp[ffi_state_rel_def]
  \\ rw[encoded_ffi_def]
  \\ imp_res_tac encode_output_inj \\ fs[]);

val runMachine_ffi_with_memory = Q.store_thm("runMachine_ffi_with_memory",
  `x' = x with robotActions updated_by (MAP (if_focal nm (with_memory p ## I))) ⇒
   runMachine (prepare x' y) = runMachine (prepare x y)`,
  strip_tac \\ imp_res_tac run_policy_ffi_with_memory
  \\ PairCases_on`y` >> rw[runMachine_def,prepare_def]);

val updateInventory_const = Q.store_thm("updateInventory_const[simp]",
  `(SND(updateInventory sq nm ra)).memory = (FST ra).memory ∧
   (SND(updateInventory sq nm ra)).frame = (FST ra).frame ∧
   (SND(updateInventory sq nm ra)).command = (FST ra).command ∧
   (SND(updateInventory sq nm ra)).processor = (FST ra).processor`,
  Cases_on`ra`\\rw[updateInventory_def] >>
  BasicProvers.CASE_TAC >> rw[])

val computeEvents_only_inventory = Q.store_thm("computeEvents_only_inventory",
  `wf_state s ∧
   sq ∈ FRANGE s.grid ∧
   MEM (nm,r) sq.robots ∧
   ev ∈ FRANGE (computeEvents s.grid) ∧
   MEM (nm,r',a) ev.robotActions
   ⇒
   ∃i. r' = r with inventory := i`,
  rw[IN_FRANGE_FLOOKUP,computeEvents_def,FLOOKUP_FMAP_MAP2,event_def] \\ fs[]
  \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,o_DEF,UNCURRY,MEM_MAP,MEM_FLAT,MEM_GENLIST,EXISTS_PROD]
  \\ rw[] \\ fs[]
  >- (
    fs[localActions_def,MEM_MAP,EXISTS_PROD]
    \\ drule same_name_same_square
    \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS,PULL_FORALL]
    \\ simp[GSYM AND_IMP_INTRO]
    \\ match_tac ([mg.ab"h1"`FLOOKUP`,mg.ab"h2"`FLOOKUP`],
         fn(a,t)=>disch_then(drule_thm(a"h1"))
                \\disch_then(drule_thm(a"h2")))
    \\ simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD,PULL_FORALL]
    \\ rpt(disch_then drule)
    \\ rw[] \\ fs[]
    \\ match_tac ([mg.ab"1"`(nm,r1_)`,mg.ab"2"`(nm,r2_)`], fn(a,t)=>
       `^(t"r1") = ^(t"r2")` by (
         metis_tac[wf_state_def,ALL_DISTINCT_MAP_FST,IN_FRANGE_FLOOKUP]))
    \\ rveq \\ fs[robot_component_equality] )
  \\ match1_tac(mg.aub`incomingFrom _ x_`,fn(a,t)=>Cases_on`^(t"x")`)
  \\ fs[incomingFrom_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ rfs[neighbours_def,EL_MAP]
  \\ drule same_name_same_square
  \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS,PULL_FORALL]
  \\ simp[GSYM AND_IMP_INTRO]
  \\ rveq
  \\ match_tac ([mg.ab"h1"`FLOOKUP`,mg.ab"h2"`FLOOKUP`],
       fn(a,t)=>disch_then(drule_thm(a"h1"))
              \\disch_then(drule_thm(a"h2"))
              \\ simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD,PULL_FORALL]
              \\ rpt(disch_then drule)
              \\ strip_tac \\ (CHANGED_TAC rveq))
  \\ match_tac ([mg.ab"1"`(nm,r1_)`,mg.ab"2"`(nm,r2_)`], fn(a,t)=>
     `^(t"r1") = ^(t"r2")` by (
       metis_tac[wf_state_def,ALL_DISTINCT_MAP_FST,IN_FRANGE_FLOOKUP]))
  \\ rveq
  \\ simp[robot_component_equality]);

val wf_state_with_hole_wf_state = Q.store_thm("wf_state_with_hole_wf_state",
  `wf_state_with_hole s ⇒ wf_state s.state`,
  rw[wf_state_with_hole_def])

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ∧
   run_policy p (get_focal_robot s).processor obs = (c',p')
   ⇒
   step (fill (with_policy c p) s) = fill (with_policy c' p') s'`,
  rw[]
  \\ imp_res_tac steph_focal_clock
  \\ pop_assum (assume_tac o SYM)
  \\ fs[steph_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac (wf_state_with_hole_def |> SPEC_ALL |> EQ_IMP_RULE |> #1)
  \\ `wf_state (fill (with_command c) s)` by metis_tac[wf_state_fill]
  \\ drule (GEN_ALL focal_event_sing)
  \\ simp[FRANGE_fill,PULL_EXISTS]
  \\ disch_then drule
  \\ simp[MAP_MAP_o]
  \\ disch_then drule
  \\ disch_then(qx_choose_then`ceva`strip_assume_tac)
  \\ fs[] \\ rveq
  \\ fs[EXTENSION]
  \\ first_x_assum(qspec_then`(c'',ev,a)`mp_tac)
  \\ simp[] \\ strip_tac
  \\ simp[Once fill_with_policy_split]
  \\ qmatch_assum_abbrev_tac`FEVERY _ events`
  \\ qmatch_assum_abbrev_tac`Abbrev(_ = _ s'.grid)`
  \\ simp[state_component_equality]
  \\ simp[step_def]
  \\ simp[fill_def]
  \\ simp[update_robots_intro]
  \\ drule (GEN_ALL computeEvents_update_robots_with_memory)
  \\ disch_then(qspecl_then[`p`,`s.focal_name`]mp_tac)
  \\ impl_tac
  >- (
    fs[FEVERY_ALL_FLOOKUP,EVERY_MEM]
    \\ metis_tac[] )
  \\ disch_then SUBST1_TAC
  \\ simp[FMAP_MAP2_o_f]
  \\ simp[o_f_FMAP_MAP2]
  \\ simp[fmap_eq_flookup]
  \\ simp[FLOOKUP_FMAP_MAP2]
  \\ gen_tac
  \\ Cases_on`FLOOKUP events k` \\ simp[]
  \\ simp[update_robots_def]
  \\ simp[event_update_robots_def,computeSquare_def]
  \\ simp[MAP_MAP_o]
  \\ simp[MEM_MAP]
  \\ match_mp_tac APPEND_EQ_suff
  \\ conj_tac
  >- (
    simp[FILTER_MAP,o_DEF,MAP_MAP_o]
    \\ simp[UNCURRY]
    \\ simp[LAMBDA_PROD]
    \\ simp[MAP_EQ_f,FORALL_PROD]
    \\ simp[MEM_FILTER]
    \\ qx_genl_tac[`nm`,`rr`,`aa`]
    \\ strip_tac
    \\ simp[if_focal_def,if_focal_eta,UNCURRY]
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      qmatch_goalsub_abbrev_tac`prepare x'`
      \\ ONCE_REWRITE_TAC[GSYM PAIR]
      \\ simp[] \\ AP_TERM_TAC
      \\ match_mp_tac (GEN_ALL runMachine_ffi_with_memory)
      \\ simp[Abbr`x'`,event_component_equality,MAP_EQ_f,FORALL_PROD,if_focal_def]
      \\ metis_tac[] )
    \\ simp[prepare_def,runMachine_def,UNCURRY,robot_component_equality]
    \\ drule (GEN_ALL same_name_same_action) \\ simp[]
    \\ disch_then drule
    \\ qpat_assum `_ = SOME ev` assume_tac
    \\ disch_then drule
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[EXTENSION]
    \\ reverse strip_tac
    >- (
      first_x_assum(qspec_then`MovedOut (opposite dir)`mp_tac)
      \\ simp[] \\ rw[] \\ fs[] )
    \\ rveq \\ fs[]
    \\ `r.processor = (get_focal_robot s).processor`
    by (
      drule (GEN_ALL computeEvents_only_inventory)
      \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
      \\ simp[Abbr`s'`,fill_def,FLOOKUP_o_f]
      \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(
           move_conj_left(can(match_term``FLOOKUP events _ = _``))))))
      \\ disch_then drule
      \\ disch_then(qspec_then`k`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev))
      \\ fs[MEM_MAP,PULL_EXISTS]
      \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(
           move_conj_left(listSyntax.is_mem)))))
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(
           move_conj_left(listSyntax.is_mem)))))
      \\ disch_then drule
      \\ rw[if_focal_eta,UNCURRY]
      \\ drule (GEN_ALL get_focal_robot_unique)
      \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS]
      \\ disch_then drule
      \\ metis_tac[PAIR] )
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`(_,x',_)`
    \\ `run_policy p r.processor (s.focal_name,x',private a) =
        run_policy p r.processor (s.focal_name,x,private a)`
    by (
      match_mp_tac (GEN_ALL run_policy_ffi_with_memory)
      \\ simp[Abbr`x'`,event_component_equality,MAP_EQ_f,FORALL_PROD,if_focal_def]
      \\ metis_tac[])
    \\ rfs[])
  \\ simp[MAP_GENLIST]
  \\ simp[GENLIST_FUN_EQ]
  \\ simp[if_focal_eta,UNCURRY]
  \\ rpt strip_tac
  \\ IF_CASES_TAC
  >- (
    fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ match1_tac(mg.ab"h"`_.time_step`,fn (a,t) => drule(a"h"))
    \\ disch_then drule
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ simp[Abbr`s'`])
  \\ simp[prepare_def]
  \\ simp[runMachine_def,UNCURRY,robot_component_equality]
  \\ qmatch_goalsub_abbrev_tac`(_,x'',_)`
  \\ qmatch_goalsub_abbrev_tac`(nm,x'',_)`
  \\ match1_tac(mg.bc`p_:'a # 'b`,fn (a,t) => Cases_on`^(t"p")`) \\ fs[]
  \\ match1_tac(mg.bc`p_:'a # 'b`,fn (a,t) => Cases_on`^(t"p")`) \\ fs[]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ REWRITE_TAC[GSYM PAIR_EQ]
  \\ pop_assum (SUBST_ALL_TAC o SYM)
  \\ pop_assum (SUBST_ALL_TAC o SYM)
  \\ match_mp_tac (GEN_ALL run_policy_ffi_with_memory)
  \\ unabbrev_all_tac \\ simp[event_component_equality]
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,if_focal_def]
  \\ metis_tac[]);

(*
val LENGTH_localActions = Q.store_thm("LENGTH_localActions[simp]",
  `LENGTH (localActions sq nb) = LENGTH sq.robots`,
  EVAL_TAC >> simp[])

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

val updateInventory_map_inspected = Q.store_thm("updateInventory_map_inspected[simp]",
  `updateInventory sq i (map_inspected f a) = updateInventory sq i a`,
  Cases_on`a`>>simp[updateInventory_def]);

val Destroyed_eq_map_inspected = Q.store_thm("Destroyed_eq_map_inspected[simp]",
  `Destroyed x = map_inspected f a ⇔ Destroyed x = a`,
  Cases_on`a`>>simp[]);

val if_name_def = Define`
  if_name n f r = if r.name = n then f r else r`;

val if_name_with_memory_const = Q.store_thm("if_name_with_memory_const[simp]",
  `(if_name n (with_memory p) r).command = r.command ∧
   (if_name n (with_memory p) r).inventory = r.inventory ∧
   (if_name n (with_memory p) r).frame = r.frame ∧
   (if_name n (with_memory p) r).name = r.name ∧
   (if_name n (with_memory p) r).processor = r.processor`,
  EVAL_TAC \\ rw[]);

val canLift_with_memory = Q.store_thm("canLift_with_memory[simp]",
  `canLift (if_name n (with_memory p) r) = canLift r`,
  rw[FUN_EQ_THM,canLift_def]);

val contested_with_memory = Q.store_thm("contested_with_memory[simp]",
  `contested (sq with robots updated_by MAP (if_name n (with_memory p))) = contested sq`,
  rw[FUN_EQ_THM,contested_def,FILTER_MAP,o_DEF]);

val findRobotInSquare_with_memory = Q.store_thm("findRobotInSquare_with_memory[simp]",
  `findRobotInSquare i (MAP (if_name n (with_memory p)) sq.robots) =
   OPTION_MAP (if_name n (with_memory p)) (findRobotInSquare i sq.robots)`,
  rw[findRobotInSquare_def,FILTER_MAP,o_DEF]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.CASE_TAC \\ fs[]);

val inspectShielded_with_memory = Q.store_thm("inspectShielded_with_memory[simp]",
  `inspectShielded (MAP (if_name n (with_memory p)) sq.robots) =
   inspectShielded sq.robots`,
  rw[FUN_EQ_THM,inspectShielded_def,MAP_MAP_o,o_DEF]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw[FUN_EQ_THM])

val inspectShielded_with_memory2 = Q.store_thm("inspectShielded_with_memory2[simp]",
  `inspectShielded rs (if_name n (with_memory p) r) =
   inspectShielded rs r`,
  rw[inspectShielded_def])

val destroyShielded_with_memory = Q.store_thm("destroyShielded_with_memory[simp]",
  `destroyShielded (MAP (if_name n (with_memory p)) sq.robots) =
   destroyShielded sq.robots`,
  rw[FUN_EQ_THM,destroyShielded_def,MAP_MAP_o,o_DEF]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw[FUN_EQ_THM])

val destroyShielded_with_memory2 = Q.store_thm("destroyShielded_with_memory2[simp]",
  `destroyShielded rs (if_name n (with_memory p) r) =
   destroyShielded rs r`,
  rw[destroyShielded_def])

val FLOOKUP_fill =
  ``FLOOKUP (fill f s) x``
  |> SIMP_CONV(srw_ss()++ETA_ss)[FLOOKUP_FMAP_MAP2,fill_def,mapRobots_def,GSYM if_name_def]

val neighbours_fill = Q.store_thm("neighbours_fill",
  `neighbours (fill f s) k =
   MAP (OPTION_MAP (mapRobotsInSquare (if_name s.focal_name f))) (neighbours s.state k)`,
  rw[neighbours_def,MAP_MAP_o,MAP_EQ_f,FLOOKUP_fill]
  \\ Cases_on`FLOOKUP s.state e` \\ fs[])

val localActions_with_memory = Q.store_thm("localActions_with_memory",
  `localActions (mapRobotsInSquare (if_name n (with_memory p)) sq) nb =
   MAP (map_inspected (if_name n (with_memory p))) (localActions sq nb)`,
  rw[localActions_def,MAP_MAP_o,mapRobotsInSquare_def,MAP_EQ_f]
  \\ rw[act_def]
  \\ BasicProvers.CASE_TAC \\ fs[]
  \\ rw[] \\ fs[]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.CASE_TAC \\ fs[]
  \\ rw[]);

val fled_with_memory = Q.store_thm("fled_with_memory[simp]",
  `fled (MAP (OPTION_MAP (mapRobotsInSquare (if_name n (with_memory p)))) nb) =
   fled nb`,
  simp[FUN_EQ_THM]
  \\ Cases \\ rw[fled_def,EQ_IMP_THM]
  \\ rfs[EL_MAP,IS_SOME_EXISTS]);

val localActions_with_memory2 = Q.store_thm("localActions_with_memory2[simp]",
  `localActions sq (MAP (OPTION_MAP (mapRobotsInSquare (if_name n (with_memory p)))) nb) =
   localActions sq nb`,
  rw[localActions_def,MAP_MAP_o,mapRobotsInSquare_def,MAP_EQ_f]
  \\ rw[act_def]
  \\ BasicProvers.CASE_TAC \\ fs[]
  \\ simp[EL_MAP]
  \\ rw[] \\ fs[] \\ rfs[]);

val MAP_robot_command_with_memory = Q.store_thm("MAP_robot_command_with_memory[simp]",
  `MAP robot_command (mapRobotsInSquare (if_name n (with_memory p)) sq).robots =
   MAP robot_command sq.robots`,
  rw[mapRobotsInSquare_def,MAP_MAP_o,MAP_EQ_f]);

val updateInventory_with_memory = Q.store_thm("updateInventory_with_memory[simp]",
  `updateInventory (mapRobotsInSquare (if_name n (with_memory p)) sq) =
   updateInventory sq`,
  rw[updateInventory_def,FUN_EQ_THM]
  \\ BasicProvers.CASE_TAC \\ fs[]
  \\ rw[robot_component_equality]
  \\ rw[mapRobotsInSquare_def]);

val updateInventory_with_memory2 = Q.store_thm("updateInventory_with_memory2[simp]",
  `updateInventory sq (if_name n (with_memory p) x) a =
   if_name n (with_memory p) (updateInventory sq x a)`,
  rw[FUN_EQ_THM,updateInventory_def]
  \\ BasicProvers.CASE_TAC \\ fs[]
  \\ rw[robot_component_equality]
  \\ rw[if_name_def]);

val incomingFrom_with_memory = Q.store_thm("incomingFrom_with_memory[simp]",
  `incomingFrom x (OPTION_MAP (mapRobotsInSquare (if_name n (with_memory p))) sq) =
   MAP (if_name n (with_memory p) ## I) (incomingFrom x sq)`,
  Cases_on`sq`\\rw[incomingFrom_def]
  \\ rw[mapRobotsInSquare_def,MAP_MAP_o,o_DEF]
  \\ rw[MAP_FLAT,MAP_MAP_o,o_DEF]
  \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f]
  \\ rw[])

val LENGTH_mapRobotsInSquare = Q.store_thm("LENGTH_mapRobotsInSquare[simp]",
  `LENGTH (mapRobotsInSquare f sq).robots = LENGTH sq.robots`,
  rw[mapRobotsInSquare_def]);

val MEM_Built_localActions_name = Q.store_thm("MEM_Built_localActions_name",
  `MEM (Built x r) (localActions sq nb) ⇒ r.name = 0`,
  simp[localActions_def,MEM_MAP,act_def,PULL_EXISTS]
  \\ gen_tac
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[construct_def]
  \\ every_case_tac \\ fs[] \\ rw[]);

val computeEvents_fill_with_memory = Q.store_thm("computeEvents_fill_with_memory",
  `s.focal_name ≠ 0 ⇒
   computeEvents (fill (with_memory p) s) =
   (λev. ev with robotActions updated_by
     MAP (              (if_name s.focal_name (with_memory p)) ##
          map_inspected (if_name s.focal_name (with_memory p))))
     o_f (computeEvents s.state)`,
  rw[fmap_eq_flookup,computeEvents_def,FLOOKUP_FMAP_MAP2,FLOOKUP_o_f,FLOOKUP_fill]
  \\ Cases_on`FLOOKUP s.state k` \\ fs[neighbours_fill]
  \\ qpat_abbrev_tac`nb = neighbours _ _`
  \\ rw[event_def,localActions_with_memory]
  >- (
    qmatch_goalsub_abbrev_tac`FLAT (MAP f _)`
    \\ rw[MAP_MAP_o]
    \\ qmatch_goalsub_abbrev_tac`f o g`
    \\ `f o g = f`
    by (
      simp[FUN_EQ_THM,Abbr`f`,Abbr`g`]
      \\ Cases \\ simp[] )
    \\ fs[]
    \\ match_mp_tac APPEND_EQ_suff
    \\ simp[LENGTH_ZIP]
    \\ conj_tac
    >- (
      simp[LENGTH_FLAT]
      \\ AP_TERM_TAC
      \\ simp[MAP_GENLIST,o_DEF]
      \\ simp[Once LIST_EQ_REWRITE,EL_MAP] )
    \\ conj_tac
    >- (
      match_mp_tac APPEND_EQ_suff
      \\ simp[]
      \\ conj_tac
      >- (
        simp[ZIP_MAP,UNCURRY,LAMBDA_PROD,MAP_MAP_o,o_DEF]
        \\ simp[mapRobotsInSquare_def]
        \\ simp[ZIP_MAP,MAP_MAP_o,o_DEF]
        \\ simp[MAP_EQ_f,FORALL_PROD,Abbr`g`] )
      \\ simp[MAP_FLAT,MAP_GENLIST]
      \\ AP_TERM_TAC
      \\ simp[o_DEF]
      \\ simp[Once LIST_EQ_REWRITE]
      \\ simp[EL_MAP]
      \\ simp[MAP_EQ_f,FORALL_PROD]
      \\ rw[]
      \\ imp_res_tac incomingFrom_MovedIn
      \\ fs[Abbr`g`] )
    \\ simp[MAP_EQ_ID,REPLICATE_GENLIST,FORALL_PROD,MEM_ZIP,PULL_EXISTS,Abbr`g`]
    \\ simp[GSYM(SIMP_RULE(srw_ss())[MEM_EL,PULL_EXISTS]MAP_EQ_ID)]
    \\ simp[MAP_FLAT,MAP_MAP_o,o_DEF]
    \\ AP_TERM_TAC
    \\ srw_tac[ETA_ss][]
    \\ simp[MAP_EQ_f]
    \\ Cases \\ simp[Abbr`f`]
    \\ rw[if_name_def]
    \\ imp_res_tac MEM_Built_localActions_name
    \\ fs[])
  >- (
    simp[Once mapRobotsInSquare_def]
    \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
    \\ simp[FUN_EQ_THM]
    \\ rw[EXISTS_MAP]
    \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
    \\ simp[FUN_EQ_THM]
    \\ Cases \\ simp[] )
  >- (
    AP_TERM_TAC
    \\ simp[Once LIST_EQ_REWRITE]
    \\ simp[EL_MAP,EL_ZIP]
    \\ rw[]
    \\ match_mp_tac EQ_SYM
    \\ BasicProvers.CASE_TAC \\ fs[]
    \\ simp[mapRobotsInSquare_def,EL_MAP] )
  >- (
    AP_TERM_TAC
    \\ simp[MEM_MAP]
    \\ simp[MAP_MAP_o]
    \\ simp[Once LIST_EQ_REWRITE]
    \\ simp[EL_MAP,EL_ZIP]
    \\ simp[mapRobotsInSquare_def,EL_MAP]
    \\ rw[]
    \\ rw[shatter_def]))

val neighbour_coords_imp_opposite = Q.store_thm("neighbour_coords_imp_opposite",
  `d1 < 8 ∧ d2 < 8 ∧
   EL d1 (neighbour_coords (EL d2 (neighbour_coords c))) = c ⇒
   d1 = opposite d2`,
  Cases_on`EL d2 (neighbour_coords c)` >>
  Cases_on`c`>>
  fs[neighbour_coords_def]
  \\ rw[less8,opposite_def]
  \\ fs[] \\ rveq
  \\ simp[]
  \\ intLib.COOPER_TAC);

val immigration_sources = Q.store_thm("immigration_sources",
  `immigrations = FLAT (GENLIST (λi. incomingFrom (f i) (EL i nb)) (LENGTH nb)) ⇒
   ∃sources.
     ALL_DISTINCT sources ∧
     LENGTH sources = LENGTH immigrations ∧
     ∀k. k < LENGTH sources ⇒
       ∃i j sq.
         EL k sources = (i,j) ∧
         i < LENGTH nb ∧
         EL i nb = SOME sq ∧
         j < LENGTH sq.robots ∧
         (EL j sq.robots).command = Move (opposite (f i)) ∧
         EL k immigrations = (EL j sq.robots,MovedIn (f i))`,
  strip_tac
  \\ rveq
  \\ qid_spec_tac`f`
  \\ Induct_on`nb`
  \\ simp[]
  >- ( simp[LENGTH_NIL] )
  \\ Cases
  \\ simp[] \\ fs[]
  >- (
    simp[GENLIST_CONS]
    \\ simp[incomingFrom_def]
    \\ simp[o_DEF]
    \\ gen_tac
    \\ first_x_assum(qspec_then`f o SUC`strip_assume_tac)
    \\ qexists_tac`MAP (λ(i,j). (SUC i,j)) sources`
    \\ simp[] \\ rfs[]
    \\ conj_tac
    >- (
      match_mp_tac ALL_DISTINCT_MAP_INJ
      \\ simp[UNCURRY]
      \\ Cases \\ simp[] )
    \\ gen_tac \\ strip_tac
    \\ first_x_assum drule
    \\ strip_tac
    \\ simp[EL_MAP] )
  \\ gen_tac
  \\ simp[GENLIST_CONS]
  \\ simp[incomingFrom_def]
  \\ qpat_abbrev_tac`here = FLAT(MAP _ _)`
  \\ simp[o_DEF]
  \\ first_x_assum(qspec_then`f o SUC`strip_assume_tac)
  \\ rfs[]
  \\ `∃hs.
        ALL_DISTINCT hs ∧
        LENGTH hs = LENGTH here ∧
        ∀k. k < LENGTH hs ⇒
          ∃j sq.
            EL k hs = j ∧
            sq = x ∧
            j < LENGTH sq.robots ∧
            (EL j sq.robots).command = Move (opposite (f 0)) ∧
            EL k here = (EL j sq.robots,MovedIn (f 0))`
  by (
    simp[]
    \\ ntac 3 (pop_assum kall_tac)
    \\ simp[Abbr`here`]
    \\ qspec_tac(`x.robots`,`ls`)
    \\ Induct >> simp[LENGTH_NIL]
    \\ qx_gen_tac`r`
    \\ fs[]
    \\ reverse IF_CASES_TAC \\ fs[]
    >- (
      qexists_tac`MAP SUC hs`
      \\ simp[]
      \\ conj_tac
      >- (
        match_mp_tac ALL_DISTINCT_MAP_INJ
        \\ simp[] )
      \\ rfs[]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum drule
      \\ strip_tac
      \\ simp[EL_MAP] )
    \\ qexists_tac`0::(MAP SUC hs)`
    \\ simp[]
    \\ conj_tac
    >- (
      simp[MEM_MAP]
      \\ match_mp_tac ALL_DISTINCT_MAP_INJ
      \\ simp[] )
    \\ Cases \\ simp[]
    \\ strip_tac \\ rfs[]
    \\ first_x_assum drule
    \\ strip_tac
    \\ simp[EL_MAP] )
  \\ qexists_tac`MAP (λj. (0,j)) hs ++ MAP (λ(i,j). (SUC i,j)) sources`
  \\ simp[]
  \\ conj_tac
  >- (
    simp[ALL_DISTINCT_APPEND]
    \\ conj_tac
    >- (
      match_mp_tac ALL_DISTINCT_MAP_INJ
      \\ simp[] )
    \\ conj_tac
    >- (
      match_mp_tac ALL_DISTINCT_MAP_INJ
      \\ simp[UNCURRY]
      \\ Cases \\ simp[])
    \\ simp[MEM_MAP,PULL_EXISTS,UNCURRY] )
  \\ gen_tac
  \\ strip_tac
  \\ Cases_on`k < LENGTH hs`
  \\ simp[EL_APPEND1,EL_APPEND2]
  >- (
    first_x_assum drule
    \\ strip_tac
    \\ simp[EL_MAP]
    \\ rveq \\ simp[] )
  \\ qmatch_assum_abbrev_tac`k < LENGTH here + z`
  \\ `k - LENGTH here < z` by decide_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ simp[EL_MAP]);

val computeEvents_FEMPTY = Q.store_thm("computeEvents_FEMPTY[simp]",
  `computeEvents FEMPTY = FEMPTY`,
  rw[computeEvents_def,fmap_eq_flookup,FLOOKUP_FMAP_MAP2]);

val step_FEMPTY = Q.store_thm("step_FEMPTY[simp]",
  `step FEMPTY = FEMPTY`,
  rw[step_def,mkNames_def,allNames_def,ITSET_EMPTY]);

val allCoords_FEMPTY = Q.store_thm("allCoords_FEMPTY[simp]",
  `allCoords FEMPTY = []`, rw[allCoords_def,QSORT_DEF]);

val allNames_FEMPTY = Q.store_thm("allNames_FEMPTY[simp]",
  `allNames FEMPTY = []`, rw[allNames_def]);

val eventOldRobotNames_def = Define`
  eventOldRobotNames =
    MAP (robot_name o FST) o
    FILTER ((λa. ¬isMovedIn a ∧ a ≠ Created) o SND) o
    event_robotActions`

val eventNewRobotNames_def = Define`
  eventNewRobotNames ev =
    MAP (robot_name o FST)
      (FILTER (λ(r,a). ¬isMovedOut a ∧
                       ¬MEM (Destroyed r.name) (MAP SND ev.robotActions))
              ev.robotActions)`;

val eventMovedRobotNames_def = Define`
  eventMovedRobotNames ev =
    MAP (robot_name o FST)
      (FILTER (λ(r,a). ¬isMovedOut a ∧
                       ¬MEM (Destroyed r.name) (MAP SND ev.robotActions) ∧
                       a ≠ Created)
              ev.robotActions)`;

val eventAllNames_def = Define`
  eventAllNames f = FLAT (MAP (eventOldRobotNames o $' f) (allCoords f))`;

val eventAllNewNames_def = Define`
  eventAllNewNames f = FLAT (MAP (eventNewRobotNames o $' f) (allCoords f))`;

val updateInventory_name = Q.store_thm("updateInventory_name[simp]",
  `(updateInventory sq r a).name = r.name`,
  rw[updateInventory_def]
  \\ CASE_TAC \\ fs[]);

val FILTER_0_eventMovedRobotNames = Q.store_thm("FILTER_0_eventMovedRobotNames",
  `EVERY ($<> 0) (robotNames sq) ∧ EVERY (OPTION_EVERY (EVERY ($<> 0) o robotNames)) nb ⇒
   FILTER ($<> 0) (eventNewRobotNames (event sq nb)) = eventMovedRobotNames (event sq nb)`,
  rw[eventMovedRobotNames_def,eventNewRobotNames_def,event_def]
  \\ qmatch_goalsub_abbrev_tac`FLAT (MAP f (localActions _ _))`
  \\ qmatch_goalsub_abbrev_tac`FILTER P (veterans ++ immigrations ++ children)`
  \\ simp[FILTER_MAP,FILTER_FILTER]
  \\ qmatch_goalsub_abbrev_tac`FILTER P1 _`
  \\ qmatch_goalsub_abbrev_tac`_ = MAP _ (FILTER P2 _)`
  \\ AP_TERM_TAC
  \\ simp[FILTER_APPEND]
  \\ match_mp_tac APPEND_EQ_suff
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ `FILTER P1 veterans = FILTER P2 veterans`
  by (
    simp[FILTER_EQ]
    \\ simp[Abbr`P1`,Abbr`P2`,Abbr`P`]
    \\ simp[FORALL_PROD]
    \\ rpt gen_tac \\ strip_tac
    \\ EQ_TAC \\ fs[] \\ strip_tac
    \\ qpat_assum`MEM _ _`mp_tac
    \\ simp[Abbr`veterans`,MEM_ZIP]
    \\ strip_tac \\ rveq
    \\ simp[localActions_def,EL_MAP,EL_ZIP]
    \\ simp[act_def]
    >- ( rpt(CASE_TAC \\ simp[]) )
    \\ fs[EVERY_MEM,MEM_EL,robotNames_def]
    \\ metis_tac[EL_MAP])
  \\ fs[]
  \\ reverse conj_asm1_tac \\ fs[]
  \\ fs[Abbr`P`]
  \\ conj_tac
  >- (
    simp[FILTER_EQ]
    \\ simp[Abbr`P1`,Abbr`P2`,FORALL_PROD]
    \\ rpt gen_tac \\ strip_tac
    \\ EQ_TAC \\ fs[] \\ strip_tac
    \\ qpat_assum`MEM _ _`mp_tac
    \\ simp[Abbr`immigrations`,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
    \\ rw[]
    \\ imp_res_tac incomingFrom_MovedIn
    \\ fs[]
    \\ Cases_on`EL i nb` \\ fs[incomingFrom_def]
    \\ fs[MEM_FLAT,MEM_MAP,EVERY_MEM]
    \\ rw[]
    \\ qpat_assum`MEM _ _`mp_tac
    \\ rw[]
    \\ fs[MEM_EL,PULL_EXISTS]
    \\ first_x_assum drule
    \\ simp[EVERY_MEM,MEM_EL,robotNames_def]
    \\ metis_tac[EL_MAP] )
  \\ simp[FILTER_EQ]
  \\ simp[Abbr`children`,REPLICATE_GENLIST,localActions_def]
  \\ rw[]
  \\ imp_res_tac MEM_ZIP_MEM_MAP \\ fs[]
  \\ fs[MEM_GENLIST,MEM_FLAT,MEM_MAP] \\ rw[]
  \\ qpat_assum`MEM _ _`mp_tac
  \\ simp[act_def]
  \\ simp[Abbr`f`]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ rator_x_assum`construct`mp_tac
  \\ simp[construct_def]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ rw[]
  \\ Cases_on`x` \\ fs[]
  \\ rw[Abbr`P1`,Abbr`P2`]);

val allCoords_computeEvents = Q.store_thm("allCoords_computeEvents[simp]",
  `allCoords (computeEvents g) = allCoords g`,
  rw[allCoords_def,computeEvents_def,FMAP_MAP2_THM]);

val robot_name_o_UNCURRY_updateInventory = Q.store_thm("robot_name_o_UNCURRY_updateInventory",
  `robot_name o UNCURRY (updateInventory sq) = robot_name o FST`,
  rw[FUN_EQ_THM,UNCURRY,updateInventory_def]
  \\ CASE_TAC \\ rw[]);

val computeEvents_names = Q.store_thm("computeEvents_names",
  `(eventAllNames (computeEvents g)) = allNames g`,
  rw[allNames_def,eventAllNames_def]
  \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f]
  \\ qx_gen_tac`c`
  \\ strip_tac
  \\ `c ∈ FDOM g` by ( fs[allCoords_def,QSORT_MEM] )
  \\ simp[eventOldRobotNames_def,robotNames_def]
  \\ rw[computeEvents_def]
  \\ qpat_abbrev_tac`sq = g ' c`
  \\ simp[FMAP_MAP2_THM]
  \\ rw[event_def]
  \\ qmatch_goalsub_abbrev_tac`FLAT (MAP f (localActions _ _))`
  \\ qmatch_goalsub_abbrev_tac`FILTER P (veterans ++ immigrations ++ children)`
  \\ `FILTER P (veterans ++ immigrations ++ children) = veterans`
  by (
    simp[FILTER_APPEND]
    \\ `FILTER P children = []`
    by (
      simp[FILTER_EQ_NIL,Abbr`children`,Abbr`P`]
      \\ qho_match_abbrev_tac`EVERY (λx. P (SND x)) _`
      \\ simp[every_zip_snd,LENGTH_REPLICATE,EVERY_REPLICATE]
      \\ simp[Abbr`P`] )
    \\ `FILTER P immigrations = []`
    by (
      simp[FILTER_EQ_NIL,Abbr`immigrations`,Abbr`P`]
      \\ simp[EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_GENLIST]
      \\ rw[]
      \\ imp_res_tac incomingFrom_MovedIn
      \\ simp[] )
    \\ simp[FILTER_EQ_ID]
    \\ simp[Abbr`P`,Abbr`veterans`]
    \\ simp[o_DEF]
    \\ qho_match_abbrev_tac`EVERY (λx. P (SND x)) _`
    \\ simp[every_zip_snd]
    \\ simp[localActions_def,EVERY_MAP]
    \\ simp[EVERY_MEM]
    \\ simp[act_def]
    \\ rw[]
    \\ BasicProvers.CASE_TAC \\ simp[Abbr`P`]
    \\ rw[]
    \\ BasicProvers.CASE_TAC \\ rw[] )
  \\ rw[GSYM MAP_MAP_o]
  \\ simp[Abbr`veterans`,MAP_ZIP]
  \\ simp[MAP_MAP_o,robot_name_o_UNCURRY_updateInventory]
  \\ simp[MAP_ZIP]);

val MEM_allNames_robotNames = Q.store_thm("MEM_allNames_robotNames",
  `x ∈ FDOM g ⇒ set (robotNames (g ' x)) ⊆  set (allNames g)`,
  rw[SUBSET_DEF,allNames_def,robotNames_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ rw[allCoords_def,QSORT_MEM]
  \\ metis_tac[]);

val MEM_allNames_neighbours = Q.store_thm("MEM_allNames_neighbours",
  `x ∈ FDOM g ∧ MEM (SOME sq) (neighbours g x) ⇒
   set (robotNames sq) ⊆ set (allNames g)`,
  rw[SUBSET_DEF,allNames_def,robotNames_def,neighbours_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ rw[allCoords_def,QSORT_MEM]
  \\ fs[FLOOKUP_DEF]
  \\ metis_tac[]);

val eventJustMovedNames_def = Define`
  eventJustMovedNames = MAP (robot_name o FST) o (FILTER (isMovedIn o SND)) o event_robotActions`;

val eventJustLeftNames_def = Define`
  eventJustLeftNames = MAP (robot_name o FST) o (FILTER (isMovedOut o SND)) o event_robotActions`;

val eventStationaryNames_def = Define`
  eventStationaryNames = MAP (robot_name o FST)
    o (FILTER ((λa. ¬isMovedIn a ∧ ¬isMovedOut a ∧ a ≠ Created) o SND))
    o event_robotActions`;

val eventDeadNames_def = Define`
  eventDeadNames ev = MAP (robot_name o FST)
    (FILTER (λ(r,a). MEM (Destroyed r.name) (MAP SND ev.robotActions)) ev.robotActions)`;

val eventOldRobotNames_thm = Q.store_thm("eventOldRobotNames_thm",
  `PERM (eventOldRobotNames ev) (eventStationaryNames ev ++ eventJustLeftNames ev)`,
  rw[eventOldRobotNames_def,eventStationaryNames_def,eventJustLeftNames_def]
  \\ REWRITE_TAC[GSYM MAP_APPEND]
  \\ match_mp_tac PERM_MAP
  \\ qmatch_abbrev_tac`PERM l1 (l2 ++ l3)`
  \\ `l2 = FILTER ($~ o isMovedOut o SND) l1`
  by (
    simp[Abbr`l2`,Abbr`l1`,FILTER_FILTER,o_DEF]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM,EQ_IMP_THM] )
  \\ `l3 = FILTER ($~ o ($~ o isMovedOut o SND)) l1`
  by (
    simp[Abbr`l3`,Abbr`l1`,FILTER_FILTER,o_DEF]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM,EQ_IMP_THM]
    \\ Cases_on`SND x` \\ fs[] )
  \\ metis_tac[PERM_FILTER_SPLIT]);

(*
val eventMovedRobotNames_thm = Q.store_thm("eventMovedRobotNames_thm",
  `PERM (eventNewRobotNames ev) (eventStationaryNames`,
  eventMovedRobotNames_def

val ALL_DISTINCT_eventAllNames_imp_new = Q.store_thm("ALL_DISTINCT_eventAllNames_imp_new",
  `wf_state g ∧
   ALL_DISTINCT (eventAllNames (computeEvents g)) ⇒
   ALL_DISTINCT (FILTER ($<> 0) (eventAllNewNames (computeEvents g)))`,
  rw[eventAllNames_def,eventAllNewNames_def,ALL_DISTINCT_FLAT,wf_state_def]
  \\ rw[FILTER_FLAT]
  \\ simp[ALL_DISTINCT_FLAT]
  \\ simp[MAP_MAP_o,o_DEF]
  \\ qpat_abbrev_tac`ls = MAP _ (allCoords g)`
  \\ `ls = MAP (eventMovedRobotNames o FAPPLY (computeEvents g)) (allCoords g)`
  by (
    simp[Abbr`ls`,MAP_EQ_f]
    \\ rpt strip_tac
    \\ `x ∈ FDOM g` by fs[allCoords_def,QSORT_MEM]
    \\ simp[computeEvents_def,FMAP_MAP2_THM]
    \\ match_mp_tac FILTER_0_eventMovedRobotNames
    \\ conj_tac
    >- (
      imp_res_tac MEM_allNames_robotNames
      \\ fs[EVERY_MEM,SUBSET_DEF]
      \\ metis_tac[prim_recTheory.LESS_REFL] )
    \\ imp_res_tac MEM_allNames_neighbours
    \\ fs[EVERY_MEM]
    \\ Cases \\ fs[]
    \\ strip_tac \\ res_tac
    \\ fs[SUBSET_DEF,EVERY_MEM]
    \\ metis_tac[prim_recTheory.LESS_REFL] )
  \\ fs[Abbr`ls`]
  \\ pop_assum kall_tac


val eventAllNames_move = Q.store_thm("eventAllNames_move",
  `∃P. PERM (FILTER ($<> 0) (eventAllNewNames f)) (FILTER P (eventAllNames f))`,
  rw[eventAllNewNames_def,eventAllNames_def]
  \\ rw[eventNewRobotNames_def,eventOldRobotNames_def]
  PERM_ALL_DISTINCT
*)

(*
val PERM_allNames_FUPDATE = Q.store_thm("PERM_allNames_FUPDATE",
  `∀s x y. PERM (allNames (s |+ (x,y))) (allNames (s \\ x) ++ robotNames y)`,
  rw[allNames_def,allCoords_def]
  \\ rw[GSYM FLAT_SNOC]
  \\ match_mp_tac PERM_FLAT
  \\ match_mp_tac (PERM_SYM |> SPEC_ALL |> EQ_IMP_RULE |> #1)
  \\ simp[PERM_SNOC]
  \\ simp[PERM_CONS_EQ_APPEND]
  \\ qexists_tac`PARTITION

  ho_match_mp_tac fmap_INDUCT \\ rw[]
  >- ( rw[allNames_def,allCoords_def] \\ EVAL_TAC \\ rw[] )
  >- (
    rw[allNames_def,allCoords_def,FAPPLY_FUPDATE_THM]
    \\ rw[GSYM FLAT_SNOC]
    \\ match_mp_tac PERM_FLAT
    \\ cheat )

val ALL_DISTINCT_allNames_FUPDATE = Q.store_thm("ALL_DISTINCT_allNames_FUPDATE",
  `ALL_DISTINCT (allNames (s |+ (x,y))) ⇔
   ALL_DISTINCT (allNames (s \\ x) ++ robotNames y)`,
  rw[allNames_def,ALL_DISTINCT_APPEND,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  ALL_DISTINCT_FLAT
  rw[allNames_def,ALL_DISTINCT_QSORT,ALL_DISTINCT_APPEND,QSORT_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP]
  \\ qpat_abbrev_tac`lsy = FLAT (MAP _ _)`
  \\ qpat_abbrev_tac`ls = FLAT _`
  \\ `PERM lsy (ls ++ robotNames y)`
  by (
    unabbrev_all_tac

val wf_state_preserved = Q.store_thm("wf_state_preserved",
  `∀s. wf_state s ⇒ wf_state (step s)`,
  ho_match_mp_tac fmap_INDUCT
  \\ conj_tac >- ( rw[wf_state_def] )
  \\ rw[]
  step_def
  wf_state_def
  allNames_def
    ,allNames_def,step_def,computeEvents_def,mkNames_def,FMAP_MAP2_THM]
  rw[wf_state_def,step_def,allNames_def]

val focal_preserved = Q.store_thm("focal_preserved",
  `∀s. wf_state_with_hole s ⇒
   wf_state_with_hole (s with state := step s.state)`,
  ho_match_mp_tac fmap_INDUCT

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
    `∀i. i < LENGTH l ⇒ ((EL i (MAP f l)).focal ⇔ (FST(SND(EL i l))).focal)` by (
      simp[EL_MAP] >>
      simp[Abbr`f`] >>
      gen_tac >>
      Cases_on`EL i l` >>
      Cases_on`r` >>
      simp[prepare_def] >>
      simp[runMachine_def] >>
      simp[UNCURRY]) >>
    qsuff_tac`∃i. i < LENGTH l ∧ (FST(SND(EL i l))).focal ∧ R i`>-metis_tac[] >>
    simp[Abbr`f`] >>
    qmatch_assum_abbrev_tac`Abbrev(l = FILTER P l1)` >>
    `s.focal_index < LENGTH l1` by (
      simp[Abbr`l1`] >> simp[event_def] ) >>
    `∀k. k < LENGTH l1 ⇒ ((FST(SND (EL k l1))).focal ⇔ (s.focal_index = k))` by (
      simp[Abbr`l1`,EL_GENLIST] >> rw[] >>
      simp[event_def] >>
      Cases_on`k < LENGTH sq.robots` >- (
        simp[EL_APPEND1,LENGTH_ZIP,EL_ZIP] >>
        reverse(rw[EQ_IMP_THM]) >> rw[] >>
        spose_not_then strip_assume_tac >>
        qpat_assum`_.focal`mp_tac >> simp[] >>
        first_x_assum match_mp_tac >> simp[] >>
        metis_tac[] ) >>
      reverse EQ_TAC >- (
        strip_tac >> fs[] ) >>
      qmatch_abbrev_tac`(FST (EL k (l1 ++ l2 ++ l3))).focal ⇒ _` >>
      `LENGTH l1 ≤ k` by simp[Abbr`l1`] >>
      ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      simp[EL_APPEND2] >>
      `∀x. MEM x (MAP FST (l2 ++ l3)) ⇒ ¬x.focal` by (
        simp[] >>
        simp[Abbr`l3`,MAP_ZIP,REPLICATE_GENLIST] >>
        simp[Abbr`l2`,MEM_FLAT,PULL_EXISTS,MEM_MAP,EXISTS_PROD,MEM_GENLIST] >>
        rw[] >- (
          Cases_on`EL i nb`>> fs[incomingFrom_def] >>
          fs[MEM_FLAT,MEM_MAP] >> rveq >>
          qpat_assum`MEM _ _`mp_tac >> rw[] >>
          qpat_assum`MEM _ _`mp_tac >>
          rw[MEM_EL] >>
          first_x_assum match_mp_tac >> rw[] >>
          qpat_assum`EL i nb = _`mp_tac >>
          simp[Abbr`nb`] >>
          Cases_on`s.focal_coordinate` >>
          qpat_assum`i < _`mp_tac >>
          simp[neighbours_def,neighbour_coords_def] >>
          simp[less8] >>
          strip_tac >> rw[] >>
          asm_exists_tac >> simp[] >>
          disj1_tac >> intLib.COOPER_TAC) >>
        pop_assum mp_tac >>
        BasicProvers.TOP_CASE_TAC >> rw[] >>
        imp_res_tac MEM_Built_localActions_not_focal ) >>
      `k - LENGTH l1 < LENGTH (l2 ++ l3)` by (
        qpat_assum`k < _`mp_tac >>
        simp[event_def] ) >>
      metis_tac[MEM_EL,MEM_MAP] ) >>
    qispl_then[`l1`,`s.focal_index`](mp_tac o Q.GEN`R`) unique_index_filter >>
    disch_then(qspec_then`λx. (FST(SND x)).focal`mp_tac) >>
    impl_tac >- (
      simp[Abbr`P`,UNCURRY] >>
      conj_tac >- (
        qpat_assum`¬_`mp_tac >> fs[Abbr`l1`] ) >>
      rator_x_assum`EVERY`mp_tac >>
      fs[Abbr`l1`] >>
      simp[EVERY_MEM] >>
      simp[MEM_MAP] >>
      metis_tac[] ) >>
    strip_tac >> rfs[] >>
    asm_exists_tac >> simp[] >>
    simp[Abbr`R`] >>
    rpt gen_tac >>
    BasicProvers.TOP_CASE_TAC >> simp[] >>
    simp[GSYM AND_IMP_INTRO] >>
    strip_tac >> rveq >> simp[] >>
    strip_tac >> simp[EL_MAP] >>
    Cases_on`c = s.focal_coordinate`>>fs[]>-(
      rw[] >> rfs[] >> rveq >> rfs[] ) >>
    rveq >> rfs[] >>
    last_assum drule >> simp[] >>
    strip_tac >>
    `EVERY ($~ o robot_focal) sq'.robots` by (
      simp[EVERY_MEM] >> simp[MEM_EL,PULL_EXISTS] ) >>
    qmatch_abbrev_tac`¬(FST(SND(EL i (FILTER P' ls)))).focal` >>
    `EVERY ($~ o robot_focal) (MAP (FST o SND) ls)` suffices_by (
      simp[EVERY_MAP] >>
      simp[EVERY_MEM] >>
      metis_tac[MEM_EL,MEM_FILTER] ) >>
    simp[Abbr`ls`,EVERY_MAP,EVERY_GENLIST] >>
    qpat_abbrev_tac`ls = _.robotActions` >>
    `EVERY ($~ o robot_focal) (MAP FST ls)` suffices_by (
      simp[EVERY_MAP] >> simp[EVERY_MEM] >> simp[MEM_EL,PULL_EXISTS] ) >>
    simp[Abbr`ls`] >>
    qpat_abbrev_tac`nb' = neighbours _ _` >>
    simp[event_def,MAP_ZIP,REPLICATE_GENLIST] >>
    reverse conj_tac >- (
      simp[EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      gen_tac >> Cases >> simp[] >>
      rw[] >> imp_res_tac MEM_Built_localActions_not_focal ) >>
    conj_tac >- (
      simp[EVERY_MEM,MEM_GENLIST,PULL_EXISTS] ) >>
    simp[EVERY_MAP,MEM_FLAT,EVERY_MEM,PULL_EXISTS,MEM_GENLIST] >>
    rpt gen_tac >>
    simp[GSYM AND_IMP_INTRO] >> strip_tac >>
    qpat_abbrev_tac`opt = EL _ _` >>
    Cases_on`opt`>>simp[incomingFrom_def] >>
    pop_assum mp_tac >> simp[markerTheory.Abbrev_def] >>
    disch_then(assume_tac o SYM) >>
    simp[MEM_FLAT,PULL_EXISTS,MEM_MAP] >> rw[] >>
    pop_assum mp_tac >>
    rw[MEM_EL] >>
    `∀c. FLOOKUP s.state c = SOME sq ⇒ c = s.focal_coordinate` by (
      rw[] >> res_tac >>
      spose_not_then strip_assume_tac >> fs[] ) >>
    first_x_assum match_mp_tac >>
    simp[] >>
    spose_not_then strip_assume_tac >>
    `∃c. FLOOKUP s.state c = SOME x'` by (
      qunabbrev_tac`nb'` >>
      qpat_assum`_ = SOME _`mp_tac >>
      Cases_on`c` >>
      qpat_assum`_ < LENGTH (neighbours _ _)`mp_tac >>
      simp[neighbours_def,neighbour_coords_def] >>
      simp[less8] >> strip_tac >> simp[] >> rw[] >>
      asm_exists_tac >> simp[] ) >>
    first_x_assum drule >> strip_tac >> rveq >>
    rfs[] >> rveq >>
    qpat_assum`¬isMovedOut _`mp_tac >>
    simp[] >>
    simp[event_def,EL_APPEND1,EL_ZIP,localActions_def,act_def] >>
    rfs[Abbr`nb`] >>
    Cases_on`s.focal_coordinate` >>
    Cases_on`c` >>
    unabbrev_all_tac >>
    qpat_assum`_ ≠ _`mp_tac >>
    fs[neighbours_def,neighbour_coords_def,opposite_def] >>
    fs[less8] >> rveq >> fs[] >> rfs[] >>
    first_x_assum drule >> simp[] >>
    strip_tac >> rveq >> simp[] >>
    simp[int_arithTheory.elim_minus_ones]) >>
  `∃dir.
    (EL s.focal_index sq.robots).command = Move dir ∧ dir < 8 ∧
    IS_SOME (FLOOKUP s.state (EL dir (neighbour_coords s.focal_coordinate)))`
  by (
    qpat_assum`isMovedOut _`mp_tac >>
    simp[event_def,EL_APPEND1,EL_ZIP,localActions_def] >>
    simp[act_def] >>
    BasicProvers.TOP_CASE_TAC >> simp[]>> rw[] >- (
      fs[Abbr`nb`] )
    >- (
      fs[neighbours_def,Abbr`nb`] >> rfs[EL_MAP] ) >>
    BasicProvers.CASE_TAC >> simp[] ) >>
  qexists_tac`EL dir (neighbour_coords s.focal_coordinate)` >>
  fs[IS_SOME_EXISTS] >>
  simp[computeSquare_def] >>
  qho_match_abbrev_tac`∃i. (i < LENGTH l ∧ (EL i (MAP f l)).focal) ∧ R i` >>
  `∀i. i < LENGTH l ⇒ ((EL i (MAP f l)).focal ⇔ (FST(SND(EL i l))).focal)` by (
    simp[EL_MAP] >>
    simp[Abbr`f`]) >>
  qsuff_tac`∃i. i < LENGTH l ∧ (FST(SND(EL i l))).focal ∧ R i`>-metis_tac[] >>
  simp[Abbr`f`] >>
  qmatch_assum_abbrev_tac`Abbrev(l = FILTER P l1)` >>
  `∃i. i < LENGTH l1  ∧ (∀k. k < LENGTH l1 ⇒ ((FST(SND(EL k l1))).focal ⇔ (i = k)))
       ∧ P (EL i l1)` by (
    qmatch_assum_abbrev_tac`Abbrev(l1 = GENLIST (λi. (i,EL i l2)) (LENGTH l2))` >>
    `MAP SND l1 = l2` by (
      simp[Abbr`l1`,Abbr`l2`,LIST_EQ_REWRITE,EL_MAP] ) >>
    simp[Once (GSYM EL_MAP)] >>
    qho_match_abbrev_tac`∃i. i < LENGTH l1 ∧ Q i ∧ P (EL i l1)`
    \\ `∃i. i < LENGTH l1 ∧ Q i ∧ ¬isMovedOut (SND (EL i l2)) ∧ ¬MEM (Destroyed i) (MAP SND l2)`
    suffices_by (
      strip_tac
      \\ asm_exists_tac
      \\ simp[Abbr`P`]
      \\ simp[UNCURRY]
      \\ simp[Abbr`l1`]
      \\ fs[]) \\
    simp[Abbr`Q`,Abbr`P`] >>
    pop_assum kall_tac >>
    simp[Abbr`l1`] >>
    simp[Abbr`l2`] >>
    qpat_abbrev_tac`nxb = neighbours _ _` >>
    simp[event_def,REPLICATE_GENLIST,LENGTH_ZIP] >>
    qpat_abbrev_tac`veterans = ZIP(_,localActions _ _)` >>
    qpat_abbrev_tac`immigrations = FLAT (GENLIST _ _)` >>
    qpat_abbrev_tac`children = ZIP(_,GENLIST(K Created)_)` >>
    qpat_abbrev_tac`builders = FLAT(MAP _ _)` >>
    `EVERY ($~ o robot_focal) (MAP FST veterans)` by (
      simp[Abbr`veterans`,MAP_ZIP,EVERY_GENLIST] >> rw[] >>
      first_x_assum match_mp_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      qpat_assum`dir < _`mp_tac >>
      Cases_on`s.focal_coordinate` >>
      simp[less8,neighbour_coords_def] >>
      strip_tac >> simp[] >>
      intLib.COOPER_TAC ) >>
    `EVERY ($~ o robot_focal) (MAP FST children)` by (
      simp[Abbr`children`,MAP_ZIP] >>
      simp[Abbr`builders`,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
      gen_tac >> Cases >> simp[] >> rw[] >>
      imp_res_tac MEM_Built_localActions_not_focal ) >>
    `∃j. j < LENGTH immigrations ∧ (∀k. k < LENGTH immigrations ⇒ ((EL k (MAP FST immigrations)).focal ⇔ (k = j)))` by (
      ntac 4 (pop_assum kall_tac) >>
      simp[Abbr`veterans`,Abbr`R`] >>
      qmatch_assum_abbrev_tac`r.focal` >>
      `MEM r (MAP FST immigrations)` by (
        simp[Abbr`immigrations`,MAP_FLAT,MEM_FLAT,MAP_GENLIST,MEM_GENLIST,PULL_EXISTS]
        \\ drule (GEN_ALL neighbours_EL_neighbour_coords)
        \\ last_assum(fn th => disch_then(strip_assume_tac o C MATCH_MP th))
        \\ qexists_tac`opposite dir`
        \\ rfs[]
        \\ conj_tac >- ( simp[Abbr`nxb`,opposite_def] )
        \\ simp[incomingFrom_def]
        \\ simp[MAP_FLAT,MEM_FLAT,MAP_MAP_o,o_DEF,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
        \\ CONV_TAC SWAP_EXISTS_CONV
        \\ qexists_tac`r` >> simp[]
        \\ simp[MEM_EL,Abbr`r`]
        \\ metis_tac[] )
      \\ pop_assum mp_tac
      \\ simp[MEM_EL]
      \\ strip_tac
      \\ asm_exists_tac
      \\ simp[]
      \\ qx_gen_tac`k` >> strip_tac
      \\ Cases_on`k=n` >- fs[]
      \\ simp[Abbr`r`]
      \\ first_assum(
           strip_assume_tac o
           MATCH_MP (SIMP_RULE std_ss [](Q.SPEC`I`(Q.GEN`f`immigration_sources))) o
           SIMP_RULE std_ss [markerTheory.Abbrev_def])
      \\ rfs[]
      \\ first_assum(qspec_then`k`mp_tac)
      \\ first_x_assum(qspec_then`n`mp_tac)
      \\ simp[]
      \\ strip_tac
      \\ rfs[EL_MAP]
      \\ fs[]
      \\ `sq = sq' ∧ j = s.focal_index`
      by (
        spose_not_then strip_assume_tac
        \\ qpat_assum`_.focal`mp_tac
        \\ simp[]
        \\ first_x_assum match_mp_tac
        \\ simp[]
        \\ qpat_assum`_ = SOME sq'`mp_tac
        \\ simp[Abbr`nxb`]
        \\ fs[]
        \\ simp[neighbours_def]
        \\ simp[EL_MAP]
        \\ strip_tac
        \\ asm_exists_tac
        \\ simp[]
        \\ spose_not_then strip_assume_tac
        \\ fs[] )
      \\ strip_tac
      \\ fs[]
      \\ first_assum match_mp_tac
      \\ qpat_assum`_ = SOME sq''`mp_tac
      \\ qpat_assum`_ = SOME sq'`mp_tac
      \\ simp[Abbr`nxb`]
      \\ fs[neighbours_def]
      \\ simp[EL_MAP]
      \\ ntac 2 strip_tac
      \\ asm_exists_tac
      \\ simp[]
      \\ `(i,j) ≠ (i',j')` by metis_tac[ALL_DISTINCT_EL_IMP]
      \\ spose_not_then strip_assume_tac
      \\ fs[] \\ rfs[]
      \\ rveq
      \\ metis_tac[opposite_inj])
    \\ qexists_tac`LENGTH veterans + j`
    \\ `LENGTH veterans = LENGTH x.robots` by ( simp[Abbr`veterans`] )
    \\ simp[]
    \\ reverse conj_tac
    >- (
      simp[EL_APPEND1,EL_APPEND2]
      \\ conj_tac
      >- (
        `∀x. MEM x (MAP SND immigrations) ⇒ ¬isMovedOut x`
        suffices_by ( simp[MEM_MAP,PULL_EXISTS,MEM_EL] )
        \\ simp[Abbr`immigrations`]
        \\ simp[MEM_MAP,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
        \\ rw[] \\ imp_res_tac incomingFrom_MovedIn
        \\ simp[] )
      \\ reverse conj_tac
      >- (
        simp[Abbr`children`,MAP_ZIP,MEM_GENLIST] )
      \\ reverse conj_tac
      >- (
        simp[Abbr`immigrations`]
        \\ simp[MEM_MAP,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
        \\ spose_not_then strip_assume_tac
        \\ imp_res_tac incomingFrom_MovedIn
        \\ fs[] )
      \\ simp[Abbr`veterans`]
      \\ simp[MAP_ZIP]
      \\ simp[localActions_def]
      \\ simp[MEM_GENLIST]
      \\ simp[act_def]
      \\ rw[]
      \\ BasicProvers.TOP_CASE_TAC \\ simp[]
      \\ rw[]
      \\ TRY BasicProvers.CASE_TAC
      \\ decide_tac)
    \\ qx_gen_tac`k`>>strip_tac
    \\ Cases_on`k < LENGTH veterans` \\ simp[EL_APPEND1]
    >- (
      fs[EVERY_MAP,EVERY_MEM,MEM_EL,PULL_EXISTS]
      \\ metis_tac[] )
    \\ Cases_on`k < LENGTH veterans + LENGTH immigrations`
    \\ simp[EL_APPEND1,EL_APPEND2]
    >- (
      first_x_assum(qspec_then`k - LENGTH x.robots`mp_tac)
      \\ simp[EL_MAP] )
    \\ `LENGTH builders = LENGTH children` by simp[Abbr`children`]
    \\ fs[EVERY_MAP,EVERY_MEM,MEM_EL,PULL_EXISTS]
    \\ first_x_assum match_mp_tac
    \\ simp[]) >>
  qispl_then[`l1`,`i`](mp_tac o Q.GEN`R`) unique_index_filter >>
  disch_then(qspec_then`λx. (FST(SND x)).focal`mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> rfs[] >>
  asm_exists_tac >> simp[] >>
  simp[Abbr`R`] >>
  rpt gen_tac >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[GSYM AND_IMP_INTRO] >>
  strip_tac >> rveq >> simp[] >>
  strip_tac >> simp[EL_MAP]
  \\ Cases_on`c = EL dir (neighbour_coords s.focal_coordinate)`
  >- ( fs[] \\ rfs[] \\ rveq \\ fs[] \\ rfs[])
  \\ simp[]
  \\ qmatch_abbrev_tac`¬ (FST (SND (EL _ (FILTER P' ls)))).focal`
  \\ `∀r. MEM r ls ∧ P' r ⇒ ¬(FST(SND r)).focal`
  suffices_by (
    rw[] \\ fs[]
    \\ first_x_assum match_mp_tac
    \\ qpat_abbrev_tac`e = EL _ _`
    \\ `MEM e (FILTER P' ls)`
    by ( simp[MEM_EL] \\ metis_tac[] )
    \\ fs[MEM_FILTER])
  \\ simp[Abbr`ls`,MAP_GENLIST,o_DEF]
  \\ simp[MEM_GENLIST]
  \\ Cases_on`FLOOKUP s.state c` \\ fs[]
  \\ qpat_abbrev_tac`nxb = neighbours _ _`
  \\ qpat_abbrev_tac`ras = _.robotActions`
  \\ rveq
  \\ Cases_on`c = s.focal_coordinate`
  >- (
    fs[] \\ rfs[]
    \\ rveq
    \\ `∀r. MEM r ras ∧ ¬isMovedOut(SND r) ⇒ ¬(FST r).focal`
    suffices_by (
      simp[Abbr`P'`,PULL_EXISTS,MEM_EL,UNCURRY] )
    \\ simp[Abbr`ras`,event_def,REPLICATE_GENLIST]
    \\ qpat_abbrev_tac`veterans = ZIP(_,localActions _ _)`
    \\ qpat_abbrev_tac`immigrations = FLAT (GENLIST _ _)`
    \\ qpat_abbrev_tac`children = ZIP(_,GENLIST(K Created)_)`
    \\ gen_tac
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ simp[GSYM AND_IMP_INTRO]
    \\ strip_tac
    \\ Cases_on`MEM r veterans`
    \\ simp[]
    >- (
      pop_assum mp_tac
      \\ simp[Abbr`veterans`,MAP_ZIP,ZIP_GENLIST]
      \\ simp[MEM_ZIP,PULL_EXISTS]
      \\ simp[GSYM AND_IMP_INTRO]
      \\ rw[]
      \\ first_x_assum match_mp_tac
      \\ asm_exists_tac \\ simp[]
      \\ spose_not_then strip_assume_tac
      \\ rveq
      \\ qpat_assum`¬isMovedOut _`mp_tac
      \\ simp[localActions_def]
      \\ simp[act_def,Abbr`nb`]
      \\ simp[neighbours_def,EL_MAP] )
    \\ Cases_on`MEM r children`
    \\ simp[]
    >- (
      `MEM (FST r) (MAP FST children)` by metis_tac[MEM_MAP]
      \\ pop_assum mp_tac
      \\ simp[Abbr`children`,MAP_ZIP,MEM_FLAT,PULL_EXISTS]
      \\ simp[MEM_MAP,PULL_EXISTS]
      \\ Cases \\ simp[]
      \\ metis_tac[MEM_Built_localActions_not_focal] )
    \\ simp[Abbr`immigrations`,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
    \\ simp[Abbr`children`] \\ pop_assum kall_tac
    \\ qx_gen_tac`z`
    \\ simp[GSYM AND_IMP_INTRO]
    \\ strip_tac
    \\ Cases_on`EL z nb`
    \\ simp[incomingFrom_def]
    \\ simp[MEM_FLAT,MEM_MAP,PULL_EXISTS]
    \\ rw[]
    \\ pop_assum mp_tac
    \\ rw[MEM_EL]
    \\ first_x_assum match_mp_tac
    \\ fs[Abbr`nb`]
    \\ qpat_assum`_ = SOME _`mp_tac
    \\ Cases_on`s.focal_coordinate`
    \\ simp[neighbours_def,neighbour_coords_def]
    \\ qpat_assum`z < 8`mp_tac
    \\ simp[less8]
    \\ strip_tac \\ rw[]
    \\ asm_exists_tac \\ simp[]
    \\ spose_not_then strip_assume_tac
    \\ intLib.COOPER_TAC)
  \\ `∀r. MEM r ras ⇒ ¬(FST r).focal`
  suffices_by (
    simp[Abbr`P'`,PULL_EXISTS,MEM_EL,UNCURRY] )
  \\ simp[Abbr`ras`,event_def,REPLICATE_GENLIST]
  \\ qpat_abbrev_tac`veterans = ZIP(_,localActions _ _)`
  \\ qpat_abbrev_tac`immigrations = FLAT (GENLIST _ _)`
  \\ qpat_abbrev_tac`children = ZIP(_,GENLIST(K Created)_)`
  \\ gen_tac
  \\ Cases_on`MEM r veterans`
  \\ simp[]
  >- (
    pop_assum mp_tac
    \\ simp[Abbr`veterans`,MAP_ZIP,ZIP_GENLIST]
    \\ simp[MEM_ZIP,PULL_EXISTS]
    \\ simp[GSYM AND_IMP_INTRO]
    \\ rw[]
    \\ first_x_assum match_mp_tac
    \\ asm_exists_tac \\ simp[])
  \\ Cases_on`MEM r children`
  \\ simp[]
  >- (
    `MEM (FST r) (MAP FST children)` by metis_tac[MEM_MAP]
    \\ pop_assum mp_tac
    \\ simp[Abbr`children`,MAP_ZIP,MEM_FLAT,PULL_EXISTS]
    \\ simp[MEM_MAP,PULL_EXISTS]
    \\ Cases \\ simp[]
    \\ metis_tac[MEM_Built_localActions_not_focal] )
  \\ simp[Abbr`immigrations`,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
  \\ simp[Abbr`children`] \\ pop_assum kall_tac
  \\ qx_gen_tac`z`
  \\ simp[GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ Cases_on`EL z nxb`
  \\ simp[incomingFrom_def]
  \\ simp[MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[MEM_EL]
  \\ first_x_assum match_mp_tac
  \\ fs[Abbr`nxb`]
  \\ `FLOOKUP s.state (EL z (neighbour_coords c)) = SOME x'`
  by ( fs[neighbours_def] \\ rfs[EL_MAP] )
  \\ asm_exists_tac
  \\ simp[]
  \\ spose_not_then strip_assume_tac
  \\ fs[] \\ rveq
  \\ fs[] \\ rveq
  \\ metis_tac[neighbour_coords_opposite_imp]);
*)

val isMovedOut_map_inspected = Q.store_thm("isMovedOut_map_inspected[simp]",
  `isMovedOut (map_inspected f x) = isMovedOut x`,
  Cases_on`x` \\ simp[]);

val steph_focal_clock = Q.store_thm("steph_focal_clock",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ⇒
   (get_focal_robot s).processor = (get_focal_robot s').processor`,
  rw[steph_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[get_focal_robot_def]
  \\ fs[step_def,IN_FRANGE_FLOOKUP]
  \\ cheat);

val mapRobotsInSquare_compose = Q.store_thm("mapRobotsInSquare_compose",
  `mapRobotsInSquare (f o g) = mapRobotsInSquare f o mapRobotsInSquare g`,
  rw[FUN_EQ_THM,mapRobotsInSquare_def]
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ rw[FUN_EQ_THM,MAP_MAP_o]);

val mapRobots_compose = Q.store_thm("mapRobots_compose",
  `mapRobots f (mapRobots g x) = mapRobots (f o g) x`,
  rw[mapRobots_def,FMAP_MAP2_SND_compose,mapRobotsInSquare_compose]);

val fill_with_policy_split = Q.store_thm("fill_with_policy_split",
  `fill (with_policy c p) s =
   fill (memory_fupd (K p))
   (s with state := fill (command_fupd (K c)) s)`,
  rw[fill_def,mapRobots_compose]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[] \\ fs[])

val wf_state_with_hole_focal_name_nonzero = Q.store_thm("wf_state_with_hole_focal_name_nonzero",
  `wf_state_with_hole s ⇒ s.focal_name ≠ 0`,
  rw[wf_state_with_hole_def,wf_state_def,EVERY_MEM]
  \\ res_tac \\ fs[]);

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ∧
   run_policy p (get_focal_robot s).processor obs = (c',p')
   ⇒
   step (fill (with_policy c p) s) = fill (with_policy c' p') s'`,
  rw[steph_def]
  \\ imp_res_tac wf_state_with_hole_focal_name_nonzero
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ simp[fill_with_policy_split,SimpLHS]
  \\ simp[step_def]
  \\ simp[computeEvents_fill_with_memory]
  \\ simp[o_DEF]
  \\ qpat_abbrev_tac`events = computeEvents _`
  \\ cheat)
*)

(*
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
  rveq
  \\ drule (GEN_ALL focal_preserved)
  \\ simp[]
  \\ strip_tac
  \\ drule wf_state_with_hole_find_focal
  \\ simp[]
  \\ strip_tac \\ rveq
  \\ first_assum mp_tac
  \\ simp_tac std_ss [wf_state_with_hole_def]
  \\ strip_tac
  \\ fs[]
  \\ IF_CASES_TAC >> fs[] >- (
    rveq >>
    simp[computeSquare_def,square_update_robot_def]
    \\ match_mp_tac EQ_SYM
    \\ qpat_abbrev_tac`ls = FILTER _ _`
    \\ `i < LENGTH ls`
    by (
      fs[FLOOKUP_o_f]
      \\ rfs[]
      \\ rveq
      \\ fs[computeSquare_def,LET_THM] )
    \\ simp[EL_MAP]
    \\ simp[LIST_EQ_REWRITE]
    \\ conj_tac
    >- (
      simp[Abbr`ls`]
      \\ simp[MAP_MAP_o,o_DEF]
      \\ simp[MEM_MAP]
      \\ match_mp_tac LENGTH_FILTER_EQ
      \\ simp[EL_MAP,UNCURRY] )
    \\ gen_tac \\ strip_tac
    \\ simp[EL_MAP,EL_LUPDATE]
    \\ qpat_abbrev_tac`ls' = MAP _ (FILTER _ _)`
    \\ `x' < LENGTH ls'`
    by (
      simp[Abbr`ls'`]
      \\ pop_assum mp_tac
      \\ simp[Abbr`ls`]
      \\ simp[MAP_MAP_o,o_DEF,MEM_MAP,PULL_EXISTS]
      \\ qmatch_abbrev_tac`_ < LENGTH l1 ⇒ _ < LENGTH l2`
      \\ `LENGTH l1 = LENGTH l2` suffices_by rw[]
      \\ simp[Abbr`l1`,Abbr`l2`]
      \\ match_mp_tac LENGTH_FILTER_EQ
      \\ simp[]
      \\ simp[EL_MAP,UNCURRY] )
    \\ qmatch_assum_rename_tac `FLOOKUP events coord = SOME ev`
    \\ fs[Abbr`ls'`,EL_MAP]
    \\ simp[Abbr`ls`]
    \\ simp[MAP_MAP_o,o_DEF,MEM_MAP,PULL_EXISTS]
    \\ qpat_abbrev_tac`l1 = FILTER P (GENLIST _ _)`
    \\ qpat_abbrev_tac`l2 = FILTER P (GENLIST _ _)`
    \\ qmatch_assum_abbrev_tac`Abbrev(l2 = FILTER P (GENLIST (λi. (i, EL i (MAP f ras))) _))`
    \\ `l2 = FILTER P (MAP (I ## f) (GENLIST (λi. (i, EL i ras)) (LENGTH ras)))`
    by (
      simp[Abbr`l2`]
      \\ simp[MAP_GENLIST,o_DEF]
      \\ AP_TERM_TAC
      \\ simp[LIST_EQ_REWRITE,EL_MAP] )
    \\ qunabbrev_tac`l2`
    \\ simp[Abbr`l1`]
    \\ qpat_abbrev_tac`ls = GENLIST _ _`
    \\ qispl_then[`I ## f`,`P`,`ls`]mp_tac MAP_FILTER
    \\ impl_tac
    >- ( simp[Abbr`P`,Abbr`f`,UNCURRY] )
    \\ disch_then(SUBST_ALL_TAC o SYM)
    \\ qpat_abbrev_tac`ll = MAP (I ## f) _`
    \\ `x' < LENGTH ll`
    by (
      qpat_assum`x' < _`mp_tac
      \\ simp[Abbr`ll`,Abbr`ls`]
      \\ qmatch_abbrev_tac`_ < LENGTH l1 ⇒ _ < LENGTH l2`
      \\ `LENGTH l1 = LENGTH l2` suffices_by rw[]
      \\ simp[Abbr`l1`,Abbr`l2`]
      \\ simp[Abbr`P`,Abbr`f`,o_DEF,UNCURRY]
      \\ simp[MEM_MAP,PULL_EXISTS,MAP_MAP_o,o_DEF,MAP_GENLIST,UNCURRY] )
    \\ fs[Abbr`ll`,EL_MAP]
    \\ Cases_on `prepare ev (EL i (FILTER P ls))` \\ simp[UNCURRY, Once runMachine_def]
    \\ qpat_abbrev_tac `ir = EL _ (FILTER _ _)` \\ PairCases_on `ir`
    \\ pop_assum mp_tac \\ simp[markerTheory.Abbrev_def] \\ disch_then (assume_tac o SYM)
    \\ simp[Abbr`f`, prepare_def]
    \\ reverse(rw[])
    >- (
      AP_TERM_TAC \\ simp[]
      \\ simp[if_focal_def]
      \\ IF_CASES_TAC \\ fs[]
      >- (
        first_x_assum drule
        \\ simp[]
        \\ qpat_assum`FLOOKUP (_ o_f _) _ = _`mp_tac
        \\ simp[FLOOKUP_o_f]
        \\ strip_tac \\ rveq
        \\ simp[computeSquare_def]
        \\ simp[EL_MAP]
        \\ simp[MEM_MAP]
        \\ disch_then drule
        \\ simp[] )
      \\ simp[event_component_equality]
      \\ simp[MAP_EQ_ID]
      \\ simp[FORALL_PROD]
      \\ conj_asm1_tac >- cheat
      \\ AP_TERM_TAC
      \\ fsrw_tac[DNF_ss][]
      \\ match_mp_tac EQ_SYM
      \\ first_x_assum match_mp_tac
      \\ `MEM (ir0,ir1,ir2) (FILTER P ls)` by metis_tac[MEM_EL]
      \\ fs[MEM_FILTER,Abbr`ls`,MEM_GENLIST]
      \\ fs[MEM_EL]
      \\ metis_tac[] )
    \\ rw[runMachine_def]
    \\ split_pair_tac \\ fs[]
    \\ rpt(rator_x_assum`run_policy`mp_tac)
    \\ `ir1.focal`
    by (
      qpat_assum `FLOOKUP _ coord = _` mp_tac
      \\ simp[FLOOKUP_o_f] \\ rw[]
      \\ qpat_assum `_.focal` mp_tac \\ simp[computeSquare_def]
      \\ fs[MEM_MAP,PULL_EXISTS] \\ simp[EL_MAP] \\ fs[prepare_def])
    \\ simp[if_focal_def, robot_component_equality]
    \\ fs[prepare_def] \\ rveq \\ fs[]
    \\ `EL ir0 ras = (ir1,ir2) /\ ir0 < LENGTH ras` by (
        `MEM (ir0,ir1,ir2) (FILTER P ls)` by (metis_tac[MEM_EL])
        \\ fs[Abbr`ls`, MEM_FILTER, MEM_EL] \\ rfs[EL_GENLIST])
    \\ cheat)
  \\ simp[computeSquare_def]
  \\ qpat_abbrev_tac`m = MAP (_ ## _)`
  \\ `m x.robotActions = x.robotActions`
   by (
     simp[Abbr`m`,MAP_EQ_ID,FORALL_PROD,FORALL_PROD,FORALL_PROD,FORALL_PROD]
     \\ qx_genl_tac[`r`,`a`] \\ strip_tac
     \\ simp[if_focal_def]
     \\ IF_CASES_TAC \\ simp[]
     >- (
       `∃r'. MEM r' (computeSquare x).robots ∧ r'.focal`
       by (
         qpat_assum`MEM _ _`mp_tac
         \\ simp[Once MEM_EL]
         \\ simp[computeSquare_def,MEM_MAP,MEM_FILTER,MEM_GENLIST,EXISTS_PROD]
         \\ strip_tac
         \\ simp[PULL_EXISTS]
         \\ CONV_TAC(STRIP_QUANT_CONV(move_conj_left(is_eq)))
         \\ asm_exists_tac \\ simp[]
         \\ cheat )
       \\ first_x_assum(qspec_then`k`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["c"])))
       \\ simp[FLOOKUP_o_f]
       \\ fs[MEM_EL]
       \\ metis_tac[] )
     \\ cheat )
  \\ `x with robotActions updated_by m = x` by ( simp[event_component_equality] )
  \\ simp[]);
*)

(* sv theorem *)
open botworld_svTheory

val next_def = Define`
  (next MP = MP) ∧
  (next (Trust k) = Trust (k+1))`;

val canupdateh_def = Define`
  canupdateh S c = ∀s. s ∈ S ⇒ wf_state_with_hole s ∧ IS_SOME(steph c s)`;

val updateh_def = Define`
  updateh S c o' s' ⇔ ∃s. s ∈ S ∧ steph c s = SOME (o',s')`;

val _ = Parse.hide"S";

val lemmaA = Q.store_thm("lemmaA",
  `∀δ l S u c p1 p2.
     canupdateh S c ∧
     utilityfn u ∧ weaklyExtensional u ∧ discount_exists u ∧
     0 ≤ δ ∧
     (∀o' s'. updateh S c o' s' ⇒
       let k = (get_focal_robot s').processor in
       u (hist (fill_with (run_policy p1 k o') s')) + δ ≥
       u (hist (fill_with (run_policy p2 k o') s')))
     ⇒
     ∀s. s ∈ S ⇒
       u (hist (fill_with (c,p1) s)) + (discount u)*δ ≥
       u (hist (fill_with (c,p2) s))`,
  rpt gen_tac
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ `∃o' s'. steph c s = SOME (o',s') ∧ wf_state_with_hole s`
  by ( fs[canupdateh_def,IS_SOME_EXISTS,EXISTS_PROD])
  \\ `updateh S c o' s'` by metis_tac[updateh_def]
  \\ first_x_assum drule
  \\ BasicProvers.LET_ELIM_TAC
  \\ drule (GEN_ALL steph_fill_step)
  \\ disch_then drule
  \\ drule (GEN_ALL steph_focal_clock)
  \\ disch_then drule
  \\ simp[]
  \\ disch_then kall_tac
  \\ disch_then(fn th =>
       let val th = GSYM (CONV_RULE SWAP_FORALL_CONV th) in
       qspec_then`p1`mp_tac th >>
       qspec_then`p2`mp_tac th end)
  \\ Cases_on`run_policy p1 k o'`
  \\ Cases_on`run_policy p2 k o'`
  \\ simp[] \\ ntac 2 strip_tac
  \\ fs[weaklyExtensional_def]
  \\ qmatch_assum_abbrev_tac`u1 + δ ≥ u2`
  \\ `u2 - u1 ≤ δ` by ( srw_tac[realSimps.REAL_ARITH_ss][] )
  \\ `∀p. hist (fill p s) = fill p s ::: hist (step (fill p s))`
  by ( simp[hist_def,LUNFOLD_THM] )
  \\ simp[]
  \\ qmatch_abbrev_tac`u (fill cp1 s ::: h1) + _ ≥ u (fill cp2 s ::: h2)`
  \\ `u (fill cp2 s ::: h2) - u (fill cp1 s ::: h1) =
      u (fill cp1 s ::: h2) - u (fill cp1 s ::: h1)`
  by metis_tac[]
  \\ qmatch_assum_abbrev_tac`_ = rhs`
  \\ `0 ≤ discount u` by metis_tac[discount_not_negative]
  \\ `rhs ≤ discount u * δ`
  by (
    simp[Abbr`rhs`,Abbr`u2`,Abbr`u1`]
    \\ qmatch_abbrev_tac`a - b ≤ d * _`
    \\ qmatch_assum_abbrev_tac`e ≤ δ`
    \\ Cases_on`0 < e`
    >- (
      `a - b ≤ d * e` suffices_by
        metis_tac[realTheory.REAL_LE_LMUL_IMP,realTheory.REAL_LE_TRANS]
      \\ simp[GSYM realTheory.REAL_LE_LDIV_EQ]
      \\ simp[Abbr`d`,discount_def]
      \\ match_mp_tac (MP_CANON realTheory.REAL_SUP_UBOUND)
      \\ conj_tac
      >- (
        simp[UNCURRY,PULL_EXISTS,FORALL_PROD]
        \\ fs[discount_exists_def]
        \\ simp[EXISTS_PROD]
        \\ metis_tac[])
      \\ simp[UNCURRY]
      \\ simp[EXISTS_PROD]
      \\ simp[Abbr`a`,Abbr`b`,Abbr`e`]
      \\ metis_tac[realTheory.REAL_LT_REFL,realTheory.REAL_SUB_0] )
    \\ `0 ≤ d * δ` by metis_tac[realTheory.REAL_LE_MUL]
    \\ `a - b ≤ 0` suffices_by metis_tac[realTheory.REAL_LE_TRANS]
    \\ ONCE_REWRITE_TAC[GSYM realTheory.REAL_LE_NEG]
    \\ REWRITE_TAC[realTheory.REAL_NEG_SUB]
    \\ simp[realTheory.REAL_SUB_LE]
    \\ fs[utilityfn_def,Abbr`a`,Abbr`b`]
    \\ first_x_assum match_mp_tac
    \\ fs[Abbr`e`,realTheory.REAL_NOT_LT]
    \\ ONCE_REWRITE_TAC[GSYM realTheory.REAL_SUB_LE]
    \\ ONCE_REWRITE_TAC[GSYM realTheory.REAL_LE_NEG]
    \\ REWRITE_TAC[realTheory.REAL_NEG_SUB]
    \\ simp[] )
  \\ qmatch_abbrev_tac`x + y ≥ z`
  \\ `rhs = z - x`
  by ( simp[Abbr`z`,Abbr`x`,Abbr`rhs`] )
  \\ simp[realTheory.real_ge]
  \\ metis_tac[realTheory.REAL_LE_SUB_RADD,realTheory.REAL_ADD_SYM]);

val wf_game_def = Define`
  wf_game (S,u) ⇔
    (∀s. s ∈ S ⇒ wf_state_with_hole s) ∧
    (∃k. ∀s. s ∈ S ⇒ (get_focal_robot s).processor = k) ∧
    utilityfn u ∧ weaklyExtensional u ∧ discount_exists u`;

val get_game_clock_def = Define`
  get_game_clock S =
    @k. ∀s. s ∈ S ⇒ (get_focal_robot s).processor = k`;

val lemmaB = Q.store_thm("lemmaB",
  `∀a l. canupdateh S c ∧ wf_game (S,u)
   ⇒
     (∀o'.
       dominates' a l (updateh S c o',u)
         (run_policy p1 (get_game_clock S) o')
         (run_policy p2 (get_game_clock S) o'))
     ⇒
     dominates a (next l) (S,u) (c,p1) (c,p2)`,
  Cases
  \\ reverse Cases
  >- (
    simp[dominates'_def,next_def,dominates_def,ADD1,wf_game_def]
    \\ rw[]
    \\ qspec_then`0`mp_tac lemmaA
    \\ simp[Once(GSYM AND_IMP_INTRO)]
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[]
    \\ simp[PULL_FORALL]
    \\ simp[realTheory.real_ge]
    \\ disch_then (match_mp_tac o MP_CANON)
    \\ simp[] \\ fs[IN_DEF]
    \\ rw[]
    \\ `get_game_clock S = (get_focal_robot s').processor`
    by (
      simp[get_game_clock_def,IN_DEF]
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ rw[]
      \\ fs[updateh_def]
      \\ metis_tac[steph_focal_clock,IN_DEF] )
    \\ fs[] )
  \\ strip_tac
  \\ simp[dominates'_def,next_def,dominates_def]
  \\ strip_tac
  \\ Cases
  >- (
    simp[] \\ rw[]
    \\ fs[wf_game_def,utilityfn_def]
    \\ qmatch_abbrev_tac`u a ≤ u b + 1`
    \\ `u a ≤ 1` by metis_tac[]
    \\ `1 ≤ u b + 1` suffices_by metis_tac[realTheory.REAL_LE_TRANS]
    \\ ONCE_REWRITE_TAC[realTheory.REAL_ADD_COMM]
    \\ simp[realTheory.REAL_LE_ADDR] )
  \\ rw[]
  \\ first_x_assum drule
  \\ strip_tac
  \\ drule (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]lemmaA)
  \\ fs[wf_game_def]
  \\ disch_then drule
  \\ simp[]
  \\ simp[realTheory.pow]
  \\ disch_then(qspec_then`discount u pow n`mp_tac)
  \\ simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    match_mp_tac realTheory.POW_POS
    \\ match_mp_tac discount_not_negative
    \\ simp[] )
  \\ simp[PULL_FORALL,realTheory.real_ge]
  \\ disch_then (match_mp_tac o MP_CANON)
  \\ fs[IN_DEF]
  \\ rw[]
  \\ `get_game_clock S = (get_focal_robot s').processor`
  by (
    simp[get_game_clock_def,IN_DEF]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[]
    \\ fs[updateh_def]
    \\ metis_tac[steph_focal_clock,IN_DEF] )
  \\ fs[] );

val no_ffi_op_def = Define`
  (no_ffi_op (FFI n) ⇔ (n ≠ 2)) ∧
  (no_ffi_op _ ⇔ T)`;
val _ = export_rewrites["no_ffi_op_def"];

val no_ffi_def = tDefine"no_ffi"`
  (no_ffi (Raise e) ⇔ no_ffi e) ∧
  (no_ffi (Handle e pes) ⇔ no_ffi e ∧ EVERY no_ffi (MAP SND pes)) ∧
  (no_ffi (Lit _) ⇔ T) ∧
  (no_ffi (Con _ es) ⇔ EVERY no_ffi es) ∧
  (no_ffi (Var _) ⇔ T) ∧
  (no_ffi (Fun _ e) ⇔ no_ffi e) ∧
  (no_ffi (App op es) ⇔ no_ffi_op op ∧ EVERY no_ffi es) ∧
  (no_ffi (Log _ e1 e2) ⇔ no_ffi e1 ∧ no_ffi e2) ∧
  (no_ffi (If e1 e2 e3) ⇔ no_ffi e1 ∧ no_ffi e2 ∧ no_ffi e3) ∧
  (no_ffi (Mat e pes) ⇔ no_ffi e ∧ EVERY no_ffi (MAP SND pes)) ∧
  (no_ffi (Let _ e1 e2) ⇔ no_ffi e1 ∧ no_ffi e2) ∧
  (no_ffi (Letrec funs e) ⇔ EVERY no_ffi (MAP (SND o SND) funs) ∧ no_ffi e)`
(WF_REL_TAC`measure exp_size`
 \\ simp[astTheory.exp_size_def]
 \\ rpt conj_tac
 \\ gen_tac \\ Induct \\ simp[astTheory.exp_size_def]
 \\ qx_gen_tac `p`
 \\ TRY (PairCases_on`p`) \\ fs[]
 \\ rw[] \\ res_tac \\ simp[astTheory.exp_size_def]);
val no_ffi_def = save_thm("no_ffi_def",no_ffi_def |> REWRITE_RULE[ETA_AX])
val _ = export_rewrites["no_ffi_def"];

(* TODO: constrain thy to be an extension of the theory set up by the Botworld preamble *)

val sv_thm = Q.store_thm("sv_thm",
  `wf_game (S,u) ∧
   canupdateh S c ∧
   typeof Stm' = Fun observation_ty (Fun state_with_hole_ty Bool) ∧
   typeof utm = utilityfn_ty ∧
   no_ffi σ ∧
   (∀o' cp' cp''.
     (thy,[]) |- mk_target_concl o' cp' cp'' l Stm' utm ⇒
       dominates' a l (updateh S c o',u) cp' cp'')
   ⇒
   dominates a (next l) (S,u) (c, sv l Stm' utm p σ) (c,p)`,
  qpat_abbrev_tac`psv = sv _ _ _ _ _`
  \\ qpat_abbrev_tac`S' = updateh _ _`
  \\ strip_tac
  \\ match_mp_tac (MP_CANON lemmaB)
  \\ conj_tac >- simp[]
  \\ gen_tac \\ simp[]
  \\ qpat_abbrev_tac`ck = get_game_clock S`
  \\ qpat_assum`∀x. _`mp_tac
  \\ qho_match_abbrev_tac`(∀o' cp' cp''. thm o' cp' cp'' ⇒ (_ o' cp' cp'')) ⇒ _`
  \\ simp[] \\ strip_tac
  \\ `run_policy psv ck o' = run_policy p ck o' ∨
      thm o' (run_policy psv ck o') (run_policy p ck o')`
  by ( cheat (* "by inspection" *))
  >- (
    simp[]
    \\ match_mp_tac dominates'_refl
    \\ fs[wf_game_def] )
  \\ first_x_assum match_mp_tac
  \\ simp[]);

(* TODO:

Benja:  "let's say you have a program P which calls the inner HOL kernel through the module interface. if you initialize the inner HOL kernel with a context ctxt, and then do arbitrary stuff, and then end up with a thm value whose conclusion is X, such that X is syntactically valid in ctxt, then ctxt |- X"
hm
or:
 me:  some extension of ctxt
oh
you had the "syntactically valid" bit - sorry
hmm, we have not proved conservativity though
 Benja:  "then there is some definitional extension ctxt' of ctxt such that ctxt |- X"
hm
 me:  yes, that is easier
(ctxt' though)
 Benja:  right
 me:  we have conservativity at the semantic level
just not syntactically (like what your first version implied)
 Benja:  ah, good I think. can you say what the theorem about conservativity is?
like, ctxt' |= X ==> ctxt |= X?
 me:  yes
provided X is good in ctxt
 Benja:  right
 me:  and ctxt' extends ctxt
 Benja:  that should be enough
yep
 me:  so, this theorem you've described sounds like a good way to encapsulate this
it's a subproject of its own to prove that
but it's plausible that something like it is true, based on our work so far
 Benja:  right
 me:  indeed stating the theorem as we need it for our project could be a good way of setting a target for what the CakeML/Candle project needs to achieve
 Benja:  agree!
 *)

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
