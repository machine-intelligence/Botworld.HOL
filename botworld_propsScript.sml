open preamble indexedListsTheory match_goal simpleSexpTheory
     botworldTheory
     botworld_dataTheory
     botworld_serialiseTheory
     botworld_svTheory
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
  \\ rename1`FLOOKUP x k`
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
  `(SND (updateInventory sq nm y)).memory = (FST y).memory ∧
   (SND (updateInventory sq nm y)).processor = (FST y).processor ∧
   (SND (updateInventory sq nm y)).frame = (FST y).frame`,
  Cases_on`y` \\ rw[updateInventory_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]);

val FST_runMachine = Q.store_thm("FST_runMachine[simp]",
  `FST (runMachine ev nmra) = FST nmra`,
  PairCases_on`nmra`\\rw[runMachine_def,UNCURRY]);

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
    \\ qpat_x_assum`Abbrev _`(strip_assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
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
   ((FST(SND nra)).command) = Move dir ∧
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
  \\ qpat_x_assum`MEM (nm,ra1) _`assume_tac
  \\ disch_then drule
  \\ rw[]
  >- (
    rpt(qpat_x_assum`MEM _ _.robotActions`mp_tac)
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
  \\ rpt(qpat_x_assum`MEM _ _.robotActions`mp_tac)
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
    \\ qpat_x_assum`MovedIn _ = _`(assume_tac o SYM)
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
    \\ simp[computeSquare_def,MEM_MAPi,PULL_EXISTS,MEM_GENLIST,MEM_FILTER,MEM_MAP]
    \\ reverse(rw[])
    \\ TRY pairarg_tac \\ fs[]
    \\ rw[]
    \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
    \\ simp[GSYM ADD1]
    \\ match_mp_tac prim_recTheory.LESS_SUC
    \\ first_x_assum match_mp_tac
    \\ rw[]
    \\ fs[event_def]
    >- (
      asm_exists_tac
      \\ fs[MAP2_MAP,MAP2_same,ZIP_MAP]
      \\ fs[MEM_MAP,UNCURRY,EXISTS_PROD]
      \\ fs[localActions_def,MEM_MAP,UNCURRY] \\ rw[]
      \\ metis_tac[PAIR,FST,FST_updateInventory])
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
    \\ simp[ALL_DISTINCT_APPEND,MEM_GENLIST,ALL_DISTINCT_GENLIST,MEM_MAP,MEM_FILTER,PULL_EXISTS,MEM_MAPi]
    \\ simp[combinTheory.o_DEF,ETA_AX]
    \\ conj_tac
    >- (
      match_mp_tac ALL_DISTINCT_MAP_FILTER
      \\ fs[computeEvents_def,FLOOKUP_FMAP_MAP2]
      \\ simp[event_def,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX,ZIP_MAP]
      \\ simp[localActions_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ fs[PULL_EXISTS]
      \\ simp[ALL_DISTINCT_APPEND]
      \\ conj_tac >- metis_tac[]
      \\ simp[MEM_MAP,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]
      \\ simp[MAP_FLAT,MAP_GENLIST,o_DEF]
      \\ conj_tac
      >- (
        simp[ALL_DISTINCT_FLAT,MEM_GENLIST,PULL_EXISTS,ALL_DISTINCT_FILTER_GENLIST]
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
          \\ rpt(qpat_x_assum`SOME _ = _`(assume_tac o SYM))
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
          \\ rpt(qpat_x_assum`SOME _ = _`(assume_tac o SYM))
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
        \\ qpat_x_assum`FLOOKUP _ (EL d1 _) = _`assume_tac
        \\ asm_exists_tac \\ simp[]
        \\ asm_exists_tac \\ simp[]
        \\ rveq \\ fs[MEM_MAP,MEM_FILTER]
        \\ first_assum(part_match_exists_tac(el 2 o strip_conj) o concl)
        \\ fs[]
        \\ spose_not_then strip_assume_tac \\ rveq
        \\ last_x_assum drule
        \\ qpat_x_assum`FLOOKUP _ (EL d2 _) = _`assume_tac
        \\ disch_then drule
        \\ simp[GSYM NULL_EQ, NOT_NULL_MEM]
        \\ reverse conj_tac >- metis_tac[]
        \\ `d1 ≠ d2` suffices_by metis_tac[ALL_DISTINCT_neighbour_coords,EL_ALL_DISTINCT_EL_EQ,LESS_TRANS]
        \\ spose_not_then strip_assume_tac \\ fs[])
      \\ rw[]
      \\ spose_not_then strip_assume_tac
      \\ Cases_on`EL dir (neighbours s.grid k)`\\fs[incomingFrom_def]
      \\ rfs[neighbours_def,EL_MAP]
      \\ fs[MEM_MAP,MEM_FILTER,UNCURRY]
      \\ rveq \\ fs[]
      \\ last_x_assum drule
      \\ qpat_x_assum`FLOOKUP _ k = _`assume_tac
      \\ disch_then drule
      \\ simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS]
      \\ metis_tac[NOT_MEM_neighbour_coords,MEM_EL])
    \\ conj_tac >- ( simp[EL_ALL_DISTINCT_EL_EQ] )
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
    \\ pairarg_tac \\ fs[]
    \\ asm_exists_tac \\ fs[MEM_MAPi])
  \\ fs[step_def,FLOOKUP_FMAP_MAP2]
  \\ simp[computeSquare_def,MAP_MAP_o,MAP_GENLIST,o_DEF,ETA_AX]
  \\ REWRITE_TAC[CONJ_ASSOC]
  \\ reverse conj_tac
  >- (
    simp[IN_DISJOINT,MEM_MAPi]
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
      \\ qpat_x_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_x_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ disch_then drule
      \\ simp[]
      \\ qpat_x_assum`FLOOKUP _ c2 = _`assume_tac
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
      \\ qpat_x_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_x_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ qpat_x_assum`FLOOKUP _ c1 = _`assume_tac
      \\ disch_then drule
      \\ simp[]
      \\ qpat_x_assum`FLOOKUP _ c2 = _`assume_tac
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
      \\ qpat_x_assum`MEM (nm,a1) _`mp_tac
      \\ qmatch_assum_rename_tac`MEM (nm,a2) _`
      \\ strip_tac
      \\ drule (GEN_ALL wf_state_event_same_name)
      \\ disch_then drule
      \\ qpat_x_assum`MEM (nm,a2) _`assume_tac
      \\ disch_then drule
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS,GSYM CONJ_ASSOC]))
      \\ qpat_x_assum`FLOOKUP _ c1 = _`assume_tac
      \\ disch_then drule
      \\ simp[]
      \\ qpat_x_assum`FLOOKUP _ c2 = _`assume_tac
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
    \\ qpat_x_assum`FLOOKUP _ c1 = _`assume_tac
    \\ drule (GEN_ALL event_name_in_grid)
    \\ disch_then drule
    \\ rw[]
    >- (
      rw[MEM_MAP,MEM_MAPi]
      \\ spose_not_then strip_assume_tac
      \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,MEM_MAP,MEM_MAPi]
      \\ first_x_assum drule
      \\ disch_then drule \\ simp[])
    >- (
      rw[MEM_MAP]
      \\ spose_not_then strip_assume_tac
      \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,MEM_MAPi,MEM_MAP]
      \\ first_x_assum drule
      \\ disch_then drule
      \\ simp[]))
  \\ rw[]
  \\ drule (GEN_ALL event_name_in_grid)
  \\ disch_then drule
  \\ fs[MEM_MAPi]
  \\ rw[MEM_MAP]
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ fs[IN_FRANGE_FLOOKUP,MEM_MAP,PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ qpat_assum`name _ _ _ = _`(assume_tac o SYM)
  \\ fs[]);

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
    rw[event_def,MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX,ZIP_MAP]
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
        \\ qpat_x_assum`FLOOKUP _ (_ _) = _`assume_tac
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
    \\ qpat_x_assum`FLOOKUP _ k = _`assume_tac
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
  rw[steph_def,RES_FORALL_THM]
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
  \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
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

val if_focal_eta  = Q.store_thm("if_focal_eta",
  `if_focal fnm f = λ(nm,r). (nm, if nm = fnm then f r else r)`,
  rw[FUN_EQ_THM,if_focal_def,FORALL_PROD])

val get_robot_by_name_fill = Q.store_thm("get_robot_by_name_fill",
  `wf_state_with_hole s ⇒
   get_robot_by_name (fill f s) s.focal_name =
   f (get_robot_by_name s.state s.focal_name)`,
  rw[]
  \\ `wf_state (fill f s)`
  by (
    match_mp_tac wf_state_fill
    \\ fs[wf_state_with_hole_def] )
  \\ drule (GEN_ALL robots_by_name_sing)
  \\ disch_then(qspec_then`s.focal_name`mp_tac)
  \\ simp[GSYM get_focal_robot_def]
  \\ simp[get_robot_by_name_def]
  \\ strip_tac
  >- (
    fs[robots_by_name_def,EXTENSION,FRANGE_fill]
    \\ fs[wf_state_with_hole_def]
    \\ Cases_on`ALOOKUP (sq with robots updated_by MAP (if_focal s.focal_name f)).robots s.focal_name`
    >- (
      imp_res_tac ALOOKUP_FAILS
      \\ fs[MEM_MAP,EXISTS_PROD,if_focal_def] )
    \\ qmatch_assum_abbrev_tac`ALOOKUP sq'.robots _ = _`
    \\ first_x_assum(qspecl_then[`x`,`sq'`]mp_tac)
    \\ simp[square_component_equality,Abbr`sq'`]
    \\ metis_tac[] )
  \\ rw[]
  \\ drule get_focal_robot_sing
  \\ fs[robots_by_name_def,EXTENSION]
  \\ rw[]
  \\ first_x_assum(qspec_then`get_focal_robot s`mp_tac)
  \\ first_x_assum(qspec_then`r`mp_tac)
  \\ rw[]
  \\ fs[FRANGE_fill]
  \\ rw[] \\ fs[]
  \\ fs[ALOOKUP_MAP_gen,if_focal_eta] \\ rw[]
  \\ `wf_state s.state` by fs[wf_state_with_hole_def]
  \\ drule same_name_same_square
  \\ disch_then(qspecl_then[`sq'`,`x`,`s.focal_name`]mp_tac)
  \\ imp_res_tac ALOOKUP_MEM
  \\ simp[MEM_MAP,EXISTS_PROD,PULL_EXISTS]
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[] \\ fs[]);

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
    \\ fs[MEM_MAP,MEM_MAPi]
    \\ rw[]
    \\ fs[runMachine_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rw[]
    \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ qmatch_assum_abbrev_tac`MEM (nm,r) sq.robots`
    \\ `nm.built_step = s.time_step` by simp[Abbr`nm`]
    \\ metis_tac[prim_recTheory.LESS_REFL,MEM_MAP,FST] )
  \\ rw[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,MEM_FILTER]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ fs[runMachine_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ rator_x_assum`ALOOKUP`kall_tac
  \\ drule (GEN_ALL event_name_in_grid)
  \\ disch_then drule
  \\ rw[] >- (
    drule same_name_same_square
    \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ disch_then drule
    \\ qpat_x_assum`_ = SOME sq`assume_tac
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ impl_tac >- metis_tac[]
    \\ strip_tac \\ rveq
    \\ drule grid_injective
    \\ disch_then drule
    \\ qpat_x_assum`_ _ k' = _`assume_tac
    \\ disch_then drule
    \\ simp[NOT_NULL_MEM]
    \\ impl_tac >- metis_tac[]
    \\ strip_tac \\ rveq
    \\ fs[]
    \\ reverse(fs[event_def])
    >- (
      fs[MEM_FLAT,MEM_GENLIST,MEM_MAPi] \\ rw[]
      \\ imp_res_tac incomingFrom_MovedIn
      \\ fs[] )
    \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,o_DEF,UNCURRY,MEM_MAP,MEM_MAPi,ZIP_MAP]
    \\ rw[]
    \\ fs[localActions_def,MEM_MAP,UNCURRY]
    \\ rw[] \\ fs[]
    \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ metis_tac[ALL_DISTINCT_MAP_FST,PAIR,PAIR_EQ] )
  \\ Cases_on`a` \\ fs[]
  \\ drule (GEN_ALL event_MovedIn_MovedOut)
  \\ simp[computeEvents_def,FLOOKUP_FMAP_MAP2,PULL_EXISTS]
  \\ qpat_x_assum`_ = SOME sq'`assume_tac
  \\ disch_then drule \\ simp[]
  \\ strip_tac
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ qpat_x_assum`MEM (_,_,MovedIn _) _`kall_tac
  \\ reverse(fs[event_def])
  >- (
    fs[MEM_FLAT,MEM_GENLIST] \\ rw[]
    \\ imp_res_tac incomingFrom_MovedIn
    \\ fs[] )
  \\ fs[MAP2_MAP,MAP2_same,PAIR_MAP_COMPOSE,o_DEF,UNCURRY,MEM_MAP,ZIP_MAP]
  \\ rw[]
  \\ fs[localActions_def,MEM_MAP,UNCURRY]
  \\ rw[] \\ fs[]
  \\ drule same_name_same_square
  \\ simp[IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ disch_then drule
  \\ qpat_x_assum`_ = SOME sq`assume_tac
  \\ disch_then drule
  \\ simp[MEM_MAP,PULL_EXISTS]
  \\ disch_then drule
  \\ simp[AND_IMP_INTRO]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ disch_then drule
  \\ rw[] \\ fs[]
  \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
  \\ metis_tac[ALL_DISTINCT_MAP_FST,PAIR,PAIR_EQ] );

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

val event_update_robots_def = Define`
  event_update_robots nm f =
    event_robotActions_fupd
      (MAP (if_focal nm (f ## I)))`;

val SND_if_focal_with_memory_command = Q.store_thm("SND_if_focal_with_memory_command[simp]",
  `(SND (if_focal nm (robot_memory_fupd p) r)).command = (SND r).command`,
  Cases_on`r` \\ rw[if_focal_def]);

val SND_if_focal_with_memory_inventory = Q.store_thm("SND_if_focal_with_memory_inventory[simp]",
  `(SND (if_focal nm (robot_memory_fupd p) r)).inventory = (SND r).inventory`,
  Cases_on`r` \\ rw[if_focal_def]);

val SND_if_focal_with_memory_canLift = Q.store_thm("SND_if_focal_with_memory_canLift[simp]",
  `canLift (SND (if_focal nm (robot_memory_fupd p) x)) = canLift (SND x)`,
  Cases_on`x` \\ rw[if_focal_def,FUN_EQ_THM,canLift_def]);

val LENGTH_FILTER_requests_with_memory = Q.store_thm("LENGTH_FILTER_requests_with_memory",
  `LENGTH (FILTER (requests x y o SND o if_focal nm (robot_memory_fupd p)) ls) =
   LENGTH (FILTER (requests x y o SND) ls)`,
  Induct_on`ls` \\ rw[requests_def]);

val contested_with_memory = Q.store_thm("contested_with_memory[simp]",
  `contested (update_robots nm (robot_memory_fupd p) sq) = contested sq`,
  rw[FUN_EQ_THM,contested_def,update_robots_def,MAP_MAP_o]
  \\ simp[FILTER_MAP,LENGTH_FILTER_requests_with_memory]);

val usedItem_with_memory = Q.store_thm("usedItem_with_memory",
  `usedItem
    (MAP (SND o SND)
      (localActions (update_robots nm (robot_memory_fupd p) sq)
        (neighbours (update_robots nm (robot_memory_fupd p) o_f g) k))) =
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
     (localActions (update_robots nm (robot_memory_fupd p) x)
       (neighbours (update_robots nm (robot_memory_fupd p) o_f g) k)) =
   MAP (dropItem o SND) (localActions x (neighbours g k))`,
  rw[localActions_def,MAP_MAP_o,o_DEF,UNCURRY]
  \\ rw[update_robots_def,MAP_MAP_o,o_DEF,MAP_EQ_f]
  \\ rw[dropItem_def]
  \\ simp[act_def]
  \\ every_case_tac \\ fs[]);

val fled_with_memory = Q.store_thm("fled_with_memory",
  `fled (neighbours (robots_fupd (MAP (if_focal nm (robot_memory_fupd p))) o_f g) k) =
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
        (localActions (update_robots nm (robot_memory_fupd p) x)
          (neighbours (update_robots nm (robot_memory_fupd p) o_f g) k))) ⇔
   MEM (Destroyed nm')
     (MAP (SND o SND)
        (localActions x (neighbours g k)))`,
  rw[MEM_MAP,localActions_def,PULL_EXISTS,update_robots_def,UNCURRY]
  \\ rw[EQ_IMP_THM]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ asm_exists_tac \\ simp[]
  \\ qpat_x_assum`_ = _`(mp_tac o SYM)
  \\ simp[act_def]
  \\ every_case_tac \\ fs[]
  \\ fs[MAP_MAP_o,o_DEF,fled_with_memory]
  \\ fs[ALOOKUP_MAP_gen,if_focal_eta] \\ rveq \\ fs[]
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ every_case_tac \\ fs[]);

val MAP_robot_command_o_SND_update_robots_with_memory = Q.store_thm("MAP_robot_command_o_SND_update_robots_with_memory[simp]",
  `MAP (robot_command o SND) (update_robots nm (robot_memory_fupd p) sq).robots =
   MAP (robot_command o SND) sq.robots`,
  rw[update_robots_def,MAP_MAP_o,o_DEF,MAP_EQ_f]);

val FILTER_isBuilt_localActions_with_memory = Q.store_thm("FILTER_isBuilt_localActions_with_memory",
  `FILTER isBuilt
     (MAP (SND o SND)
        (localActions (update_robots nm (robot_memory_fupd p) x)
          (neighbours (update_robots nm (robot_memory_fupd p) o_f g) k))) =
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
  `canLift (r with memory updated_by p) = canLift r`,
  rw[canLift_def,FUN_EQ_THM]);

val fled_with_memory = Q.store_thm("fled_with_memory[simp]",
  `fled (neighbours (update_robots n (robot_memory_fupd p) o_f g) k) c =
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
   act (update_robots nm (robot_memory_fupd p) sq)
       (neighbours (update_robots nm (robot_memory_fupd p) o_f g) k)
       (if x = nm then r with memory updated_by p else r) =
   act sq (neighbours g k) r`,
  rw[act_def]
  \\ every_case_tac \\ fs[]
  \\ TRY (fs[LENGTH_neighbours] \\  NO_TAC)
  \\ rveq \\ fs[]
  \\ fs[neighbours_def,update_robots_def,EL_MAP,FLOOKUP_o_f]
  \\ every_case_tac \\ fs[]);

val _ = overload_on("same_shape",``λm1 m2. LIST_REL (λr1 r2. LENGTH r1 = LENGTH r2) m1 m2``);

val computeEvents_update_robots_with_memory = Q.store_thm("computeEvents_update_robots_with_memory",
  `wf_state s ∧
   LIST_REL (λr1 r2. LENGTH r1 = LENGTH r2) (get_robot_by_name s nm).memory (p (get_robot_by_name s nm).memory) ∧
   FEVERY
    (λ(_,ev). EVERY (λa. ∀r. a ≠ Inspected nm r) (MAP (SND o SND) ev.robotActions))
    (computeEvents s.grid)
   ⇒
   computeEvents (update_robots nm (robot_memory_fupd p) o_f s.grid) =
   event_update_robots nm (robot_memory_fupd p) o_f (computeEvents s.grid)`,
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
  \\ conj_tac >- (
    EVAL_TAC \\ rw[]
    \\ drule robots_by_name_sing
    \\ fs[get_robot_by_name_def]
    \\ strip_tac
    >- (
      fs[robots_by_name_def,EXTENSION,IN_FRANGE_FLOOKUP]
      \\ metis_tac[ALOOKUP_FAILS,option_CASES,NOT_SOME_NONE] )
    \\ fs[robots_by_name_def,EXTENSION,IN_FRANGE_FLOOKUP]
    \\ first_x_assum(qspec_then`r`mp_tac) \\ simp[]
    \\ strip_tac
    \\ drule same_name_same_square
    \\ fs[IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ match_tac([mg.a"1"`_`,mg.a"2"`_`],(fn(a,t) =>
         disch_then(drule_thm(a"1")) >>
         simp[GSYM AND_IMP_INTRO] >>
         disch_then(drule_thm(a"2"))))
    \\ simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD]
    \\ imp_res_tac ALOOKUP_MEM
    \\ disch_then drule \\ disch_then drule \\ rw[]
    \\ fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS] \\ rw[]
    \\ res_tac
    \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM \\ fs[]
    \\ fs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP])
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

(*
val encoded_ffi_def = Define`
  encoded_ffi ffi1 ffi2 ⇔
    encode_observation ffi1.bot_input =
    encode_observation ffi2.bot_input ∧
    encode_output ffi1.bot_output =
    encode_output ffi2.bot_output`;
*)

val botworld_call_FFI_invariant = Q.store_thm("botworld_call_FFI_invariant",
  `call_FFI_invariant botworld_oracle $=`,
  rw[call_FFI_invariant_def,ffiTheory.call_FFI_def]
  \\ pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
  \\ fs[ffiTheory.ffi_state_component_equality]
  \\ rfs[]
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]);
  (*
  \\ fs[botworld_oracle_def]
  \\ every_case_tac
  \\ fs[botworld_read_def,
        botworld_write_def,
        botworld_get_output_length_def,
        botworld_get_input_length_def,
        botworld_read_output_def]
  \\ every_case_tac \\ fs[] \\ rfs[] \\ rveq \\ fs[]);
*)

val ffi_from_observation_with_memory = Q.store_thm("ffi_from_observation_with_memory",
  `obs1 = observation nm x v ∧ obs2 = observation nm x' v ∧
   x' = x with robotActions updated_by (MAP (if_focal nm' (memory_fupd (K p) ## I)))
   ⇒
   ffi_state_rel botworld_oracle $=
    (ffi_from_observation obs1 m)
    (ffi_from_observation obs2 m)`,
  rw[ffi_state_rel_def,ffiTheory.initial_ffi_state_def,ffi_from_observation_def]
  \\ simp[encode_bytes_def]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[observationsexp_def]
  \\ simp[eventsexp_def]
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,if_focal_def]
  \\ rw[]
  \\ simp[robotsexp_def]);

val evaluate_botworld_prog_ffi =
  MATCH_MP evaluate_prog_ffi_extensional botworld_call_FFI_invariant

val preamble_env_ffi = Q.store_thm("preamble_env_ffi",
  `preamble_env ffi = (st,env) ⇒ st.ffi = ffi`,
  cheat);

val preamble_env_ignores_ffi = Q.store_thm("preamble_env_ignores_ffi",
  `preamble_env ffi1 = (st,env1) ∧
   preamble_env ffi2 = (st',env2)
   ⇒
   st' = st with ffi := st'.ffi ∧ env1 = env2`,
  cheat);

val run_policy_ffi_with_memory = Q.store_thm("run_policy_ffi_with_memory",
  `x' = x with robotActions updated_by (MAP (if_focal nm' (memory_fupd (K p') ## I))) ⇒
   run_policy (observation nm x' p) = run_policy (observation nm x p)`,
  fs[run_policy_def,FUN_EQ_THM] \\ rpt strip_tac
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac preamble_env_ffi
  \\ match_tac([mg.a"1"`_`,mg.a"2"`_`],fn(a,t)=>
       preamble_env_ignores_ffi
       |> REWRITE_RULE[GSYM AND_IMP_INTRO]
       |> GEN_ALL
       |> INST_TYPE[beta|->``:word8 list list``]
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
    \\ simp[EXISTS_PROD]
    \\ metis_tac[])
  \\ simp[ffi_state_rel_def]);

val runMachine_ffi_with_memory = Q.store_thm("runMachine_ffi_with_memory",
  `x' = x with robotActions updated_by (MAP (if_focal nm (memory_fupd (K m) ## I))) ⇒
   runMachine x' = runMachine x`,
  strip_tac \\ simp[FUN_EQ_THM] \\ qx_gen_tac`z` \\ PairCases_on`z`
  \\ simp[runMachine_def]
  \\ imp_res_tac run_policy_ffi_with_memory
  \\ rveq \\ simp[]);

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

val fill_with_policy_split = Q.store_thm("fill_with_policy_split",
  `fill (with_policy (c,p)) s =
   fill (memory_fupd (K p))
   (s with state := fill (command_fupd (K c)) s)`,
  rw[fill_def,state_with_hole_component_equality,state_component_equality]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[square_component_equality,MAP_MAP_o,o_DEF]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM,FORALL_PROD,if_focal_def,with_policy_def]);

val steph_fill_step = Q.store_thm("steph_fill_step",
  `wf_state_with_hole s ∧
   steph c s = SOME (obs,s') ∧
   run_policy obs (get_focal_robot s).processor m = (c',m') ∧
   LIST_REL (λr1 r2. LENGTH r1 = LENGTH r2) (get_focal_robot s).memory m
   ⇒
   step (fill (with_policy (c,m)) s) = fill (with_policy (c',m')) s'`,
  rw[]
  \\ imp_res_tac steph_focal_clock
  \\ pop_assum (assume_tac o SYM)
  \\ fs[steph_def,RES_FORALL_THM]
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
  \\ qmatch_asmsub_abbrev_tac`_ ∈ FRANGE events ⇒ _`
  \\ qmatch_assum_abbrev_tac`Abbrev(_ = _ s'.grid)`
  \\ simp[state_component_equality]
  \\ simp[step_def]
  \\ simp[fill_def]
  \\ simp[update_robots_intro]
  \\ drule (GEN_ALL computeEvents_update_robots_with_memory)
  \\ disch_then(qspecl_then[`K m`,`s.focal_name`]mp_tac)
  \\ impl_tac
  >- (
    fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,EVERY_MEM,FEVERY_ALL_FLOOKUP]
    \\ conj_tac
    >- (
      simp[Abbr`s'`,get_robot_by_name_fill]
      \\ fs[get_focal_robot_def])
    \\ metis_tac[] )
  \\ disch_then SUBST1_TAC
  \\ simp[FMAP_MAP2_o_f]
  \\ simp[o_f_FMAP_MAP2]
  \\ simp[fmap_eq_flookup]
  \\ simp[FLOOKUP_FMAP_MAP2]
  \\ gen_tac
  \\ rename1`FLOOKUP events k`
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
      ONCE_REWRITE_TAC[GSYM PAIR]
      \\ simp[] \\ AP_TERM_TAC
      \\ AP_THM_TAC
      \\ match_mp_tac (GEN_ALL runMachine_ffi_with_memory)
      \\ simp[event_component_equality,MAP_EQ_f,FORALL_PROD,if_focal_def]
      \\ metis_tac[] )
    \\ simp[runMachine_def,UNCURRY,robot_component_equality]
    \\ drule (GEN_ALL same_name_same_action) \\ simp[]
    \\ disch_then drule
    \\ qpat_x_assum `_ = SOME ev` assume_tac
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
    \\ qmatch_goalsub_abbrev_tac`observation _ (x' x) _`
    \\ `run_policy (observation s.focal_name (x' x) (private a)) =
        run_policy (observation s.focal_name x (private a))`
    by (
      match_mp_tac (GEN_ALL run_policy_ffi_with_memory)
      \\ simp[Abbr`x'`,event_component_equality,MAP_EQ_f,FORALL_PROD,if_focal_def]
      \\ metis_tac[])
    \\ rfs[with_policy_def])
  \\ match_mp_tac MAPi_CONG
  \\ simp[]
  \\ simp[if_focal_eta,UNCURRY]
  \\ rpt strip_tac
  \\ IF_CASES_TAC
  >- (
    fs[wf_state_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ match1_tac(mg.ab"h"`_.time_step`,fn (a,t) => drule(a"h"))
    \\ disch_then drule
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ simp[Abbr`s'`])
  \\ simp[runMachine_def,UNCURRY,robot_component_equality]
  \\ qmatch_goalsub_abbrev_tac`observation _ x'' _`
  \\ qmatch_goalsub_abbrev_tac`observation nm x''`
  \\ REWRITE_TAC[GSYM PAIR_EQ]
  \\ AP_THM_TAC \\ AP_THM_TAC
  \\ match_mp_tac (GEN_ALL run_policy_ffi_with_memory)
  \\ unabbrev_all_tac \\ simp[event_component_equality]
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,if_focal_def]
  \\ metis_tac[]);

(* sv theorem *)

val next_def = Define`
  (next MP = MP) ∧
  (next (Trust k) = Trust (k+1))`;

val canupdateh_def = Define`
  canupdateh S c =
    ∀s. s ∈ S ⇒
      wf_state_with_hole s ∧ IS_SOME(steph c s)`;

val updateh_def = Define`
  updateh S c o' s' ⇔ ∃s. s ∈ S ∧ steph c s = SOME (o',s')`;

val shape_ok_def = Define`
  shape_ok S p ⇔ ∀s. s ∈ S ⇒ same_shape (get_focal_robot s).memory p`;

val _ = Parse.hide"S";

val lemmaA = Q.store_thm("lemmaA",
  `∀δ l S u c p1 p2.
     canupdateh S c ∧
     utilityfn u ∧ weaklyExtensional u ∧ discount_exists u ∧
     0 ≤ δ ∧
     shape_ok S p1 ∧ shape_ok S p2 ∧
     (∀o' s'. updateh S c o' s' ⇒
       let k = (get_focal_robot s').processor in
       u (hist (fill (with_policy (run_policy o' k p1)) s')) + δ ≥
       u (hist (fill (with_policy (run_policy o' k p2)) s')))
     ⇒
     ∀s. s ∈ S ⇒
       u (hist (fill (with_policy (c,p1)) s)) + (discount u)*δ ≥
       u (hist (fill (with_policy (c,p2)) s))`,
  rpt gen_tac
  \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ `∃o' s'. steph c s = SOME (o',s') ∧ wf_state_with_hole s ∧
        LIST_REL (λr1 r2. LENGTH r1 = LENGTH r2) (get_focal_robot s).memory p1 ∧
        LIST_REL (λr1 r2. LENGTH r1 = LENGTH r2) (get_focal_robot s).memory p2`
  by ( fs[canupdateh_def,IS_SOME_EXISTS,EXISTS_PROD,shape_ok_def] )
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
  \\ Cases_on`run_policy o' k p1`
  \\ Cases_on`run_policy o' k p2`
  \\ simp[EQ_SYM_EQ] \\ ntac 2 strip_tac
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
  `∀a l. canupdateh S c ∧ shape_ok S p1 ∧ shape_ok S p2 ∧ wf_game (S,u)
   ⇒
     (∀o'.
       dominates' a l (updateh S c o',u)
         (run_policy o' (get_game_clock S) p1)
         (run_policy o' (get_game_clock S) p2))
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
    \\ disch_then(qspecl_then[`p1`,`p2`]mp_tac)
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

val evaluate_prog_prefix = Q.store_thm("evaluate_prog_prefix",
   `evaluate_prog st env π = (st', new_ctors, r) ⇒
    ∀ ψ. evaluate_prog st env (π ++ ψ) = case r of
                                             (Rerr e) => (st', new_ctors, Rerr e)
                                           | (Rval (new_mods,new_vals)) =>
                                              case evaluate_prog st' (extend_top_env new_mods new_vals new_ctors env) ψ of
                                                  (st'',new_ctors',r') => (st'', merge_alist_mod_env new_ctors' new_ctors,
                                                                          combine_mod_result new_mods new_vals r')`,
   cheat);

val shape_ok_sv = Q.store_thm("shape_ok_sv",
  `shape_ok S (sv l Stm utm p σ) ⇔ shape_ok S p`,
  rw[sv_def]
  \\ rw[encode_register_def]
  \\ qpat_abbrev_tac`bs = encode_bytes _ _`
  \\ Cases_on`p` \\ fs[LUPDATE_def]
  \\ rw[shape_ok_def,LENGTH_REPLICATE]);

val sv_thm = Q.store_thm("sv_thm",
  `wf_game (S,u) ∧
   canupdateh S c ∧ shape_ok S p ∧
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
  \\ conj_tac
  >- ( simp[Abbr`psv`,shape_ok_sv] )
  \\ gen_tac \\ simp[]
  \\ qpat_abbrev_tac`ck = get_game_clock S`
  \\ qpat_x_assum`∀x. _`mp_tac
  \\ qho_match_abbrev_tac`(∀o' cp' cp''. thm o' cp' cp'' ⇒ (_ o' cp' cp'')) ⇒ _`
  \\ simp[] \\ strip_tac
  \\ qmatch_goalsub_rename_tac`run_policy obs ck`
  \\ `ffi_from_observation obs psv = ffi_from_observation obs p`
  by (
    rw[ffi_from_observation_def]
    \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ `LENGTH psv = LENGTH p`
    by ( simp[Abbr`psv`,sv_def] )
    \\ rw[clear_register_def]
    >- fs[LENGTH_NIL]
    \\ `LENGTH (HD psv) = LENGTH (HD p)`
    by (
      simp[Abbr`psv`,sv_def]
      \\ qmatch_goalsub_abbrev_tac`encode_register _ _ x`
      \\ simp[encode_register_def] \\ rw[]
      \\ Cases_on`p` \\ fs[LUPDATE_def,LENGTH_REPLICATE] )
    \\ simp[]
    \\ simp[Abbr`psv`,LIST_EQ_REWRITE]
    \\ Cases \\ simp[EL_LUPDATE]
    \\ simp[GSYM LIST_EQ_REWRITE]
    \\ Cases_on`p` \\ fs[]
    \\ simp[sv_def,encode_register_def]
    \\ rw[] \\ simp[EL_LUPDATE] )
  \\ `run_policy obs ck psv = run_policy obs ck p ∨
      thm obs (run_policy obs ck psv) (run_policy obs ck p)`
  by (
    simp[run_policy_def] >> rpt (pairarg_tac >> fs[])
    >> `∃p'. read_policy psv = read_policy p ++ p'`
          by (
            rw[Abbr`psv`, sv_def]
            \\ cheat (*
                need an encode/decode register thm
                then need to assume p is big enough *)
            ) >> rveq
          >> qmatch_assum_rename_tac`evaluate_prog _ _ (_ p) = (_,r)`
          >> Cases_on`r`
          >> qmatch_assum_rename_tac`evaluate_prog _ _ (_ p) = (_,ctors,res)`
          >> imp_res_tac evaluate_prog_prefix
          >> cases_on `res` \\ fs[]
          \\ cheat )
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
      qpat_x_assum`MEM _ _`mp_tac >>
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
