open HolKernel Parse boolLib bossLib realTheory lcsymtacs
open botworld_dataTheory botworld_serialiseTheory botworld_preambleTheory
open terminationTheory

val _ = temp_tight_equality();

val _ = new_theory"botworld"

val _ = Parse.bring_to_front_overload","{Name=",",Thy="pair"};
val _ = Parse.type_abbrev("state",``:botworld_data$state``);

(* Port of Botworld to more idiomatic HOL *)

val neighbour_coords_def = Define`
  neighbour_coords ((x,y):coordinate) =
    [(x  ,y+1)
    ;(x+1,y+1)
    ;(x+1,y  )
    ;(x+1,y-1)
    ;(x  ,y-1)
    ;(x-1,y-1)
    ;(x-1,y  )
    ;(x-1,y+1)]`;

val opposite_def = Define`
  opposite d = (d + 4) MOD 8`;

val neighbours_def = Define`
  neighbours (g:grid) c = MAP (FLOOKUP g) (neighbour_coords c)`;

(* environment phase *)

val requests_def = Define`
  requests i items r =
    case r.command of
    | Lift li => li = i ∧ canLift r (EL i items)
    | Build is m => MEM i is ∧
                    EVERY (λi. i < LENGTH items) is ∧
                    IS_SOME (construct (MAP (λi. EL i items) is) m)
    | _ => F`;

val contested_def = Define`
  contested sq i ⇔
    i < LENGTH sq.items ∧
    1 < LENGTH (FILTER (requests i sq.items) (MAP SND sq.robots))`;

val fled_def = Define`
  (fled nb (Move dir) ⇔ dir < LENGTH nb ∧ IS_SOME (EL dir nb)) ∧
  (fled nb _ = F)`;

val inspectAttempts_def = Define`
  inspectAttempts intents nm =
    LENGTH (FILTER ($= (Inspect nm)) intents)`;

val inspectShielded_def = Define`
  inspectShielded intents nm inventory ⇔
    inspectAttempts intents nm ≤
    LENGTH (FILTER isInspectShield inventory)`;

val destroyAttempts_def = Define`
  destroyAttempts intents nm =
    LENGTH (FILTER ($= (Destroy nm)) intents)`;

val destroyShielded_def = Define`
  destroyShielded intents nm inventory ⇔
    destroyAttempts intents nm ≤
    LENGTH (FILTER isDestroyShield inventory)`;

val act_def = Define`
  act sq nb r =
    case r.command of
    | Move dir =>
      if dir < LENGTH nb then
        (if IS_SOME (EL dir nb) then MovedOut else MoveBlocked) dir
      else MoveBlocked dir
    | Lift i =>
      if i < LENGTH sq.items then
        if canLift r (EL i sq.items) then
          if contested sq i then GrappledOver i else Lifted i
        else CannotLift i
      else Invalid
    | Drop i =>
      if i < LENGTH r.inventory then
        Dropped i
      else Invalid
    | Inspect nm =>
      (case ALOOKUP sq.robots nm of
          NONE => Invalid
        | SOME r' => if ¬fled nb (r'.command) then
                       if ¬inspectShielded
                           (MAP (robot_command o SND) sq.robots) nm r'.inventory
                       then Inspected nm r'
                       else InspectBlocked nm
                     else InspectTargetFled nm)
    | Destroy nm =>
      (case ALOOKUP sq.robots nm of
          NONE    => Invalid
        | SOME r' => if ¬fled nb (r'.command) then
                         if ¬destroyShielded
                             (MAP (robot_command o SND) sq.robots) nm r'.inventory
                         then Destroyed nm
                         else DestroyBlocked nm
                     else DestroyTargetFled nm)
    | Build is m =>
      if EVERY (λi. i < LENGTH sq.items) is then
        if ¬EXISTS (contested sq) is then
          case construct (MAP (λi. EL i sq.items) is) m of
          | NONE => Invalid
          | SOME r => Built is r
        else BuildInterrupted is
      else Invalid
    | Pass => Passed`;

val localActions_def = Define`
  localActions sq nb =
    MAP (λ(nm,r). (nm, (r, act sq nb r))) sq.robots`;

val defend_def = Define`
  defend intents nm =
    dropN (destroyAttempts intents nm) isDestroyShield o
    dropN (inspectAttempts intents nm) isInspectShield`;

val updateInventory_def = Define`
  updateInventory sq nm (r,a) =
    let intents = MAP (robot_command o SND) sq.robots in
    (nm,
      case a of
      | MovedOut _ => r
      | Lifted n => r with inventory := (EL n sq.items)::(defend intents nm r.inventory)
      | Dropped n => r with inventory := (defend intents nm (remove_indices ($= n) 0 r.inventory))
      | _ => r with inventory := defend intents nm r.inventory)`;

val incomingFrom_def = Define`
  (incomingFrom dir NONE = []) ∧
  (incomingFrom dir (SOME sq) =
   MAP (λ(nm,r). (nm, (r, MovedIn dir)))
     (FILTER (λ(nm,r). r.command = Move (opposite dir)) sq.robots))`;

val dropItem_def = Define`
  dropItem (r,a) =
    case a of Dropped i => [EL i r.inventory] | _ => []`;

val usedItem_def = Define`
  usedItem actions i =
    EXISTS (λa. case a of Lifted l => i = l
                | Built is _ => MEM i is
                | _ => F) actions`;

val event_def = Define`
  event sq nb =
    let oldRobotsActions = localActions sq nb in
    let veterans = MAP (UNCURRY (updateInventory sq)) oldRobotsActions in
    let actions = MAP (SND o SND) oldRobotsActions in
    <| robotActions :=
       let immigrations = FLAT (GENLIST (λdir. incomingFrom dir (EL dir nb)) (LENGTH nb)) in
       MAP2 (λ(nm,r) a. (nm,(r,a))) veterans actions ++ immigrations
     ; createdRobots :=  MAP (SND o destBuilt) (FILTER isBuilt actions)
     ; untouchedItems := remove_indices (usedItem actions) 0 sq.items
     ; droppedItems := FLAT (MAP (dropItem o SND) oldRobotsActions)
     ; fallenItems :=
         MAP (λ(nm,r). <|components := shatter r
                        ;possessions := r.inventory|>)
             (FILTER (λ(nm,r). MEM (Destroyed nm) actions) veterans)
     |>`;

(* computation phase *)

val private_def = Define`
  (private (Inspected _ r) = pInspected r.processor r.memory) ∧
  (private Invalid = pInvalid) ∧
  (private _ = pNothing)`;

(* TODO:
  define this in botworld_preambleTheory, as the environment produced by
  the translator (plus extra definitions as necessary) *)
val preamble_env_def = Define`
  preamble_env (ffi:'ffi ffi_state) = ARB:('ffi semanticPrimitives$state # v environment)`;

val ffi_from_observation_def = Define`
  ffi_from_observation obs m =
    initial_ffi_state botworld_oracle
      (encode_observation obs::clear_register 0 m)`;

val run_policy_def = Define`
  run_policy obs k m =
    let ffi = ffi_from_observation obs m in
    let (st,env) = preamble_env ffi in
    let policy = read_policy m in
    let (st',_) = evaluate_prog (st with clock := k) env policy in
    case st'.ffi.ffi_state of
      (c::m') => (decode_command c, m')`;

val runMachine_def = Define`
  runMachine ev (nm,r,a) =
    let obs = observation nm ev (private a) in
    let (c,m) = run_policy obs r.processor r.memory in
    (obs.name, r with <| command := c; memory := m |>)`;

val _ = overload_on("destroyed",
  ``λnm ras. MEM (Destroyed nm) (MAP (SND o SND) ras)``);

val computeSquare_def = Define`
  computeSquare t (c,ev) =
    <| items :=
         ev.untouchedItems ++ ev.droppedItems ++
         FLAT (MAP (λc. c.components ++ c.possessions) ev.fallenItems)
     ; robots :=
         let ls =
             FILTER (λ(nm,(r,a)). ¬isMovedOut a ∧ ¬destroyed nm ev.robotActions)
                    ev.robotActions ++
             MAPi (λi r. (name t c i, (r, Passed))) ev.createdRobots in
           MAP (runMachine ev) ls
     |>`;

(* state *)

val computeEvents_def = Define`
  computeEvents (g:grid) =
    FMAP_MAP2 (λ(c,sq). event sq (neighbours g c)) g`;

val step_def = Define`
  step st =
    <| grid := FMAP_MAP2 (computeSquare st.time_step) (computeEvents st.grid)
     ; time_step := st.time_step + 1 |>`;

val wf_state_def = Define`
  wf_state st ⇔
    (∀c1 c2 s1 s2.
       FLOOKUP st.grid c1 = SOME s1 ∧
       FLOOKUP st.grid c2 = SOME s2 ∧
       c1 ≠ c2
       ⇒
       DISJOINT (set (MAP FST s1.robots)) (set (MAP FST s2.robots))) ∧
    (∀sq. sq ∈ FRANGE st.grid ⇒ ALL_DISTINCT (MAP FST sq.robots)) ∧
    (∀sq nm. sq ∈ FRANGE st.grid ∧ MEM nm (MAP FST sq.robots) ⇒
             nm.built_step < st.time_step)`;

val _ = Datatype`
  state_with_hole = <| state : state
                     ; focal_name : name
                     |>`;

val wf_state_with_hole_def = Define`
  wf_state_with_hole s ⇔
    wf_state s.state ∧
    ∃sq.
      sq ∈ FRANGE s.state.grid ∧
      MEM s.focal_name (MAP FST sq.robots)`;

val if_focal_def = Define`
  if_focal fnm f (nm, r) = (nm, if nm = fnm then f r else r)`

val fill_def = Define`
  fill f s =
  s.state with grid updated_by $o_f
    (λsq. sq with robots updated_by
          MAP (if_focal s.focal_name f))`;

val _ = overload_on("with_command",``λc. robot_command_fupd (K c)``);

val _ = overload_on("inspected",
  ``λnm ras. ∃r. MEM (Inspected nm r) (MAP (SND o SND) ras)``);

val steph_def = Define`
  steph c s =
    let s' = fill (with_command c) s in
    let events = computeEvents s'.grid in
    if ∀ev::FRANGE events.
              ¬destroyed s.focal_name ev.robotActions ∧
              ¬inspected s.focal_name ev.robotActions
    then
      let (c,ev,a) = CHOICE
        { (c,ev,a) | ∃r. MEM (s.focal_name,(r,a)) ev.robotActions ∧
                         ¬isMovedOut a ∧ FLOOKUP events c = SOME ev } in
      SOME (observation s.focal_name ev (private a), s with state := step s')
    else NONE
`;

(* histories *)

val _ = Parse.type_abbrev("history",``:state llist``);

val hist_def = Define`
  (hist:state->history) s = LUNFOLD (λs. SOME (step s,s)) s`;

val _ = export_theory()
