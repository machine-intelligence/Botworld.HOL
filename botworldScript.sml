open HolKernel Parse boolLib bossLib lcsymtacs
open botworld_dataTheory botworld_serialiseTheory
open terminationTheory initialProgramTheory

(* TODO: initialProgram should be imported by termination *)

val _ = temp_tight_equality();

val _ = new_theory"botworld"

(* Port of Botworld to more idiomatic HOL *)

val _ = Datatype`
  square = <| robots: robot list; items: item list |>`;

val opposite_def = Define`
  opposite d = d + 4 MOD 8`;

val _ = type_abbrev("coordinate",``:int # int``);
val _ = type_abbrev("grid",``:coordinate |-> square``)

val neighbours_def = Define`
  neighbours g (x,y) = MAP (FLOOKUP g)
    [(x-1,y-1)
    ;(x-1,y  )
    ;(x-1,y+1)
    ;(x  ,y-1)
    ;(x  ,y+1)
    ;(x+1,y-1)
    ;(x+1,y  )
    ;(x+1,y+1)]`;

val move_coordinate_def = Define`
  move_coordinate (x,y) (dir:num) =
    if dir = 0 then (x  ,y+1) else
    if dir = 1 then (x+1,y+1) else
    if dir = 2 then (x+1,y  ) else
    if dir = 3 then (x+1,y-1) else
    if dir = 4 then (x  ,y-1) else
    if dir = 5 then (x-1,y-1) else
    if dir = 6 then (x-1,y  ) else
    if dir = 7 then (x-1,y+1) else (x,y)`;

(* environment phase *)

val contested_def = Define`
  contested sq i ⇔
    i < LENGTH sq.items ∧
    1 < LENGTH
        (FILTER (λr. case r.command of
                     | Lift li => li = i ∧ canLift r (EL i sq.items)
                     | Build is m => MEM i is ∧
                                     EVERY (λi. i < LENGTH sq.items) is ∧
                                     IS_SOME (construct (MAP (λi. EL i sq.items) is) m)
                     | _ => F)
         sq.robots)`;

val fled_def = Define`
  (fled nb (Move dir) ⇔ dir < LENGTH nb ∧ IS_SOME (EL dir nb)) ∧
  (fled nb _ = F)`;

val inspectAttempts_def = Define`
  inspectAttempts intents i =
    LENGTH (FILTER (λc. c = Inspect i) intents)`;

val inspectShielded_def = Define`
  inspectShielded robots i ⇔
    inspectAttempts (MAP robot_command robots) i ≤
    LENGTH (FILTER isInspectShield (EL i robots).inventory)`;

val destroyAttempts_def = Define`
  destroyAttempts intents i =
    LENGTH (FILTER (λc. c = Destroy i) intents)`;

val destroyShielded_def = Define`
  destroyShielded robots i ⇔
    destroyAttempts (MAP robot_command robots) i ≤
    LENGTH (FILTER isDestroyShield (EL i robots).inventory)`;

val act_def = Define`
  act sq nb ri = if ri < LENGTH sq.robots then
    let r = EL ri sq.robots in
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
    | Inspect i =>
      if i < LENGTH sq.robots then
        if ¬fled nb (EL i sq.robots).command then
          if ¬inspectShielded sq.robots i then
            Inspected i (EL i sq.robots)
          else InspectBlocked i
        else InspectTargetFled i
      else Invalid
    | Destroy i =>
      if i < LENGTH sq.robots then
        if ¬fled nb (EL i sq.robots).command then
          if ¬destroyShielded sq.robots i then
            Destroyed i
          else DestroyBlocked i
        else DestroyTargetFled i
      else Invalid
    | Build is m =>
      if EVERY (λi. i < LENGTH sq.items) is then
        if ¬EXISTS (contested sq) is then
          case construct (MAP (λi. EL i sq.items) is) m of
          | NONE => Invalid
          | SOME r => Built is r
        else BuildInterrupted is
      else Invalid
    | Pass => Passed
  else Invalid`;

val localActions_def = Define`
  localActions sq nb =
    GENLIST (act sq nb) (LENGTH sq.robots)`;

val defend_def = Define`
  defend intents i =
    dropN (destroyAttempts intents i) isDestroyShield o
    dropN (inspectAttempts intents i) isInspectShield`;

val updateInventory_def = Define`
  updateInventory sq i a =
    let r = EL i sq.robots in
    let intents = MAP robot_command sq.robots in
    case a of
    | MovedOut _ => r
    | Lifted n => r with inventory := (EL n sq.items)::(defend intents i r.inventory)
    | Dropped n => r with inventory := (defend intents i (remove_indices ($= n) 0 r.inventory))
    | _ => r with inventory := defend intents i r.inventory`;

val incomingFrom_def = Define`
  (incomingFrom dir NONE = []) ∧
  (incomingFrom dir (SOME sq) =
   FLAT (MAP (λr. if r.command = Move (opposite dir) then [(r,MovedIn dir)] else []) sq.robots))`;

val event_def = Define`
  event sq nb =
    let actions = localActions sq nb in
    let veterans = GENLIST (λi. updateInventory sq i (EL i actions)) (LENGTH sq.robots) in
    let fallen = FLAT (GENLIST (λi. if MEM (Destroyed i) actions then
                                      [<|components := shatter (EL i veterans)
                                        ;possessions := (EL i veterans).inventory|>]
                                    else [])
                       (LENGTH veterans)) in
    <| robotActions :=
       let immigrations = FLAT (GENLIST (λi. incomingFrom i (EL i nb)) (LENGTH nb)) in
       let children = FLAT (MAP (λa. case a of Built _ r => [r] | _ => []) actions) in
       ZIP (veterans,actions) ++ immigrations ++
       ZIP (children, REPLICATE (LENGTH children) Created)
     ; untouchedItems :=
       remove_indices
         (λi. EXISTS (λa. case a of Lifted l => i = l
                                  | Built is _ => MEM i is
                                  | _ => F)
              actions)
         0 sq.items
     ; droppedItems :=
       FLAT
         (MAP (λ(r,a). case a of Dropped i => [EL i r.inventory]
                               | _ => [])
              (ZIP(sq.robots,actions)))
     ; fallenItems := fallen
     |>`;

(* computation phase *)

val private_def = Define`
  (private (Inspected _ r) = pInspected r.processor r.memory) ∧
  (private Invalid = pInvalid) ∧
  (private _ = pNothing)`;

val ffi_from_observation_def = Define`
  ffi_from_observation (obs:observation) =
    initial_ffi_state botworld_oracle
      (botworld_initial_state obs)`;

val prepare_def = Define`
  prepare ev (i,r,a) =
    (ffi_from_observation (i, ev, private a), r)`;

val runMachine_def = Define`
  runMachine (ffi,r) =
    let (st,env) = THE (basis_sem_env ffi) in
    let (st',c,res) = evaluate_prog (st with clock := r.processor) env r.memory in
    let (command,prog) = st'.ffi.ffi_state.bot_output in
    r with <| command := command; memory := prog |>`;

val computeSquare_def = Define`
  computeSquare ev =
    <| items :=
         ev.untouchedItems ++ ev.droppedItems ++
         FLAT (MAP (λc. c.components ++ c.possessions) ev.fallenItems)
     ; robots :=
         let ls = GENLIST (λi. (i,EL i ev.robotActions)) (LENGTH ev.robotActions) in
         let ls = FILTER (λ(i,r,a). ¬isMovedOut a ∧ ¬MEM (Destroyed i) (MAP SND ev.robotActions)) ls in
           MAP (runMachine o prepare ev) ls
     |>`;

(* state *)

val computeEvents_def = Define`
  computeEvents g =
    FMAP_MAP2 (λ(c,sq). event sq (neighbours g c)) g`;

val step_def = Define`
  step g = computeSquare o_f (computeEvents g)`;

val _ = Datatype`
  state_with_hole = <| state : grid
                     ; focal_coordinate : coordinate
                     ; focal_index : num
                     |>`;

val wf_state_with_hole_def = Define`
  wf_state_with_hole s ⇔
    (∃sq.
      FLOOKUP s.state s.focal_coordinate = SOME sq ∧
      s.focal_index < LENGTH sq.robots ∧
      (EL (s.focal_index) sq.robots).focal) ∧
    (∀sq c i.
       FLOOKUP s.state c = SOME sq ∧
       i < LENGTH sq.robots ∧
       (c,i) ≠ (s.focal_coordinate,s.focal_index)
       ⇒ ¬(EL i sq.robots).focal)`;

val square_update_robot_def = Define`
  square_update_robot f idx sq =
    sq with robots updated_by
      LUPDATE (f (EL idx sq.robots)) idx`;

val fill_def = Define`
  fill f s =
    s.state |+
    (s.focal_coordinate,
     square_update_robot f s.focal_index (s.state ' s.focal_coordinate))`;

val find_focal_def = Define`
  find_focal g =
    @p. ∃c i sq. p = (c,i) ∧ FLOOKUP g c = SOME sq ∧ i < LENGTH sq.robots ∧ (EL i sq.robots).focal`;

val steph_def = Define`
  steph command s =
    let events = computeEvents (fill (robot_command_fupd (K command)) s) in
    let ev = events ' s.focal_coordinate in
    if EXISTS (λa. a = Destroyed s.focal_index ∨
                   ∃r. a = Inspected s.focal_index r)
              (MAP SND ev.robotActions)
    then NONE else
    let a = SND (EL s.focal_index ev.robotActions) in
    let s' = computeSquare o_f events in
    let (c,i) = find_focal s' in
    SOME
      ((s.focal_index, ev, private a),
       <| state := s'
        ; focal_coordinate := c
        ; focal_index := i
        |>)`;

val _ = export_theory()
