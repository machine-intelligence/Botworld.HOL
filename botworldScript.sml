open HolKernel Parse boolLib bossLib lcsymtacs
open botworld_dataTheory terminationTheory

val _ = temp_tight_equality();

val _ = new_theory"botworld"

(* Port of Botworld to more idiomatic HOL *)

val _ = Datatype`
  square = <| robots: robot list; items: item list |>`;
val _ = type_abbrev("cell",``:square option``);

val opposite_def = Define`
  opposite d = d + 4 MOD 8`;

(* environment phase *)

val contested_def = Define`
  contested sq i ⇔
    i < LENGTH sq.items ∧
    1 < LENGTH
        (FILTER (λr. case r.command of
                     | Lift li => li = i ∧ canLift r (EL i sq.items)
                     | Build is _ => MEM i is ∧
                                     EVERY (λi. i < LENGTH sq.items) is ∧
                                     IS_SOME (construct (MAP (λi. EL i sq.items) is))
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
          case construct (MAP (λi. EL i sq.items) is) of
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

(*
val setInput_def = Define`
  setInput r obs =

val prepare_def = Define`
  prepare ev (i,r,a) =
    setInput r (i, ev, private a)`;

val computeSquare_def = Define`
  computeSquare ev =
    <| items = ev.untouchedItems ++ ev.droppedItems ++
               FLAT (MAP (λc. c.components ++ c.possessions) ev.fallenItems)
     ; robots =
       let ls = GENLIST (λi. (i,EL i ev.robotActions)) (LENGTH robotActions) in
       let ls = FILTER (λ(i,r,a). ¬isMovedOut a ∧ ¬MEM (Destroyed i) (MAP SND robotActions)) ls in
       MAP (runMachine o prepare ev) ls
     |>`;
*)

val _ = export_theory()
