open HolKernel Parse boolLib bossLib lcsymtacs
open terminationTheory

val _ = temp_tight_equality();

val _ = new_theory"hbotworld"

(* Port of Botworld to more idiomatic HOL *)

(* TODO: is this in a library? *)
val map_option_def = Define`
  (map_option [] = SOME []) ∧
  (map_option (NONE::_) = NONE) ∧
  (map_option (SOME x::ls) =
   case map_option ls of
   | SOME ls => SOME(x::ls)
   | NONE => NONE)`;

val remove_indices_def = Define`
  (remove_indices P i [] = []) ∧
  (remove_indices P i (x::xs) =
    if P i then remove_indices P (i+1:num) xs
       else x::(remove_indices P (i+1) xs))`;

val dropN_def = Define`
  (dropN 0 P ls = ls) ∧
  (dropN _ _ [] = []) ∧
  (dropN (SUC n) P (x::xs) =
   if P x then dropN n P xs
   else x::(dropN (SUC n) P xs))`;
(* -- *)

(* "val () = ();" top-level declaration
   used in empty registers *)
val skip_top_def = Define`
  skip_top = Tdec(Dlet(Pcon NONE [])(Con NONE []))`;

val _ = Datatype`
  frame = <| color: num; strength: num |>`;

val _ = Datatype`
  (* speed = ticks allowed per Botworld step *)
  processor = <| speed: num |>`;

val _ = Datatype`
  cargo = <| cargoType: num; cargoWeight: num |>`;

val _ = Datatype`
  item =
    Cargo cargo
  | ProcessorPart processor
  | RegisterPart top
  | FramePart frame
  | InspectShield
  | DestroyShield`;

val destRegisterPart_def = Define`
  destRegisterPart (RegisterPart r) = SOME r ∧
  destRegisterPart _ = NONE`;
val isInspectShield_def = Define`
  (isInspectShield InspectShield = T) ∧
  (isInspectShield _ = F)`;
val isDestroyShield_def = Define`
  (isDestroyShield DestroyShield = T) ∧
  (isDestroyShield _ = F)`;
val _ = export_rewrites["destRegisterPart_def","isInspectShield_def","isDestroyShield_def"];

val weight_def = Define`
  weight (Cargo c) = c.cargoWeight ∧
  weight (FramePart _) = 100 ∧
  weight _ = 1`;

val _ = Datatype`
  command =
    Move num
  | Lift num
  | Drop num
  | Inspect num
  | Destroy num
  | Build (num list) prog
  | Pass`;

val _ = Datatype`
  robot =
  <| frame : frame
   ; processor : processor
   ; memory : prog
   ; inventory : item list
   ; command : command
   |>`;

val construct_def = Define`
  construct ls =
  case ls of
  | (FramePart f::ProcessorPart p::rs) =>
    (case map_option (MAP destRegisterPart rs) of
     | SOME m =>
       SOME <| frame := f; processor := p; memory := m;
               inventory := []; command := Pass |>
     | _ => NONE)
  | _ => NONE`;

val shatter_def = Define`
  shatter r =
    (FramePart r.frame::ProcessorPart r.processor::
     MAP (K (RegisterPart skip_top)) r.memory)`;

val _ = Datatype`
  action =
    Created
  | Passed
  | MoveBlocked num
  | MovedOut num
  | MovedIn num
  | CannotLift num
  | GrappledOver num
  | Lifted num
  | Dropped num
  | InspectTargetFled num
  | InspectBlocked num
  | Inspected num robot
  | DestroyTargetFled num
  | DestroyBlocked num
  | Destroyed num
  | BuildInterrupted (num list)
  | Built (num list) robot
  | Invalid`;

val _ = Datatype`
  square = <| robots: robot list; items: item list |>`;
val _ = type_abbrev("cell",``:square option``);

val opposite_def = Define`
  opposite d = d + 4 MOD 8`;

(* step function for squares *)

(* environment phase *)

val canLift_def = Define`
  canLift r i ⇔
    SUM (MAP weight (i::r.inventory)) ≤ r.frame.strength`;

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

val _ = Datatype`
  itemCache =
  <| components: item list
   ; possessions: item list
   |>`;

val _ = Datatype`
  event = <|
    robotActions: (robot # action) list
  ; untouchedItems: item list
  ; droppedItems: item list
  ; fallenItems: itemCache list|>`;

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

val _ = export_theory()
