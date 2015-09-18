open HolKernel boolLib bossLib lcsymtacs botworld_miscTheory
val _ = new_theory"botworld_data"

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

val canLift_def = Define`
  canLift r i ⇔
    SUM (MAP weight (i::r.inventory)) ≤ r.frame.strength`;

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

val isMovedOut_def = Define`
  (isMovedOut (MovedOut _) ⇔ T) ∧
  (isMovedOut _ ⇔ F)`;
val _ = export_rewrites["isMovedOut_def"];

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

val _ = Datatype`
  privateData = pInvalid | pNothing | pInspected processor prog`;

val _ = Parse.type_abbrev("observation",``:num # event # privateData``);

val _ = export_theory()
