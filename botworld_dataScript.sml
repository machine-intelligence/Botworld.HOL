open HolKernel boolLib bossLib lcsymtacs botworld_miscTheory
val _ = new_theory"botworld_data"

val _ = Datatype`
  frame = <| color: num; strength: num |>`;

val empty_frame = Define`empty_frame = <| color := 0; strength := 0 |>`;

val _ = Datatype`
  cargo = <| cargoType: num; cargoWeight: num |>`;

val _ = Datatype`
  item =
    Cargo cargo
  | ProcessorPart num
  | FramePart frame
  | RegisterPart (word8 list)
  | InspectShield
  | DestroyShield`;

val isRegisterPart_def = Define`
  (isRegisterPart (RegisterPart _) = T) ∧
  (isRegisterPart _ = F)`;
val destRegisterPart_def = Define`
  destRegisterPart (RegisterPart ws) = ws`;
val isInspectShield_def = Define`
  (isInspectShield InspectShield = T) ∧
  (isInspectShield _ = F)`;
val isDestroyShield_def = Define`
  (isDestroyShield DestroyShield = T) ∧
  (isDestroyShield _ = F)`;
val _ = export_rewrites["isRegisterPart_def","destRegisterPart_def","isInspectShield_def","isDestroyShield_def"];

val weight_def = Define`
  weight (Cargo c) = c.cargoWeight ∧
  weight (FramePart _) = 100 ∧
  weight _ = 1`;

val _ = Parse.type_abbrev("coordinate",``:int # int``);

val _ = Datatype`
  name = <|
    built_step  : num;
    built_coord : coordinate;
    id          : num
  |>`;

val _ = Datatype`
  command =
    Move num
  | Lift num
  | Drop num
  | Inspect name
  | Destroy name
  | Build (num list) (word8 list list)
  | Pass`;

val _ = Datatype`
  robot =
  <| frame : frame
   ; processor : num (* ticks per Botworld step *)
   ; inventory : item list
   ; memory : word8 list list
     (* convention:
          1st register encodes the command
          2nd register encodes the policy
          remaining registers are storage *)
   |>`;

val empty_robot_def = Define`
  empty_robot =
    <| frame := empty_frame;
       processor := 0;
       inventory := [];
       memory := []
     |>`;

val construct_def = Define`
  construct ls m =
  case ls of
  |  (FramePart f::ProcessorPart p::rs)	 =>
     if EVERY isRegisterPart rs ∧
        LIST_REL (λp r. LENGTH (destRegisterPart p) = LENGTH r)
          rs m then
       SOME <| frame := f; processor := p; memory := m;
               inventory := [] |>
     else NONE
  | _ => NONE`;

val shatter_def = Define`
  shatter r =
    FramePart r.frame::
    ProcessorPart r.processor::
    MAP (RegisterPart o MAP (K 0w)) r.memory`;

val canLift_def = Define`
  canLift r i ⇔
    SUM (MAP weight (i::r.inventory)) ≤ r.frame.strength`;

val _ = Datatype`
  action =
    Passed
  | MoveBlocked num
  | MovedOut num
  | MovedIn num
  | CannotLift num
  | GrappledOver num
  | Lifted num
  | Dropped num
  | InspectTargetFled name
  | InspectBlocked name
  | Inspected name robot
  | DestroyTargetFled name
  | DestroyBlocked name
  | Destroyed name
  | BuildInterrupted (num list)
  | Built (num list) robot
  | Invalid`;

val isMovedOut_def = Define`
  (isMovedOut (MovedOut _) ⇔ T) ∧
  (isMovedOut _ ⇔ F)`;
val _ = export_rewrites["isMovedOut_def"];

val isMovedIn_def = Define`
  (isMovedIn (MovedIn _) ⇔ T) ∧
  (isMovedIn _ ⇔ F)`;
val _ = export_rewrites["isMovedIn_def"];

val isBuilt_def = Define`
  (isBuilt (Built _ _) ⇔ T) ∧
  (isBuilt _ ⇔ F)`;
val _ = export_rewrites["isBuilt_def"];

val destBuilt_def = Define`
  destBuilt (Built is r) = (is,r)`;
val _ = export_rewrites["destBuilt_def"];

val isDropped_def = Define`
  (isDropped (Dropped _) ⇔ T) ∧
  (isDropped _ ⇔ F)`;
val _ = export_rewrites["isDropped_def"];

val destDropped_def = Define`
  destDropped (Dropped i) = i`;
val _ = export_rewrites["destDropped_def"];

val _ = Datatype`
  itemCache =
  <| components: item list
   ; possessions: item list
   |>`;

val _ = Datatype`
  event = <|
    robotActions  : (name, robot # action) alist
  ; createdRobots : robot list
  ; untouchedItems: item list
  ; droppedItems  : item list
  ; fallenItems   : itemCache list|>`;

val _ = Datatype`
  privateData = pInvalid | pNothing | pInspected num (word8 list list)`;

val _ = Datatype`
  observation = <|
    name : name
  ; event : event
  ; private : privateData
  |>`;

val _ = Datatype`
  square = <| robots: (name,robot) alist; items: item list |>`;

val _ = Parse.type_abbrev("grid",``:coordinate |-> square``)

val _ = Datatype`
  state = <| grid : grid; time_step : num |>`;

val _ = Datatype`level = MP | Trust num`;

val _ = export_theory()
