open HolKernel Parse boolLib bossLib lcsymtacs
open bytecodeTerminationTheory
val _ = new_theory"botworld"

val _ = Datatype`
  color = Red | Orange | Yellow | Green | Blue
        | Violet | Black | White`
val color_to_num_def = Define`
  color_to_num Red = 0 ∧
  color_to_num Orange = 1 ∧
  color_to_num Yellow = 2 ∧
  color_to_num Green = 3 ∧
  color_to_num Blue = 4 ∧
  color_to_num Violet = 5 ∧
  color_to_num Black = 6 ∧
  color_to_num White = 7`

val _ = Datatype`
  frame = <| color : color
           ; strength : num
           |>`

val _ = Datatype`
  processor = <| speed : num |>`

val _ = Datatype`
  memory = <| heapSize : num
            ; machineState : bc_state
            |>`

val resetMemory_def = Define`
  resetMemory m = m with machineState := empty_bc_state`

val _ = Datatype`
  cargo = <| cargoType : num; cargoWeight : num |>`

val _ = Datatype`
  item = Cargo cargo
       | ProcessorPart processor
       | MemoryPart memory
       | FramePart frame
       | InspectShield
       | DestroyShield`

val weight_def = Define`
  weight (Cargo c) = c.cargoWeight ∧
  weight (FramePart _) = 100 ∧
  weight _ = 1`

val _ = Datatype`
  robot = <| frame : frame
           ; inventory : item list
           ; processor : processor
           ; memory : memory
           |>`

val isFrame_def = Define`
  (isFrame (FramePart _) ⇔ T) ∧
  (isFrame _ ⇔ F)`
val _ = export_rewrites["isFrame_def"]

val isProcessor_def = Define`
  (isProcessor (ProcessorPart _) ⇔ T) ∧
  (isProcessor _ ⇔ F)`
val _ = export_rewrites["isProcessor_def"]

val isMemory_def = Define`
  (isMemory (MemoryPart _) ⇔ T) ∧
  (isMemory _ ⇔ F)`
val _ = export_rewrites["isMemory_def"]

val _ = type_abbrev("robotItems",``:num#num#num``)

val construct_def = Define`
  construct (f,p,m) =
            <| frame := f
             ; inventory := []
             ; processor := p
             ; memory := m
             |>`

val shatter_def = Define`
  shatter r = (r.frame, r.processor, resetMemory r.memory)`

val canLift_def = Define`
  canLift r item ⇔ r.frame.strength ≥ SUM (MAP weight (item::r.inventory))`

val _ = Datatype`
  square = <| robotsIn : robot list ; itemsIn : item list |>`

val _ = type_abbrev("cell",``:square option``)

val _ = Datatype`
  direction = North | NorthEast | East | SouthEast |
              South | SouthWest | West | NorthWest`
val direction_to_num_def = Define`
  direction_to_num North     = 0 ∧
  direction_to_num NorthEast = 1 ∧
  direction_to_num East      = 2 ∧
  direction_to_num SouthEast = 3 ∧
  direction_to_num South     = 4 ∧
  direction_to_num SouthWest = 5 ∧
  direction_to_num West      = 6 ∧
  direction_to_num NorthWest = 7`
val opposite_def = Define`
  opposite d = d + 4 MOD 8`

val _ = Datatype`
  command = Move direction
          | Lift num
          | Drop num
          | Inspect num
          | Destroy num
          | Build robotItems memory
          | Pass`

val _ = Datatype`
  action = Created
         | Passed
         | MoveBlocked direction
         | MovedOut direction
         | MovedIn direction
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
         | BuildInterrupted robotItems
         | Built robotItems robot
         | Invalid`

val _ = Datatype`
  itemCache = <| components : item list
               ; possessions : item list
               |>`

val _ = Datatype`
  event = <| robotActions : (robot#action) list
           ; untouchedItems : item list
           ; droppedItems : item list
           ; fallenItems : itemCache list
           |>`

val isValidLift_def = Define`
  isValidLift items r i ⇔
    i < LENGTH items ∧
    canLift r (EL i items)`

val allLifts_def = Define`
  allLifts items robots intents =
    FLAT (MAP (λ(r,c).
      case c of
      | SOME (Lift i) =>
        if isValidLift items r i then [i] else []
      | _ => [])
              (ZIP(robots,intents)))`

val isValidBuild_def = Define`
  isValidBuild items (fi,pi,mi) ⇔
    fi < LENGTH items ∧
    pi < LENGTH items ∧
    mi < LENGTH items ∧
    isFrame (EL fi items) ∧
    isProcessor (EL pi items) ∧
    isMemory (EL mi items)`

val allBuilds_def = Define`
  allBuilds items intents =
    FLAT (MAP (λc.
      case c of
      | SOME (Build (fi,pi,mi) _) =>
          if isValidBuild items (fi,pi,mi)
          then [fi;pi;mi]
          else []
      | _ => [])
              intents)`

val isContested_def = Define`
  isContested uses i ⇔ LENGTH (FILTER ($= i) uses) ≤ 1`

val contested_def = Define`
  contested sq robots intents =
  let uses = (allLifts sq.itemsIn robots intents ++
              allBuilds sq.itemsIn intents) in
    GENLIST (isContested uses) (LENGTH (sq.itemsIn))`

(*
val allAttacks_def = Define`
  allAttacks intents =
    FLAT (MAP (λc.
      case c of
      | SOME (Inspect i

val numAttacks_def = Define`
  numAttacks intents i = LENGTH (FILTER ($= i) (allAttacks intents))`

val attacks_def = Define`
  attacks sq intents =
    GENLIST (numAttacks intents) (LENGTH sq.robotsIn)`
*)

val _ = export_theory()
