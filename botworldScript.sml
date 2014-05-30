open HolKernel Parse boolLib bossLib lcsymtacs
val _ = new_theory"botworld"
val _ = temp_tight_equality()

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

val _ = type_abbrev("processor",``:num``) (* TODO *)
val _ = type_abbrev("register",``:num``) (* TODO *)
val _ = type_abbrev("memory",``:register list``)
(* If we move from the Constree language to CakeML, and we still want to be
able to partially execute programs, it probably makes sense to use CakeML's
small-step semantics and have the robots have slots for each of its state
components (replacing the registers). Actually it probably makes more sense
to use CakeML Bytecode (or some other imperative language in the new
backend) in the robots, so we have a clear notion of speed (instructions per
step) and memory usage (number of reachable values). *)

val _ = Datatype`
  cargo = <| cargoType : num; cargoWeight : num |>`

val _ = Datatype`
  item = Cargo cargo
       | ProcessorPart processor
       | RegisterPart register
       | FramePart frame
       | Shield`

val weight_def = Define`
  weight (Cargo c) = c.cargoWeight ∧
  weight Shield = 1 ∧
  weight (RegisterPart _) = 1 ∧
  weight (ProcessorPart _) = 1 ∧
  weight (FramePart _) = 100`

val _ = Datatype`
  robot = <| frame : frame
           ; inventory : item list
           ; processor : processor
           ; memory : memory
           |>`

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
          | Build (num list) memory
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
         | BuildInterrupted (num list)
         | Built (num list) robot
         | Invalid`

val _ = export_theory()
