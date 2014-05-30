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
(* If we move from the Constree language to CakeML, and we still want to be able to partially execute programs, it probably makes sense to use CakeML's small-step semantics and have the robots have slots for each of its state components (replacing the registers) *)

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
           ; memory : register list
           |>`

val canLift_def = Define`
  canLift r item ⇔ r.frame.strength ≥ SUM (MAP weight (item::r.inventory))`

val _ = Datatype`
  square = <| robotsIn : robot list ; itemsIn : item list |>`

val _ = type_abbrev("cell",``:square option``)

val _ = export_theory()
