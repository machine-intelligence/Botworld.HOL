open HolKernel boolLib bossLib lcsymtacs
val _ = new_theory"botworld_misc"

(* TODO: move these to HOL if appropriate *)

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

(* "val () = ();" top-level declaration
   used in empty registers *)
val skip_top_def = Define`
  skip_top = Tdec(Dlet(Pcon NONE [])(Con NONE []))`;

val _ = export_theory()
