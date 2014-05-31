open HolKernel boolLib bossLib lcsymtacs
val _ = new_theory"constree"
val _ = tight_equality()
val _ = numLib.prefer_num()

val _ = Datatype`
  constree = Cons constree constree | Nil`

val _ = Datatype`
  register = <| limit : num; contents : constree |>`

val size_def = Define`
  size Nil = 0 ∧
  size (Cons t1 t2) = size t1 + size t2 + 1`

val trim_def = Define`
  trim _ Nil = Nil ∧
  trim x (Cons front back) =
    if size (Cons front back) ≤ x
      then Cons front back
    else if size front < x
      then Cons front (trim (x - (size front + 1)) back)
    else Nil`

val forceR_def = Define`
  forceR t r = r with contents := if size t ≤ r.limit then t else Nil`

val _ = Datatype`
  instruction = Nilify num
              | Construct num num num
              | Deconstruct num num num
              | CopyIfNil num num num`

val _ = Datatype`
  error = BadInstruction constree
        | NoSuchRegister num
        | DeconstructNil num
        | OutOfMemory num
        | InvalidOutput`

val getTree_def = Define`
  getTree n m = if n < LENGTH m
    then INR (EL n m).contents
    else INL (NoSuchRegister n)`

val setTree_def = Define`
  setTree t n m = if n < LENGTH m
    then
      if size t > (EL n m).limit
        then INL (OutOfMemory n)
      else INR (LUPDATE ((EL n m) with contents := t) n m)
    else INL (NoSuchRegister n)`

open monadsyntax

val sum_bind_def = Define`
  sum_bind (INL error) f = INL error ∧
  sum_bind (INR x) f = f x`

val _ = Parse.overload_on("monad_bind",``sum_bind``)

val execute_def = Define`
  execute (Nilify tgt) m = setTree Nil tgt m ∧
  execute (Construct fnt bck tgt) m = do
    front <- getTree fnt m ;
    back <- getTree bck m ;
    setTree (Cons front back) tgt m od ∧
  execute (Deconstruct src fnt bck) m =
   (case getTree src m of
    | INL err => INL err
    | INR Nil => INL (DeconstructNil src)
    | INR (Cons front back) =>
      sum_bind (setTree front fnt m) (setTree back bck))∧
  execute (CopyIfNil tst src tgt) m =
    case getTree tst m of
    | INL err => INL err
    | INR Nil => sum_bind (getTree src m) (λt. setTree t tgt m)
    | INR _ => INR m`

val _ = export_theory()
