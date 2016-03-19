open HolKernel Parse boolLib bossLib lcsymtacs
open simpleSexpTheory fromSexpTheory monadsyntax
open simpleSexpParseTheory
open botworld_dataTheory

val _ = new_theory"botworld_serialise"

val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)
val _ = temp_overload_on ("lift", ``OPTION_MAP``)
val _ = temp_overload_on ("guard", ``λb m. monad_unitbind (assert b) m``)
val _ = temp_overload_on ("sexpnum", ``odestSXNUM``)

(* decoding from sexp *)

val sexpframe_def = Define`
  sexpframe s =
    do
      (color,strength) <- sexppair sexpnum sexpnum s;
      return <| color:=color; strength:=strength|>
    od`;

val sexpcommand_def = Define`
  sexpcommand s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Move" ∧ LENGTH args = 1)
            (lift Move (sexpnum (EL 0 args))) ++
      guard (nm = "Lift" ∧ LENGTH args = 1)
            (lift Lift (sexpnum (EL 0 args))) ++
      guard (nm = "Drop" ∧ LENGTH args = 1)
            (lift Drop (sexpnum (EL 0 args))) ++
      guard (nm = "Inspect" ∧ LENGTH args = 1)
            (lift Inspect (sexpnum (EL 0 args))) ++
      guard (nm = "Destroy" ∧ LENGTH args = 1)
            (lift Destroy (sexpnum (EL 0 args))) ++
      guard (nm = "Build" ∧ LENGTH args = 2)
            (lift2 Build (sexplist sexpnum (EL 0 args))
                         (sexplist sexptop (EL 1 args))) ++
      guard (nm = "Pass" ∧ LENGTH args = 0)
            (return Pass)
    od`;

val sexpcargo_def = Define`
  sexpcargo s =
    do
      (cargoType,cargoWeight) <- sexppair sexpnum sexpnum s;
      return <| cargoType:=cargoType; cargoWeight:=cargoWeight|>
    od`;

val sexpitem_def = Define`
  sexpitem s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Cargo" ∧ LENGTH args = 1)
            (lift Cargo (sexpcargo (EL 0 args))) ++
      guard (nm = "ProcessorPart" ∧ LENGTH args = 1)
            (lift ProcessorPart (sexpnum (EL 0 args))) ++
      guard (nm = "FramePart" ∧ LENGTH args = 1)
            (lift FramePart (sexpframe (EL 0 args))) ++
      guard (nm = "InspectShield" ∧ args = [])
            (return InspectShield) ++
      guard (nm = "DestroyShield" ∧ args = [])
            (return DestroyShield)
    od`;

val sexprobot_def = Define`
  sexprobot s =
    do
      (frame,inventory) <- sexppair sexpframe (sexplist sexpitem) s;
      return (empty_robot with <| frame:=frame; inventory:=inventory |>)
    od`;

val sexpaction_def = Define`
  sexpaction s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Created" ∧ args = [])
            (return Created) ++
      guard (nm = "Passed" ∧ args = [])
            (return Passed) ++
      guard (nm = "MoveBlocked" ∧ LENGTH args = 1)
            (lift MoveBlocked (sexpnum (EL 0 args))) ++
      guard (nm = "MovedOut" ∧ LENGTH args = 1)
            (lift MovedOut (sexpnum (EL 0 args))) ++
      guard (nm = "MovedIn" ∧ LENGTH args = 1)
            (lift MovedIn (sexpnum (EL 0 args))) ++
      guard (nm = "CannotLift" ∧ LENGTH args = 1)
            (lift CannotLift (sexpnum (EL 0 args))) ++
      guard (nm = "GrappledOver" ∧ LENGTH args = 1)
            (lift GrappledOver (sexpnum (EL 0 args))) ++
      guard (nm = "Lifted" ∧ LENGTH args = 1)
            (lift Lifted (sexpnum (EL 0 args))) ++
      guard (nm = "Dropped" ∧ LENGTH args = 1)
            (lift Dropped (sexpnum (EL 0 args))) ++
      guard (nm = "InspectTargetFled" ∧ LENGTH args = 1)
            (lift InspectTargetFled (sexpnum (EL 0 args))) ++
      guard (nm = "InspectBlocked" ∧ LENGTH args = 1)
            (lift InspectBlocked (sexpnum (EL 0 args))) ++
      guard (nm = "Inspected" ∧ LENGTH args = 1)
            (lift2 Inspected
                   (sexpnum (EL 0 args))
                   (return empty_robot)) ++
      guard (nm = "DestroyTargetFled" ∧ LENGTH args = 1)
            (lift DestroyTargetFled (sexpnum (EL 0 args))) ++
      guard (nm = "DestroyBlocked" ∧ LENGTH args = 1)
            (lift DestroyBlocked (sexpnum (EL 0 args))) ++
      guard (nm = "Destroyed" ∧ LENGTH args = 1)
            (lift Destroyed (sexpnum (EL 0 args))) ++
      guard (nm = "BuildInterrupted" ∧ LENGTH args = 1)
            (lift BuildInterrupted (sexplist sexpnum (EL 0 args))) ++
      guard (nm = "Built" ∧ LENGTH args = 1)
            (lift2 Built
                   (sexplist sexpnum (EL 0 args))
                   (return empty_robot))
    od`;

val sexpoutput_def = Define`
  sexpoutput = sexppair sexpcommand (sexplist sexptop)`;

val sexpitemCache_def = Define`
  sexpitemCache s = do (com,pos) <- sexppair (sexplist sexpitem) (sexplist sexpitem) s;
                       return <| components := com ; possessions := pos |>
                    od`;

val sexpprivateData_def = Define`
  sexpprivateData s = do (nm,args) <- dstrip_sexp s;
                         guard (nm = "pInvalid" ∧ args = [])
                               (return pInvalid) ++
                         guard (nm = "pNothing" ∧ args = [])
                               (return pNothing) ++
                         guard (nm = "pInspected" ∧ LENGTH args = 2)
                               (lift2 pInspected (sexpnum (EL 0 args))
                                                 (sexplist sexptop (EL 1 args)))
                      od`;

val sexpevent_def = Define`
sexpevent s = do (ras,unt,drop,fall) <- sexppair (sexplist (sexppair sexprobot sexpaction))
                 (sexppair (sexplist sexpitem)
                           (sexppair (sexplist sexpitem)
                                     (sexplist sexpitemCache))) s ;
                  return <| robotActions := ras; untouchedItems := unt; droppedItems := drop; fallenItems := fall |>
              od
`;

val sexpobservation_def = Define`
  sexpobservation = sexppair sexpnum (sexppair sexpevent sexpprivateData)
`;

val decode_observation_def = Define`
  decode_observation (bytes:word8 list) = do
    s <- parse_sexp (MAP (CHR o w2n) bytes);
    sexpobservation s
  od`;

val decode_output_def = Define`
  decode_output (bytes:word8 list) = do
    s <- parse_sexp (MAP (CHR o w2n) bytes);
    sexpoutput s
  od`;

(* encoding to sexp *)

val framesexp_def = Define`
  framesexp f =
    SX_CONS (SX_NUM f.color) (SX_NUM f.strength)`;

val cargosexp_def = Define`
  cargosexp c =
    SX_CONS (SX_NUM c.cargoType) (SX_NUM c.cargoWeight)`;

val itemsexp_def = Define`
  (itemsexp (Cargo c) = listsexp [SX_SYM "Cargo"; cargosexp c]) ∧
  (itemsexp (ProcessorPart p) = listsexp [SX_SYM "ProcessorPart"; SX_NUM p]) ∧
  (itemsexp (FramePart f) = listsexp [SX_SYM "FramePart"; framesexp f]) ∧
  (itemsexp (InspectShield) = listsexp [SX_SYM "InspectShield"]) ∧
  (itemsexp (DestroyShield) = listsexp [SX_SYM "DestroyShield"])`;

val commandsexp_def = Define`
  (commandsexp (Move num) = listsexp [SX_SYM "Move"; SX_NUM num]) ∧
  (commandsexp (Lift num) = listsexp [SX_SYM "Lift"; SX_NUM num]) ∧
  (commandsexp (Drop num) = listsexp [SX_SYM "Drop"; SX_NUM num]) ∧
  (commandsexp (Inspect num) = listsexp [SX_SYM "Inspect"; SX_NUM num]) ∧
  (commandsexp (Destroy num) = listsexp [SX_SYM "Destroy"; SX_NUM num]) ∧
  (commandsexp (Build ns prog) = listsexp [SX_SYM "Build"; listsexp (MAP SX_NUM ns); listsexp (MAP topsexp prog)]) ∧
  (commandsexp (Pass) = listsexp [SX_SYM "Pass"])`;

val robotsexp_def = Define`
  robotsexp r =
    SX_CONS (framesexp r.frame) (listsexp (MAP itemsexp r.inventory))`;

val actionsexp_def = Define`
  (actionsexp (Created) = listsexp [SX_SYM "Created"]) ∧
  (actionsexp (Passed) = listsexp [SX_SYM "Passed"]) ∧
  (actionsexp (MoveBlocked num) = listsexp [SX_SYM "MoveBlocked"; SX_NUM num]) ∧
  (actionsexp (MovedOut num) = listsexp [SX_SYM "MovedOut"; SX_NUM num]) ∧
  (actionsexp (MovedIn num) = listsexp [SX_SYM "MovedIn"; SX_NUM num]) ∧
  (actionsexp (CannotLift num) = listsexp [SX_SYM "CannotLift"; SX_NUM num]) ∧
  (actionsexp (GrappledOver num) = listsexp [SX_SYM "GrappledOver"; SX_NUM num]) ∧
  (actionsexp (Lifted num) = listsexp [SX_SYM "Lifted"; SX_NUM num]) ∧
  (actionsexp (Dropped num) = listsexp [SX_SYM "Dropped"; SX_NUM num]) ∧
  (actionsexp (InspectTargetFled num) = listsexp [SX_SYM "InspectTargetFled"; SX_NUM num]) ∧
  (actionsexp (InspectBlocked num) = listsexp [SX_SYM "InspectBlocked"; SX_NUM num]) ∧
  (actionsexp (Inspected num _) = listsexp [SX_SYM "Inspected"; SX_NUM num]) ∧
  (actionsexp (DestroyTargetFled num) = listsexp [SX_SYM "DestroyTargetFled"; SX_NUM num]) ∧
  (actionsexp (DestroyBlocked num) = listsexp [SX_SYM "DestroyBlocked"; SX_NUM num]) ∧
  (actionsexp (Destroyed num) = listsexp [SX_SYM "Destroyed"; SX_NUM num]) ∧
  (actionsexp (BuildInterrupted ns) = listsexp [SX_SYM "BuildInterrupted"; listsexp (MAP SX_NUM ns)]) ∧
  (actionsexp (Built ns _) = listsexp [SX_SYM "Built"; listsexp (MAP SX_NUM ns)]) ∧
  (actionsexp (Invalid) = listsexp [SX_SYM "Passed"])`;

val itemCachesexp_def = Define`
  itemCachesexp c =
    SX_CONS (listsexp (MAP itemsexp c.components))
      (listsexp (MAP itemsexp c.possessions))`;

val eventsexp_def = Define`
  eventsexp e =
    SX_CONS (listsexp (MAP (UNCURRY SX_CONS o (robotsexp ## actionsexp)) e.robotActions))
      (SX_CONS (listsexp (MAP itemsexp e.untouchedItems))
        (SX_CONS (listsexp (MAP itemsexp e.droppedItems))
          (listsexp (MAP itemCachesexp e.fallenItems))))`;

val privateDatasexp_def = Define`
  (privateDatasexp pInvalid = listsexp [SX_SYM "pInvalid"]) ∧
  (privateDatasexp pNothing = listsexp [SX_SYM "pNothing"]) ∧
  (privateDatasexp (pInspected proc prog) =
   listsexp [SX_SYM "pInspected";
             SX_NUM proc;
             listsexp (MAP topsexp prog)])`;

val observationsexp_def = Define`
  observationsexp ((i,e,p):observation) =
    SX_CONS (SX_NUM i)
      (SX_CONS (eventsexp e) (privateDatasexp p))`;

val outputsexp_def = Define`
  outputsexp (c,p) = SX_CONS (commandsexp c) (listsexp (MAP topsexp p))`;

val encode_observation_def = Define`
  (encode_observation:observation -> word8 list) =
    MAP (n2w o ORD) o print_sexp o observationsexp`;

val encode_output_def = Define`
  encode_output : command # prog -> word8 list=
    MAP (n2w o ORD) o print_sexp o outputsexp`;

(* botworld ffi *)

val _ = Datatype`
  botworld_ffi_state = <|
    bot_input : observation
  ; bot_output : command # prog |>`;

val botworld_get_input_length_def = Define`
  botworld_get_input_length st bytes =
    let n = LENGTH (encode_observation st.bot_input) in
    let s = print_sexp (SX_NUM n) in
    if LENGTH bytes ≤ LENGTH s then
      Oracle_return st (MAP (K (0w:word8)) bytes)
    else
      Oracle_return st (MAP (n2w o ORD) s ++ GENLIST (K 0w) (LENGTH bytes - LENGTH s))`;

val botworld_read_def = Define`
  botworld_read st bytes =
    let bytes' = encode_observation st.bot_input in
    if LENGTH bytes < LENGTH bytes' then Oracle_fail else
      Oracle_return st (bytes' ++ (GENLIST (K 0w) (LENGTH bytes - LENGTH bytes')))`;

val botworld_write_def = Define`
  botworld_write st bytes =
    case decode_output bytes of
    | SOME output => Oracle_return (st with bot_output := output) bytes
    | NONE => Oracle_return st bytes`;

val botworld_get_output_length_def = Define`
  botworld_get_output_length st bytes =
    let n = LENGTH (encode_output st.bot_output) in
    let s = print_sexp (SX_NUM n) in
    if LENGTH bytes ≤ LENGTH s then
      Oracle_return st (MAP (K (0w:word8)) bytes)
    else
      Oracle_return st (MAP (n2w o ORD) s ++ GENLIST (K 0w) (LENGTH bytes - LENGTH s))`;

val botworld_read_output_def = Define`
  botworld_read_output st bytes =
    let bytes' = encode_output st.bot_output in
    if LENGTH bytes < LENGTH bytes' then Oracle_fail else
      Oracle_return st (bytes' ++ (GENLIST (K 0w) (LENGTH bytes - LENGTH bytes')))`;

val botworld_oracle_def = Define`
  botworld_oracle n =
    if n = 0n then botworld_get_input_length
    else if n = 1 then botworld_read
    else if n = 2 then botworld_write
    else if n = 3 then botworld_get_output_length
    else botworld_read_output`;

val botworld_initial_state_def = Define`
  botworld_initial_state obs =
    <| bot_input := obs ; bot_output := (Pass, []) |>`;

val _ = export_theory()
