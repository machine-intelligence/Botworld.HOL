open preamble
open simpleSexpTheory fromSexpTheory monadsyntax
open simpleSexpParseTheory
open botworld_miscTheory
open botworld_dataTheory
open terminationTheory

val _ = new_theory"botworld_serialise"

(* TODO: move *)

val escape_string_11 = Q.store_thm("escape_string_11[simp]",
  `∀s s'. escape_string s = escape_string s' ⇔ s = s'`,
  ho_match_mp_tac simpleSexpParseTheory.escape_string_ind \\ rw[]
  \\ rw[Once simpleSexpParseTheory.escape_string_def]
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[Once simpleSexpParseTheory.escape_string_def,SimpRHS]))
  \\ every_case_tac \\ fs[]);

val print_sexp_11 = Q.store_thm("print_sexp_11",
  `∀x y. valid_sexp x ∧ valid_sexp y ∧ print_sexp x = print_sexp y ⇒ x = y`,
  metis_tac[simpleSexpParseTheory.parse_print,SOME_11]);

(* -- *)

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

val sexpint_def = Define`
  sexpint s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "+" ∧ LENGTH args = 1)
            (lift int_of_num (sexpnum (EL 0 args))) ++
      guard (nm = "-" ∧ LENGTH args = 1)
            (lift ($~ o int_of_num) (sexpnum (EL 0 args)))
    od`;

val _ = Parse.overload_on("sexpcoord",``sexppair sexpint sexpint``);

val sexpname_def = Define`
  sexpname s =
    do
      (built_step,built_coord,id) <- sexppair sexpnum (sexppair sexpcoord sexpnum) s;
      return <| built_step := built_step; built_coord := built_coord; id := id |>
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
            (lift Inspect (sexpname (EL 0 args))) ++
      guard (nm = "Destroy" ∧ LENGTH args = 1)
            (lift Destroy (sexpname (EL 0 args))) ++
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
            (lift InspectTargetFled (sexpname (EL 0 args))) ++
      guard (nm = "InspectBlocked" ∧ LENGTH args = 1)
            (lift InspectBlocked (sexpname (EL 0 args))) ++
      guard (nm = "Inspected" ∧ LENGTH args = 1)
            (lift2 Inspected (sexpname (EL 0 args)) (return empty_robot)) ++
      guard (nm = "DestroyTargetFled" ∧ LENGTH args = 1)
            (lift DestroyTargetFled (sexpname (EL 0 args))) ++
      guard (nm = "DestroyBlocked" ∧ LENGTH args = 1)
            (lift DestroyBlocked (sexpname (EL 0 args))) ++
      guard (nm = "Destroyed" ∧ LENGTH args = 1)
            (lift Destroyed (sexpname (EL 0 args))) ++
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
sexpevent s = do (ras,crs,unt,drop,fall) <-
                 sexppair
                 (sexplist (sexppair sexpname (sexppair sexprobot sexpaction)))
                 (sexppair (sexplist sexprobot)
                           (sexppair (sexplist sexpitem)
                                     (sexppair (sexplist sexpitem)
                                               (sexplist sexpitemCache)))) s ;
                  return <| robotActions := ras;
                            createdRobots := crs;
                            untouchedItems := unt;
                            droppedItems := drop;
                            fallenItems := fall |>
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

val intsexp_def = Define`
  intsexp i =
    listsexp [SX_SYM (if i < 0i then "-" else "+");
              SX_NUM (Num(ABS i))]`;

val _ = Parse.overload_on("coordsexp",``λ(i,j). SX_CONS (intsexp i) (intsexp j)``);

val namesexp_def = Define`
  namesexp nm = SX_CONS (SX_NUM nm.built_step) (SX_CONS (coordsexp nm.built_coord) (SX_NUM nm.id))`;

val commandsexp_def = Define`
  (commandsexp (Move num) = listsexp [SX_SYM "Move"; SX_NUM num]) ∧
  (commandsexp (Lift num) = listsexp [SX_SYM "Lift"; SX_NUM num]) ∧
  (commandsexp (Drop num) = listsexp [SX_SYM "Drop"; SX_NUM num]) ∧
  (commandsexp (Inspect nm) = listsexp [SX_SYM "Inspect"; namesexp nm]) ∧
  (commandsexp (Destroy nm) = listsexp [SX_SYM "Destroy"; namesexp nm]) ∧
  (commandsexp (Build ns prog) = listsexp [SX_SYM "Build"; listsexp (MAP SX_NUM ns); listsexp (MAP topsexp prog)]) ∧
  (commandsexp (Pass) = listsexp [SX_SYM "Pass"])`;

val robotsexp_def = Define`
  robotsexp r =
    SX_CONS (framesexp r.frame) (listsexp (MAP itemsexp r.inventory))`;

val actionsexp_def = Define`
  (actionsexp (Passed) = listsexp [SX_SYM "Passed"]) ∧
  (actionsexp (MoveBlocked num) = listsexp [SX_SYM "MoveBlocked"; SX_NUM num]) ∧
  (actionsexp (MovedOut num) = listsexp [SX_SYM "MovedOut"; SX_NUM num]) ∧
  (actionsexp (MovedIn num) = listsexp [SX_SYM "MovedIn"; SX_NUM num]) ∧
  (actionsexp (CannotLift num) = listsexp [SX_SYM "CannotLift"; SX_NUM num]) ∧
  (actionsexp (GrappledOver num) = listsexp [SX_SYM "GrappledOver"; SX_NUM num]) ∧
  (actionsexp (Lifted num) = listsexp [SX_SYM "Lifted"; SX_NUM num]) ∧
  (actionsexp (Dropped num) = listsexp [SX_SYM "Dropped"; SX_NUM num]) ∧
  (actionsexp (InspectTargetFled nm) = listsexp [SX_SYM "InspectTargetFled"; namesexp nm]) ∧
  (actionsexp (InspectBlocked nm) = listsexp [SX_SYM "InspectBlocked"; namesexp nm]) ∧
  (actionsexp (Inspected nm _) = listsexp [SX_SYM "Inspected"; namesexp nm]) ∧
  (actionsexp (DestroyTargetFled nm) = listsexp [SX_SYM "DestroyTargetFled"; namesexp nm]) ∧
  (actionsexp (DestroyBlocked nm) = listsexp [SX_SYM "DestroyBlocked"; namesexp nm]) ∧
  (actionsexp (Destroyed nm) = listsexp [SX_SYM "Destroyed"; namesexp nm]) ∧
  (actionsexp (BuildInterrupted ns) = listsexp [SX_SYM "BuildInterrupted"; listsexp (MAP SX_NUM ns)]) ∧
  (actionsexp (Built ns _) = listsexp [SX_SYM "Built"; listsexp (MAP SX_NUM ns)]) ∧
  (actionsexp (Invalid) = listsexp [SX_SYM "Passed"])`;

val itemCachesexp_def = Define`
  itemCachesexp c =
    SX_CONS (listsexp (MAP itemsexp c.components))
      (listsexp (MAP itemsexp c.possessions))`;

val eventsexp_def = Define`
  eventsexp e =
    SX_CONS (listsexp (MAP (λ(nm,(r,a)). SX_CONS (namesexp nm) (SX_CONS (robotsexp r) (actionsexp a))) e.robotActions))
      (SX_CONS (listsexp (MAP robotsexp e.createdRobots))
        (SX_CONS (listsexp (MAP itemsexp e.untouchedItems))
          (SX_CONS (listsexp (MAP itemsexp e.droppedItems))
            (listsexp (MAP itemCachesexp e.fallenItems)))))`;

val privateDatasexp_def = Define`
  (privateDatasexp pInvalid = listsexp [SX_SYM "pInvalid"]) ∧
  (privateDatasexp pNothing = listsexp [SX_SYM "pNothing"]) ∧
  (privateDatasexp (pInspected proc prog) =
   listsexp [SX_SYM "pInspected";
             SX_NUM proc;
             listsexp (MAP topsexp prog)])`;

val observationsexp_def = Define`
  observationsexp ((nm,e,p):observation) =
    SX_CONS (namesexp nm)
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

val botworld_get_output_length_def = Define`
  botworld_get_output_length st bytes =
    let n = LENGTH (encode_output st.bot_output) in
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

val botworld_read_output_def = Define`
  botworld_read_output st bytes =
    let bytes' = encode_output st.bot_output in
    if LENGTH bytes < LENGTH bytes' then Oracle_fail else
      Oracle_return st (bytes' ++ (GENLIST (K 0w) (LENGTH bytes - LENGTH bytes')))`;

val botworld_write_def = Define`
  botworld_write st bytes =
    case decode_output bytes of
    | SOME output => Oracle_return (st with bot_output := output) bytes
    | NONE => Oracle_return st bytes`;

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

(* CakeML declarations of helper functions for interfacing with the Botworld FFI *)

val ByteArrayFromList_dec_def = Define`
  ByteArrayFromList_dec =
    Dlet(Pvar"fromList")
      (Fun "ls"
         (Let (SOME "a") (App Aw8alloc [App Opapp [Var(Long"Botworld""length");Var(Short"ls")]])
            (Letrec [("f","ls",Fun "i" (Mat (Var(Short"ls"))
              [(Pcon(SOME(Short"nil"))[],Var(Short"a"))
              ;(Pcon(SOME(Short"::"))[Pvar"h";Pvar"t"],
                  Let NONE (App Aw8update [Var(Short"a");Var(Short"i");Var(Short"h")])
                    (App Opapp [App Opapp [Var(Short"f");Var(Short"t")];
                                App (Opn Plus) [Var(Short"i");Lit(IntLit 1)]]))]))]
              (App Opapp [App Opapp [Var(Short"f");Var(Short"ls")];Lit(IntLit 0)]))))`;

val ByteArrayToList_dec_def = Define`
  ByteArrayToList_dec =
    Dlet(Pvar"toList")
      (Fun "a"
        (Letrec [("f","ls",Fun "i"
          (If (App Equality [Var(Short"i"); Lit(IntLit 0)])
              (Var(Short"ls"))
              (App Opapp
                [App Opapp [Var(Short"f");
                            Con (SOME(Short"::"))
                              [App Aw8sub [Var(Short"a"); Var(Short"i")];
                               Var(Short"ls")]];
                 App (Opn Minus) [Var(Short"i"); Lit(IntLit 1)]])))]
          (App Opapp [App Opapp [Var (Short"f"); Con (SOME(Short"nil")) []];
                      App Aw8length [Var(Short"a")]])))`;

val write_output_dec_def = Define`
  write_output_dec =
    Dlet(Pvar"write_output")
      (Fun "x"
        (App (FFI 2)
          [App Opapp
             [Var(Long"ByteArray""fromList");
              App Opapp [Var(Long"Botworld""encode_output");Var(Short"x")]]]))`;

val length_rec_def = Define`
    length_rec bs n =
      if EVERY (λb. b = 0w : word8) bs
      then INL (2n * n)
      else INR (OPTION_BIND (parse_sexp (MAP (CHR o w2n) bs)) odestSXNUM)`;

(* TODO: this is wrong because length_rec expects a list of bytes, whereas bs
         is a reference to a byte array *)
val get_input_length_loop_body_def = Define`
 get_input_length_loop_body =
           (Let (SOME "bs") (App Aw8alloc [Var(Short"n"); Lit(Word8 0w)])
                (Let NONE (App (FFI 0) [Var(Short"bs")])
                     (Mat (App Opapp [App Opapp [Var(Long "Botworld" "length_rec"); Var(Short"bs")]; Var(Short "n")])
                          [(Pcon (SOME(Short "inl")) [Pvar "n"], App Opapp [Var(Short"f"); Var(Short"n")] )
                          ;(Pcon (SOME(Short "inr")) [Pcon (SOME(Short "some")) [Pvar "len"]], Var(Short"len"))])))`

val get_input_length_body_def = Define`
  get_input_length_body =
    (Letrec [("f","n",get_input_length_loop_body)] (App Opapp [Var(Short "f") ; Lit(IntLit 1)]))`;

val get_input_length_dec_def = Define`
  get_input_length_dec = Dlet(Pvar "get_input_length") (Fun "x" get_input_length_body)`

val get_output_length_body_def = Define`
  get_output_length_body =
  (Letrec [("f","n",
            (Let (SOME "bs") (App Aw8alloc [Var(Short"n"); Lit(Word8 0w)])
                 (Let NONE (App (FFI 3) [Var(Short"bs")])
                      (Mat (App Opapp [App Opapp [Var(Long "Botworld" "length_rec"); Var(Short"bs")]; Var(Short "n")])
                           [(Pcon (SOME(Short "inl")) [Pvar "n"], App Opapp [Var(Short"f"); Var(Short"n")] )
                           ;(Pcon (SOME(Short "inr")) [Pcon (SOME(Short "some")) [Pvar "len"]], Var(Short"len"))]))))]
          (App Opapp [Var(Short "f") ; Lit(IntLit 1)]))`;

val get_output_length_dec_def = Define`
  get_output_length_dec = Dlet (Pvar "get_output_length") (Fun "x" get_output_length_body)`;

val read_observation_dec_def = Define`
  read_observation_dec =
    Dlet (Pvar "read_observation")
      (Fun "unit"
           (Let (SOME "bs") (App Aw8alloc [App Opapp [Var(Short"get_input_length"); Var(Short"unit")]])
           (Let NONE (App (FFI 1) [Var(Short"bs")])
           (App Opapp [Var(Long "Botworld" "decode_observation"); App Opapp [Var(Long "ByteArray" "toList") ; Var(Short"bs")]]))))`;

val read_output_dec_def = Define`
    read_output_dec =
    Dlet (Pvar "read_output")
      (Fun "unit"
           (Let (SOME "bs") (App Aw8alloc [App Opapp [Var(Short"get_output_length"); Var(Short"unit")]])
           (Let NONE (App (FFI 4) [Var(Short"bs")])
           (App Opapp [Var(Long "Botworld" "decode_output"); App Opapp [Var(Long "ByteArray" "toList") ; Var(Short"bs")]]))))`;

(* properties of the encoding *)

val intsexp_11 = Q.store_thm("intsexp_11[simp]",
  `∀ i1 i2. intsexp i1 = intsexp i2 ⇔ i1 = i2`,
  rw[intsexp_def] >> intLib.COOPER_TAC);

val coordsexp_11 = Q.store_thm("coordsexp_11[simp]",
  `coordsexp c1 = coordsexp c2 ⇔ c1 = c2`,
  cases_on `c1` >> cases_on `c2` >> fs[]);

val namesexp_11 = Q.store_thm("namesexp_11[simp]",
  `∀ n1 n2. namesexp n1 = namesexp n2 ⇔ n1 = n2`,
  Induct >> gen_tac >> cases_on `n2` >> fs[namesexp_def]);

val commandsexp_11 = Q.store_thm("commandsexp_11[simp]",
  `∀ c c'. commandsexp c = commandsexp c' ⇔ c = c'`,
  Induct >> gen_tac >> cases_on `c'` >> fs[commandsexp_def, listsexp_11]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac \\ rw[]);

val outputsexp_11 = Q.store_thm("outputsexp_11[simp]",
  `outputsexp x = outputsexp y ⇔ x = y`,
  cases_on `x` \\ cases_on `y` \\ simp[outputsexp_def]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ fs[]);

val outputsexp_valid = Q.store_thm("outputsexp_valid",
  `∀x. valid_sexp (outputsexp x)`,
  cheat);

val _ = export_theory()
