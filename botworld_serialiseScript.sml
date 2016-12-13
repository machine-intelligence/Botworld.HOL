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
val _ = temp_add_monadsyntax()

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

val sexpbytes_def = Define`
  (sexpbytes (SX_STR s) = SOME (MAP (n2w o ORD) s)) ∧
  (sexpbytes _ = (NONE:word8 list option))`;

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
                         (sexplist sexpbytes (EL 1 args))) ++
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
                                                 (sexplist sexpbytes (EL 1 args)))
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
  sexpobservation s = do
    (name,event,private) <- sexppair sexpname (sexppair sexpevent sexpprivateData) s;
    return <| name := name; event := event; private := private |>
  od
`;

val decode_bytes_def = Define`
  decode_bytes f (bytes:word8 list) = do
    s <- parse_sexp (MAP (CHR o w2n) bytes);
    f s
  od`;

val _ = overload_on("decode_observation",``decode_bytes sexpobservation``);

val decode_command_def = Define`
  decode_command c =
    option_CASE (decode_bytes sexpcommand c) Pass I`;

val decode_register_def = Define`
  decode_register n f d m =
    if LENGTH m ≤ n then d else
      option_CASE (decode_bytes f (EL n m)) d I`;

val read_code_def = Define`
  read_code = decode_register 0 (sexplist sexptop) []`;

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

val bytessexp_def = Define`
  bytessexp (bs:word8 list) = listsexp (MAP (SX_NUM o w2n) bs)`;

val namesexp_def = Define`
  namesexp nm = SX_CONS (SX_NUM nm.built_step) (SX_CONS (coordsexp nm.built_coord) (SX_NUM nm.id))`;

val commandsexp_def = Define`
  (commandsexp (Move num) = listsexp [SX_SYM "Move"; SX_NUM num]) ∧
  (commandsexp (Lift num) = listsexp [SX_SYM "Lift"; SX_NUM num]) ∧
  (commandsexp (Drop num) = listsexp [SX_SYM "Drop"; SX_NUM num]) ∧
  (commandsexp (Inspect nm) = listsexp [SX_SYM "Inspect"; namesexp nm]) ∧
  (commandsexp (Destroy nm) = listsexp [SX_SYM "Destroy"; namesexp nm]) ∧
  (commandsexp (Build ns m) = listsexp [SX_SYM "Build"; listsexp (MAP SX_NUM ns); listsexp (MAP bytessexp m)]) ∧
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
  (privateDatasexp (pInspected proc mem) =
   listsexp [SX_SYM "pInspected";
             SX_NUM proc;
             listsexp (MAP bytessexp mem)])`;

val observationsexp_def = Define`
  observationsexp obs =
    SX_CONS (namesexp obs.name)
      (SX_CONS (eventsexp obs.event) (privateDatasexp obs.private))`;

val encode_bytes_def = Define`
  encode_bytes f x =
    MAP (n2w o ORD) (print_sexp (f x)) : word8 list`;

val _ = overload_on("encode_observation",``encode_bytes observationsexp``);

val encode_register_def = Define`
  encode_register n f x m =
    if LENGTH m ≤ n then m else
    let z = LENGTH (EL n m) in
    let bs = encode_bytes f x in
    if z < LENGTH bs then m
    else LUPDATE (bs ++ REPLICATE (z - LENGTH bs) (n2w(ORD #" "))) n m`;

val LENGTH_encode_register = Q.store_thm("LENGTH_encode_register[simp]",
  `LENGTH (encode_register n f x m) = LENGTH m`,
  rw[encode_register_def]);

val clear_register_def = Define`
  clear_register n (m:word8 list list) =
    if LENGTH m ≤ n then m else
      LUPDATE (REPLICATE (LENGTH (EL n m)) 0w) n m`;

(* botworld ffi *)

(* ffi state = word8 list list
   conventions:
   first element is encoded observation,
   remaining elements are bot's memory
   thus 2nd and 3rd elements are
   the previous command and policy
*)

val ffi_get_num_def = Define`
  ffi_get_num n bytes =
    let s = print_sexp (SX_NUM n) in
    if LENGTH bytes ≤ LENGTH s then
      (MAP (K (0w:word8)) bytes)
    else
      (MAP (n2w o ORD) s ++ GENLIST (K 0w) (LENGTH bytes - LENGTH s))`;

val botworld_get_count_def = Define`
  botworld_get_count st bytes =
    Oracle_return st (ffi_get_num (LENGTH st) bytes)`;

val botworld_get_size_def = Define`
  botworld_get_size n st bytes =
  if n < LENGTH st then
    Oracle_return st (ffi_get_num (LENGTH (EL n st)) bytes)
  else Oracle_fail`;

val botworld_read_def = Define`
  botworld_read st bytes =
    if LENGTH bytes = LENGTH (FLAT st) then
      Oracle_return st (FLAT st)
    else Oracle_fail`;

val UNFLAT_def = Define`
  (UNFLAT [] _ = []) ∧
  (UNFLAT (n::ns) ls  =
   (TAKE n ls)::(UNFLAT ns (DROP n ls)))`;

val botworld_write_def = Define`
  botworld_write st bytes =
    if LENGTH (FLAT (TL st)) ≤ LENGTH bytes then
      let extra = LENGTH bytes - LENGTH (FLAT (TL st)) in
        Oracle_return (HD st::TAKE extra bytes::(UNFLAT (MAP LENGTH st) (DROP extra bytes))) bytes
    else Oracle_fail`;

val botworld_oracle_def = Define`
  botworld_oracle n =
    if n = "get_count" then botworld_get_count else
    if n = "read" then botworld_read else
    if n = "write" then botworld_write else
    botworld_get_size (num_from_dec_string n)`;

(* CakeML declarations of helper functions for interfacing with the Botworld FFI *)
(* TODO: these should be replaced with CF verified functions *)

(*
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
*)

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

val bytessexp_11 = Q.store_thm("bytessexp_11[simp]",
  `∀l1 l2. bytessexp l1 = bytessexp l2 ⇔ l1 = l2`,
  rw[bytessexp_def,EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac \\ rw[]);

val commandsexp_11 = Q.store_thm("commandsexp_11[simp]",
  `∀ c c'. commandsexp c = commandsexp c' ⇔ c = c'`,
  Induct >> gen_tac >> cases_on `c'` >> fs[commandsexp_def, listsexp_11]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac \\ rw[]);

val intsexp_valid = Q.store_thm("intsexp_valid[simp]",
  `∀i. valid_sexp (intsexp i)`,
  rw[intsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ EVAL_TAC);

val coordsexp_valid = Q.store_thm("coordsexp_valid[simp]",
  `∀p. valid_sexp (coordsexp p)`,
  Cases \\ simp[]);

val namesexp_valid = Q.store_thm("namesexp_valid[simp]",
  `∀n. valid_sexp (namesexp n)`,
  Cases \\ simp[namesexp_def]);

val bytessexp_valid = Q.store_thm("bytessexp_valid[simp]",
  `∀ls. valid_sexp (bytessexp ls)`,
  rw[bytessexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP]);

val commandsexp_valid = Q.store_thm("commandsexp_valid[simp]",
  `∀c. valid_sexp (commandsexp c)`,
  Cases \\ simp[commandsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ rpt conj_tac
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP]);

val _ = export_theory()
