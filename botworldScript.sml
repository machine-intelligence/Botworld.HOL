open HolKernel Parse boolLib bossLib realTheory lcsymtacs
open botworld_dataTheory botworld_serialiseTheory botworld_preambleTheory
open terminationTheory initialProgramTheory

(* TODO: initialProgram should be imported by termination *)

val _ = temp_tight_equality();

val _ = new_theory"botworld"

(* Port of Botworld to more idiomatic HOL *)

val neighbour_coords_def = Define`
  neighbour_coords ((x,y):coordinate) =
    [(x  ,y+1)
    ;(x+1,y+1)
    ;(x+1,y  )
    ;(x+1,y-1)
    ;(x  ,y-1)
    ;(x-1,y-1)
    ;(x-1,y  )
    ;(x-1,y+1)]`;

val opposite_def = Define`
  opposite d = (d + 4) MOD 8`;

val neighbours_def = Define`
  neighbours (g:grid) c = MAP (FLOOKUP g) (neighbour_coords c)`;

(* environment phase *)

val contested_def = Define`
  contested sq i ⇔
    i < LENGTH sq.items ∧
    1 < LENGTH
        (FILTER (λr. case r.command of
                     | Lift li => li = i ∧ canLift r (EL i sq.items)
                     | Build is m => MEM i is ∧
                                     EVERY (λi. i < LENGTH sq.items) is ∧
                                     IS_SOME (construct (MAP (λi. EL i sq.items) is) m)
                     | _ => F)
         sq.robots)`;

val fled_def = Define`
  (fled nb (Move dir) ⇔ dir < LENGTH nb ∧ IS_SOME (EL dir nb)) ∧
  (fled nb _ = F)`;

val inspectAttempts_def = Define`
  inspectAttempts intents i =
    LENGTH (FILTER (λc. c = Inspect i) intents)`;

val inspectShielded_def = Define`
  inspectShielded robots i ⇔
    inspectAttempts (MAP robot_command robots) i ≤
    LENGTH (FILTER isInspectShield (EL i robots).inventory)`;

val destroyAttempts_def = Define`
  destroyAttempts intents i =
    LENGTH (FILTER (λc. c = Destroy i) intents)`;

val destroyShielded_def = Define`
  destroyShielded robots i ⇔
    destroyAttempts (MAP robot_command robots) i ≤
    LENGTH (FILTER isDestroyShield (EL i robots).inventory)`;

val act_def = Define`
  act sq nb ri = if ri < LENGTH sq.robots then
    let r = EL ri sq.robots in
    case r.command of
    | Move dir =>
      if dir < LENGTH nb then
        (if IS_SOME (EL dir nb) then MovedOut else MoveBlocked) dir
      else MoveBlocked dir
    | Lift i =>
      if i < LENGTH sq.items then
        if canLift r (EL i sq.items) then
          if contested sq i then GrappledOver i else Lifted i
        else CannotLift i
      else Invalid
    | Drop i =>
      if i < LENGTH r.inventory then
        Dropped i
      else Invalid
    | Inspect i =>
      if i < LENGTH sq.robots then
        if ¬fled nb (EL i sq.robots).command then
          if ¬inspectShielded sq.robots i then
            Inspected i (EL i sq.robots)
          else InspectBlocked i
        else InspectTargetFled i
      else Invalid
    | Destroy i =>
      if i < LENGTH sq.robots then
        if ¬fled nb (EL i sq.robots).command then
          if ¬destroyShielded sq.robots i then
            Destroyed i
          else DestroyBlocked i
        else DestroyTargetFled i
      else Invalid
    | Build is m =>
      if EVERY (λi. i < LENGTH sq.items) is then
        if ¬EXISTS (contested sq) is then
          case construct (MAP (λi. EL i sq.items) is) m of
          | NONE => Invalid
          | SOME r => Built is r
        else BuildInterrupted is
      else Invalid
    | Pass => Passed
  else Invalid`;

val localActions_def = Define`
  localActions sq nb =
    GENLIST (act sq nb) (LENGTH sq.robots)`;

val defend_def = Define`
  defend intents i =
    dropN (destroyAttempts intents i) isDestroyShield o
    dropN (inspectAttempts intents i) isInspectShield`;

val updateInventory_def = Define`
  updateInventory sq i a =
    let r = EL i sq.robots in
    let intents = MAP robot_command sq.robots in
    case a of
    | MovedOut _ => r
    | Lifted n => r with inventory := (EL n sq.items)::(defend intents i r.inventory)
    | Dropped n => r with inventory := (defend intents i (remove_indices ($= n) 0 r.inventory))
    | _ => r with inventory := defend intents i r.inventory`;

val incomingFrom_def = Define`
  (incomingFrom dir NONE = []) ∧
  (incomingFrom dir (SOME sq) =
   FLAT (MAP (λr. if r.command = Move (opposite dir) then [(r,MovedIn dir)] else []) sq.robots))`;

val event_def = Define`
  event sq nb =
    let actions = localActions sq nb in
    let veterans = GENLIST (λi. updateInventory sq i (EL i actions)) (LENGTH sq.robots) in
    let fallen = FLAT (GENLIST (λi. if MEM (Destroyed i) actions then
                                      [<|components := shatter (EL i veterans)
                                        ;possessions := (EL i veterans).inventory|>]
                                    else [])
                       (LENGTH veterans)) in
    <| robotActions :=
       let immigrations = FLAT (GENLIST (λi. incomingFrom i (EL i nb)) (LENGTH nb)) in
       let children = FLAT (MAP (λa. case a of Built _ r => [r] | _ => []) actions) in
       ZIP (veterans,actions) ++ immigrations ++
       ZIP (children, REPLICATE (LENGTH children) Created)
     ; untouchedItems :=
       remove_indices
         (λi. EXISTS (λa. case a of Lifted l => i = l
                                  | Built is _ => MEM i is
                                  | _ => F)
              actions)
         0 sq.items
     ; droppedItems :=
       FLAT
         (MAP (λ(r,a). case a of Dropped i => [EL i r.inventory]
                               | _ => [])
              (ZIP(sq.robots,actions)))
     ; fallenItems := fallen
     |>`;

(* computation phase *)

val private_def = Define`
  (private (Inspected _ r) = pInspected r.processor r.memory) ∧
  (private Invalid = pInvalid) ∧
  (private _ = pNothing)`;

val ffi_from_observation_def = Define`
  ffi_from_observation (obs:observation) =
    initial_ffi_state botworld_oracle
      (botworld_initial_state obs)`;

val prepare_def = Define`
  prepare ev (i,r,a) = ((i, ev, private a), r)`;

val run_policy_def = Define`
  run_policy policy clock obs =
    let ffi = ffi_from_observation obs in
    let (st,env) = THE (prim_sem_env ffi) in
    let (st',c,res) = evaluate_prog (st with clock := clock) env policy in
    st'.ffi.ffi_state.bot_output`;

val runMachine_def = Define`
  runMachine (obs,r) =
    let (command,prog) = run_policy r.memory r.processor obs in
    r with <| command := command; memory := prog |>`;

val computeSquare_def = Define`
  computeSquare ev =
    <| items :=
         ev.untouchedItems ++ ev.droppedItems ++
         FLAT (MAP (λc. c.components ++ c.possessions) ev.fallenItems)
     ; robots :=
         let ls = GENLIST (λi. (i,EL i ev.robotActions)) (LENGTH ev.robotActions) in
         let ls = FILTER (λ(i,r,a). ¬isMovedOut a ∧ ¬MEM (Destroyed i) (MAP SND ev.robotActions)) ls in
           MAP (runMachine o prepare ev) ls
     |>`;

(* state *)

val computeEvents_def = Define`
  computeEvents (g:grid) =
    FMAP_MAP2 (λ(c,sq). event sq (neighbours g c)) g`;

val step_def = Define`
  step g = computeSquare o_f (computeEvents g)`;

val _ = Datatype`
  state_with_hole = <| state : grid
                     ; focal_coordinate : coordinate
                     ; focal_index : num
                     |>`;

val wf_state_with_hole_def = Define`
  wf_state_with_hole s ⇔
    (∃sq.
      FLOOKUP s.state s.focal_coordinate = SOME sq ∧
      s.focal_index < LENGTH sq.robots ∧
      (EL (s.focal_index) sq.robots).focal) ∧
    (∀sq c i.
       FLOOKUP s.state c = SOME sq ∧
       i < LENGTH sq.robots ∧
       (c,i) ≠ (s.focal_coordinate,s.focal_index)
       ⇒ ¬(EL i sq.robots).focal)`;

val square_update_robot_def = Define`
  square_update_robot f idx sq =
    sq with robots updated_by
      LUPDATE (f (EL idx sq.robots)) idx`;

val fill_def = Define`
  fill f s =
    s.state |+
    (s.focal_coordinate,
     square_update_robot f s.focal_index (s.state ' s.focal_coordinate))`;

val _ = overload_on("with_policy",``λc p.  robot_memory_fupd (K p) o robot_command_fupd (K c)``);

val find_focal_def = Define`
  find_focal g =
    @p. ∃c i sq. p = (c,i) ∧ FLOOKUP g c = SOME sq ∧ i < LENGTH sq.robots ∧ (EL i sq.robots).focal`;

val steph_def = Define`
  steph command s =
    let events = computeEvents (fill (robot_command_fupd (K command)) s) in
    let ev = events ' s.focal_coordinate in
    if EXISTS (λa. a = Destroyed s.focal_index ∨
                   ∃r. a = Inspected s.focal_index r)
              (MAP SND ev.robotActions)
    then NONE else
    let a = SND (EL s.focal_index ev.robotActions) in
    let s' = computeSquare o_f events in
    let (c,i) = find_focal s' in
    SOME
      ((s.focal_index, ev, private a),
       <| state := s'
        ; focal_coordinate := c
        ; focal_index := i
        |>)`;

(* histories *)

val _ = Parse.type_abbrev("history",``:grid llist``);

val hist_def = Define`
  hist s = LUNFOLD (λs. SOME (step s,s)) s`;

(* utility *)

val _ = Parse.type_abbrev("utilityfn",``:history -> real``);

val utilityfn_def = Define`
  utilityfn (u:utilityfn) ⇔
    (∀x. 0 ≤ u x ∧ u x ≤ 1) ∧
    ∀s h h'. u h ≤ u h' ⇒ u (s ::: h) ≤ u (s ::: h')`;

val discount_def = Define`
  discount (u:utilityfn) = sup { (u (s ::: h) - u (s ::: h')) / (u h - u h') | (s,h,h') | u h ≠ u h' }`

val weaklyExtensional_def = Define`
  weaklyExtensional (u:utilityfn) ⇔
    ∀s p1 p2 h. u (fill p1 s ::: h) = u (fill p2 s ::: h)`;

(* suggester/verifier *)

val dominates_def = Define`
  (dominates (:α) (Trust k) (S,u) cp cp' ⇔
     LCA k (UNIV:α set) ⇒
     ∀s. s ∈ S ⇒
       u (hist (fill (UNCURRY with_policy cp') s)) ≤
       u (hist (fill (UNCURRY with_policy cp) s))) ∧
  (dominates (:α) MP (S,u) cp cp' ⇔
   ∀k. LCA k (UNIV:α set) ⇒
       ∀s. s ∈ S ⇒
         u (hist (fill (UNCURRY with_policy cp') s)) ≤
         u (hist (fill (UNCURRY with_policy cp) s))
           + ((discount u) pow k))`;

val level_to_deep = Define`
  level_to_deep (l:level) = (ARB:exp) (* TODO *)`;

val term_to_deep = Define`
  term_to_deep (t:term) = (ARB:exp) (* TODO *)`;

(* -- *)

val sv_def = Define`
  sv l Stm utm π σ =
    (* assumes preamble gets run by botworld, defining all the requisite types *)
    (* preamble also includes helper functions:
       Botworld.read_observation : unit -> observation
       Botworld.read_output : unit -> command * prog
       Botworld.check_theorem : thm * level * term * observation * term * (command * prog) * (command * prog) -> bool
       However, the preamble syntactically contains no FFI-writing (on FFI 2) capability.
       This is declared separately (by write_output_dec) _after_ the suggester
       is defined, so it is easy to show that the suggester does not write anything.
       The write helper has this signature:
       Botworld_writer.write_output : command * prog -> unit
    *)
    (* assume σ is an expression that is closed by the definitions of the
       preamble and two variables "observation" and "fallback", and it returns
       a (command * prog * thm) option *)
    [Tdec(Dlet(Pvar"suggester")(Fun "observation" (Fun "fallback" σ)));
     Tmod"Botworld_writer"NONE[write_output_dec]] ++
    π (* this will read the observation and write the fallback *) ++
    [Tdec(Dlet(Pvar"observation")(App Opapp [Var(Long"Botworld""read_observation");Con NONE []]));
     Tdec(Dlet(Pvar"fallback")(App Opapp [Var(Long"Botworld""read_output");Con NONE []]));
     Tdec(Dlet(Pvar"result")
           (Mat (App Opapp [App Opapp [Var(Short"suggester");Var(Short"observation")];Var(Short"fallback")])
              [(Pcon(SOME(Short"NONE"))[],Con NONE [])
              ;(Pcon(SOME(Short"SOME"))[Pcon NONE [Pvar"policy";Pvar"thm"]],
               If (App Opapp
                   [Var(Long"Botworld""check_theorem");
                    Con NONE
                      [Var(Short"thm")
                      ;level_to_deep l
                      ;term_to_deep Stm
                      ;Var(Short"observation")
                      ;term_to_deep utm
                      ;Var(Short"policy")
                      ;Var(Short"fallback")
                      ]])
                   (App Opapp [Var(Long"Botworld""write_output");Var(Short"policy")])
                   (Con NONE []))]))]`;

val _ = export_theory()
