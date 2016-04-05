open HolKernel boolLib bossLib ml_translatorLib
     holSyntaxTheory
     botworld_dataTheory
     botworld_serialiseTheory
local open std_preludeLib in end

val _ = new_theory"botworld_preamble";

val _ = translate_into_module "Botworld";

val _ = std_preludeLib.std_prelude();

(* TODO: want a version of sexp that uses mlstring rather than string *)
(* more precisely, here are some example steps to follow:
   1. Define a copy of sexp (from $HOLDIR/examples/formal-languages/context-free/simpleSexpScript.sml
      that uses mlstring instead of string
   2. Define conversions between old sexp and new sexp (mlstringTheory already has the conversions between string and mlstring)
   3. Prove some rewrite rules?
   4. Apply some transformations (either rewrites, or automatic definitions of
      new constants if necessary...) to the below definitions, so that the
      translator sees mlstring.
*)

val _ = Datatype `
  mlsexp = sx_cons mlsexp mlsexp
         | sx_sym mlstring
         | sx_num num
         | sx_str mlstring
`

val sexp_of_mls_def = Define `
  sexp_of_mls (sx_cons s1 s2) = SX_CONS (sexp_of_mls s1) (sexp_of_mls s2) ∧
  sexp_of_mls (sx_sym (strlit s)) = SX_SYM s ∧
  sexp_of_mls (sx_num n) = SX_NUM n ∧
  sexp_of_mls (sx_str (strlit s)) = SX_STR s
`
val _ = export_rewrites["sexp_of_mls_def"];

val mls_of_sexp_def = Define `
  mls_of_sexp (SX_CONS s1 s2) = sx_cons (mls_of_sexp s1) (mls_of_sexp s2) ∧
  mls_of_sexp (SX_SYM s) = sx_sym (strlit s) ∧
  mls_of_sexp (SX_NUM n) = sx_num n ∧
  mls_of_sexp (SX_STR s) = sx_str (strlit s)
`
val _ = export_rewrites["mls_of_sexp_def"];

val mls_sexp_inv = Q.prove(
  `!s. mls_of_sexp (sexp_of_mls s) = s`,
  rpt Induct >> rw[mls_of_sexp_def,sexp_of_mls_def]
)

val sexp_mls_inv = Q.prove(
  `!s. sexp_of_mls (mls_of_sexp s) = s`,
  rpt Induct >> rw[mls_of_sexp_def,sexp_of_mls_def]
)

val mlsexp_factors = Q.prove(
  `!f. ?f'. f = f' o mls_of_sexp`,
  rw[FUN_EQ_THM] >> qexists_tac `f o sexp_of_mls` >> rw[sexp_mls_inv]
)

val sexp_factors = Q.prove(
  `!f. ?f'. f = f' o sexp_of_mls`,
  rw[FUN_EQ_THM] >> qexists_tac `f o mls_of_sexp` >> rw[mls_sexp_inv]
)

val case_sexp_of_mls = Q.store_thm("case_sexp_of_mls",
  `(case sexp_of_mls x of
    | SX_CONS h t => f1 h t
    | SX_SYM s => f2 s
    | SX_NUM n => f3 n
    | SX_STR s => f4 s)
   =
   (case x of
    | sx_cons h t => f (sexp_of_mls h) (sexp_of_mls t)
    | sx_sym (strlit s) => f2 s
    | sx_num n => f3 n
    | sx_str (strlit s) => f4 s)`,
  match_mp_tac EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]);

val ml_strip_sxcons_def = Define`
  ml_strip_sxcons = OPTION_MAP (MAP mls_of_sexp) o strip_sxcons o sexp_of_mls`;

val compose_mlsexp_CASE = Q.store_thm("compose_mlsexp_CASE",
  `g (mlsexp_CASE m f f1 f2 f3) =
   mlsexp_CASE m (($o g) o f) (g o f1) (g o f2) (g o f3)`,
  Cases_on`m`\\EVAL_TAC);

(*
val OPTION_MAP_cases = Q.store_thm("OPTION_MAP_cases",
  `OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME (f y)`,
  CASE_TAC \\ EVAL_TAC)

``ml_strip_sxcons s``
|> SIMP_CONV std_ss [
    ml_strip_sxcons_def,combinTheory.o_DEF,
    Once simpleSexpTheory.strip_sxcons_def,case_sexp_of_mls,
    compose_mlsexp_CASE,optionTheory.OPTION_MAP_COMPOSE,
    listTheory.MAP,mls_sexp_inv]
*)

val res = translate simpleSexpTheory.strip_sxcons_def;
val res = translate simpleSexpParseTheory.print_space_separated_def;
val res = translate simpleSexpParseTheory.escape_string_def;
val res = translate simpleSexpParseTheory.print_sexp_def;
val res = translate fromSexpTheory.listsexp_def;
val res = translate fromSexpTheory.optsexp_def;
val res = translate fromSexpTheory.idsexp_def;
val res = translate fromSexpTheory.tctorsexp_def;
val res = translate fromSexpTheory.typesexp_def;
val res = translate fromSexpTheory.type_defsexp_def;
val res = translate fromSexpTheory.specsexp_def;

val litsexp_IntLit_alt = Q.prove(
  `∀i. litsexp (IntLit i) = if i < 0 then listsexp [SX_SYM "-"; ((&Num (ABS (-i))))] else &Num(ABS i)`,
  rw[fromSexpTheory.litsexp_def,integerTheory.INT_ABS]
  \\ `F` by intLib.COOPER_TAC)

val res = translate (
  fromSexpTheory.litsexp_def
  |> CONJUNCTS |> tl
  |> cons litsexp_IntLit_alt
  |> LIST_CONJ
)

val res = translate fromSexpTheory.patsexp_def;
val res = translate fromSexpTheory.opsexp_def;
val res = translate fromSexpTheory.lopsexp_def;
val res = translate fromSexpTheory.expsexp_def;
val res = translate fromSexpTheory.decsexp_def;
val res = translate fromSexpTheory.topsexp_def;
val res = translate commandsexp_def;
val res = translate outputsexp_def;

val res = translate (
  encode_output_def
  |> SIMP_RULE std_ss [FUN_EQ_THM,combinTheory.o_DEF]
  );

val res = translate (
  fromSexpTheory.sexppair_def
)

val res = translate fromSexpTheory.odestSXNUM_def;

val res = translate optionTheory.OPTION_BIND_def;

(* TODO: parse_sexp needs to be translated;
   look to CakeML v1 for how to translate the parser on wfGs
   e.g., see how coreloop_total is used to get rid of the side condition on WHILE etc.
*)

(*
requires parse_sexp
val res = translate (
  decode_observation_def
  |> SIMP_RULE std_ss [FUN_EQ_THM,combinTheory.o_DEF]
  );
*)

(* TODO: not sure what's going on here...

open patternMatchesLib

val res = translate (
  fromSexpTheory.sexppair_def
  |> CONV_RULE (STRIP_QUANT_CONV(RAND_CONV PMATCH_INTRO_CONV))
  )

val res = translate fromSexpTheory.odestSXNUM_def;

val res = translate optionTheory.OPTION_BIND_def;

val sexplist_alt = Q.prove(
  `∀p s. sexplist p s =
    PMATCH s
    [PMATCH_ROW (λ(h,t). SX_CONS h t) (λ(h,t). T) (λ(h,t). OPTION_BIND (p h) (λph. OPTION_BIND (sexplist p t) (λpt. SOME (ph::pt))));
     PMATCH_ROW (λ(). SX_SYM "nil") (λ(). T) (λ(). SOME []);
     PMATCH_ROW (λ_. _) (λ_. T) (λ_. NONE)]`,
  rw[Once fromSexpTheory.sexplist_def]
  \\ BasicProvers.CASE_TAC
  \\ fsrw_tac[PMATCH_SIMP_ss][] \\ rw[]
  \\ fsrw_tac[PMATCH_SIMP_ss][]);

val res = translate sexplist_alt;

val res = translate (
  decode_observation_def
  |> SIMP_RULE std_ss [FUN_EQ_THM,combinTheory.o_DEF]
  );
*)

(* preamble declarations *)

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

(* encode_output_dec obtained by translating botworld_serialiseTheory.encode_output_def *)

val write_output_dec_def = Define`
  write_output_dec =
    Dlet(Pvar"write_output")
      (Fun "x"
        (App (FFI 2)
          [App Opapp
             [Var(Long"ByteArray""fromList");
              App Opapp [Var(Long"Botworld""encode_output");Var(Short"x")]]]))`;

val output_length_rec_def = Define`
    output_length_rec bs n =
      if EVERY (λb. b = 0w) bs
      then INL (2 * n)
      else INR (OPTION_BIND (parse_sexp (MAP (CHR o w2n) bs)) odestSXNUM)`;

val get_input_length_dec_def = Define`
  get_input_length_dec =
    Dlet(Pvar "get_input_length")
    (Fun "x"
      (Letrec [("f","n",
                (Let (SOME "bs") (App Aw8alloc [Var(Short"n")])
                (Let NONE (App (FFI 0) [Var(Short"bs")])
                (Mat (App Opapp [App Opapp [Var(Long "Botworld" "output_length_rec"); Var(Short"bs")]; Var(Short "n")])
                     [(Pcon (SOME(Short "inl")) [Pvar "n"], App Opapp [Var(Short"f"); Var(Short"n")] )
                     ;(Pcon (SOME(Short "inr")) [Pcon (SOME(Short "some")) [Pvar "len"]], Var(Short"len"))
                     ]))))] (App Opapp [Var(Short "f") ; Lit(IntLit 1)])))`

val read_observation_dec_def = Define`
  read_observation_dec =
    Dlet (Pvar "read_observation")
      (Fun "x"
           (Let (SOME "bs") (App Aw8alloc [App Opapp [Var(Short"get_input_length"); Var(Short"x")]])
           (Let NONE (App (FFI 1) [Var(Short"bs")])
           (App Opapp [Var(Long "Botworld" "decode_observation"); App Opapp [Var(Long "ByteArray" "toList") ; Var(Short"bs")]]))))`

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
