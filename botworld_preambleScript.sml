open HolKernel boolLib bossLib ml_translatorLib
     holSyntaxTheory
     botworld_dataTheory botworld_serialiseTheory
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

val res = translate decode_observation_def;

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
    output_length_rec bs n = if EVERY (λb. b = 0w) bs
                             then INL (2 * n)
                             else INR do p <- parse_sexp (MAP (CHR o w2n) bs) ; odestSXNUM p od
`

val get_input_length_dec_def = Define`
  get_input_length_dec =
    Dlet(Pvar "get_input_length")
    (Fun "x"
      (Letrec [("f","n", 
                (Let (SOME "bs") (App Aw8alloc [Var(Short"n")])
                (Let NONE (App (FFI 0) (Var(Short"bs"))))
                (Mat (App Opapp [App Opapp [Var(Long "Botworld" "output_length_rec"); Var(Short"bs")]; Var(Short "n")])
                     [(Pcon (SOME(Short "inl")) [Pvar "n"], App Opapp [Var(Short"f"); Var(Short"n")] )
                     ;(Pcon (SOME(Short "inr")) [Pcon (SOME(Short "some")) [Pvar "len"]], Var(Short"len"))
                     ])))] (App Opapp [Var(Short "f") ; Lit(IntLit 1)])))
`

val read_observation_dec_def = Define`
  read_observation_dec =
    Dlet (Pvar "read_observation")
      (Fun "x" 
           (Let (SOME "bs") (App Aw8alloc [App Opapp [Var(Short"get_input_length"); Var(Short"x")]]))
           (Let NONE (App (FFI 1) [Var(Short"bs")]))
           (App Opapp [Var(Long "Botworld" "decode_observation"); App Opapp [Var(Long "ByteArray" "toList") ; Var(Short"bs")]])
)
`

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();

