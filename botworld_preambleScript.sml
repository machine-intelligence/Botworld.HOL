open HolKernel boolLib bossLib ml_translatorLib
     holSyntaxTheory
     botworld_dataTheory botworld_serialiseTheory
local open std_preludeLib in end

val _ = new_theory"botworld_preamble";

val _ = translate_into_module "Botworld";

val _ = std_preludeLib.std_prelude();

(* TODO: want a version of sexp that uses mlstring rather than string *)

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

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
