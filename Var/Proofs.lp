require open ctt.Symbols;
require open ctt.Contexts.DeBruijn;
require open ctt.Contexts.Typing;
require open ctt.Var.Syntax;
require open ctt.Lemmas.TermEquality;

require open ctt.Contexts.Shift;
require open ctt.Lemmas.Commutations;
require open ctt.Var.Subst;
symbol aux_teq_shift_shift_var (i j n : DBId) :
  DBLe i j → DBEq (dbshift i (dbshift j n)) (dbshift (dbsucc j) (dbshift i n));

rule aux_teq_shift_shift_var db0 $j $n _ ↪ DBRefl (dbsucc (dbshift $j $n))
with aux_teq_shift_shift_var (dbsucc _) (dbsucc _) db0 _ ↪ DBRefl db0
with aux_teq_shift_shift_var (dbsucc $i) (dbsucc $j) (dbsucc $n) $h ↪
      dbcong dbsucc (aux_teq_shift_shift_var $i $j $n (dble_S_n $h))
with swap_shift_shift $i $j (tvar $n) $h ↪ dbcongT tvar (aux_teq_shift_shift_var $i $j $n $h);

require open ctt.Lemmas.Derivations.Shifting;
require open ctt.Univ.Syntax;
require open ctt.Contexts.Definition;
symbol der_context_shift_n [Γ : Context] [sa : Sort] [A : Term] (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa)) :
  DBLe (dbsucc i) (len (sc_to_ctx sc)) →
  der (sc_to_sctx dA sc) (tvar (dbshift id i)) (shift id (shiftgetΓ (sc_to_ctx sc) i)) (getS (sc_to_ctx sc) i) ≔
begin
  assume Γ sa A id i sc dA h;
  refine JT (shiftget_ctx_sctx i sc dA) _;
  refine Jl (getS_ctx_sctx i sc dA) _;
  refine der_var _;
  refine len_ctx_sctx i sc dA h
end;
rule der_shift_n $id $sc $d (@der_var _ $i $le) ↪ der_context_shift_n $id $i $sc $d $le;

require open ctt.Translation;
require open ctt.Univ.Subst;
require open ctt.Lemmas.Derivations;
rule inv_type $dΓ (@der_var _ $id _) ↪ der_shift $id $dΓ (der_getΓ $id $dΓ);

// TODO translation of variables (and thus translation contexts)
require open ctt.Translation.Context;
require open ctt.ctt;
symbol tΓ : TContext;
symbol id : DBId;
symbol Γ : Context;
symbol h : DBLe (dbsucc id) (len Γ);
symbol p ≔ convert_T tΓ (der_shift id (τ_dΓ tΓ) (tgetD id tΓ)) (der_shift id (τ_dΓ tΓ) (der_getΓ id (τ_dΓ tΓ)));
symbol t_var ≔ convtransp [τ_lev (tgetS id tΓ)] [(τ_T tΓ (der_shift id (τ_dΓ tΓ) (tgetD id tΓ)))] [(τ_T tΓ [_] [(tgetS id tΓ)] (der_shift id (τ_dΓ tΓ) (der_getΓ id (τ_dΓ tΓ))))] p (tgetShift id tΓ);
rule τ $Γ (@der_var _ $id _) ↪
  let p ≔ convert_T $Γ (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) (der_shift $id (τ_dΓ $Γ) (der_getΓ $id (τ_dΓ $Γ))) in
     convtransp p (tgetShift $id $Γ);

