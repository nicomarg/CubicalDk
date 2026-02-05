require open ctt.Var.Syntax;
require open ctt.Lemmas.TermEquality;

require open ctt.Lemmas.Commutations;
require open ctt.Var.Subst_def;
symbol aux_teq_shift_shift_var (i j n : DBId) :
  DBLe i j → DBEq (dbshift i (dbshift j n)) (dbshift (dbsucc j) (dbshift i n));

rule aux_teq_shift_shift_var db0 $j $n _ ↪ DBRefl (dbsucc (dbshift $j $n))
with aux_teq_shift_shift_var (dbsucc _) (dbsucc _) db0 _ ↪ DBRefl db0
with aux_teq_shift_shift_var (dbsucc $i) (dbsucc $j) (dbsucc $n) $h ↪
      dbcong dbsucc (aux_teq_shift_shift_var $i $j $n (dble_S_n $h))
with swap_shift_shift $i $j (tvar $n) $h ↪ dbcongT tvar (aux_teq_shift_shift_var $i $j $n $h);

require open ctt.Lemmas.Derivations.Shifting;
// require open ctt.Univ.Syntax;
// require open ctt.Contexts.Definition;
symbol der_context_shift_n [Γ : Context] [sa : Sort] [A : Typ] (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der_type Γ A sa) :
  DBLe (dbsucc i) (len (sc_to_ctx sc)) →
  der (sc_to_sctx dA sc) (tvar (dbshift id i)) (tshift id (shiftgetΓ (sc_to_ctx sc) i)) (getS (sc_to_ctx sc) i);
//  ≔
// begin
//   assume Γ sa A id i sc dA h;
//   refine JT (shiftget_ctx_sctx i sc dA) _;
//   refine Jl (getS_ctx_sctx i sc dA) _;
//   refine der_var _;
//   refine len_ctx_sctx i sc dA h
// end;
rule der_shift_n $id $sc $d (@der_var _ $i $le) ↪ der_context_shift_n $id $i $sc $d $le;
rule der_context_shift_n db0 _ (SC0 _) _ $h
  ↪ der_var (dble_n_S $h)
with der_context_shift_n (dbsucc $id) db0 (SCSucc [_] [_] [$A] _ _) _ _
  ↪ JT (swap_tshift_tshift db0 $id $A (dble_0_n _)) (der_var dble_db0)
with der_context_shift_n (dbsucc $id) (dbsucc $i) (SCSucc $sc $dA) $d $h
  ↪ JT (swap_tshift_tshift db0 $id (tshiftΓ (sc_to_ctx $sc) $i (get (sc_to_ctx $sc) $i)) (dble_0_n _)) (der_shift0 (der_type_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc) (der_context_shift_n $id $i $sc $d (dble_S_n $h)));

// require open ctt.Translation;
// require open ctt.Univ.Subst;
require open ctt.Lemmas.Derivations;
require open ctt.Lemmas.Inversions;
rule inv_type $dΓ (@der_var _ $id _) ↪ der_type_shift $id $dΓ (der_getΓ $id $dΓ);

// // TODO translation of variables (and thus translation contexts)
// require open ctt.Translation.Context;
// require open ctt.ctt;
// symbol tΓ : TContext;
// symbol id : DBId;
// symbol Γ : Context;
// symbol h : DBLe (dbsucc id) (len Γ);
// symbol p ≔ convert_T tΓ (der_shift id (τ_dΓ tΓ) (tgetD id tΓ)) (der_shift id (τ_dΓ tΓ) (der_getΓ id (τ_dΓ tΓ)));
// symbol t_var ≔ convtransp [τ_lev (tgetS id tΓ)] [(τ_T tΓ (der_shift id (τ_dΓ tΓ) (tgetD id tΓ)))] [(τ_T tΓ [_] [(tgetS id tΓ)] (der_shift id (τ_dΓ tΓ) (der_getΓ id (τ_dΓ tΓ))))] p (tgetShift id tΓ);
require open ctt.Var.TContext;
rule τ_type $Γ (@der_var _ $id _) ↪ tgetTShift $id $Γ;
rule τ $Γ (@der_var _ $id _) ↪ tgetShift $id $Γ;
// rule τ $Γ (@der_var _ $id _) ↪
//   let p ≔ convert_T $Γ (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) (der_shift $id (τ_dΓ $Γ) (der_getΓ $id (τ_dΓ $Γ))) in
//      convtransp p (tgetShift $id $Γ);
require open ctt.Lemmas.Irrel;
rule τ_type_compat _ (@der_var _ _ _) ↪ convrefl;
rule τ_irrel_rec $Γ (@der_var _ $id _) (@der_var _ $id _) ↪ pgetHShift $id $Γ;

require open ctt.Lemmas.Translation;
symbol τ_context_shift_n [Γ : TContext] [sa : Sort] [A : Typ] (id i : DBId)
                         (sc : ShiftTContext Γ id) (dA : der_type (τ_Γ Γ) A sa)
                         (a : eps (τ_T Γ dA)) (h : DBLe (dbsucc i) (len (tsc_to_ctx sc))) :
  tH (tgetShift i (tsc_to_tc sc))
     (τ (tsc_to_stc dA a sc) (der_context_shift_n id i (tsc_to_sc sc) dA h));

rule @τ_shift_n $Γ _ $s' _ _ $A $id $sc (@der_var _ $i $h) $dA $a ↪ @τ_context_shift_n $Γ $s' $A $id $i $sc $dA $a $h;

rule τ_context_shift_n db0 $i (TSC0 $Γ _) $d $x _ ↪
     tgetShift_eq $i $Γ $d $x;
rule τ_context_shift_n (dbsucc $id) db0 (@TSCSucc _ _ $A _ $sc $dA $a) $d $x _ ↪ 
     heq_trans (heq_conj
                (heq_of_transport $a
                                   (τ_shiftT_n _ $sc $dA $d $x))
                (τ_shift0T_eq (tsc_to_tc $sc) $dA $dA $a)
                (τ_shift0T_eq (tsc_to_stc $d $x $sc)
                              (der_type_shift_n _ (tsc_to_sc $sc) $d $dA)
                              (der_type_shift_n _ (tsc_to_sc $sc) $d $dA)
                              (convtransp (τ_shiftT_n _ $sc $dA $d $x) $a)))
               (heq_sym (Jτ (tsc_to_stc $d $x (TSCSucc $sc $dA $a)) (TRefl _)
                            (swap_tshift_tshift db0 $id $A (dble_0_n $id))
                            (der_var (dble_n_S (dble_0_n (len (sc_to_sctx $d (tsc_to_sc $sc))))))));
rule τ_context_shift_n (dbsucc $id) (dbsucc $i) (TSCSucc $sc $dA $a) $d $x $h ↪
     heq_trans
     (heq_sym (heq_of_transport
               (tgetShift $i (tsc_to_tc $sc))
               (τ_shift0T_eq (tsc_to_tc $sc)
                             (der_type_shift $i (τ_dΓ (tsc_to_tc $sc)) (tgetD $i (tsc_to_tc $sc)))
                             $dA $a)))
     (heq_trans (τ_context_shift_n $id $i $sc $d $x (dble_S_n $h))
                (heq_trans 
                 (τ_shift0_eq (tsc_to_stc $d $x $sc)
                              (sc_to_dsctx $d (tsc_to_sc $sc))
                              (der_context_shift_n $id $i (tsc_to_sc $sc) $d (dble_S_n $h))
                              (der_type_shift_n _ (tsc_to_sc $sc) $d $dA)
                              (convtransp (τ_shiftT_n _ $sc $dA $d $x) $a))
                 (heq_sym (Jτ (tsc_to_stc $d $x (TSCSucc $sc $dA $a)) (TRefl _)
                              (swap_tshift_tshift db0 $id (tshiftΓ (sc_to_ctx (tsc_to_sc $sc)) $i (get (sc_to_ctx (tsc_to_sc $sc)) $i)) (dble_0_n $id))
                              (der_shift_n db0 (SC0 (sc_to_dsctx $d (tsc_to_sc $sc))) (der_type_shift_n $id (tsc_to_sc $sc) $d $dA)
                                           (der_context_shift_n $id $i (tsc_to_sc $sc) $d (dble_S_n $h)))))));
