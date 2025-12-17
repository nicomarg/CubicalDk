require open ctt.Structural.Syntax;

require open ctt.Translation;
require open ctt.Lemmas.Irrel;
require open ctt.Structural.Lemmas;

rule τ_eqT_t1 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d
with τ_eqT_t2 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d;
rule τ_eqT_t1_compat _ (der_eqT_refl _ _ _ _) ↪ convrefl
with τ_eqT_t2_compat _ (der_eqT_refl _ _ _ _) ↪ convrefl;
rule τ_eqT _ (der_eqT_refl _ _ _ _) ↪ convrefl;

rule τ_eqT_t1 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t1 $Γ $d;
rule τ_eqT_t1_compat $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t2_compat $Γ $d
with τ_eqT_t2_compat $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t1_compat $Γ $d;
rule τ_eqT $Γ (der_eqT_sym _ _ _ _ $d) ↪ xsymmetry (τ_eqT $Γ $d);

rule τ_eqT_t1 $Γ (der_eqT_trans _ _ _ _ _ $d _) ↪ τ_eqT_t1 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_trans _ _ _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d;
rule τ_eqT_t1_compat $Γ (der_eqT_trans _ _ _ _ _ $d _) ↪ τ_eqT_t1_compat $Γ $d
with τ_eqT_t2_compat $Γ (der_eqT_trans _ _ _ _ _ _ $d) ↪ τ_eqT_t2_compat $Γ $d;
rule τ_eqT $Γ (der_eqT_trans _ _ _ _ _ $d1 $d2) ↪
     xtransitivity (τ_eqT $Γ $d1)
                   (xtransitivity (τ_eqT_t1_t2_compat $Γ $d1 $d2)
                                  (τ_eqT $Γ $d2));

rule τ_eq_type1 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ_type $Γ $d
with τ_eq_type2 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ_type $Γ $d;
rule τ_eq_type1_compat _ (der_eq_refl _ _ _ _ _) ↪ convrefl
with τ_eq_type2_compat _ (der_eq_refl _ _ _ _ _) ↪ convrefl;
rule τ_eq_t1 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ $Γ $d
with τ_eq_t2 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ $Γ $d;
rule τ_eq_t1_compat _ (der_eq_refl _ _ _ _ _) ↪ heq_refl _
with τ_eq_t2_compat _ (der_eq_refl _ _ _ _ _) ↪ heq_refl _;
rule τ_eq $Γ (der_eq_refl _ _ _ _ $d) ↪ heq_refl (τ $Γ $d);

rule τ_eq_type1 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type2 $Γ $d
with τ_eq_type2 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type1 $Γ $d;
rule τ_eq_type1_compat $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type2_compat $Γ $d
with τ_eq_type2_compat $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type1_compat $Γ $d;
rule τ_eq_t1 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t2 $Γ $d
with τ_eq_t2 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t1 $Γ $d;
rule τ_eq_t1_compat $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t2_compat $Γ $d
with τ_eq_t2_compat $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t1_compat $Γ $d;
rule τ_eq $Γ (der_eq_sym _ _ _ _ _ $d) ↪ heq_sym (τ_eq $Γ $d);

rule τ_eq_type1 $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_type1 $Γ $d
with τ_eq_type2 $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_type2 $Γ $d;
rule τ_eq_type1_compat $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_type1_compat $Γ $d
with τ_eq_type2_compat $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_type2_compat $Γ $d;
rule τ_eq_t1 $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_t1 $Γ $d
with τ_eq_t2 $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_t2 $Γ $d;
rule τ_eq_t1_compat $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_t1_compat $Γ $d
with τ_eq_t2_compat $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_t2_compat $Γ $d;
rule τ_eq $Γ (der_eq_trans _ _ _ _ _ _ $d1 $d2) ↪
     heq_trans (τ_eq $Γ $d1)
               (heq_trans (τ_eq_t1_t2_compat $Γ $d1 $d2)
                             (τ_eq $Γ $d2));

rule τ_type $Γ (der_conv _ $deq) ↪ τ_eqT_t2 $Γ $deq;
rule τ_type_compat $Γ (der_conv _ $deq) ↪ τ_eqT_t2_compat $Γ $deq;
rule τ $Γ (der_conv $d $deq) ↪
     convtransp (xtransitivity (τ_type_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq)) (τ $Γ $d);

rule τ_eq_type1 $Γ (der_eq_conv _ $deq) ↪ τ_eqT_t2 $Γ $deq
with τ_eq_type2 $Γ (der_eq_conv _ $deq) ↪ τ_eqT_t2 $Γ $deq;
rule τ_eq_type1_compat $Γ (der_eq_conv _ $deq) ↪ convrefl
with τ_eq_type2_compat $Γ (der_eq_conv _ $deq) ↪ convrefl;
rule τ_eq_t1 $Γ (der_eq_conv $d $deq) ↪
     convtransp (xtransitivity (τ_eq_type1_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq)) (τ_eq_t1 $Γ $d)
with τ_eq_t2 $Γ (der_eq_conv $d $deq) ↪
     convtransp (xtransitivity (τ_eq_type2_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq)) (τ_eq_t2 $Γ $d);
rule τ_eq_t1_compat $Γ (der_eq_conv $d $deq) ↪
     heq_conj (τ_eq_t1_compat $Γ $d)
              (xtransitivity (τ_eq_type1_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq))
              (xtransitivity (τ_type_t1_compat $Γ (inv_eq_t1 (τ_dΓ $Γ) $d) $deq) (τ_eqT $Γ $deq))
with τ_eq_t2_compat $Γ (der_eq_conv $d $deq) ↪
     heq_conj (τ_eq_t2_compat $Γ $d)
              (xtransitivity (τ_eq_type2_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq))
              (xtransitivity (τ_type_t1_compat $Γ (inv_eq_t2 (τ_dΓ $Γ) $d) $deq) (τ_eqT $Γ $deq));
rule τ_eq $Γ (der_eq_conv $d $deq) ↪
     heq_conj (τ_eq $Γ $d)
              (xtransitivity (τ_eq_type1_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq))
              (xtransitivity (τ_eq_type2_t1_compat $Γ $d $deq) (τ_eqT $Γ $deq));

rule τ_eq_I _ (der_eq_I_refl _ _ _) ↪ xrefl;
rule τ_eq_I $Γ (der_eq_I_sym _ _ _ $d) ↪ xsymmetry (τ_eq_I $Γ $d);
rule τ_eq_I $Γ (der_eq_I_trans _ _ _ _ $d1 $d2) ↪ xtransitivity (τ_eq_I $Γ $d1) (τ_eq_I $Γ $d2);

rule τ_eq_F _ (der_eq_F_refl _ _ _) ↪ xrefl;
rule τ_eq_F $Γ (der_eq_F_sym _ _ _ $d) ↪ xsymmetry (τ_eq_F $Γ $d);
rule τ_eq_F $Γ (der_eq_F_trans _ _ _ _ $d1 $d2) ↪ xtransitivity (τ_eq_F $Γ $d1) (τ_eq_F $Γ $d2);
