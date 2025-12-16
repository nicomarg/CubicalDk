require open ctt.Structural.Syntax;

require open ctt.Translation;
require open ctt.Lemmas.Irrel;

rule τ_eqT_t1 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d
with τ_eqT_t2 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d;
rule τ_eqT _ (der_eqT_refl _ _ _ _) ↪ convrefl;

rule τ_eqT_t1 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t1 $Γ $d;
rule τ_eqT $Γ (der_eqT_sym _ _ _ _ $d) ↪ xsymmetry (τ_eqT $Γ $d);

rule τ_eqT_t1 $Γ (der_eqT_trans _ _ _ _ _ $d _) ↪ τ_eqT_t1 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_trans _ _ _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d;
rule τ_eqT $Γ (der_eqT_trans _ _ _ _ _ $d1 $d2) ↪
     xtransitivity (xtransitivity (τ_eqT $Γ $d1) (τ_eqT_t2_compat $Γ $d1))
                   (xtransitivity (τ_T_irrel $Γ (inv_eqT_t2 (τ_dΓ $Γ) $d1) (inv_eqT_t1 (τ_dΓ $Γ) $d2))
                                  (xtransitivity (xsymmetry (τ_eqT_t1_compat $Γ $d2)) (τ_eqT $Γ $d2)));

rule τ_eq_type1 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ_type $Γ $d
with τ_eq_type2 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ_type $Γ $d;
rule τ_eq_t1 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ $Γ $d
with τ_eq_t2 $Γ (der_eq_refl _ _ _ _ $d) ↪ τ $Γ $d;
rule τ_eq $Γ (der_eq_refl _ _ _ _ $d) ↪ heq_refl (τ $Γ $d);

rule τ_eq_type1 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type2 $Γ $d
with τ_eq_type2 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_type1 $Γ $d;
rule τ_eq_t1 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t2 $Γ $d
with τ_eq_t2 $Γ (der_eq_sym _ _ _ _ _ $d) ↪ τ_eq_t1 $Γ $d;
rule τ_eq $Γ (der_eq_sym _ _ _ _ _ $d) ↪ heq_sym (τ_eq $Γ $d);

rule τ_eq_type1 $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_type1 $Γ $d;
rule τ_eq_type2 $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_type2 $Γ $d;
rule τ_eq_t1 $Γ (der_eq_trans _ _ _ _ _ _ $d _) ↪ τ_eq_t1 $Γ $d
with τ_eq_t2 $Γ (der_eq_trans _ _ _ _ _ _ _ $d) ↪ τ_eq_t2 $Γ $d;
rule τ_eq $Γ (der_eq_trans _ _ _ _ _ _ $d1 $d2) ↪
     heq_trans (heq_trans (τ_eq $Γ $d1) (τ_eq_t2_compat $Γ $d1))
                  (heq_trans (τ_irrel $Γ (inv_eq_t2 (τ_dΓ $Γ) $d1) (inv_eq_t1 (τ_dΓ $Γ) $d2))
                             (heq_trans (heq_sym (τ_eq_t1_compat $Γ $d2)) (τ_eq $Γ $d2)));
