require open ctt.Structural.Syntax;

require open ctt.Translation;

rule τ_eqT_t1 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d
with τ_eqT_t2 $Γ (der_eqT_refl _ _ _ $d) ↪ τ_T $Γ $d;
rule τ_eqT _ (der_eqT_refl _ _ _ _) ↪ convrefl;

rule τ_eqT_t1 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_sym _ _ _ _ $d) ↪ τ_eqT_t1 $Γ $d;
rule τ_eqT $Γ (der_eqT_sym _ _ _ _ $d) ↪ xsymmetry (τ_eqT $Γ $d);

rule τ_eqT_t1 $Γ (der_eqT_trans _ _ _ _ _ $d _) ↪ τ_eqT_t1 $Γ $d
with τ_eqT_t2 $Γ (der_eqT_trans _ _ _ _ _ _ $d) ↪ τ_eqT_t2 $Γ $d;
rule τ_eqT $Γ (der_eqT_trans _ _ _ _ _ $d1 $d2) ↪ xtransitivity (τ_eqT $Γ $d1) (τ_eqT $Γ $d2);
