require open ctt.Translation.Context;

symbol convert_T (Γ : TContext) [A : Term] [l : Sort] (d1 d2 : der (τ_Γ Γ) A (tuniv l) (tlsuc l)) :
  tconvtype (τ_T Γ d1) (τ_T Γ d2);
symbol convertR (Γ : TContext) (h : PContext Γ) [l : Sort] [t T1 T2 : Term]
                (d1 : der (τ_Γ (projΓ1 h)) t T1 l)
                (d2 : der (τ_Γ (projΓ2 h)) t T2 l) :
  let ds1 ≔ inv_type (τ_dΓ (projΓ1 h)) d1 in
  let ds2 ≔ inv_type (τ_dΓ (projΓ2 h)) d2 in
  tHconv (τ_lev l) (τ_T (projΓ1 h) ds1) (τ_T (projΓ2 h) ds2) (τ (projΓ1 h) d1) (τ (projΓ2 h) d2);
symbol convert (Γ : TContext) [l : Sort] [t T : Term] (d1 d2 : der (τ_Γ Γ) t T l) :
  let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
  let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
  tHconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);

// convert wrapper for types
rule convert_T $Γ $d1 $d2
  ↪ heq_to_eq (convert $Γ $d1 $d2);

// convert wrapper
rule convert $Γ $d1 $d2
  ↪ convertR $Γ (PCEmpty $Γ) $d1 $d2;
