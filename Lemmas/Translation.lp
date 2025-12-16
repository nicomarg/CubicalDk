require open ctt.Contexts.Shift;
require open ctt.Translation;
require open ctt.Lemmas.Derivations;
require open ctt.Univ.Subst;

symbol τ_shift0T_eq (Γ : TContext) [s s' : Sort] [T A : Term]
                    (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                    (dA : der (τ_Γ Γ) A (tuniv s') (tlsuc s'))
                    (a : eps (τ_T Γ dA)) :
  tconvtype
      (τ_T Γ dT)
      (τ_T (TPush Γ s' A dA a) (der_shift0 dA (τ_dΓ Γ) dT));
symbol τ_shift0T (Γ : TContext) [s s' : Sort] [T A : Term]
                 (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                 (dA : der (τ_Γ Γ) A (tuniv s') (tlsuc s'))
                 (a : eps (τ_T Γ dA)) ≔
  convtransp (τ_shift0T_eq Γ dT dA a);
symbol τ_shift0T' (Γ : TContext) [s s' : Sort] [T A : Term]
                  (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                  (dA : der (τ_Γ Γ) A (tuniv s') (tlsuc s'))
                  (a : eps (τ_T Γ dA)) ≔
  convtransp (xsymmetry (τ_shift0T_eq Γ dT dA a));

symbol τ_Ishift0T_eq (Γ : TContext) [s : Sort] [T : Term]
                     (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                     (i : tI):
  tconvtype
      (τ_T Γ dT)
      (τ_T (TPushI Γ i) (der_Ishift0 (τ_dΓ Γ) dT));
symbol τ_Ishift0T (Γ : TContext) [s : Sort] [T : Term]
                  (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                  (i : tI) ≔
  convtransp (τ_Ishift0T_eq Γ dT i);
symbol τ_Ishift0T' (Γ : TContext) [s : Sort] [T : Term]
                   (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                   (i : tI) ≔
  convtransp (xsymmetry (τ_Ishift0T_eq Γ dT i));

symbol τ_Fshift0T_eq (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
                     (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                     (df : der_F (τ_Γ Γ) f)
                     (fone : tisOne (τ_F Γ df)):
  tconvtype
      (τ_T Γ dT)
      (τ_T (TPushF Γ f df fone) (der_weakF (τ_dΓ Γ) dT df));
symbol τ_Fshift0T (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
                  (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                  (df : der_F (τ_Γ Γ) f)
                  (fone : tisOne (τ_F Γ df)) ≔
  convtransp (τ_Fshift0T_eq Γ dT df fone);
symbol τ_Fshift0T' (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
                   (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
                   (df : der_F (τ_Γ Γ) f)
                   (fone : tisOne (τ_F Γ df)) ≔
  convtransp (xsymmetry (τ_Fshift0T_eq Γ dT df fone));
