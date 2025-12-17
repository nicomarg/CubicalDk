require open ctt.Translation;
require open ctt.Lemmas.Inversions;

symbol PContext : TYPE;
symbol PBase : TContext → PContext;

symbol projΓ1 : PContext → TContext;
symbol projΓ2 : PContext → TContext;
rule projΓ1 (PBase $Γ) ↪ $Γ
with projΓ2 (PBase $Γ) ↪ $Γ;

symbol τ_T_irrel_rec (Γ : PContext) [l : Sort] [t : Typ]
                (d1 : der_type (τ_Γ (projΓ1 Γ)) t l)
                (d2 : der_type (τ_Γ (projΓ2 Γ)) t l) :
  tconvtype (τ_T (projΓ1 Γ) d1) (τ_T (projΓ2 Γ) d2);
symbol τ_irrel_rec (Γ : PContext) [l : Sort] [t : Term] [T1 T2 : Typ]
                (d1 : der (τ_Γ (projΓ1 Γ)) t T1 l)
                (d2 : der (τ_Γ (projΓ2 Γ)) t T2 l) :
  tH (τ (projΓ1 Γ) d1) (τ (projΓ2 Γ) d2);

symbol τ_T_irrel (Γ : TContext) [A : Typ] [l : Sort] (d1 d2 : der_type (τ_Γ Γ) A l) :
  tconvtype (τ_T Γ d1) (τ_T Γ d2) ≔ τ_T_irrel_rec (PBase Γ) d1 d2;

symbol τ_irrel (Γ : TContext) [t : Term] [A : Typ] [l : Sort] (d1 d2 : der (τ_Γ Γ) t A l) :
  tH (τ Γ d1) (τ Γ d2) ≔ τ_irrel_rec (PBase Γ) d1 d2;

symbol τ_eqT_t1_compat (Γ : TContext) [t u : Typ] [l : Sort] (d : der_eqT (τ_Γ Γ) t u l) :
  tconvtype (τ_eqT_t1 Γ d) (τ_T Γ (inv_eqT_t1 (τ_dΓ Γ) d));
symbol τ_eqT_t2_compat (Γ : TContext) [t u : Typ] [l : Sort] (d : der_eqT (τ_Γ Γ) t u l) :
  tconvtype (τ_eqT_t2 Γ d) (τ_T Γ (inv_eqT_t2 (τ_dΓ Γ) d));

symbol τ_type_compat (Γ : TContext) [t : Term] [A : Typ] [l : Sort] (d : der (τ_Γ Γ) t A l) :
  tconvtype (τ_type Γ d) (τ_T Γ (inv_type (τ_dΓ Γ) d));

symbol τ_eq_type1_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tconvtype (τ_eq_type1 Γ d) (τ_type Γ (inv_eq_t1 (τ_dΓ Γ) d));
symbol τ_eq_type2_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tconvtype (τ_eq_type2 Γ d) (τ_type Γ (inv_eq_t2 (τ_dΓ Γ) d));
symbol τ_eq_t1_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tH (τ_eq_t1 Γ d) (τ Γ (inv_eq_t1 (τ_dΓ Γ) d));
symbol τ_eq_t2_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tH (τ_eq_t2 Γ d) (τ Γ (inv_eq_t2 (τ_dΓ Γ) d));

// Compositions of compatibility and irrelevance
symbol τ_type_t1_compat (Γ : TContext) [t : Term] [A B : Typ] [l : Sort] (d : der (τ_Γ Γ) t A l) (deq : der_eqT (τ_Γ Γ) A B l) :
  tconvtype (τ_type Γ d) (τ_eqT_t1 Γ deq) ≔
  xtransitivity (xtransitivity (τ_type_compat Γ d) (τ_T_irrel Γ (inv_type (τ_dΓ Γ) d) (inv_eqT_t1 (τ_dΓ Γ) deq)))
                (xsymmetry (τ_eqT_t1_compat Γ deq));

symbol τ_type_t2_compat (Γ : TContext) [t : Term] [A B : Typ] [l : Sort] (d : der (τ_Γ Γ) t B l) (deq : der_eqT (τ_Γ Γ) A B l) :
  tconvtype (τ_type Γ d) (τ_eqT_t2 Γ deq) ≔
  xtransitivity (xtransitivity (τ_type_compat Γ d) (τ_T_irrel Γ (inv_type (τ_dΓ Γ) d) (inv_eqT_t2 (τ_dΓ Γ) deq)))
                (xsymmetry (τ_eqT_t2_compat Γ deq));

symbol τ_eqT_t1_t2_compat (Γ : TContext) [A B C : Typ] [l : Sort] (d1 : der_eqT (τ_Γ Γ) A B l) (d2 : der_eqT (τ_Γ Γ) B C l) :
  tconvtype (τ_eqT_t2 Γ d1) (τ_eqT_t1 Γ d2) ≔
     xtransitivity (τ_eqT_t2_compat Γ d1)
                   (xtransitivity (τ_T_irrel Γ (inv_eqT_t2 (τ_dΓ Γ) d1) (inv_eqT_t1 (τ_dΓ Γ) d2))
                                  (xsymmetry (τ_eqT_t1_compat Γ d2)));

symbol τ_eq_t1_t2_compat (Γ : TContext) [t u v : Term] [A : Typ] [l : Sort] (d1 : der_eq (τ_Γ Γ) t u A l) (d2 : der_eq (τ_Γ Γ) u v A l) :
  tH (τ_eq_t2 Γ d1) (τ_eq_t1 Γ d2) ≔
     heq_trans (τ_eq_t2_compat Γ d1)
               (heq_trans (τ_irrel Γ (inv_eq_t2 (τ_dΓ Γ) d1) (inv_eq_t1 (τ_dΓ Γ) d2))
                          (heq_sym (τ_eq_t1_compat Γ d2)));

symbol τ_eq_type1_t1_compat (Γ : TContext) [t u : Term] [A B : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) (deq : der_eqT (τ_Γ Γ) A B l) :
  tconvtype (τ_eq_type1 Γ d) (τ_eqT_t1 Γ deq) ≔
     xtransitivity (xtransitivity (τ_eq_type1_compat Γ d) (τ_type_compat Γ (inv_eq_t1 (τ_dΓ Γ) d)))
                   (xtransitivity (τ_T_irrel Γ (inv_type (τ_dΓ Γ) (inv_eq_t1 (τ_dΓ Γ) d)) (inv_eqT_t1 (τ_dΓ Γ) deq))
                                  (xsymmetry (τ_eqT_t1_compat Γ deq)));

symbol τ_eq_type2_t1_compat (Γ : TContext) [t u : Term] [A B : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) (deq : der_eqT (τ_Γ Γ) A B l) :
  tconvtype (τ_eq_type2 Γ d) (τ_eqT_t1 Γ deq) ≔
     xtransitivity (xtransitivity (τ_eq_type2_compat Γ d) (τ_type_compat Γ (inv_eq_t2 (τ_dΓ Γ) d)))
                   (xtransitivity (τ_T_irrel Γ (inv_type (τ_dΓ Γ) (inv_eq_t2 (τ_dΓ Γ) d)) (inv_eqT_t1 (τ_dΓ Γ) deq))
                                  (xsymmetry (τ_eqT_t1_compat Γ deq)));
