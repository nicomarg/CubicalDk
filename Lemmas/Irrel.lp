require open ctt.Translation;

symbol τ_T_irrel (Γ : TContext) [A : Typ] [l : Sort] (d1 d2 : der_type (τ_Γ Γ) A l) :
  tconvtype (τ_T Γ d1) (τ_T Γ d2);

symbol τ_eqT_t1_compat (Γ : TContext) [t u : Typ] [l : Sort] (d : der_eqT (τ_Γ Γ) t u l) :
  tconvtype (τ_eqT_t1 Γ d) (τ_T Γ (inv_eqT_t1 (τ_dΓ Γ) d));
symbol τ_eqT_t2_compat (Γ : TContext) [t u : Typ] [l : Sort] (d : der_eqT (τ_Γ Γ) t u l) :
  tconvtype (τ_eqT_t2 Γ d) (τ_T Γ (inv_eqT_t2 (τ_dΓ Γ) d));

symbol τ_type_compat (Γ : TContext) [t : Term] [A : Typ] [l : Sort] (d : der (τ_Γ Γ) t A l) :
  tconvtype (τ_type Γ d) (τ_T Γ (inv_type (τ_dΓ Γ) d));

symbol τ_irrel (Γ : TContext) [t : Term] [A : Typ] [l : Sort] (d1 d2 : der (τ_Γ Γ) t A l) :
  tH (τ Γ d1) (τ Γ d2);

symbol τ_eq_type_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tconvtype (τ_eq_type Γ d) (τ_T Γ (inv_eq_type (τ_dΓ Γ) d));
symbol τ_eq_t1_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tH (τ_eq_t1 Γ d) (τ Γ (inv_eq_t1 (τ_dΓ Γ) d));
symbol τ_eq_t2_compat (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tH (τ_eq_t2 Γ d) (τ Γ (inv_eq_t2 (τ_dΓ Γ) d));

symbol τ_I_irrel (Γ : TContext) [t : ITerm] (d1 d2 : der_I (τ_Γ Γ) t) :
  xtEq (τ_I Γ d1) (τ_I Γ d2);

symbol τ_eq_I_t1_compat (Γ : TContext) [t u : ITerm] (d : der_eq_I (τ_Γ Γ) t u) :
  xtEq (τ_eq_I_t1 Γ d) (τ_I Γ (inv_eq_I_t1 (τ_dΓ Γ) d));
symbol τ_eq_I_t2_compat (Γ : TContext) [t u : ITerm] (d : der_eq_I (τ_Γ Γ) t u) :
  xtEq (τ_eq_I_t2 Γ d) (τ_I Γ (inv_eq_I_t2 (τ_dΓ Γ) d));

symbol τ_F_irrel (Γ : TContext) [t : FTerm] (d1 d2 : der_F (τ_Γ Γ) t) :
  xtEq (τ_F Γ d1) (τ_F Γ d2);

symbol τ_eq_F_t1_compat (Γ : TContext) [t u : FTerm] (d : der_eq_F (τ_Γ Γ) t u) :
  xtEq (τ_eq_F_t1 Γ d) (τ_F Γ (inv_eq_F_t1 (τ_dΓ Γ) d));
symbol τ_eq_F_t2_compat (Γ : TContext) [t u : FTerm] (d : der_eq_F (τ_Γ Γ) t u) :
  xtEq (τ_eq_F_t2 Γ d) (τ_F Γ (inv_eq_F_t2 (τ_dΓ Γ) d));

symbol τ_isOne_t_compat (Γ : TContext) [t : FTerm] (d : der_isOne (τ_Γ Γ) t) :
  xtEq (τ_isOne_t Γ d) (τ_F Γ (inv_isOne (τ_dΓ Γ) d));
