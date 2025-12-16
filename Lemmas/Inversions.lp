require open ctt.Symbols;

// Lemmas

symbol inv_eqT_t1 [Γ : Context] [l : Sort] [A B : Typ] : der_context Γ → der_eqT Γ A B l → der_type Γ A l;
symbol inv_eqT_t2 [Γ : Context] [l : Sort] [A B : Typ] : der_context Γ → der_eqT Γ A B l → der_type Γ B l;

symbol inv_type [Γ : Context] [l : Sort] [t : Term] [T : Typ] : der_context Γ → der Γ t T l → der_type Γ T l;
symbol inv_eq_type [Γ : Context] [l : Sort] [t1 t2 : Term] [T : Typ] : der_context Γ → der_eq Γ t1 t2 T l →
                                                               der_type Γ T l;
symbol inv_eq_t1   [Γ : Context] [l : Sort] [t1 t2 : Term] [T : Typ] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t1 T l;
symbol inv_eq_t2   [Γ : Context] [l : Sort] [t1 t2 : Term] [T : Typ] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t2 T l;

symbol inv_eq_I_t1 [Γ : Context] [t1 t2 : ITerm] : der_context Γ → der_eq_I Γ t1 t2 → der_I Γ t1;
symbol inv_eq_I_t2 [Γ : Context] [t1 t2 : ITerm] : der_context Γ → der_eq_I Γ t1 t2 → der_I Γ t2;

symbol inv_eq_F_t1 [Γ : Context] [t1 t2 : FTerm] : der_context Γ → der_eq_F Γ t1 t2 → der_F Γ t1;
symbol inv_eq_F_t2 [Γ : Context] [t1 t2 : FTerm] : der_context Γ → der_eq_F Γ t1 t2 → der_F Γ t2;

symbol inv_isOne [Γ : Context] [t1 : FTerm] : der_context Γ → der_isOne Γ t1 → der_F Γ t1;
