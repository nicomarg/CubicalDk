require open ctt.Symbols;

constant symbol der_eqT_refl : Π(Γ : Context) (l : Sort) (A : Typ), der_type Γ A l → der_eqT Γ A A l;
constant symbol der_eqT_sym : Π (Γ : Context) (l : Sort) (A B : Typ),
  der_eqT Γ A B l → der_eqT Γ B A l;
constant symbol der_eqT_trans : Π (Γ : Context) (l : Sort) (A B C : Typ),
  der_eqT Γ A B l → der_eqT Γ B C l → der_eqT Γ A C l;

constant symbol der_eq_refl : Π(Γ : Context) (l : Sort) (u : Term) (A : Typ), der Γ u A l → der_eq Γ u u A l;
constant symbol der_eq_sym : Π (Γ : Context) (l : Sort) (u v : Term) (A : Typ),
  der_eq Γ u v A l → der_eq Γ v u A l;
constant symbol der_eq_trans : Π (Γ : Context) (l : Sort) (u v w : Term) (A : Typ),
  der_eq Γ u v A l → der_eq Γ v w A l → der_eq Γ u w A l;

constant symbol der_conv [Γ : Context] [l : Sort] [u : Term] [A B : Typ] :
  der Γ u A l → der_eqT Γ A B l → der Γ u B l;

constant symbol der_eq_conv [Γ : Context] [l : Sort] [u v : Term] [A B : Typ] :
  der_eq Γ u v A l → der_eqT Γ A B l → der_eq Γ u v B l;

constant symbol der_eq_I_refl : Π (Γ : Context) (i : ITerm), der_I Γ i → der_eq_I Γ i i;
constant symbol der_eq_I_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ i j → der_eq_I Γ j i;
constant symbol der_eq_I_trans : Π (Γ : Context) (i j k : ITerm), der_eq_I Γ i j → der_eq_I Γ j k → der_eq_I Γ i k;

constant symbol der_eq_F_refl : Π (Γ : Context) (f : FTerm), der_F Γ f → der_eq_F Γ f f;
constant symbol der_eq_F_sym : Π (Γ : Context) (f g : FTerm), der_eq_F Γ f g → der_eq_F Γ g f;
constant symbol der_eq_F_trans : Π (Γ : Context) (f g h : FTerm), der_eq_F Γ f g → der_eq_F Γ g h → der_eq_F Γ f h;
