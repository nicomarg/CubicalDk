require open ctt.Symbols;

constant symbol tuniv : Sort → Typ;

constant symbol der_univ : Π [Γ : Context] [l : Sort], der_type Γ (tuniv l) (tlsuc l);

constant symbol tel : Term → Typ;

constant symbol der_el : Π [Γ : Context] [l : Sort] [t : Term], der Γ t (tuniv l) (tlsuc l) → der_type Γ (tel t) l;

constant symbol as_term : Typ → Term;

constant symbol der_as_term : Π [Γ : Context] [l : Sort] [T : Typ], der_type Γ T l → der Γ (as_term T) (tuniv l) (tlsuc l);

constant symbol der_eq_el_as_term [Γ : Context] [l : Sort] [t : Typ] : der_type Γ t l → der_eqT Γ t (tel (as_term t)) l;
constant symbol der_eq_as_term_el [Γ : Context] [l : Sort] [t : Term] : der Γ t (tuniv l) (tlsuc l) → der_eq Γ t (as_term (tel t)) (tuniv l) (tlsuc l);

constant symbol der_eq_cong_el [Γ : Context] [l : Sort] [t u : Term] : der_eq Γ t u (tuniv l) (tlsuc l) → der_eqT Γ (tel t) (tel u) l;
constant symbol der_eq_cong_as_term [Γ : Context] [l : Sort] [t u : Typ] : der_eqT Γ t u l → der_eq Γ (as_term t) (as_term u) (tuniv l) (tlsuc l);
