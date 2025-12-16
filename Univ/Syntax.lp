require open ctt.Symbols;

// universes need to be defined very early
constant symbol tuniv : Sort → Term;

constant symbol der_univ : Π [Γ : Context] [l : Sort], der Γ (tuniv l) (tuniv (tlsuc l)) (tlsuc (tlsuc l));
