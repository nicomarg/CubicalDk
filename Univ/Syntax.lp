require open ctt.Symbols;

// universes need to be defined very early
constant symbol tuniv : tLev → Term;

constant symbol der_univ : Π [Γ : Context] [l : tLev], der Γ (tuniv l) (tuniv (tlsuc l)) (tlsuc (tlsuc l));
