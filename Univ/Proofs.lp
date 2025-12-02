require open ctt.Lemmas.Commutations;
require open ctt.Univ.Subst;
rule swap_shift_shift _ _ (tuniv _) _ ↪ TRefl _
with swap_shift_Ishift _ _ (tuniv _) ↪ TRefl _;

require open ctt.Lemmas.Derivations.Shifting;
rule der_shift_n _   _   _  der_univ ↪ der_univ;

// inversion lemmas
require open ctt.Lemmas.Inversions;
rule inv_type $dΓ der_univ ↪ der_univ;

// translation
require open ctt.Translation;
rule τ _ (@der_univ _ $l)  ↪ t (τ_lev $l);
