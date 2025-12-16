require open ctt.Structural.Syntax;

require open ctt.Lemmas.Inversions;
rule inv_eqT_t1 $dΓ (der_eqT_refl _ _ _ $dA) ↪ $dA
with inv_eqT_t2 $dΓ (der_eqT_refl _ _ _ $dA) ↪ $dA;
rule inv_eqT_t1 $dΓ (der_eqT_sym _ _ _ _ $dAB) ↪ inv_eqT_t2 $dΓ $dAB
with inv_eqT_t2 $dΓ (der_eqT_sym _ _ _ _ $dAB) ↪ inv_eqT_t1 $dΓ $dAB;
rule inv_eqT_t1 $dΓ (der_eqT_trans _ _ _ _ _ $dAB $dBC) ↪ inv_eqT_t1 $dΓ $dAB
with inv_eqT_t2 $dΓ (der_eqT_trans _ _ _ _ _ $dAB $dBC) ↪ inv_eqT_t2 $dΓ $dBC;

rule inv_eq_t1 $dΓ (der_eq_refl _ _ _ _ $dA) ↪ $dA
with inv_eq_t2 $dΓ (der_eq_refl _ _ _ _ $dA) ↪ $dA;
rule inv_eq_t1 $dΓ (der_eq_sym _ _ _ _ _ $dAB) ↪ inv_eq_t2 $dΓ $dAB
with inv_eq_t2 $dΓ (der_eq_sym _ _ _ _ _ $dAB) ↪ inv_eq_t1 $dΓ $dAB;
rule inv_eq_t1 $dΓ (der_eq_trans _ _ _ _ _ _ $dAB $dBC) ↪ inv_eq_t1 $dΓ $dAB
with inv_eq_t2 $dΓ (der_eq_trans _ _ _ _ _ _ $dAB $dBC) ↪ inv_eq_t2 $dΓ $dBC;

rule inv_type $dΓ (der_conv $d $deq) ↪ inv_eqT_t2 $dΓ $deq;
rule inv_eq_type $dΓ (der_eq_conv $d $deq) ↪ inv_eqT_t2 $dΓ $deq
with inv_eq_t1 $dΓ (der_eq_conv $d $deq) ↪ der_conv (inv_eq_t1 $dΓ $d) $deq
with inv_eq_t2 $dΓ (der_eq_conv $d $deq) ↪ der_conv (inv_eq_t2 $dΓ $d) $deq;

rule inv_eq_I_t1 $dΓ (der_eq_I_refl _ _ $dA) ↪ $dA
with inv_eq_I_t2 $dΓ (der_eq_I_refl _ _ $dA) ↪ $dA;
rule inv_eq_I_t1 $dΓ (der_eq_I_sym _ _ _ $dAB) ↪ inv_eq_I_t2 $dΓ $dAB
with inv_eq_I_t2 $dΓ (der_eq_I_sym _ _ _ $dAB) ↪ inv_eq_I_t1 $dΓ $dAB;
rule inv_eq_I_t1 $dΓ (der_eq_I_trans _ _ _ _ $dAB $dBC) ↪ inv_eq_I_t1 $dΓ $dAB
with inv_eq_I_t2 $dΓ (der_eq_I_trans _ _ _ _ $dAB $dBC) ↪ inv_eq_I_t2 $dΓ $dBC;

rule inv_eq_F_t1 $dΓ (der_eq_F_refl _ _ $dA) ↪ $dA
with inv_eq_F_t2 $dΓ (der_eq_F_refl _ _ $dA) ↪ $dA;
rule inv_eq_F_t1 $dΓ (der_eq_F_sym _ _ _ $dAB) ↪ inv_eq_F_t2 $dΓ $dAB
with inv_eq_F_t2 $dΓ (der_eq_F_sym _ _ _ $dAB) ↪ inv_eq_F_t1 $dΓ $dAB;
rule inv_eq_F_t1 $dΓ (der_eq_F_trans _ _ _ _ $dAB $dBC) ↪ inv_eq_F_t1 $dΓ $dAB
with inv_eq_F_t2 $dΓ (der_eq_F_trans _ _ _ _ $dAB $dBC) ↪ inv_eq_F_t2 $dΓ $dBC;
