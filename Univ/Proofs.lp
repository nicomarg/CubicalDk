require open ctt.Lemmas.Commutations;
require open ctt.Univ.Subst;
rule swap_tshift_tshift _ _ (tuniv _) _ ↪ TyRefl _;
rule swap_tshift_tshift $i $j (tel $t) $h ↪ JtTcong tel (swap_shift_shift $i $j $t $h);
rule swap_shift_shift $i $j (as_term $t) $h ↪ JTtcong as_term (swap_tshift_tshift $i $j $t $h);
// with swap_shift_Ishift _ _ (tuniv _) ↪ TRefl _;

require open ctt.Lemmas.Derivations.Shifting;
rule der_type_shift_n _   _   _  der_univ ↪ der_univ;
rule der_type_shift_n $id $sc $da (der_el $d) ↪ der_el (der_shift_n $id $sc $da $d);
rule der_shift_n $id $sc $da (der_as_term $d) ↪ der_as_term (der_type_shift_n $id $sc $da $d);
rule der_eqT_shift_n $id $sc $da (der_eq_el_as_term $d) ↪ der_eq_el_as_term (der_type_shift_n $id $sc $da $d);
rule der_eq_shift_n $id $sc $da (der_eq_as_term_el $d) ↪ der_eq_as_term_el (der_shift_n $id $sc $da $d);
rule der_eqT_shift_n $id $sc $da (der_eq_cong_el $d) ↪ der_eq_cong_el (der_eq_shift_n $id $sc $da $d);
rule der_eq_shift_n $id $sc $da (der_eq_cong_as_term $d) ↪ der_eq_cong_as_term (der_eqT_shift_n $id $sc $da $d);

// inversion lemmas
require open ctt.Lemmas.Inversions;
rule inv_type _ (der_as_term _) ↪ der_univ;
rule inv_eqT_t1 _ (der_eq_el_as_term $d) ↪ $d;
rule inv_eqT_t2 _ (der_eq_el_as_term $d) ↪ der_el (der_as_term $d);
rule inv_eq_type _ (der_eq_as_term_el _) ↪ der_univ;
rule inv_eq_t1 _ (der_eq_as_term_el $d) ↪ $d;
rule inv_eq_t2 _ (der_eq_as_term_el $d) ↪ der_as_term (der_el $d);
rule inv_eqT_t1 $dΓ (der_eq_cong_el $d) ↪ der_el (inv_eq_t1 $dΓ $d);
rule inv_eqT_t2 $dΓ (der_eq_cong_el $d) ↪ der_el (inv_eq_t2 $dΓ $d);
rule inv_eq_type _ (der_eq_cong_as_term _) ↪ der_univ;
rule inv_eq_t1 $dΓ (der_eq_cong_as_term $d) ↪ der_as_term (inv_eqT_t1 $dΓ $d);
rule inv_eq_t2 $dΓ (der_eq_cong_as_term $d) ↪ der_as_term (inv_eqT_t2 $dΓ $d);

// translation
require open ctt.Lemmas.Irrel;
require open ctt.Translation;
rule τ_T _ (@der_univ _ $l)  ↪ t (τ_lev $l);
rule τ_T $Γ (der_el $d) ↪ convtransp (xtransitivity (τ_type_compat $Γ $d) (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) $d) der_univ)) (τ $Γ $d);
rule τ_type _ (@der_as_term _ $l _ _) ↪ t (τ_lev $l);
rule τ $Γ (der_as_term $d) ↪ (τ_T $Γ $d);
rule τ_eqT_t1 $Γ (der_eq_el_as_term $d) ↪ τ_T $Γ $d;
rule τ_eqT_t2 $Γ (der_eq_el_as_term $d) ↪ τ_T $Γ $d;
rule τ_eqT _ (der_eq_el_as_term _) ↪ xrefl;
rule τ_eq_type1 $Γ (der_eq_as_term_el $d) ↪ τ_type $Γ $d;
rule τ_eq_type2 $Γ (der_eq_as_term_el $d) ↪ τ_type $Γ $d;
rule τ_eq_t1 $Γ (der_eq_as_term_el $d) ↪ τ $Γ $d;
rule τ_eq_t2 $Γ (der_eq_as_term_el $d) ↪ τ $Γ $d;
rule τ_eq _ (der_eq_as_term_el _) ↪ heq_refl _;
rule τ_eqT_t1 $Γ (der_eq_cong_el $d) ↪ convtransp (xtransitivity (τ_eq_type1_compat $Γ $d)
                                                                 (xtransitivity (τ_type_compat $Γ (inv_eq_t1 (τ_dΓ $Γ) $d))
                                                                                (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t1 (τ_dΓ $Γ) $d)) der_univ)))
                                                  (τ_eq_t1 $Γ $d);
rule τ_eqT_t2 $Γ (der_eq_cong_el $d) ↪ convtransp (xtransitivity (τ_eq_type2_compat $Γ $d)
                                                                 (xtransitivity (τ_type_compat $Γ (inv_eq_t2 (τ_dΓ $Γ) $d))
                                                                                (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t2 (τ_dΓ $Γ) $d)) der_univ)))
                                                  (τ_eq_t2 $Γ $d);
rule τ_eqT $Γ (der_eq_cong_el $d) ↪
     heq_to_eq (heq_conj (τ_eq $Γ $d)
                         (xtransitivity (τ_eq_type1_compat $Γ $d)
                                        (xtransitivity (τ_type_compat $Γ (inv_eq_t1 (τ_dΓ $Γ) $d))
                                                       (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t1 (τ_dΓ $Γ) $d)) der_univ)))
                         (xtransitivity (τ_eq_type2_compat $Γ $d)
                                        (xtransitivity (τ_type_compat $Γ (inv_eq_t2 (τ_dΓ $Γ) $d))
                                                       (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t2 (τ_dΓ $Γ) $d)) der_univ))));
rule τ_eq_type1 _ (@der_eq_cong_as_term _ $l _ _ _) ↪ t (τ_lev $l); 
rule τ_eq_type2 _ (@der_eq_cong_as_term _ $l _ _ _) ↪ t (τ_lev $l); 
rule τ_eq_t1 $Γ (der_eq_cong_as_term $d) ↪ τ_eqT_t1 $Γ $d;
rule τ_eq_t2 $Γ (der_eq_cong_as_term $d) ↪ τ_eqT_t2 $Γ $d;
rule τ_eq $Γ (der_eq_cong_as_term $d) ↪ eq_to_heq (τ_eqT $Γ $d);

rule τ_T_irrel_rec _ der_univ der_univ ↪ convrefl;
rule τ_T_irrel_rec $Γ (der_el $d1) (der_el $d2) ↪
     heq_to_eq (heq_conj (τ_irrel_rec $Γ $d1 $d2)
                         (xtransitivity (τ_type_compat (projΓ1 $Γ) $d1) (τ_T_irrel (projΓ1 $Γ) (inv_type (τ_dΓ (projΓ1 $Γ)) $d1) der_univ))
                         (xtransitivity (τ_type_compat (projΓ2 $Γ) $d2)  (τ_T_irrel (projΓ2 $Γ) (inv_type (τ_dΓ (projΓ2 $Γ)) $d2) der_univ)));
rule τ_irrel_rec $Γ (der_as_term $d1) (der_as_term $d2) ↪ eq_to_heq (τ_T_irrel_rec $Γ $d1 $d2);
rule τ_type_compat _ (der_as_term _) ↪ convrefl;
rule τ_eqT_t1_compat $Γ (der_eq_el_as_term $d) ↪ convrefl;
rule τ_eqT_t2_compat $Γ (der_eq_el_as_term $d) ↪ convrefl;
rule τ_eq_type1_compat $Γ (der_eq_as_term_el $d) ↪ convrefl;
rule τ_eq_type2_compat $Γ (der_eq_as_term_el $d) ↪ (xtransitivity (τ_type_compat $Γ $d) (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) $d) der_univ));
rule τ_eq_t1_compat $Γ (der_eq_as_term_el $d) ↪ heq_refl _;
rule τ_eq_t2_compat $Γ (der_eq_as_term_el $d) ↪ heq_of_transport _ (xtransitivity (τ_type_compat $Γ $d) (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) $d) der_univ));
rule τ_eqT_t1_compat $Γ (der_eq_cong_el $d) ↪
     heq_to_eq (heq_conj (τ_eq_t1_compat $Γ $d) 
                         (xtransitivity (τ_eq_type1_compat $Γ $d)
                                        (xtransitivity (τ_type_compat $Γ (inv_eq_t1 (τ_dΓ $Γ) $d))
                                                       (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t1 (τ_dΓ $Γ) $d)) der_univ)))
                         (xtransitivity (τ_type_compat $Γ (inv_eq_t1 (τ_dΓ $Γ) $d)) (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t1 (τ_dΓ $Γ) $d)) der_univ)));
rule τ_eqT_t2_compat $Γ (der_eq_cong_el $d) ↪
     heq_to_eq (heq_conj (τ_eq_t2_compat $Γ $d) 
                         (xtransitivity (τ_eq_type2_compat $Γ $d)
                                        (xtransitivity (τ_type_compat $Γ (inv_eq_t2 (τ_dΓ $Γ) $d))
                                                       (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t2 (τ_dΓ $Γ) $d)) der_univ)))
                         (xtransitivity (τ_type_compat $Γ (inv_eq_t2 (τ_dΓ $Γ) $d)) (τ_T_irrel $Γ (inv_type (τ_dΓ $Γ) (inv_eq_t2 (τ_dΓ $Γ) $d)) der_univ)));
rule τ_eq_type1_compat $Γ (der_eq_cong_as_term $d) ↪ convrefl;
rule τ_eq_type2_compat $Γ (der_eq_cong_as_term $d) ↪ convrefl;
rule τ_eq_t1_compat $Γ (der_eq_cong_as_term $d) ↪ eq_to_heq (τ_eqT_t1_compat $Γ $d);
rule τ_eq_t2_compat $Γ (der_eq_cong_as_term $d) ↪ eq_to_heq (τ_eqT_t2_compat $Γ $d);

require open ctt.Lemmas.Translation;
rule τ_shiftT_n _ _ der_univ _ _ ↪ convrefl;
rule τ_shiftT_n $id $sc (der_el $d) $dA $a ↪
    heq_to_eq (heq_conj (τ_shift_n $id $sc $d $dA $a)
                        (xtransitivity (τ_type_compat (tsc_to_tc $sc) $d) (τ_T_irrel (tsc_to_tc $sc) (inv_type (τ_dΓ (tsc_to_tc $sc)) $d) der_univ))
                        (xtransitivity (τ_type_compat (tsc_to_stc $dA $a $sc) (der_shift_n $id (tsc_to_sc $sc) $dA $d))
                                       (τ_T_irrel (tsc_to_stc $dA $a $sc) (inv_type (τ_dΓ (tsc_to_stc $dA $a $sc)) (der_shift_n $id (tsc_to_sc $sc) $dA $d))
                                                  der_univ)));
rule τ_shift_n $id $sc (der_as_term $d) $dA $a ↪ eq_to_heq (τ_shiftT_n $id $sc $d $dA $a);
