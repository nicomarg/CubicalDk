
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;
require open ctt.Lemmas;
// require ETT.ITT as ITT;

// Lemmas
symbol inv_type [Γ : Context] [l : Lev] [t T : Term] : der_context Γ → der Γ t T l → der Γ T (tuniv l) (lsuc l);
symbol inv_eq_type [Γ : Context] [l : Lev] [T t1 t2 : Term] : der_context Γ → der_eq Γ t1 t2 T l →
                                                              der Γ T (tuniv l) (lsuc l);
symbol inv_eq_t2   [Γ : Context] [l : Lev] [T t1 t2 : Term] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t2 T l;
symbol inv_eq_t1   [Γ : Context] [l : Lev] [T t1 t2 : Term] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t1 T l;

// symbol inv_teq_sort [Γ : Context] [s : Sort] [T S t1 t2 : Term] : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ T (tsort s) (snext s);
// symbol inv_teq_t1   [Γ : Context] [s : Sort] [T S t1 t2 : Term] : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ t1 T s;
// symbol inv_teq_t2   [Γ : Context] [s : Sort] [T S t1 t2 : Term] : der_context Γ → der Γ (teq T t1 t2) S (snext s) → der Γ t2 T s;

// Helpers
symbol pushIΓ [Γ : Context] [l : Lev] [t T : Term] (dΓ : der_context Γ) (d: der Γ t T l)
              : der_context (Push T l Γ) ≔
  pushΓ (inv_type dΓ d) dΓ;
symbol pushEΓ [Γ : Context] [l : Lev] [t1 t2 T : Term] (dΓ : der_context Γ) (deq: der_eq Γ t1 t2 T l)
              : der_context (Push T l Γ) ≔
  pushΓ (inv_eq_type dΓ deq) dΓ;
symbol push1Γ [Γ : Context] [l : Lev] [T1 T2 : Term] (dΓ : der_context Γ) (deq: der_eq Γ T1 T2 (tuniv l) (lsuc l))
              : der_context (Push T1 l Γ) ≔
  pushΓ (inv_eq_t1 dΓ deq) dΓ;
symbol push2Γ [Γ : Context] [l : Lev] [T1 T2 : Term] (dΓ : der_context Γ) (deq: der_eq Γ T1 T2 (tuniv l) (lsuc l))
              : der_context (Push T2 l Γ) ≔
  pushΓ (inv_eq_t2 dΓ deq) dΓ;

// with inv_eq_t2 $dΓ (der_eq_rec_suc $Γ $l $l' $P $z $H $n $dP $dz $dH $dn) ↪
//      der_app $Γ $l' $l' (apply1 $P $n) (tapp $H $n) (trec $P $z $H $n) (Shift (apply1 $P (tsuc $n)))
//              (substitution $dΓ $P $dn) (substitution $dΓ $P)
symbol test (Γ : Context) (dΓ : der_context Γ) (l l' : Lev) (P z H n : Term)
            (dP : der (Push tnat l Γ) P (tuniv l') (lsuc l')) (dz : der Γ z (apply1 P tzero) l')
            (dH : der Γ H (tpi tnat (tpi P (Shift (apply1 (Shift1 P) (tsuc (tvar db0)))))) (lmax l l'))
            (dn : der Γ n tnat l) :
  der Γ (tapp (tapp H n) (trec P z H n)) (apply1 P (tsuc n)) l' ≔
begin
  assume Γ dΓ l l' P z H n dP dz dH dn;
  refine der_app Γ l' l' (apply1 P n) (tapp H n) (trec P z H n)
                 (Shift (apply1 (apply1 (Shift1 P) (tsuc (tvar db0))) n)) _ _ _ _
  { refine substitution dΓ dP dn}
  { refine der_shift0 (substitution dΓ dP dn) dΓ (substitution dΓ dP (der_suc Γ l n dn)); }
  { refine der_app Γ l l' tnat H n (tpi P (Shift (apply1 (Shift1 P) (tsuc (tvar db0))))) (der_nat Γ l) _ dH dn;
    refine der_pi (Push tnat l Γ) l' l' P _ dP _ ;
    refine @der_shift0 (Push tnat l Γ) (apply1 (Shift1 P) (tsuc (tvar db0))) P (tuniv l') (lsuc l') l'
            dP (pushΓ (der_nat Γ l) dΓ) _;
    refine @substitution (Push tnat l Γ) l (lsuc l') tnat (tuniv l') (Shift1 P)
            (pushΓ (der_nat Γ l) dΓ) _ (tsuc (tvar db0)) _
    { refine der_shift1 (der_nat Γ l) (der_nat Γ l) dΓ dP }
    { refine der_suc _ _ (tvar db0) _;
  refine der_var _ _ _;
  refine dble_n_S (dble_0_n (len Γ)) }
  }
  { refine der_rec Γ l l' P z H n dP dz _ dn;
    }
end;

// Definition of inv_sort
rule inv_type _ (der_empty_face $Γ $l _ $A $dz) ↪ der_empty_face $Γ (lsuc $l) $A (tuniv $l) $dz
with inv_type $dΓ (der_union_face $Γ $l _ $A $f $g $d1 $d2 $df) ↪
     der_union_face $Γ (lsuc $l) $A (tuniv $l) $f $g (inv_type (pushΓF $f $dΓ) $d1) (inv_type (pushΓF $g $dΓ) $d2) $df
with inv_type $dΓ (der_var _ $id _) ↪ der_shift $id $dΓ (der_getΓ $id $dΓ)
with inv_type _ (der_univ $Γ $l) ↪ der_univ $Γ (lsuc $l)
with inv_type _ (der_pi $Γ $l $l' _ _ _ _) ↪ der_univ $Γ (lmax $l $l')
with inv_type $dΓ (der_abs $Γ $l $l' $A _ $B $dA $dB $dt) ↪ der_pi $Γ $l $l' $A $B $dA $dB // inv_type t instead of dB
with inv_type $dΓ (der_app _ _ _ _ _ _ _ _ $dB _ $du) ↪ substitution $dΓ $dB $du
with inv_type $dΓ (der_type_conv _ _ _ _ _ _ $deq) ↪ inv_eq_t2 $dΓ $deq
with inv_type _ (der_nat $Γ $l) ↪ der_univ $Γ $l
with inv_type _ (der_zero $Γ $l) ↪ der_nat $Γ $l
with inv_type _ (der_suc $Γ $l _ _) ↪ der_nat $Γ $l
with inv_type $dΓ (der_rec _ _ $l _ _ _ _ $dP _ _ $dn) ↪ substitution $dΓ $dP $dn
with inv_type _ (der_sig $Γ $s $s' _ _ _ _) ↪ der_univ $Γ (lmax $s $s')
with inv_type $dΓ (der_pair $Γ $s $s' $A $B _ _ $dA $dB _ _) ↪ der_sig $Γ $s $s' $A $B $dA $dB // inv_type ?
with inv_type _ (der_p1 _ _ _ _ _ _ $dA _ _) ↪ $dA
with inv_type $dΓ (der_p2 $Γ $s $s' $A $B $p $dA $dB $dp) ↪
     substitution $dΓ $dB [tp1 $p] (der_p1 $Γ $s $s' $A $B $p $dA $dB $dp)
with inv_type _ (der_sum $Γ $l $l' _ _ _ _) ↪ der_univ $Γ (lmax $l $l')
with inv_type _ (der_injl $Γ $l $l' $A $B _ $dA $dB _) ↪ der_sum $Γ $l $l' $A $B $dA $dB
with inv_type _ (der_injr $Γ $l $l' $A $B _ $dA $dB _) ↪ der_sum $Γ $l $l' $A $B $dA $dB
with inv_type $dΓ (der_case $Γ $l $l' $m $A $B $P $hA $Hb $x $dA $dB $dP $dHa $dHb $dx) ↪
     substitution $dΓ $dP $dx
with inv_type _ (der_path $Γ $l _ _ _ _ _ _) ↪ der_univ $Γ $l
with inv_type $dΓ (der_lamP $Γ $l $A $t $dA $dt) ↪
     der_path $Γ $l $A (applyI1 $t it0) (applyI1 $t it1) $dA
              (Isubstitution $dΓ $dt (der_I_0 $Γ)) (Isubstitution $dΓ $dt (der_I_1 $Γ))
with inv_type $dΓ (der_appP _ _ _ _ _ _ _ $dA _ _ _ $di) ↪ Isubstitution $dΓ $dA $di
with inv_type _ (der_sys _ _ _ _ _ _ _ $dA _ _ _ _ _ _) ↪ $dA
with inv_type _ (der_sys_empty _ _ _ $dA _) ↪ $dA
with inv_type $dΓ (der_transp $Γ _ _ _ _ $dA _ _ _) ↪ Isubstitution $dΓ $dA (der_I_1 $Γ)
with inv_type _ (der_hcomp _ _ _ _ _ _ $dA _ _ _ _) ↪ $dA
;

// Definition of inv_eq*
// Structural rules
rule inv_eq_type $dΓ (der_eq_refl _ _ _ _ $du) ↪ inv_type $dΓ $du
with inv_eq_t1   _   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_t2   _   (der_eq_refl _ _ _ _ $du) ↪ $du
with inv_eq_type $dΓ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_type $dΓ $duv
with inv_eq_t1   $dΓ (der_eq_trans _ _ _ _ _ _ $duv _) ↪ inv_eq_t1 $dΓ $duv
with inv_eq_t2   $dΓ (der_eq_trans _ _ _ _ _ _ _ $dvw) ↪ inv_eq_t2 $dΓ $dvw
with inv_eq_type $dΓ (der_eq_sym _ _ _ _ _ $duv) ↪ inv_eq_type $dΓ $duv
with inv_eq_t1   $dΓ (der_eq_sym _ _ _ _ _ $duv) ↪ inv_eq_t2 $dΓ $duv
with inv_eq_t2   $dΓ (der_eq_sym _ _ _ _ _ $duv) ↪ inv_eq_t1 $dΓ $duv
// Conversion
with inv_eq_type $dΓ (der_eq_conv _ _ _ _ _ _ _ $deqT) ↪ inv_eq_t2 $dΓ $deqT
with inv_eq_t1   $dΓ (der_eq_conv $Γ $s $t1 _ $T1 $T2 $deq $deqT) ↪
     der_type_conv $Γ $s $t1 $T1 $T2 (inv_eq_t1 $dΓ $deq) $deqT
with inv_eq_t2   $dΓ (der_eq_conv $Γ $s _ $t2 $T1 $T2 $deq $deqT) ↪
     der_type_conv $Γ $s $t2 $T1 $T2 (inv_eq_t2 $dΓ $deq) $deqT
// Face reasoning
with inv_eq_type _ (der_eq_isOne_zero $Γ $l $A _ _ $dz) ↪ der_empty_face $Γ (lsuc $l) $A (tuniv $l) $dz
with inv_eq_t1 _ (der_eq_isOne_zero $Γ $l $A $t1 _ $dz) ↪ der_empty_face $Γ $l $t1 $A $dz
with inv_eq_t2 _ (der_eq_isOne_zero $Γ $l $A _ $t2 $dz) ↪ der_empty_face $Γ $l $t2 $A $dz
with inv_eq_type $dΓ (der_eq_isOne_max $Γ $l $A _ _ $f $g $d1 $d2 $df) ↪
     der_union_face $Γ (lsuc $l) $A (tuniv $l) $f $g (inv_eq_type (pushΓF $f $dΓ) $d1)
                                                     (inv_eq_type (pushΓF $g $dΓ) $d2) $df
with inv_eq_t1 $dΓ (der_eq_isOne_max $Γ $l $A $t1 _ $f $g $d1 $d2 $df) ↪
     der_union_face $Γ $l $t1 $A $f $g (inv_eq_t1 (pushΓF $f $dΓ) $d1) (inv_eq_t1 (pushΓF $g $dΓ) $d2) $df
with inv_eq_t2 $dΓ (der_eq_isOne_max $Γ $l $A _ $t2 $f $g $d1 $d2 $df) ↪
     der_union_face $Γ $l $t2 $A $f $g (inv_eq_t2 (pushΓF $f $dΓ) $d1) (inv_eq_t2 (pushΓF $g $dΓ) $d2) $df
// Computation
with inv_eq_type $dΓ (der_eq_beta _  _  _   _  _  _  _  _ $dB _ $du) ↪
     substitution $dΓ $dB $du
with inv_eq_t1 $dΓ (der_eq_beta $Γ $s $s' $u $A $t $B $dA $dB $dt $du) ↪
     der_app $Γ $s $s' $A (tabs $A $t) $u $B $dA $dB (der_abs $Γ $s $s' $A $t $B $dA $dB $dt) $du
with inv_eq_t2   $dΓ (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution $dΓ $dt $du
with inv_eq_type _   (der_eq_eta  $Γ $s $s' $A $B _ $dA $dB _  ) ↪ der_pi $Γ $s $s' $A $B $dA $dB
with inv_eq_t1   $dΓ (der_eq_eta  $Γ $s $s' $A $B $f $dA $dB $df) ↪
     der_abs $Γ $s $s' $A (tapp (Shift $f) (tvar db0)) $B $dA $dB
             (der_app (Push $A $s $Γ) $s $s' (Shift $A) (Shift $f) (tvar db0) (Shift1 $B)
                      (der_shift0 $dA $dΓ $dA) (der_shift1 $dA $dA $dΓ $dB)
                      (der_shift0 $dA $dΓ $df) (der_var (Push $A $s $Γ) db0 (dble_n_S (dble_0_n (len $Γ)))))
with inv_eq_t2   _   (der_eq_eta  _  _  _   _  _  _  _   _   $df) ↪ $df
with inv_eq_type $dΓ (der_eq_rec_zero $Γ $l _ _ _ _ $dP _ _) ↪ substitution $dΓ $dP (der_zero $Γ $l)
with inv_eq_t1 _ (der_eq_rec_zero $Γ $l $l' $P $z $H $dP $dz $dH) ↪
     der_rec $Γ $l $l' $P $z $H tzero $dP $dz $dH (der_zero $Γ $l)
with inv_eq_t2 _ (der_eq_rec_zero _ _ _ _ _ _ _ $dz _) ↪ $dz
with inv_eq_type $dΓ (der_eq_rec_suc $Γ $l _ _ _ _ $n $dP _ _ $dn) ↪ substitution $dΓ $dP (der_suc $Γ $l $n $dn)
with inv_eq_t1 _ (der_eq_rec_suc $Γ $l $l' $P $z $H $n $dP $dz $dH $dn) ↪
     der_rec $Γ $l $l' $P $z $H (tsuc $n) $dP $dz $dH (der_suc $Γ $l $n $dn)
// TODO : work out DeBruijn mess
with inv_eq_t2 $dΓ (der_eq_rec_suc $Γ $l $l' $P $z $H $n $dP $dz $dH $dn) ↪
     der_app $Γ $l' $l' (apply1 $P $n) (tapp $H $n) (trec $P $z $H $n) (Shift (apply1 $P (tsuc $n)))
             (substitution $dΓ $P $dn) (substitution $dΓ $P)
with inv_eq_sort $dΓ (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ inv_sort $dΓ $du
with inv_eq_t1   $dΓ (der_eq_π1 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                               (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)
with inv_eq_t2   _   (der_eq_π1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ $du
with inv_eq_sort $dΓ (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ inv_sort $dΓ $dv
with inv_eq_t1   $dΓ (der_eq_π2 $Γ $s $s' $u $A $v $B _ $du $dB $dv) ↪ der_type_conv $Γ (π2 $A $B (tpair $A $B $u $v)) (apply1 $B (π1 $A $B (tpair $A $B $u $v))) (apply1 $B $u) $s'
                                                                            (der_π2 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                              (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv))
                                                                            (der_eq_cong_apply $dΓ
                                                                              (der_eq_refl $Γ (snext $s) $A (tsort $s) (inv_sort $dΓ $du))
                                                                              (der_eq_refl (Push $A $s $Γ) (snext $s') $B (tsort $s') $dB)
                                                                              (der_eq_π1 $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)
                                                                              $dB $dB
                                                                              (der_π1 $Γ $s $s' (tpair $A $B $u $v) $A $B (inv_sort $dΓ $du) $dB
                                                                                (der_pair $Γ $s $s' $u $A $v $B (inv_sort $dΓ $du) $du $dB $dv)) $du)
with inv_eq_t2   _   (der_eq_π2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ $dv
// Congruence
// Lambda-calculus
with inv_eq_sort _   (der_eq_cong_tfun $Γ $s $s' _   _   _   _   _     _ _    _   ) ↪ der_sort $Γ (smax $s $s')
with inv_eq_t1   $dΓ (der_eq_cong_tfun $Γ $s $s' $A1 _   $B1 _   $deqA _ $dB1 _   ) ↪ der_prod $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t2   $dΓ (der_eq_cong_tfun $Γ $s $s' _   $A2 _   $B2 $deqA _ _    $dB2) ↪ der_prod $Γ $s $s' $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2
with inv_eq_sort $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 _   $B1 _   _   _   $deqA _     _ $dB1 _    _    _   ) ↪ der_prod $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t1   $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 _   $B1 _   $t1 _   $deqA _     _ $dB1 _    $dt1 _   ) ↪ der_abs $Γ $s $s' $A1 $t1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dt1
with inv_eq_t2   $dΓ (der_eq_cong_tabs $Γ $s $s' $A1 $A2 $B1 $B2 _   $t2 $deqA $deqB _ $dB1 $dB2 _    $dt2)
   ↪ der_type_conv $Γ (tabs $A2 $B2 $t2) (tfun $A2 $B2) (tfun $A1 $B1) (smax $s $s')
                    (der_abs $Γ $s $s' $A2 $t2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dt2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_tfun $Γ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2))
with inv_eq_sort $dΓ (der_eq_cong_tapp _  _  _   _   _   _   _   _   _   _   _   _     _     _ _     $dB1 _    _    _    $da1 _   ) ↪ substitution $dΓ $dB1 $da1
with inv_eq_t1   $dΓ (der_eq_cong_tapp $Γ $s $s' $A1 _   $B1 _   $f1 _   $a1 _   $deqA _     _ _     $dB1 _    $df1 _    $da1 _   ) ↪ der_app $Γ $s $s' $A1 $f1 $a1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $df1 $da1
with inv_eq_t2   $dΓ (der_eq_cong_tapp $Γ $s $s' _   $A2 $B1 $B2 _   $f2 $a1 $a2 $deqA $deqB _ $deqa $dB1 $dB2 _    $df2 $da1 $da2)
   ↪ der_type_conv $Γ (tapp $A2 $B2 $f2 $a2) (apply1 $B2 $a2) (apply1 $B1 $a1) $s'
                    (der_app $Γ $s $s' $A2 $f2 $a2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $df2 $da2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_apply $dΓ $deqA $deqB $deqa $dB1 $dB2 $da1 $da2))
// Pairs
with inv_eq_sort _   (der_eq_cong_tsum $Γ $s $s' _   _   _   _   _     _ _    _   ) ↪ der_sort $Γ (smax $s $s')
with inv_eq_t1   $dΓ (der_eq_cong_tsum $Γ $s $s' $A1 _   $B1 _   $deqA _ $dB1 _   ) ↪ der_sigma $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t2   $dΓ (der_eq_cong_tsum $Γ $s $s' _   $A2 _   $B2 $deqA _ _    $dB2) ↪ der_sigma $Γ $s $s' $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2
with inv_eq_sort $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 _   $B1 _   _   _   _   _   $deqA _     _ _ $dB1 _    _    _    _    _   ) ↪ der_sigma $Γ $s $s' $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1
with inv_eq_t1   $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 _   $B1 _   $a1 _   $b1 _   $deqA _     _ _ $dB1 _    $da1 _    $db1 _   ) ↪ der_pair $Γ $s $s' $a1 $A1 $b1 $B1 (inv_eq_t1 $dΓ $deqA) $da1 $dB1 $db1
with inv_eq_t2   $dΓ (der_eq_cong_tpair $Γ $s $s' $A1 $A2 $B1 $B2 _   $a2 _   $b2 $deqA $deqB _ _ $dB1 $dB2 _    $da2 _    $db2)
   ↪ der_type_conv $Γ (tpair $A2 $B2 $a2 $b2) (tsum $A2 $B2) (tsum $A1 $B1) (smax $s $s')
                    (der_pair $Γ $s $s' $a2 $A2 $b2 $B2 (inv_eq_t2 $dΓ $deqA) $da2 $dB2 $db2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_tsum $Γ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2))
with inv_eq_sort $dΓ (der_eq_cong_π1 _  _  _   _   _   _   _   _   _   $deqA _ _ _    _    _    _   ) ↪ inv_eq_t1 $dΓ $deqA
with inv_eq_t1   $dΓ (der_eq_cong_π1 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _ _ $dB1 _    $dp1 _   ) ↪ der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_π1 $Γ $s $s' $A1 $A2 _   $B2 _   $p2 $deqA _ _ _    $dB2 _    $dp2)
   ↪ der_type_conv $Γ (π1 $A2 $B2 $p2) $A2 $A1 $s
                    (der_π1 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)
                    (der_eq_symm _ _ _ _ _ $deqA)
with inv_eq_sort $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _     _     $dB1 _    $dp1 _   ) ↪ substitution $dΓ $dB1 (der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1)
with inv_eq_t1   $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 _   $B1 _   $p1 _   $deqA _     _     $dB1 _    $dp1 _   ) ↪ der_π2 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_π2 $Γ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
   ↪ der_type_conv $Γ (π2 $A2 $B2 $p2) (apply1 $B2 (π1 $A2 $B2 $p2)) (apply1 $B1 (π1 $A1 $B1 $p1)) $s'
                    (der_π2 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)
                    (der_eq_symm _ _ _ _ _
                     (der_eq_cong_apply $dΓ $deqA $deqB
                      (der_eq_cong_π1 $Γ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
                      $dB1 $dB2
                      (der_π1 $Γ $s $s' $p1 $A1 $B1 (inv_eq_t1 $dΓ $deqA) $dB1 $dp1)
                      (der_π1 $Γ $s $s' $p2 $A2 $B2 (inv_eq_t2 $dΓ $deqA) $dB2 $dp2)))
// Equalities
with inv_eq_sort _   (der_eq_cong_teq $Γ $s _   _   _   _   _   _   _     _ _ _    _    _    _   ) ↪ der_sort $Γ $s
with inv_eq_t1   $dΓ (der_eq_cong_teq $Γ $s $A1 _   $a1 _   $b1 _   $deqA _ _ $da1 _    $db1 _   ) ↪ der_prop_type_eq $Γ $s $A1 $a1 $b1 (inv_eq_t1 $dΓ $deqA) $da1 $db1
with inv_eq_t2   $dΓ (der_eq_cong_teq $Γ $s _   $A2 _   $a2 _   $b2 $deqA _ _ _    $da2 _    $db2) ↪ der_prop_type_eq $Γ $s $A2 $a2 $b2 (inv_eq_t2 $dΓ $deqA) $da2 $db2
with inv_eq_sort $dΓ (der_eq_cong_trefl $Γ $s $A1 _   $a1 _   $deqA _     $da1 _   ) ↪ der_prop_type_eq $Γ $s $A1 $a1 $a1 (inv_eq_t1 $dΓ $deqA) $da1 $da1
with inv_eq_t1   $dΓ (der_eq_cong_trefl $Γ $s $A1 _   $a1 _   $deqA _     $da1 _   ) ↪ der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1
with inv_eq_t2   $dΓ (der_eq_cong_trefl $Γ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
   ↪ der_type_conv $Γ (trefl $A2 $a2) (teq $A2 $a2 $a2) (teq $A1 $a1 $a1) $s
                    (der_refl $Γ $s $a2 $A2 (inv_eq_t2 $dΓ $deqA) $da2)
                    (der_eq_symm _ _ _ _ _ (der_eq_cong_teq $Γ $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2))
with inv_eq_sort $dΓ (der_eq_cong_tK $Γ $s $A1 _   $a1 _   $p1 _   $deqA _     _     $da1 _    $dp1 _   )
   ↪ der_prop_type_eq $Γ $s (teq $A1 $a1 $a1) $p1 (trefl $A1 $a1)
                       (der_prop_type_eq $Γ $s $A1 $a1 $a1 (inv_eq_t1 $dΓ $deqA) $da1 $da1)
                       $dp1 (der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1)
with inv_eq_t1   $dΓ (der_eq_cong_tK $Γ $s $A1 _   $a1 _   $p1 _   $deqA _     _     $da1 _    $dp1 _   )
   ↪ der_K $Γ $s $A1 $a1 $p1 (inv_eq_t1 $dΓ $deqA) $da1 $dp1
with inv_eq_t2   $dΓ (der_eq_cong_tK $Γ $s $A1 $A2 $a1 $a2 $p1 $p2 $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
   ↪ der_type_conv $Γ (tK $A2 $a2 $p2) (teq (teq $A2 $a2 $a2) $p2 (trefl $A2 $a2)) (teq (teq $A1 $a1 $a1) $p1 (trefl $A1 $a1)) $s
                    (der_K $Γ $s $A2 $a2 $p2 (inv_eq_t2 $dΓ $deqA) $da2 $dp2)
                    (der_eq_symm _ _ _ _ _
                      (der_eq_cong_teq $Γ $s (teq $A1 $a1 $a1) (teq $A2 $a2 $a2) $p1 $p2 (trefl $A1 $a1) (trefl $A2 $a2)
                        (der_eq_cong_teq $Γ $s $A1 $A2 $a1 $a2 $a1 $a2 $deqA $deqa $deqa $da1 $da2 $da1 $da2)
                        $deqp (der_eq_cong_trefl $Γ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
                        $dp1 $dp2 (der_refl $Γ $s $a1 $A1 (inv_eq_t1 $dΓ $deqA) $da1) (der_refl $Γ $s $a2 $A2 (inv_eq_t2 $dΓ $deqA) $da2)))
;

// Propositional equality inversion
rule inv_teq_sort _   (der_prop_type_eq _ _ _ _ _ $dA _    _   ) ↪ $dA
with inv_teq_t1   _   (der_prop_type_eq _ _ _ _ _ _   $da1 _   ) ↪ $da1
with inv_teq_t2   _   (der_prop_type_eq _ _ _ _ _ _   _    $da2) ↪ $da2
with inv_teq_sort $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_sort $dΓ $du
with inv_teq_t1   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t1   $dΓ $du
with inv_teq_t2   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t2   $dΓ $du
;
