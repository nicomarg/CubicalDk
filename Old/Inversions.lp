
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;
require open ctt.Lemmas;
require open ctt.TermEquality;
// require ETT.ITT as ITT;


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

// symbol test (Γ : Context) (dΓ : der_context Γ) (l l' : Lev) (A B u v : Term) (f : FTerm)
//   (dA : der (PushI Γ) A (tuniv l) (lsuc l)) (dB : der (Push A l (PushI Γ)) B (tuniv l') (lsuc l'))
//   (df : der_F Γ f) (deq_A : der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l))
//   (deq_B : der_eq (Push A l (PushF (IShiftF f) (PushI Γ))) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l'))
//   (du : der Γ u (applyI1 (tpi A B) it0) (lmax l l')) (dv : der Γ v (applyI1 A it1) l) :
//   der Γ
//          (ttransp (apply1 B (ttransp (applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0))))
//                                      (ftmax (IShiftF f) (fteq0 db0)) (IShift v)))
//                   f (tapp u (ttransp (applyI1 (IShift1 A) (itsym (itvar db0))) f v)))
//  (apply1 (applyI1 B it1) v) l' ≔
// begin
//   assume Γ dΓ l l' A B u v f dA dB df deq_A deq_B du dv;
//   refine der_type_conv (der_transp _ df _ _) _
//   { refine substitution (pushΓI dΓ) dB [ttransp (applyI1 (IShift1 (IShift1 A))
//                                                          (itmax (itvar db1) (itsym (itvar db0))))
//                                                 (ftmax (IShiftF f) (fteq0 db0)) (IShift v)] _;
//     refine der_type_conv (der_transp _ _ _ _) _
//     { refine Isubstitution [_] [lsuc l] [tuniv l] [IShift1 (IShift1 A)] (pushΓI (pushΓI dΓ)) _
//              (der_I_max (der_I_var dble_db1) (der_I_sym (der_I_var dble_db0)));
//       refine der_Ishift1 (pushΓI dΓ) (der_Ishift1 dΓ dA)}
//     { refine der_F_max (der_Ishift0F dΓ df) (der_F_eq0 dble_db0)}
//     { refine JT (teq_inv (teq_Isubst_Iapply db0 it0 (itmax (itvar db1) (itsym (itvar db0))) (IShift1 (IShift1 A)))) _;
//       simplify;
//       refine @Isubstitution_conv_arg _ _ (IShift (IShift v)) (Ishift db1 A) it1 (itmax (itvar db0) (itsym it0))
//                                      (pushΓI dΓ) (der_Ishift0 dΓ dv) _;
//       refine der_eq_I_sym _ _ _ _;
//       refine der_eq_I_trans _ _ (itmax (itvar db0) it1) _ _
//                                     (der_eq_I_max_one _ _);
//       refine der_eq_I_cong_max _ _ _ _ _ (der_eq_I_refl _ _ (der_I_var dble_db0)) (der_eq_I_sym_zero _);
//     }
//     { refine der_eq_isOne_max _ _ (tuniv l) (applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0))))
//                               (IShift (applyI1 (applyI1 (IShift1 (IShift1 A))
//                                                         (itmax (itvar db1) (itsym (itvar db0)))) it0))
//                               (IShiftF (IShiftF f)) (IShiftF (fteq0 db0))
//                               _
//                               _
//                               _
//                               _
//                               (der_isOne_axiom _ _)
//       { refine der_weakFF (pushΓI (pushΓI dΓ)) (der_Ishift0F (pushΓI dΓ) (der_Ishift0F dΓ df)) _;
//         refine der_Ishift0F (pushΓI dΓ) (der_F_max (der_Ishift0F dΓ df) (der_F_eq0 dble_db0))
//       }
//       { refine der_weakFF (pushΓI (pushΓI dΓ)) (der_Ishift0F (pushΓI dΓ) (der_F_eq0 dble_db0)) _;
//         refine der_Ishift0F (pushΓI dΓ) (der_F_max (der_Ishift0F dΓ df) (der_F_eq0 dble_db0))
//       }
//       //(applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0))))
//       //(IShift (applyI1 (applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0)))) it0))
//       {  }
//       {};
//     }
//     {}
//   }
//   {}
//   {}
//   {}
// end;
// print test;
// Definition of inv_sort
rule inv_type _ (der_empty_face $dz) ↪ der_empty_face $dz
with inv_type $dΓ (@der_union_face _ _ _ _ _ _ $df $dg $d1 $d2 $di1) ↪
     der_union_face $df $dg (inv_type (pushΓF $df $dΓ) $d1) (inv_type (pushΓF $dg $dΓ) $d2) $di1
with inv_type $dΓ (@der_var _ $id _) ↪ der_shift $id $dΓ (der_getΓ $id $dΓ)
with inv_type _ der_univ ↪ der_univ
with inv_type _ (der_pi _ _) ↪ der_univ
with inv_type _ (der_abs $dA $dB _) ↪ der_pi $dA $dB // inv_type t instead of dB
with inv_type $dΓ (der_app _ _ _ _ _ $dB _ $du) ↪ substitution $dΓ $dB $du
with inv_type $dΓ (der_type_conv _ $deq) ↪ inv_eq_t2 $dΓ $deq
with inv_type _ der_nat ↪ der_univ
with inv_type _ der_zero ↪ der_nat
with inv_type _ (der_suc _) ↪ der_nat
with inv_type _ (der_rec $dP _ _ $dn) ↪
     der_app _ _ _ _ der_nat der_univ $dP $dn
with inv_type _ (der_sig _ _) ↪ der_univ
with inv_type _ (der_pair $dA $dB _ _) ↪ der_sig $dA $dB // inv_type ?
with inv_type _ (der_p1 $dA _ _) ↪ $dA
with inv_type $dΓ (der_p2 $dA $dB $dp) ↪
     substitution $dΓ $dB (der_p1 $dA $dB $dp)
with inv_type _ (der_sum _ _) ↪ der_univ
with inv_type _ (der_injl $dA $dB _) ↪ der_sum $dA $dB
with inv_type _ (der_injr $dA $dB _) ↪ der_sum $dA $dB
with inv_type _ (der_case $dA $dB $dP _ _ $dx) ↪
     der_app (tsum _ _) _ _ (tuniv _) (der_sum $dA $dB)
             der_univ $dP $dx
with inv_type _ (der_path _ _ _) ↪ der_univ
with inv_type $dΓ (der_lamP $dA $dt) ↪
     der_path $dA (Isubstitution $dΓ $dt der_I_0) (Isubstitution $dΓ $dt der_I_1)
with inv_type $dΓ (der_appP _ _ _ _ _ $dA _ _ _ $di) ↪ Isubstitution $dΓ $dA $di
with inv_type _ (der_sys $dA _ _ _ _ _ _) ↪ $dA
with inv_type _ (der_sys_empty $dA _) ↪ $dA
with inv_type $dΓ (der_transp $dA _ _ _) ↪ Isubstitution $dΓ $dA der_I_1
with inv_type _ (der_hcomp $dA _ _ _ _) ↪ $dA
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
with inv_eq_t1   $dΓ (der_eq_conv _ _ _ _ _ _ $deq $deqT) ↪
     der_type_conv (inv_eq_t1 $dΓ $deq) $deqT
with inv_eq_t2   $dΓ (der_eq_conv _ _ _ _ _ _ $deq $deqT) ↪
     der_type_conv (inv_eq_t2 $dΓ $deq) $deqT
// Face reasoning
with inv_eq_type _ (der_eq_isOne_zero _ _ _ _ _ $dz) ↪ der_empty_face $dz
with inv_eq_t1 _ (der_eq_isOne_zero _ _ _ _ _ $dz) ↪ der_empty_face $dz
with inv_eq_t2 _ (der_eq_isOne_zero _ _ _ _ _ $dz) ↪ der_empty_face $dz
with inv_eq_type $dΓ (der_eq_isOne_max _ _ _ _ _ _ _ $df $dg $d1 $d2 $di1) ↪
     der_union_face $df $dg (inv_eq_type (pushΓF $df $dΓ) $d1) (inv_eq_type (pushΓF $dg $dΓ) $d2) $di1
with inv_eq_t1 $dΓ (der_eq_isOne_max _ _ _ _ _ _ _ $df $dg $d1 $d2 $di1) ↪
     der_union_face $df $dg (inv_eq_t1 (pushΓF $df $dΓ) $d1) (inv_eq_t1 (pushΓF $dg $dΓ) $d2) $di1
with inv_eq_t2 $dΓ (der_eq_isOne_max _ _ _ _ _ _ _ $df $dg $d1 $d2 $di1) ↪
     der_union_face $df $dg (inv_eq_t2 (pushΓF $df $dΓ) $d1) (inv_eq_t2 (pushΓF $dg $dΓ) $d2) $di1
// Computation
with inv_eq_type $dΓ (der_eq_beta _  _  _   _  _  _  _  _ $dB _ $du) ↪
     substitution $dΓ $dB $du
with inv_eq_t1 _ (der_eq_beta _ _ _ $u $A $t $B $dA $dB $dt $du) ↪
     der_app $A (tabs $A $t) $u $B $dA $dB (der_abs $dA $dB $dt) $du
with inv_eq_t2   $dΓ (der_eq_beta _  _  _   _  _  _  _  _ _ $dt $du) ↪ substitution $dΓ $dt $du
with inv_eq_type _   (der_eq_eta _ _ _ _ _ _ $dA $dB _  ) ↪ der_pi $dA $dB
with inv_eq_t1   $dΓ (der_eq_eta _ _ _ $A $B $f $dA $dB $df) ↪
     der_abs $dA $dB
             (der_app (Shift $A) (Shift $f) (tvar db0) (Shift1 $B)
                      (der_shift0 $dA $dΓ $dA) (der_shift1 $dA $dA $dΓ $dB)
                      (der_shift0 $dA $dΓ $df) (der_var (dble_n_S (dble_0_n _))))
with inv_eq_t2   _   (der_eq_eta  _  _  _   _  _  _  _   _   $df) ↪ $df
with inv_eq_type _ (der_eq_rec_zero _ $l $l' $P _ _ $dP _ _) ↪
     @der_app _ $l (lsuc $l') tnat $P tzero (tuniv _) der_nat der_univ $dP der_zero
with inv_eq_t1 _ (der_eq_rec_zero _ $l $l' _ _ _ $dP $dz $dH) ↪
     der_rec [_] [$l] [$l'] $dP $dz $dH der_zero
with inv_eq_t2 _ (der_eq_rec_zero _ _ _ _ _ _ _ $dz _) ↪ $dz
with inv_eq_type _ (der_eq_rec_suc _ _ $l' $P _ _ $n $dP _ _ $dn) ↪
     der_app tnat $P (tsuc $n) (tuniv $l') der_nat der_univ $dP (der_suc $dn)
with inv_eq_t1 _ (der_eq_rec_suc _ _ _ _ _ _ _ $dP $dz $dH $dn) ↪
     der_rec $dP $dz $dH (der_suc $dn)
with inv_eq_t2 $dΓ (der_eq_rec_suc $Γ _ $l' $P $z $H $n $dP $dz $dH $dn) ↪
     der_app (tapp $P $n) (tapp $H $n) (trec $P $z $H $n) (tapp (Shift $P) (tsuc (Shift $n)))
             (der_app tnat $P $n (tuniv $l') der_nat der_univ $dP $dn)
             (der_shift0 (der_app tnat $P $n (tuniv $l') der_nat der_univ $dP $dn) $dΓ
                         (der_app tnat $P (tsuc $n) (tuniv $l') der_nat der_univ $dP (der_suc $dn)))
             (der_app tnat $H $n (tpi (tapp (Shift $P) (tvar db0)) (tapp (Shift (Shift $P)) (tsuc (tvar db1))))
                      der_nat
                      (der_pi (der_app tnat (Shift $P) (tvar db0) (tuniv $l') der_nat der_univ
                                       (der_shift0 der_nat $dΓ $dP) (der_var (dble_n_S (dble_0_n (len $Γ)))))
                              (der_shift0 (der_app tnat (Shift $P) (tvar db0) (tuniv $l') der_nat der_univ
                                                   (der_shift0 der_nat $dΓ $dP)
                                                   (der_var (dble_n_S (dble_0_n (len $Γ)))))
                                          (pushΓ der_nat $dΓ)
                                          (der_app tnat (Shift $P) (tsuc (tvar db0)) (tuniv $l') der_nat der_univ
                                                   (der_shift0 der_nat $dΓ $dP)
                                                   (der_suc (der_var (dble_n_S (dble_0_n (len $Γ))))))))
                      $dH $dn)
             (der_rec $dP $dz $dH $dn)
with inv_eq_type $dΓ (der_eq_p1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ inv_type $dΓ $du
with inv_eq_t1   _ (der_eq_p1 _ _ _ _ _ _ _ $dA $du $dB $dv) ↪
     der_p1 $dA $dB (der_pair $dA $dB $du $dv)
with inv_eq_t2   _   (der_eq_p1 _  _  _   _  _  _  _  _ $du _   _  ) ↪ $du
with inv_eq_type $dΓ (der_eq_p2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ inv_type $dΓ $dv
with inv_eq_t1   $dΓ (der_eq_p2 $Γ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     @der_type_conv $Γ $s' (tp2 (tpair $u $v)) (apply1 $B (tp1 (tpair $u $v))) (apply1 $B $u)
                    (der_p2 $dA $dB (der_pair $dA $dB $du $dv))
                    (der_eq_cong_apply $dΓ (der_eq_refl $Γ (lsuc $s) $A (tuniv $s) $dA)
                                       (der_eq_refl (Push $A $s $Γ) (lsuc $s') $B (tuniv $s') $dB)
                                       (der_eq_p1 $Γ $s $s' $A $u $B $v $dA $du $dB $dv)
                                       $dB $dB (der_p1 $dA $dB (der_pair $dA $dB $du $dv)) $du)
with inv_eq_t2   _   (der_eq_p2 _  _  _   _  _  _  _  _ _   _   $dv) ↪ $dv
with inv_eq_type _ (der_eq_pair _ _ _ _ _ _ _ $dA $dB _ _ _ _) ↪
     der_sig $dA $dB
with inv_eq_t1 _ (der_eq_pair _ _ _ _ _ _ _ _ _ $dt _ _ _) ↪ $dt
with inv_eq_t2 _ (der_eq_pair _ _ _ _ _ _ _ _ _ _ $du _ _) ↪ $du
with inv_eq_type _ (der_eq_case_left _ _ _ $m $A $B $P _ _ $a $dA $dB $dP _ _ $da) ↪
     der_app (tsum $A $B) $P (tinjl $a) (tuniv $m) (der_sum $dA $dB) der_univ $dP (der_injl $dA $dB $da)
with inv_eq_t1 _ (der_eq_case_left _ _ _ _ _ _ _ _ _ _ $dA $dB $dP $dHa $dHb $da) ↪
     der_case $dA $dB $dP $dHa $dHb (der_injl $dA $dB $da)
with inv_eq_t2 $dΓ (der_eq_case_left _ _ _ $m $A $B $P $Ha _ $a $dA $dB $dP $dHa _ $da) ↪
     der_app $A $Ha $a (tapp (Shift $P) (tinjl (tvar db0))) $dA
             (der_app (tsum (Shift $A) (Shift $B)) (Shift $P) (tinjl (tvar db0)) (tuniv $m)
                      (der_shift0 $dA $dΓ (der_sum $dA $dB)) der_univ (der_shift0 $dA $dΓ $dP)
                      (der_injl (der_shift0 $dA $dΓ $dA) (der_shift0 $dA $dΓ $dB) (der_var dble_db0)))
             $dHa $da
with inv_eq_type _ (der_eq_case_right _ _ _ $m $A $B $P _ _ $b $dA $dB $dP _ _ $db) ↪
     der_app (tsum $A $B) $P (tinjr $b) (tuniv $m) (der_sum $dA $dB) der_univ $dP (der_injr $dA $dB $db)
with inv_eq_t1 _ (der_eq_case_right _ _ _ _ _ _ _ _ _ _ $dA $dB $dP $dHa $dHb $db) ↪
     der_case $dA $dB $dP $dHa $dHb (der_injr $dA $dB $db)
with inv_eq_t2 $dΓ (der_eq_case_right _ _ _ $m $A $B $P _ $Hb $b $dA $dB $dP _ $dHb $db) ↪
     der_app $B $Hb $b (tapp (Shift $P) (tinjr (tvar db0))) $dB
             (der_app (tsum (Shift $A) (Shift $B)) (Shift $P) (tinjr (tvar db0)) (tuniv $m)
                      (der_shift0 $dB $dΓ (der_sum $dA $dB)) der_univ (der_shift0 $dB $dΓ $dP)
                      (der_injr (der_shift0 $dB $dΓ $dA) (der_shift0 $dB $dΓ $dB) (der_var dble_db0)))
             $dHb $db
with inv_eq_type $dΓ (der_eq_betaP _ _ _ _ _ $dA _ $di) ↪
     Isubstitution $dΓ $dA $di
with inv_eq_t1 $dΓ (der_eq_betaP _ _ $A $t $i $dA $dt $di) ↪
     der_appP $A (tlamP $t) (applyI1 $t it0) (applyI1 $t it1) $i $dA
              (Isubstitution $dΓ $dt der_I_0) (Isubstitution $dΓ $dt der_I_1)
              (der_lamP $dA $dt) $di
with inv_eq_t2 $dΓ (der_eq_betaP _ _ _ _ _ _ $dt $di) ↪
     Isubstitution $dΓ $dt $di
with inv_eq_type _ (der_eq_etaP _ _ _ _ _ _ $dA $dx $dy _) ↪
     der_path $dA $dx $dy
with inv_eq_t1 $dΓ (der_eq_etaP $Γ $l $A $t $x $y $dA $dx $dy $dt) ↪
     der_type_conv (der_lamP $dA (der_appP (IShift1 $A) (IShift $t) (IShift $x) (IShift $y) (itvar db0)
                                           (der_Ishift1 $dΓ $dA) (der_Ishift0 $dΓ $dx) (der_Ishift0 $dΓ $dy)
                                           (der_Ishift0 $dΓ $dt) (der_I_var dble_db0)))
                   (der_eq_cong_path $Γ $l $A $A (tappP $t it0) $x (tappP $t it1) $y
                                     (der_eq_refl (PushI $Γ) (lsuc $l) $A (tuniv $l) $dA)
                                     (der_eq_appP_zero $Γ $l $A $t $x $y $dA $dx $dy $dt)
                                     (der_eq_appP_one $Γ $l $A $t $x $y $dA $dx $dy $dt)
                                     (der_appP $A $t $x $y it0 $dA $dx $dy $dt der_I_0) $dx
                                     (der_appP $A $t $x $y it1 $dA $dx $dy $dt der_I_1) $dy)
with inv_eq_t2 _ (der_eq_etaP _ _ _ _ _ _ _ _ _ $dt) ↪
     $dt
with inv_eq_type $dΓ (der_eq_appP_zero _ _ _ _ _ _ $dA _ _ _) ↪
     Isubstitution $dΓ $dA der_I_0
with inv_eq_t1 _ (der_eq_appP_zero _ _ $A $t $x $y $dA $dx $dy $dt) ↪
     (der_appP $A $t $x $y it0 $dA $dx $dy $dt der_I_0)
with inv_eq_t2 _ (der_eq_appP_zero _ _ _ _ _ _ _ $dx _ _) ↪
     $dx
with inv_eq_type $dΓ (der_eq_appP_one _ _ _ _ _ _ $dA _ _ _) ↪
     Isubstitution $dΓ $dA der_I_1
with inv_eq_t1 _ (der_eq_appP_one _ _ $A $t $x $y $dA $dx $dy $dt) ↪
     (der_appP $A $t $x $y it1 $dA $dx $dy $dt der_I_1)
with inv_eq_t2 _ (der_eq_appP_one _ _ _ _ _ _ _ _ $dy _) ↪
     $dy
with inv_eq_type _ (der_eq_sys_left _ _ _ _ _ _ _ $dA _ _ _ _ _ _) ↪
     $dA
with inv_eq_t1 _ (der_eq_sys_left _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq_uv $d1f) ↪
     der_sys $dA $df $dg $du $dv (der_isOne_max_intro_left _ _ _ $d1f) $deq_uv
with inv_eq_t2 $dΓ (der_eq_sys_left _ _ _ _ _ _ _ _ $df _ $du _ _ $d1f) ↪
     Fsubstitution $dΓ $du $df $d1f
with inv_eq_type _ (der_eq_sys_right _ _ _ _ _ _ _ $dA _ _ _ _ _ _) ↪
     $dA
with inv_eq_t1 _ (der_eq_sys_right _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq_uv $d1g) ↪
     der_sys $dA $df $dg $du $dv (der_isOne_max_intro_right _ _ _ $d1g) $deq_uv
with inv_eq_t2 $dΓ (der_eq_sys_right _ _ _ _ _ _ _ _ _ $dg _ $dv _ $d1g) ↪
     Fsubstitution $dΓ $dv $dg $d1g
with inv_eq_type $dΓ (der_eq_transp _ _ _ _ _ $dA _ _ _ _) ↪
     Isubstitution $dΓ $dA der_I_1
with inv_eq_t1 _ (der_eq_transp _ _ _ _ _ $dA $df $du $deq_A _) ↪
     der_transp $dA $df $du $deq_A
with inv_eq_t2 $dΓ (der_eq_transp $Γ $l $A $f _ _ $df $du $deq_A $d1f) ↪
     der_type_conv $du (der_eq_sym $Γ (lsuc $l) (applyI1 $A it1) (applyI1 $A it0) (tuniv $l)
                                   (Isubstitution_eq $dΓ (Fsubstitution_eq (pushΓI $dΓ) $deq_A
                                                                           (der_Ishift0F $dΓ $df)
                                                                           (der_isOne_weakI $Γ $f $d1f)) der_I_1))
with inv_eq_type $dΓ (der_eq_transp_pi _ _ _ _ _ _ _ _ $dA $dB _ _ _ _ $dv) ↪
     substitution $dΓ (Isubstitution1 $dΓ $dA $dB der_I_1) $dv
with inv_eq_t1 $dΓ (der_eq_transp_pi $Γ $l $l' $A $B $f $u $v $dA $dB $df $deq_A $deq_B $du $dv) ↪
     der_app (applyI1 $A it1) (ttransp (tpi $A $B) $f $u) $v (applyI1 $B it1) (Isubstitution $dΓ $dA der_I_1)
             (Isubstitution1 $dΓ $dA $dB der_I_1)
             (der_transp (der_pi $dA $dB) $df $du
                         (der_eq_cong_pi
                             (PushF (IShiftF $f) (PushI $Γ)) $l $l' $A (IShift (applyI1 $A it0))
                             $B (IShift (applyI1 $B it0)) $deq_A $deq_B
                             (der_weakF1 (pushΓI $dΓ) $dA $dB (der_Ishift0F $dΓ $df))
                             (der_weakF1 (pushΓI $dΓ) (der_Ishift0 $dΓ (Isubstitution $dΓ $dA der_I_0))
                                         (der_Ishift_context $dΓ (Isubstitution $dΓ $dA der_I_0)
                                                             (der_Ishift0 (pushΓ (Isubstitution $dΓ $dA der_I_0) $dΓ)
                                                                          (Isubstitution1 $dΓ $dA $dB der_I_0)))
                                                     (der_Ishift0F $dΓ $df)))) $dv
with inv_eq_t2 $dΓ (der_eq_transp_pi $Γ $l $l' $A $B $f $u $v $dA $dB $df $deq_A $deq_B $du $dv) ↪
     TYPE
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
// rule inv_teq_sort _   (der_prop_type_eq _ _ _ _ _ $dA _    _   ) ↪ $dA
// with inv_teq_t1   _   (der_prop_type_eq _ _ _ _ _ _   $da1 _   ) ↪ $da1
// with inv_teq_t2   _   (der_prop_type_eq _ _ _ _ _ _   _    $da2) ↪ $da2
// with inv_teq_sort $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_sort $dΓ $du
// with inv_teq_t1   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t1   $dΓ $du
// with inv_teq_t2   $dΓ (der_type_conv _ (teq _ _ _) _ _ _ $du _) ↪ inv_teq_t2   $dΓ $du
// ;
