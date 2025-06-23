require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;
require open ctt.Lemmas;
require open ctt.Inversions;

// Pair of contexts with equalities
// Extensional equivalent of PContext
constant symbol EqContext : TYPE;
symbol ec_to_ctx1 : EqContext → Context;
symbol ec_to_ctx2 : EqContext → Context;
symbol ec_to_dctx1 (ec : EqContext) : der_context (ec_to_ctx1 ec);
symbol ec_to_dctx2 (ec : EqContext) : der_context (ec_to_ctx2 ec);
symbol ec_get1 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id)
                                                     (tuniv (getS (ec_to_ctx1 ec) id))
                                                     (lsuc (getS (ec_to_ctx1 ec) id));
symbol ec_get2 (ec : EqContext) (id : DBId) : der_eq (getΓ (ec_to_ctx2 ec) id)
                                                     (get (ec_to_ctx1 ec) id)
                                                     (get (ec_to_ctx2 ec) id)
                                                     (tuniv (getS (ec_to_ctx1 ec) id))
                                                     (lsuc (getS (ec_to_ctx1 ec) id));
constant symbol EC0 [Γ : Context] : der_context Γ → EqContext;
constant symbol ECPush [s : Lev] [T1 T2 : Term]
                       (ec : EqContext)
                       : der (ec_to_ctx1 ec) T1 (tuniv s) (lsuc s)
                       → der (ec_to_ctx2 ec) T2 (tuniv s) (lsuc s)
                       → der_eq (ec_to_ctx1 ec) T1 T2 (tuniv s) (lsuc s)
                       → EqContext;
constant symbol ECI (ec: EqContext) : EqContext;
constant symbol ECF [f1 f2 : FTerm] (ec : EqContext) :
  der_F (ec_to_ctx1 ec) f1 → der_F (ec_to_ctx2 ec) f2 → der_eq_F (ec_to_ctx1 ec) f1 f2 → EqContext;
rule ec_to_ctx1 (@EC0 $Γ _) ↪ $Γ
with ec_to_ctx1 (@ECPush $s $T1 _ $ec _ _ _) ↪ Push $T1 $s (ec_to_ctx1 $ec)
with ec_to_ctx1 (ECI $ec) ↪ PushI (ec_to_ctx1 $ec)
with ec_to_ctx1 (@ECF $f1 _ $ec _ _ _) ↪ PushF $f1 (ec_to_ctx1 $ec)
with ec_to_ctx2 (@EC0 $Γ _) ↪ $Γ
with ec_to_ctx2 (@ECPush $s _ $T2 $ec _ _ _) ↪ Push $T2 $s (ec_to_ctx2 $ec)
with ec_to_ctx2 (ECI $ec) ↪ PushI (ec_to_ctx2 $ec)
with ec_to_ctx2 (@ECF _ $f2 $ec _ _ _) ↪ PushF $f2 (ec_to_ctx2 $ec)
// getS and shiftΓ have the same values (syntactically) on equal contexts
with getS (ec_to_ctx2 $ec) $id ↪ getS (ec_to_ctx1 $ec) $id
with shiftΓ (ec_to_ctx2 $ec) $id $t ↪ shiftΓ (ec_to_ctx1 $ec) $id $t;
rule ec_to_dctx1 (EC0 $dΓ) ↪ $dΓ
with ec_to_dctx1 (ECPush $ec $d1 _ _) ↪ pushΓ $d1 (ec_to_dctx1 $ec)
with ec_to_dctx1 (ECI $ec) ↪ pushΓI (ec_to_dctx1 $ec)
with ec_to_dctx1 (ECF $ec $d1 _ _) ↪ pushΓF $d1 (ec_to_dctx1 $ec)
with ec_to_dctx2 (EC0 $dΓ) ↪ $dΓ
with ec_to_dctx2 (ECPush $ec _ $d2 _) ↪ pushΓ $d2 (ec_to_dctx2 $ec)
with ec_to_dctx2 (ECI $ec) ↪ pushΓI (ec_to_dctx2 $ec)
with ec_to_dctx2 (ECF $ec _ $d2 _) ↪ pushΓF $d2 (ec_to_dctx2 $ec);

// Convert in the context
symbol convert_der [s : Lev] [t A : Term] (ec : EqContext)
                   : der (ec_to_ctx1 ec) t A s → der (ec_to_ctx2 ec) t A s;
symbol convert_der_eq [s : Lev] [t1 t2 A : Term] (ec : EqContext)
                      : der_eq (ec_to_ctx1 ec) t1 t2 A s → der_eq (ec_to_ctx2 ec) t1 t2 A s;
symbol convert_der_I [t : ITerm] (ec : EqContext)
                     : der_I (ec_to_ctx1 ec) t → der_I (ec_to_ctx2 ec) t;
symbol convert_der_eq_I [t1 t2 : ITerm] (ec : EqContext)
                        : der_eq_I (ec_to_ctx1 ec) t1 t2 → der_eq_I (ec_to_ctx2 ec) t1 t2;
symbol convert_der_F [t : FTerm] (ec : EqContext)
                     : der_F (ec_to_ctx1 ec) t → der_F (ec_to_ctx2 ec) t;
symbol convert_der_eq_F [t1 t2 : FTerm] (ec : EqContext)
                        : der_eq_F (ec_to_ctx1 ec) t1 t2 → der_eq_F (ec_to_ctx2 ec) t1 t2;
symbol convert_der_isOne [t : FTerm] (ec : EqContext)
                         : der_isOne (ec_to_ctx1 ec) t → der_isOne (ec_to_ctx2 ec) t;
symbol convert'_der [s : Lev] [t A : Term] (ec : EqContext)
                    : der (ec_to_ctx2 ec) t A s → der (ec_to_ctx1 ec) t A s;
symbol convert'_der_eq [s : Lev] [t1 t2 A : Term] (ec : EqContext)
                       : der_eq (ec_to_ctx2 ec) t1 t2 A s → der_eq (ec_to_ctx1 ec) t1 t2 A s;
symbol convert'_der_I [t : ITerm] (ec : EqContext)
                      : der_I (ec_to_ctx2 ec) t → der_I (ec_to_ctx1 ec) t;
symbol convert'_der_eq_I [t1 t2 : ITerm] (ec : EqContext)
                         : der_eq_I (ec_to_ctx2 ec) t1 t2 → der_eq_I (ec_to_ctx1 ec) t1 t2;
symbol convert'_der_F [t : FTerm] (ec : EqContext)
                      : der_F (ec_to_ctx2 ec) t → der_F (ec_to_ctx1 ec) t;
symbol convert'_der_eq_F [t1 t2 : FTerm] (ec : EqContext)
                         : der_eq_F (ec_to_ctx2 ec) t1 t2 → der_eq_F (ec_to_ctx1 ec) t1 t2;
symbol convert'_der_isOne [t : FTerm] (ec : EqContext)
                          : der_isOne (ec_to_ctx2 ec) t → der_isOne (ec_to_ctx1 ec) t;

rule ec_get1 (EC0 $dΓ) $id ↪ der_eq_refl _ _ _ _ (der_getΓ $id $dΓ)
with ec_get1 (ECPush _ _ _ $deq) db0 ↪ $deq
with ec_get1 (ECPush $ec _ _ _) (dbsucc $id) ↪ ec_get1 $ec $id
with ec_get1 (ECI $ec) $id ↪ ec_get1 $ec $id
with ec_get1 (ECF $ec _ _ _) $id ↪ ec_get1 $ec $id
with ec_get2 (EC0 $dΓ) $id ↪ der_eq_refl _ _ _ _ (der_getΓ $id $dΓ)
with ec_get2 (ECPush $ec _ _ $deq) db0 ↪ convert_der_eq $ec $deq
with ec_get2 (ECPush $ec _ _ _) (dbsucc $id) ↪ ec_get2 $ec $id
with ec_get2 (ECI $ec) $id ↪ ec_get2 $ec $id
with ec_get2 (ECF $ec _ _ _) $id ↪ ec_get2 $ec $id ;

symbol pushEC [s : Lev] [A : Term]
              (ec : EqContext) (d : der (ec_to_ctx1 ec) A (tuniv s) (lsuc s))
              : EqContext ≔
  ECPush ec d (convert_der ec d) (der_eq_refl _ _ _ _ d);
symbol pushFEC [f : FTerm]
               (ec : EqContext) (d : der_F (ec_to_ctx1 ec) f)
               : EqContext ≔
  ECF ec d (convert_der_F ec d) (der_eq_F_refl _ _ d);
symbol pushEC' [s : Lev] [A : Term]
               (ec : EqContext) (d : der (ec_to_ctx2 ec) A (tuniv s) (lsuc s))
               : EqContext ≔
  ECPush ec (convert'_der ec d) d (der_eq_refl _ _ _ _ (convert'_der ec d));
symbol pushFEC' [f : FTerm]
                (ec : EqContext) (d : der_F (ec_to_ctx2 ec) f)
                : EqContext ≔
  ECF ec (convert'_der_F ec d) d (der_eq_F_refl _ _ (convert'_der_F ec d));

symbol ec_len (ec : EqContext) : DBEq (len (ec_to_ctx1 ec)) (len (ec_to_ctx2 ec));
symbol ec_lenI (ec : EqContext) : DBEq (lenI (ec_to_ctx1 ec)) (lenI (ec_to_ctx2 ec));

rule ec_len (EC0 _) ↪ DBRefl _
with ec_len (ECPush $ec _ _ _) ↪ dbcong dbsucc (ec_len $ec)
with ec_len (ECI $ec) ↪ ec_len $ec
with ec_len (ECF $ec _ _ _) ↪ ec_len $ec
with ec_lenI (EC0 _) ↪ DBRefl _
with ec_lenI (ECPush $ec _ _ _) ↪ ec_lenI $ec
with ec_lenI (ECI $ec) ↪ dbcong dbsucc (ec_lenI $ec)
with ec_lenI (ECF $ec _ _ _) ↪ ec_lenI $ec;

symbol ec_len_12 (ec : EqContext) [i : DBId] : DBLe i (len (ec_to_ctx1 ec)) → DBLe i (len (ec_to_ctx2 ec)) ≔
  λ h, dble_eq_right _ _ _ (ec_len ec) h;
symbol ec_len_21 (ec : EqContext) [i : DBId] : DBLe i (len (ec_to_ctx2 ec)) → DBLe i (len (ec_to_ctx1 ec)) ≔
  λ h, dble_eq_right _ _ _ (dbeq_inv (ec_len ec)) h;
symbol ec_lenI_12 (ec : EqContext) [i : DBId] : DBLe i (lenI (ec_to_ctx1 ec)) → DBLe i (lenI (ec_to_ctx2 ec)) ≔
  λ h, dble_eq_right _ _ _ (ec_lenI ec) h;
symbol ec_lenI_21 (ec : EqContext) [i : DBId] : DBLe i (lenI (ec_to_ctx2 ec)) → DBLe i (lenI (ec_to_ctx1 ec)) ≔
  λ h, dble_eq_right _ _ _ (dbeq_inv (ec_lenI ec)) h;

rule convert_der $ec (der_empty_face $done) ↪ der_empty_face (convert_der_isOne $ec $done)
with convert_der $ec (der_union_face $df $dg $dtf $dtg $done) ↪
     der_union_face (convert_der_F $ec $df) (convert_der_F $ec $dg)
                    (convert_der (pushFEC $ec $df) $dtf) (convert_der (pushFEC $ec $dg) $dtg)
                    (convert_der_isOne $ec $done)
with convert_der $ec (@der_var _ $id $h) ↪
     der_type_conv (der_var (ec_len_12 $ec $h))
                   (der_eq_sym _ _ _ _ _ (der_eq_shift $id (ec_to_dctx2 $ec) (ec_get2 $ec $id)))
with convert_der _ (der_univ) ↪ der_univ
with convert_der $ec (der_pi $dA $dB) ↪
     der_pi (convert_der $ec $dA) (convert_der (pushEC $ec $dA) $dB)
with convert_der $ec (der_abs $dA $dB $dt) ↪
     der_abs (convert_der $ec $dA)
             (convert_der (pushEC $ec $dA) $dB)
             (convert_der (pushEC $ec $dA) $dt)
with convert_der $ec (der_app $A $t $u $B $dA $dB $dt $du) ↪
     der_app $A $t $u $B
             (convert_der $ec $dA)
             (convert_der (pushEC $ec $dA) $dB)
             (convert_der $ec $dt)
             (convert_der $ec $du)
with convert_der $ec (der_type_conv $du $deq) ↪
     der_type_conv (convert_der $ec $du)
                   (convert_der_eq $ec $deq)
with convert_der _ (der_nat) ↪ der_nat
with convert_der _ (der_zero) ↪ der_zero
with convert_der $ec (der_suc $d) ↪ der_suc (convert_der $ec $d)
with convert_der $ec (der_rec $dP $dz $dH $dn) ↪
     der_rec (convert_der $ec $dP) (convert_der $ec $dz)
             (convert_der $ec $dH) (convert_der $ec $dn)
with convert_der $ec (der_sig $dA $dB) ↪
     der_sig  (convert_der $ec $dA) (convert_der (pushEC $ec $dA) $dB)
with convert_der $ec (der_pair $dA $dB $du $dv) ↪
     der_pair  (convert_der $ec $dA)
               (convert_der (pushEC $ec $dA) $dB)
               (convert_der $ec $du)
               (convert_der $ec $dv)
with convert_der $ec (der_p1 $dA $dB $dp) ↪
     der_p1 (convert_der $ec $dA)
            (convert_der (pushEC $ec $dA) $dB)
            (convert_der $ec $dp)
with convert_der $ec (der_p2 $dA $dB $dp) ↪
     der_p2 (convert_der $ec $dA)
            (convert_der (pushEC $ec $dA) $dB)
            (convert_der $ec $dp)
with convert_der $ec (der_sum $dA $dB) ↪
     der_sum  (convert_der $ec $dA)
              (convert_der $ec $dB)
with convert_der $ec (der_injl $dA $dB $dp) ↪
     der_injl (convert_der $ec $dA)
              (convert_der $ec $dB)
              (convert_der $ec $dp)
with convert_der $ec (der_injr $dA $dB $dp) ↪
     der_injr (convert_der $ec $dA)
              (convert_der $ec $dB)
              (convert_der $ec $dp)
with convert_der $ec (der_case $dA $dB $dP $dHa $dHb $dx) ↪
     der_case (convert_der $ec $dA) (convert_der $ec $dB)
              (convert_der $ec $dP) (convert_der $ec $dHa)
              (convert_der $ec $dHb) (convert_der $ec $dx)
with convert_der $ec (der_path $dA $du $dv) ↪
     der_path (convert_der (ECI $ec) $dA) (convert_der $ec $du) (convert_der $ec $dv)
with convert_der $ec (der_lamP $dA $dt) ↪
     der_lamP (convert_der (ECI $ec) $dA) (convert_der (ECI $ec) $dt)
with convert_der $ec (der_appP $A $t $x $y $i $dA $dx $dy $dt $di) ↪
     der_appP $A $t $x $y $i
             (convert_der (ECI $ec) $dA) (convert_der $ec $dx) (convert_der $ec $dy)
             (convert_der $ec $dt) (convert_der_I $ec $di)
with convert_der $ec (der_sys $dA $df $dg $du $dv $done $deq) ↪
     der_sys (convert_der $ec $dA) (convert_der_F $ec $df) (convert_der_F $ec $dg)
             (convert_der (pushFEC $ec $df) $du) (convert_der (pushFEC $ec $dg) $dv)
             (convert_der_isOne $ec $done)
             (convert_der_eq (pushFEC $ec (der_F_min $df $dg)) $deq)
with convert_der $ec (der_sys_empty $dA $done) ↪
     der_sys_empty (convert_der $ec $dA) (convert_der_isOne $ec $done)
with convert_der $ec (der_transp $dA $df $du $deq)↪
     der_transp (convert_der (ECI $ec) $dA) (convert_der_F $ec $df)
                (convert_der $ec $du) (convert_der_eq (pushFEC (ECI $ec) (der_Ishift0F (ec_to_dctx1 $ec) $df)) $deq)
with convert_der $ec (der_hcomp $dA $df $du $du0 $deq) ↪
     der_hcomp (convert_der $ec $dA) (convert_der_F $ec $df)
               (convert_der (pushFEC (ECI $ec) (der_Ishift0F (ec_to_dctx1 $ec) $df)) $du)
               (convert_der $ec $du0) (convert_der_eq (pushFEC $ec $df) $deq)
with convert_der_eq $ec (der_eq_refl _ _ _ _ $du) ↪
     der_eq_refl _ _ _ _ (convert_der $ec $du)
with convert_der_eq $ec (der_eq_trans _ $s $u $v $w $A $duv $dvw) ↪
     der_eq_trans _ $s $u $v $w $A
                  (convert_der_eq $ec $duv)
                  (convert_der_eq $ec $dvw)
with convert_der_eq $ec (der_eq_sym _ $s $u $v $A $duv) ↪
     der_eq_sym _ $s $u $v $A (convert_der_eq $ec $duv)
with convert_der_eq $ec (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du) ↪
     der_eq_beta _ $s $s' $u $A $t $B
                 (convert_der $ec $dA)
                 (convert_der (pushEC $ec $dA) $dB)
                 (convert_der (pushEC $ec $dA) $dt)
                 (convert_der $ec $du)
with convert_der_eq $ec (der_eq_eta _ $s $s' $A $f $B $dA $dB $df) ↪
     der_eq_eta _ $s $s' $A $f $B
                (convert_der $ec $dA)
                (convert_der (pushEC $ec $dA) $dB)
                (convert_der $ec $df)
with convert_der_eq $ec (der_eq_rec_zero _ $s _ _ _ _ $dP $dz $dH) ↪
     der_eq_rec_zero _ $s _ _ _ _
                     (convert_der $ec $dP) (convert_der $ec $dz)
                     (convert_der $ec $dH)
with convert_der_eq $ec (der_eq_rec_suc _ _ _ _ _ _ _ $dP $dz $dH $dn) ↪
     der_eq_rec_suc _ _ _ _ _ _ _
                     (convert_der $ec $dP) (convert_der $ec $dz)
                     (convert_der $ec $dH) (convert_der $ec $dn)
with convert_der_eq $ec (der_eq_p1 _ $s $s' $u $A $v $B $dA $du $dB $dv) ↪
     der_eq_p1 _ $s $s' $u $A $v $B
               (convert_der $ec $dA)
               (convert_der $ec $du)
               (convert_der (pushEC $ec $dA) $dB)
               (convert_der $ec $dv)
with convert_der_eq $ec (der_eq_p2 _ $s $s' $u $A $v $B $dA $du $dB $dv) ↪
     der_eq_p2 _ $s $s' $u $A $v $B
               (convert_der $ec $dA)
               (convert_der $ec $du)
               (convert_der (pushEC $ec $dA) $dB)
               (convert_der $ec $dv)

with convert_der_eq $ec (der_eq_pair _ _ _ _ _ _ _ $dA $dB $dt $du $deq1 $deq2) ↪
     der_eq_pair _ _ _ _ _ _ _
                 (convert_der $ec $dA) (convert_der (pushEC $ec $dA) $dB)
                 (convert_der $ec $dt) (convert_der $ec $du)
                 (convert_der_eq $ec $deq1) (convert_der_eq $ec $deq2)
with convert_der_eq $ec (der_eq_case_left _ _ _ _ _ _ _ _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_eq_case_left _ _ _ _ _ _ _ _ _ _
                     (convert_der $ec $dA) (convert_der $ec $dB)
                     (convert_der $ec $dP) (convert_der $ec $dHa)
                     (convert_der $ec $dHb) (convert_der $ec $dx)
with convert_der_eq $ec (der_eq_case_right _ _ _ _ _ _ _ _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_eq_case_right _ _ _ _ _ _ _ _ _ _
                     (convert_der $ec $dA) (convert_der $ec $dB)
                     (convert_der $ec $dP) (convert_der $ec $dHa)
                     (convert_der $ec $dHb) (convert_der $ec $dx)
with convert_der_eq $ec (der_eq_betaP _ $s $A $t $i $dA $dt $di) ↪
     der_eq_betaP _ $s $A $t $i
                 (convert_der (ECI $ec) $dA)
                 (convert_der (ECI $ec) $dt)
                 (convert_der_I $ec $di)
with convert_der_eq $ec (der_eq_etaP _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_etaP _ $s $A $t $x $y
                 (convert_der (ECI $ec) $dA) (convert_der $ec $dx)
                 (convert_der $ec $dy) (convert_der $ec $dt)
with convert_der_eq $ec (der_eq_appP_zero _ _ _ _ _ _ $dA $dx $dy $dt) ↪
     der_eq_appP_zero _ _ _ _ _ _
                 (convert_der (ECI $ec) $dA) (convert_der $ec $dx)
                 (convert_der $ec $dy) (convert_der $ec $dt)
with convert_der_eq $ec (der_eq_appP_one _ _ _ _ _ _ $dA $dx $dy $dt) ↪
     der_eq_appP_one _ _ _ _ _ _
                 (convert_der (ECI $ec) $dA) (convert_der $ec $dx)
                 (convert_der $ec $dy) (convert_der $ec $dt)
with convert_der_eq $ec (der_eq_sys_left _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq $done) ↪
     der_eq_sys_left _ _ _ _ _ _ _
                 (convert_der $ec $dA) (convert_der_F $ec $df)
                 (convert_der_F $ec $dg) (convert_der (pushFEC $ec $df) $du)
                 (convert_der (pushFEC $ec $dg) $dv) (convert_der_eq (pushFEC $ec (der_F_min $df $dg)) $deq)
                 (convert_der_isOne $ec $done)
with convert_der_eq $ec (der_eq_sys_right _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq $done) ↪
     der_eq_sys_right _ _ _ _ _ _ _
                 (convert_der $ec $dA) (convert_der_F $ec $df)
                 (convert_der_F $ec $dg) (convert_der (pushFEC $ec $df) $du)
                 (convert_der (pushFEC $ec $dg) $dv) (convert_der_eq (pushFEC $ec (der_F_min $df $dg)) $deq)
                 (convert_der_isOne $ec $done)
// with convert_der_eq $ec (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
//   ↪ der_eq_conversion _ $s $t1 $t2 $T1 $T2
//                        (convert_der_eq $ec $deqt)
//                        (convert_der_eq $ec $deqT)
// with convert_der_eq $ec (der_eq_lift _ $s $e $u $v $A $de)
//   ↪ der_eq_lift _ $s $e $u $v $A
//                  (convert_der $ec $de)
// with convert_der_eq $ec (der_eq_cong_tfun _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
//   ↪ der_eq_cong_tfun _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
// with convert_der_eq $ec (der_eq_cong_tabs _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
//   ↪ der_eq_cong_tabs _ _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqt)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dt1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dt2)
// with convert_der_eq $ec (der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
//   ↪ der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der_eq $ec $deqf)
//        (convert_der_eq $ec $deqa)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
//        (convert_der $ec $df1) (convert_der $ec $df2)
//        (convert_der $ec $da1) (convert_der $ec $da2)
// with convert_der_eq $ec (der_eq_cong_tsum _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
//   ↪ der_eq_cong_tsum _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
// with convert_der_eq $ec (der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
//   ↪ der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der_eq $ec $deqa)
//        (convert_der_eq $ec $deqb)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
//        (convert_der $ec $da1) (convert_der $ec $da2)
//        (convert_der $ec $db1) (convert_der $ec $db2)
// with convert_der_eq $ec (der_eq_cong_π1 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
//   ↪ der_eq_cong_π1 _ _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der_eq $ec $deqp)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
//        (convert_der $ec $dp1) (convert_der $ec $dp2)
// with convert_der_eq $ec (der_eq_cong_π2 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
//   ↪ der_eq_cong_π2 _ _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $deqB)
//        (convert_der_eq $ec $deqp)
//        (convert_der (pushEC $ec (inv_eq_t1 (ec_to_dctx1 $ec) $deqA)) $dB1)
//        (convert_der (pushEC $ec (inv_eq_t2 (ec_to_dctx1 $ec) $deqA)) $dB2)
//        (convert_der $ec $dp1) (convert_der $ec $dp2)
// with convert_der_eq $ec (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
//   ↪ der_eq_cong_teq _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq $ec $deqa)
//        (convert_der_eq $ec $deqb)
//        (convert_der $ec $da1) (convert_der $ec $da2)
//        (convert_der $ec $db1) (convert_der $ec $db2)
// with convert_der_eq $ec (der_eq_cong_trefl _ _ _ _ _ _ $deqA $deqa $da1 $da2)
//   ↪ der_eq_cong_trefl _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq $ec $deqa)
//        (convert_der $ec $da1) (convert_der $ec $da2)
// with convert_der_eq $ec (der_eq_cong_tK _ _ _ _ _ _ _ _ $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
//   ↪ der_eq_cong_tK _ _ _ _ _ _ _ _
//        (convert_der_eq $ec $deqA)
//        (convert_der_eq $ec $deqa)
//        (convert_der_eq $ec $deqp)
//        (convert_der $ec $da1) (convert_der $ec $da2)
//        (convert_der $ec $dp1) (convert_der $ec $dp2)
// ;
;

rule convert'_der $ec (der_empty_face $done) ↪ der_empty_face (convert'_der_isOne $ec $done)
with convert'_der _ (der_univ) ↪ der_univ
// rule convert'_der _ (der_sort _ $s)
//   ↪ der_sort _ $s
// with convert'_der $ec (der_prod _ $s $s' $A $B $dA $dB)
//   ↪ der_prod _ $s $s' $A $B
//               (convert'_der $ec $dA)
//               (convert'_der (pushEC' $ec $dA) $dB)
// with convert'_der $ec (der_sigma _ $s $s' $A $B $dA $dB)
//   ↪ der_sigma _ $s $s' $A $B
//                (convert'_der $ec $dA)
//                (convert'_der (pushEC' $ec $dA) $dB)
// with convert'_der $ec (der_prop_type_eq _ $s $A $u $v $dA $du $dv)
//   ↪ der_prop_type_eq _ $s $A $u $v
//                       (convert'_der $ec $dA)
//                       (convert'_der $ec $du)
//                       (convert'_der $ec $dv)
// with convert'_der $ec (der_var _ $id)
//   ↪ der_type_conv _ _ _ _ _
//                    (der_var _ $id)
//                    (der_eq_shift $id (ec_to_dctx1 $ec) (ec_get1 $ec $id))
// with convert'_der $ec (der_type_conv _ $u $A $B $s $du $deq)
//   ↪ der_type_conv _ $u $A $B $s
//                    (convert'_der $ec $du)
//                    (convert'_der_eq $ec $deq)
// with convert'_der $ec (der_abs _ $s $s' $A $t $B $dA $dB $dt)
//   ↪ der_abs _ $s $s' $A $t $B
//              (convert'_der $ec $dA)
//              (convert'_der (pushEC' $ec $dA) $dB)
//              (convert'_der (pushEC' $ec $dA) $dt)
// with convert'_der $ec (der_app _ $s $s' $A $t $u $B $dA $dB $dt $du)
//   ↪ der_app _ $s $s' $A $t $u $B
//              (convert'_der $ec $dA)
//              (convert'_der (pushEC' $ec $dA) $dB)
//              (convert'_der $ec $dt)
//              (convert'_der $ec $du)
// with convert'_der $ec (der_pair _ $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ der_pair _ $s $s' $u $A $v $B
//               (convert'_der $ec $dA)
//               (convert'_der $ec $du)
//               (convert'_der (pushEC' $ec $dA) $dB)
//               (convert'_der $ec $dv)
// with convert'_der $ec (der_π1 _ $s $s' $p $A $B $dA $dB $dp)
//   ↪ der_π1 _ $s $s' $p $A $B
//             (convert'_der $ec $dA)
//             (convert'_der (pushEC' $ec $dA) $dB)
//             (convert'_der $ec $dp)
// with convert'_der $ec (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
//   ↪ der_π2 _ $s $s' $p $A $B
//             (convert'_der $ec $dA)
//             (convert'_der (pushEC' $ec $dA) $dB)
//             (convert'_der $ec $dp)
// with convert'_der $ec (der_refl _ $s $u $A $dA $du)
//   ↪ der_refl _ $s $u $A
//               (convert'_der $ec $dA)
//               (convert'_der $ec $du)
// with convert'_der $ec (der_K _ $s $A $a $p $dA $da $dp)
//   ↪ der_K _ $s $A $a $p
//            (convert'_der $ec $dA)
//            (convert'_der $ec $da)
//            (convert'_der $ec $dp)
// with convert'_der_eq $ec (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
//   ↪ der_eq_beta _ $s $s' $u $A $t $B
//                  (convert'_der $ec $dA)
//                  (convert'_der (pushEC' $ec $dA) $dB)
//                  (convert'_der (pushEC' $ec $dA) $dt)
//                  (convert'_der $ec $du)
// with convert'_der_eq $ec (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
//   ↪ der_eq_eta _ $s $s' $A $f $B
//                 (convert'_der $ec $dA)
//                 (convert'_der (pushEC' $ec $dA) $dB)
//                 (convert'_der $ec $df)
// with convert'_der_eq $ec (der_eq_π1 _ $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ der_eq_π1 _ $s $s' $u $A $v $B
//                (convert'_der $ec $dA)
//                (convert'_der $ec $du)
//                (convert'_der (pushEC' $ec $dA) $dB)
//                (convert'_der $ec $dv)
// with convert'_der_eq $ec (der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
//   ↪ der_eq_π2 _ $s $s' $u $A $v $B
//                (convert'_der $ec $dA)
//                (convert'_der $ec $du)
//                (convert'_der (pushEC' $ec $dA) $dB)
//                (convert'_der $ec $dv)
// with convert'_der_eq $ec (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
//   ↪ der_eq_conversion _ $s $t1 $t2 $T1 $T2
//                        (convert'_der_eq $ec $deqt)
//                        (convert'_der_eq $ec $deqT)
// with convert'_der_eq $ec (der_eq_lift _ $s $e $u $v $A $de)
//   ↪ der_eq_lift _ $s $e $u $v $A
//                  (convert'_der $ec $de)
// with convert'_der_eq $ec (der_eq_refl _ $s $u $A $du)
//   ↪ der_eq_refl _ $s $u $A (convert'_der $ec $du)
// with convert'_der_eq $ec (der_eq_trans _ $s $u $v $w $A $duv $dvw)
//   ↪ der_eq_trans _ $s $u $v $w $A
//                   (convert'_der_eq $ec $duv)
//                   (convert'_der_eq $ec $dvw)
// with convert'_der_eq $ec (der_eq_symm _ $s $u $v $A $duv)
//   ↪ der_eq_symm _ $s $u $v $A (convert'_der_eq $ec $duv)
// with convert'_der_eq $ec (der_eq_cong_tfun _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
//   ↪ der_eq_cong_tfun _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
// with convert'_der_eq $ec (der_eq_cong_tabs _ _ _ _ _ _ _ _ _ $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
//   ↪ der_eq_cong_tabs _ _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqt)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dt1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dt2)
// with convert'_der_eq $ec (der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
//   ↪ der_eq_cong_tapp _ _ _ _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der_eq $ec $deqf)
//        (convert'_der_eq $ec $deqa)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
//        (convert'_der $ec $df1) (convert'_der $ec $df2)
//        (convert'_der $ec $da1) (convert'_der $ec $da2)
// with convert'_der_eq $ec (der_eq_cong_tsum _ _ _ _ _ _ _ $deqA $deqB $dB1 $dB2)
//   ↪ der_eq_cong_tsum _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
// with convert'_der_eq $ec (der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _ $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
//   ↪ der_eq_cong_tpair _ _ _ _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der_eq $ec $deqa)
//        (convert'_der_eq $ec $deqb)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
//        (convert'_der $ec $da1) (convert'_der $ec $da2)
//        (convert'_der $ec $db1) (convert'_der $ec $db2)
// with convert'_der_eq $ec (der_eq_cong_π1 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
//   ↪ der_eq_cong_π1 _ _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der_eq $ec $deqp)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
//        (convert'_der $ec $dp1) (convert'_der $ec $dp2)
// with convert'_der_eq $ec (der_eq_cong_π2 _ _ _ _ _ _ _ _ _ $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
//   ↪ der_eq_cong_π2 _ _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $deqB)
//        (convert'_der_eq $ec $deqp)
//        (convert'_der (pushEC' $ec (inv_eq_t1 (ec_to_dctx2 $ec) $deqA)) $dB1)
//        (convert'_der (pushEC' $ec (inv_eq_t2 (ec_to_dctx2 $ec) $deqA)) $dB2)
//        (convert'_der $ec $dp1) (convert'_der $ec $dp2)
// with convert'_der_eq $ec (der_eq_cong_teq _ _ _ _ _ _ _ _ $deqA $deqa $deqb $da1 $da2 $db1 $db2)
//   ↪ der_eq_cong_teq _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq $ec $deqa)
//        (convert'_der_eq $ec $deqb)
//        (convert'_der $ec $da1) (convert'_der $ec $da2)
//        (convert'_der $ec $db1) (convert'_der $ec $db2)
// with convert'_der_eq $ec (der_eq_cong_trefl _ _ _ _ _ _ $deqA $deqa $da1 $da2)
//   ↪ der_eq_cong_trefl _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq $ec $deqa)
//        (convert'_der $ec $da1) (convert'_der $ec $da2)
// with convert'_der_eq $ec (der_eq_cong_tK _ _ _ _ _ _ _ _ $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
//   ↪ der_eq_cong_tK _ _ _ _ _ _ _ _
//        (convert'_der_eq $ec $deqA)
//        (convert'_der_eq $ec $deqa)
//        (convert'_der_eq $ec $deqp)
//        (convert'_der $ec $da1) (convert'_der $ec $da2)
//        (convert'_der $ec $dp1) (convert'_der $ec $dp2)
;
