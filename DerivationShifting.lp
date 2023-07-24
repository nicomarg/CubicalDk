
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;
require open ctt.TermEquality;

// Exported lemmas TODO : define them
// Shifting derivation
symbol der_shift0 [Γ : Context] [t A T : Term] [l l' : Lev]
                  (_ : der Γ A (tuniv l') (lsuc l')) (_ : der_context Γ) (_ : der Γ t T l) :
  der (Push A l' Γ) (Shift t) (Shift T) l;
symbol der_Ishift0 [Γ : Context] [t T : Term] [l : Lev]
                  (_ : der_context Γ) (_ : der Γ t T l) :
  der (PushI Γ) (IShift t) (IShift T) l;
symbol der_Ishift0F [Γ : Context] [f : FTerm]
                  (_ : der_context Γ) (_ : der_F Γ f) :
  der_F (PushI Γ) (IShiftF f);
symbol der_eq_shift0 [Γ : Context] [t1 t2 A T : Term] [l l' : Lev]
                     (_ : der Γ A (tuniv l') (lsuc l')) (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) :
  der_eq (Push A l' Γ) (Shift t1) (Shift t2) (Shift T) l;
symbol der_shift1 [Γ : Context] [t A T B : Term] [l la lb : Lev]
                  (_ : der Γ A (tuniv la) (lsuc la))
                  (_ : der Γ B (tuniv lb) (lsuc lb))
                  (_ : der_context Γ)
                  (_ : der (Push A la Γ) t T l) : der (Push (Shift A) la (Push B lb Γ)) (Shift1 t) (Shift1 T) l;
symbol der_Ishift1 [Γ : Context] [t T : Term] [l: Lev]
                  (_ : der_context Γ)
                  (_ : der (PushI Γ) t T l) : der (PushI (PushI Γ)) (IShift1 t) (IShift1 T) l;

symbol der_Ishift_context [Γ : Context] [t T A : Term] [l l' : Lev]
                          (_ : der_context Γ) (_ : der Γ A (tuniv l) (lsuc l))
                          (_ : der (PushI (Push A l Γ)) t T l') : der (Push (IShift A) l (PushI Γ)) t T l';
symbol der_weakF [Γ : Context] [t T : Term] [f : FTerm] [l : Lev]
                 (_ : der_context Γ) (_ : der Γ t T l) (_ : der_F Γ f) :
  der (PushF f Γ) t T l;
symbol der_weakFF [Γ : Context] [f g : FTerm]
                 (_ : der_context Γ) (_ : der_F Γ g) (_ : der_F Γ f) :
  der_F (PushF f Γ) g;
symbol der_weakF1 [Γ : Context] [t A T : Term] [f : FTerm] [l l' : Lev]
                 (_ : der_context Γ) (_ : der Γ A (tuniv l') (lsuc l')) (_ : der (Push A l' Γ) t T l) (_ : der_F Γ f) :
  der (Push A l' (PushF f Γ)) t T l;

// Iterated shifting
symbol der_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [t T : Term] [l : Lev] (_ : der (getΓ Γ id) t T l) :
  der Γ (ShiftN id t) (ShiftN id T) l;
rule der_shift db0 (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ $d
with der_shift (dbsucc $id) (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ (der_shift $id $dΓ $d);
symbol der_eq_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [t1 t2 T : Term] [l : Lev]
                    (_ : der_eq (getΓ Γ id) t1 t2 T l) :
  der_eq Γ (ShiftN id t1) (ShiftN id t2) (ShiftN id T) l;

// Generic der_shift
constant symbol ShiftContext : Context → DBId → TYPE;
symbol sc_to_ctx [Γ : Context] [id : DBId] : ShiftContext Γ id → Context;
symbol sc_to_sctx [Γ : Context] [id : DBId] [s : Lev] [A : Term] :
  der Γ A (tuniv s) (lsuc s) → ShiftContext Γ id → Context;
symbol sc_to_dctx [Γ : Context] [id : DBId] (sc : ShiftContext Γ id) : der_context (sc_to_ctx sc);
symbol sc_to_dsctx [Γ : Context] [id : DBId] [s : Lev] [A : Term] (dA : der Γ A (tuniv s) (lsuc s))
                   (sc : ShiftContext Γ id) : der_context (sc_to_sctx dA sc);
constant symbol SC0 [Γ : Context] : der_context Γ → ShiftContext Γ db0;
constant symbol SCSucc [Γ : Context] [s : Lev] [A : Term] [id : DBId] (sc : ShiftContext Γ id) :
  der (sc_to_ctx sc) A (tuniv s) (lsuc s) → ShiftContext Γ (dbsucc id);
constant symbol SCI [Γ : Context] [id : DBId] (sc : ShiftContext Γ id) : ShiftContext Γ id;
constant symbol SCF [Γ : Context] [f : FTerm] [id : DBId] (sc : ShiftContext Γ id) :
  der_F (sc_to_ctx sc) f → ShiftContext Γ id;
rule sc_to_ctx (@SC0 $Γ _) ↪ $Γ
with sc_to_ctx (@SCSucc _ $s $A _ $sc _) ↪ Push $A $s (sc_to_ctx $sc)
with sc_to_ctx (SCI $sc) ↪ PushI (sc_to_ctx $sc)
with sc_to_ctx (@SCF _ $f _ $sc _) ↪ PushF $f (sc_to_ctx $sc)
with @sc_to_sctx _ _ $sa $A _ (@SC0 $Γ _) ↪ Push $A $sa $Γ
with sc_to_sctx $d (@SCSucc _ $s $A $id $sc _) ↪ Push (shift $id $A) $s (sc_to_sctx $d $sc)
with sc_to_sctx $d (SCI $sc) ↪ PushI (sc_to_sctx $d $sc)
with sc_to_sctx $d (@SCF _ $f _ $sc _) ↪ PushF $f (sc_to_sctx $d $sc);
rule sc_to_dctx (SC0 $dΓ) ↪ $dΓ
with sc_to_dctx (SCSucc $sc $d) ↪ der_context_Push _ _ _ $d (sc_to_dctx $sc)
with sc_to_dctx (SCI $sc) ↪ der_context_PushI _ (sc_to_dctx $sc)
with sc_to_dctx (SCF $sc $d) ↪ der_context_PushF _ _ $d (sc_to_dctx $sc);
symbol der_shift_n [Γ : Context] [sa s : Lev] [A t T : Term] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                   (d : der (sc_to_ctx sc) t T s)
                   : der (sc_to_sctx dA sc) (shift id t) (shift id T) s;
symbol der_eq_shift_n [Γ : Context] [sa s : Lev] [A T t1 t2 : Term] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                      (deq : der_eq (sc_to_ctx sc) t1 t2 T s) :
  der_eq (sc_to_sctx dA sc) (shift id t1) (shift id t2) (shift id T) s;
symbol der_I_shift_n [Γ : Context] [sa : Lev] [A : Term] [t : ITerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                   (d : der_I (sc_to_ctx sc) t)
                   : der_I (sc_to_sctx dA sc) t;
symbol der_eq_I_shift_n [Γ : Context] [sa : Lev] [A : Term] [t1 t2 : ITerm] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                      (deq : der_eq_I (sc_to_ctx sc) t1 t2) :
  der_eq_I (sc_to_sctx dA sc) t1 t2;
symbol der_F_shift_n [Γ : Context] [sa : Lev] [A : Term] [f : FTerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                   (d : der_F (sc_to_ctx sc) f)
                   : der_F (sc_to_sctx dA sc) f;
symbol der_eq_F_shift_n [Γ : Context] [sa : Lev] [A : Term] [t1 t2 : FTerm] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                      (deq : der_eq_F (sc_to_ctx sc) t1 t2) :
  der_eq_F (sc_to_sctx dA sc) t1 t2;
symbol der_isOne_shift_n [Γ : Context] [sa : Lev] [A : Term] [f : FTerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                   (d : der_isOne (sc_to_ctx sc) f)
                   : der_isOne (sc_to_sctx dA sc) f;
symbol der_context_shift_n [Γ : Context] [sa : Lev] [A : Term] (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa)) :
  der (sc_to_sctx dA sc) (tvar (dbshift id i)) (shift id (ShiftN i (get (sc_to_ctx sc) i))) (getS (sc_to_ctx sc) i);

rule sc_to_dsctx $d (SC0 $dΓ) ↪ der_context_Push _ _ _ $d $dΓ
with sc_to_dsctx $d (SCSucc $sc $dA) ↪ der_context_Push _ _ _ (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc);

symbol test [Γ : Context] [sa s : Lev] [A B u : Term] [f : FTerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa))
                   (dB : der (PushI (sc_to_ctx sc)) B (tuniv s) (lsuc s))
                   (df : der_F (sc_to_ctx sc) f)
                   (du : der (sc_to_ctx sc) u (applyI1 B it0) s)
                   (deq : der_eq (PushF (IShiftF f) (PushI (sc_to_ctx sc))) B (IShift (applyI1 B it0))
                                 (tuniv s) (lsuc s))
                   : der (sc_to_sctx dA sc) (shift id (ttransp B f u))
                         (shift id (applyI1 B it1)) s ≔
begin
  assume Γ sa s A B u f id sc dA dB df du deq;
  refine der_transp (der_shift_n id (SCI sc) dA dB) (der_F_shift_n id sc dA df)
                    (der_shift_n id sc dA du)
                    _ ;
  refine Jeq (TRefl _) (TRefl _) _
                    (der_eq_shift_n id (SCF (SCI sc) (der_Ishift0F (sc_to_dctx sc) df)) dA deq);
  refine teq_trans (aux_teq_shift_Ishift id db0 (applyI1 B it0))
                   (Jcong (λ v, IShift v) (aux_teq_Isubst_shift db0 id it0 B))
end;
print test;
// der_shift_n
rule der_shift_n $id $sc $d (der_empty_face $d1) ↪ der_empty_face (der_isOne_shift_n $id $sc $d $d1)
with der_shift_n $id $sc $d (der_union_face $df $dg $d1 $d2 $dfg) ↪
     der_union_face (der_F_shift_n $id $sc $d $df)
                    (der_F_shift_n $id $sc $d $dg)
                    (der_shift_n $id (SCF $sc $df) $d $d1)
                    (der_shift_n $id (SCF $sc $dg) $d $d2)
                    (der_isOne_shift_n $id $sc $d $dfg)
with der_shift_n $id $sc $d (@der_var _ $i _) ↪ der_context_shift_n $id $i $sc $d
with der_shift_n _   _   _  der_univ ↪ der_univ
with der_shift_n $id $sc $d (der_pi $dA $dB) ↪
     der_pi (der_shift_n $id $sc $d $dA)
            (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
with der_shift_n $id $sc $d (der_abs $dA $dB $dt) ↪
     der_abs (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
             (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dt)
with der_shift_n $id $sc $d (der_app $A $t $u $B $dA $dB $dt $du) ↪
     der_app (shift $id $A) (shift $id $t) (shift $id $u) (shift (dbsucc $id) $B)
             (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
             (der_shift_n $id $sc $d $dt) (der_shift_n $id $sc $d $du)
with der_shift_n $id $sc $d (der_type_conv $du $deq) ↪
     der_type_conv (der_shift_n $id $sc $d $du) (der_eq_shift_n $id $sc $d $deq)
with der_shift_n _   _   _  der_nat ↪ der_nat
with der_shift_n _   _   _  der_zero ↪ der_zero
with der_shift_n $id $sc $d (der_suc $du) ↪
     der_suc (der_shift_n $id $sc $d $du)
with der_shift_n $id $sc $d (der_rec $dP $dz $dH $dn) ↪
     der_rec (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dz)
             (der_shift_n $id $sc $d $dH) (der_shift_n $id $sc $d $dn)
with der_shift_n $id $sc $d (der_sig $dA $dB) ↪
     der_sig (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
with der_shift_n $id $sc $d (der_pair $dA $dB $du $dv) ↪
     der_pair (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
              (der_shift_n $id $sc $d $du) (der_shift_n $id $sc $d $dv)
with der_shift_n $id $sc $d (der_p1 $dA $dB $dp) ↪
     der_p1 (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_p2 $dA $dB $dp) ↪
     der_p2 (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_sum $dA $dB) ↪
     der_sum (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
with der_shift_n $id $sc $d (der_injl $dA $dB $dp) ↪
     der_injl (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_injr $dA $dB $dp) ↪
     der_injr (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
            (der_shift_n $id $sc $d $dp)
with der_shift_n $id $sc $d (der_case $dA $dB $dP $dHa $dHb $dx) ↪
     der_case (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
              (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dHa)
              (der_shift_n $id $sc $d $dHb) (der_shift_n $id $sc $d $dx)
with der_shift_n $id $sc $d (der_path $dA $dx $dy) ↪
     der_path (der_shift_n $id (SCI $sc) $d $dA)
              (der_shift_n $id $sc $d $dx)
              (der_shift_n $id $sc $d $dy)
with der_shift_n $id $sc $d (der_lamP $dA $dt) ↪
        der_lamP (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id (SCI $sc) $d $dt)
with der_shift_n $id $sc $d (der_appP _ _ _ _ _ $dA $dx $dy $dt $di) ↪
     der_appP _ _ _ _ _ (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id $sc $d $dx)
              (der_shift_n $id $sc $d $dy) (der_shift_n $id $sc $d $dt)
              (der_I_shift_n $id $sc $d $di)
with der_shift_n $id $sc $d (der_sys $dA $df $dg $du $dv $d1fg $deq) ↪
     der_sys (der_shift_n $id $sc $d $dA) (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
             (der_shift_n $id (SCF $sc $df) $d $du) (der_shift_n $id (SCF $sc $dg) $d $dv)
             (der_isOne_shift_n $id $sc $d $d1fg)
             (der_eq_shift_n $id (SCF $sc (der_F_min $df $dg)) $d $deq)
with der_shift_n $id $sc $d (der_sys_empty $dA $d1) ↪
     der_sys_empty (der_shift_n $id $sc $d $dA) (der_isOne_shift_n $id $sc $d $d1)
with der_shift_n $id $sc $d (@der_transp _ _ $A _ _ $dA $df $du $deq) ↪
     der_transp (der_shift_n $id (SCI $sc) $d $dA) (der_F_shift_n $id $sc $d $df)
                (der_shift_n $id $sc $d $du)
                (Jeq (TRefl (tuniv _)) (TRefl _)
                     (teq_trans (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                                (Jcong (λ v, IShift v) (aux_teq_Isubst_shift db0 $id it0 $A)))
                     (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deq))
with der_shift_n $id $sc $d (der_hcomp $dA $df $du $du0 $deq) ↪
     der_hcomp (der_shift_n $id $sc $d $dA) (der_F_shift_n $id $sc $d $df)
               (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du)
               (der_shift_n $id $sc $d $du0)
               (der_eq_shift_n $id (SCF $sc $df) $d $deq)
// der_context_shift_n
with der_context_shift_n db0 $i (SC0 _) _
  ↪ der_var _ (dbsucc $i)
with der_context_shift_n (dbsucc _) db0 (SCSucc _ _) _
  ↪ der_var _ db0
with der_context_shift_n (dbsucc $id) (dbsucc $i) (SCSucc $sc $dA) $d
  ↪ der_shift0 (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc) (der_context_shift_n $id $i $sc $d)
// der_eq_shift_n
with der_eq_shift_n $id $sc $d (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du)
  ↪ der_eq_beta _ $s $s' (shift $id $u) (shift $id $A) (shift (dbsucc $id) $t) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dt) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_eta _ $s $s' $A $f $B $dA $dB $df)
  ↪ der_eq_eta _ $s $s' (shift $id $A) (shift $id $f) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
       (der_shift_n $id $sc $d $df)
with der_eq_shift_n $id $sc $d (der_eq_π1 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π1 _ $s $s' (shift $id $u) (shift $id $A) (shift $id $v) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_π2 _ $s $s' $u $A $v $B $dA $du $dB $dv)
  ↪ der_eq_π2 _ $s $s' (shift $id $u) (shift $id $A) (shift $id $v) (shift (dbsucc $id) $B)
       (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
       (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_conversion _ $s $t1 $t2 $T1 $T2 $deqt $deqT)
  ↪ der_eq_conversion _ $s (shift $id $t1) (shift $id $t2) (shift $id $T1) (shift $id $T2)
       (der_eq_shift_n $id $sc $d $deqt) (der_eq_shift_n $id $sc $d $deqT)
with der_eq_shift_n $id $sc $d (der_eq_lift _ $s $e $u $v $A $de)
  ↪ der_eq_lift _ $s (shift $id $e) (shift $id $u) (shift $id $v) (shift $id $A)
       (der_shift_n $id $sc $d $de)
with der_eq_shift_n $id $sc $d (der_eq_refl _ $s $u $A $du)
  ↪ der_eq_refl _ $s (shift $id $u) (shift $id $A) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_trans _ $s $u $v $w $A $duv $dvw)
  ↪ der_eq_trans _ $s (shift $id $u) (shift $id $v) (shift $id $w) (shift $id $A)
       (der_eq_shift_n $id $sc $d $duv) (der_eq_shift_n $id $sc $d $dvw)
with der_eq_shift_n $id $sc $d (der_eq_symm _ $s $u $v $A $deq)
  ↪ der_eq_symm _ $s (shift $id $u) (shift $id $v) (shift $id $A) (der_eq_shift_n $id $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_tfun _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tfun _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tabs _ $s $s' $A1 $A2 $B1 $B2 $t1 $t2 $deqA $deqB $deqt $dB1 $dB2 $dt1 $dt2)
  ↪ der_eq_cong_tabs _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift (dbsucc $id) $t1) (shift (dbsucc $id) $t2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqt)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dt1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dt2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tapp _ $s $s' $A1 $A2 $B1 $B2 $f1 $f2 $a1 $a2 $deqA $deqB $deqf $deqa $dB1 $dB2 $df1 $df2 $da1 $da2)
  ↪ der_eq_cong_tapp _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                               (shift $id $f1) (shift $id $f2) (shift $id $a1) (shift $id $a2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqf) (der_eq_shift_n _ $sc $d $deqa)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $df1) (der_shift_n _ $sc $d $df2) (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tsum _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2)
  ↪ der_eq_cong_tsum _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tpair _ $s $s' $A1 $A2 $B1 $B2 $a1 $a2 $b1 $b2 $deqA $deqB $deqa $deqb $dB1 $dB2 $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_tpair _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                                (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2) (der_shift_n _ $sc $d $db1) (der_shift_n _ $sc $d $db2)
with der_eq_shift_n $id $sc $d (der_eq_cong_π1 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π1 _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqp)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $dp1) (der_shift_n _ $sc $d $dp2)
with der_eq_shift_n $id $sc $d (der_eq_cong_π2 _ $s $s' $A1 $A2 $B1 $B2 $p1 $p2 $deqA $deqB $deqp $dB1 $dB2 $dp1 $dp2)
  ↪ der_eq_cong_π2 _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
       (der_eq_shift_n _ $sc $d $deqp)
       (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1) (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
       (der_shift_n _ $sc $d $dp1) (der_shift_n _ $sc $d $dp2)
with der_eq_shift_n $id $sc $d (der_eq_cong_teq _ $s $A1 $A2 $a1 $a2 $b1 $b2 $deqA $deqa $deqb $da1 $da2 $db1 $db2)
  ↪ der_eq_cong_teq _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
        (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
        (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2) (der_shift_n _ $sc $d $db1) (der_shift_n _ $sc $d $db2)
with der_eq_shift_n $id $sc $d (der_eq_cong_trefl _ $s $A1 $A2 $a1 $a2 $deqA $deqa $da1 $da2)
  ↪ der_eq_cong_trefl _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqa)
       (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2)
with der_eq_shift_n $id $sc $d (der_eq_cong_tK _ $s $A1 $A2 $a1 $a2 $p1 $p2 $deqA $deqa $deqp $da1 $da2 $dp1 $dp2)
  ↪ der_eq_cong_tK _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqp)
       (der_shift_n _ $sc $d $da1) (der_shift_n _ $sc $d $da2)
       (der_shift_n _ $sc $d $dp1) (der_shift_n _ $sc $d $dp2)
;

// Implementation of der_shift{0,1}
rule der_shift0 $dA $dΓ $dt ↪ der_shift_n db0 (SC0 $dΓ) $dA $dt
with der_eq_shift0 $dA $dΓ $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA $deq
with der_shift1 $dA $dB $dΓ $dt ↪ der_shift_n db1 (SCSucc (SC0 $dΓ) $dA) $dB $dt;

// Implementation of der_eq_shift
rule der_eq_shift db0 (der_context_push _ _ _ $dA $dΓ) $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA $deq
with der_eq_shift (dbsucc $id) (der_context_push _ _ _ $dA $dΓ) $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA (der_eq_shift $id $dΓ $deq);
