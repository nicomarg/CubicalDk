
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.derived;
require open ctt.Typing;
require open ctt.TermEquality;
require open ctt.Lemmas;

// Exported lemmas TODO : define them
symbol der_Ishift_context [Γ : Context] [t T A : Term] [l l' : Lev]
                          (_ : der_context Γ) (_ : der Γ A (tuniv l) (lsuc l))
                          (_ : der (PushI (Push A l Γ)) t T l') : der (Push (IShift A) l (PushI Γ)) t T l';

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

symbol shiftget_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id) [l : Lev] [A : Term]
                         (dA : der Γ A (tuniv l) (lsuc l)) :
  TEq (shiftgetΓ (sc_to_sctx dA sc) (dbshift id i)) (shift id (shiftgetΓ (sc_to_ctx sc) i));
rule shiftget_ctx_sctx db0 (SC0 _) _ ↪ TRefl _
with shiftget_ctx_sctx (dbsucc _) (SC0 _) _ ↪ TRefl _
with shiftget_ctx_sctx db0 (SCSucc _ _) _ ↪ TRefl _
with shiftget_ctx_sctx (dbsucc $i) (SCSucc $sc _) $dA ↪ Jcong Shift (shiftget_ctx_sctx $i $sc $dA)
with @shiftget_ctx_sctx _ $id $i (SCI $sc) _ _ $dA ↪
     teq_trans (Jcong IShift (shiftget_ctx_sctx $i $sc $dA))
               (teq_inv (aux_teq_shift_Ishift $id db0 (shiftgetΓ (sc_to_ctx $sc) $i)))
with shiftget_ctx_sctx $i (SCF $sc _) $dA ↪ shiftget_ctx_sctx $i $sc $dA;

symbol getS_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                     [l : Lev] [A : Term] (dA : der Γ A (tuniv l) (lsuc l)) :
  LEq (getS (sc_to_sctx dA sc) (dbshift id i)) (getS (sc_to_ctx sc) i);
rule getS_ctx_sctx _ (SC0 _) _ ↪ LRefl _
with getS_ctx_sctx db0 (SCSucc _ _) _ ↪ LRefl _
with getS_ctx_sctx (dbsucc $i) (SCSucc $sc _) $dA ↪ getS_ctx_sctx $i $sc $dA
with getS_ctx_sctx $i (SCI $sc) $dA ↪ getS_ctx_sctx $i $sc $dA
with getS_ctx_sctx $i (SCF $sc _) $dA ↪ getS_ctx_sctx $i $sc $dA;

symbol len_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                    [l : Lev] [A : Term] (dA : der Γ A (tuniv l) (lsuc l)) :
  DBLe (dbsucc i) (len (sc_to_ctx sc)) → DBLe (dbsucc (dbshift id i)) (len (sc_to_sctx dA sc));
rule len_ctx_sctx _ (SC0 _) _ $h ↪ dble_n_S $h
with len_ctx_sctx db0 (SCSucc _ _) _ _ ↪ dble_n_S (dble_0_n _)
with len_ctx_sctx (dbsucc $i) (SCSucc $sc _) $dA $h ↪ dble_n_S (len_ctx_sctx $i $sc $dA (dble_S_n $h))
with len_ctx_sctx $i (SCI $sc) $dA $h ↪ len_ctx_sctx $i $sc $dA $h
with len_ctx_sctx $i (SCF $sc _) $dA $h ↪ len_ctx_sctx $i $sc $dA $h;

symbol lenI_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                     [l : Lev] [A : Term] (dA : der Γ A (tuniv l) (lsuc l)) :
  DBLe (dbsucc i) (lenI (sc_to_ctx sc)) → DBLe (dbsucc i) (lenI (sc_to_sctx dA sc));
rule lenI_ctx_sctx _ (SC0 _) _ $h ↪ $h
with lenI_ctx_sctx $id (SCSucc $sc _) $d $h ↪ lenI_ctx_sctx $id $sc $d $h
with lenI_ctx_sctx db0 (SCI _) _ _ ↪ dble_n_S (dble_0_n _)
with lenI_ctx_sctx (dbsucc $i) (SCI $sc) $dA $h ↪ dble_n_S (lenI_ctx_sctx $i $sc $dA (dble_S_n $h))
with lenI_ctx_sctx $i (SCF $sc _) $dA $h ↪ lenI_ctx_sctx $i $sc $dA $h;

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
symbol test2 [Γ : Context] [sa s s' : Lev] [T : Term] (id : DBId)
             (sc : ShiftContext Γ id) (d : der Γ T (tuniv sa) (lsuc sa))
             (A B u u0 : Term) (f : FTerm)
             (dA : der (sc_to_ctx sc) A (tuniv s) (lsuc s))
             (dB : der (Push A s (sc_to_ctx sc)) B (tuniv s') (lsuc s'))
             (df : der_F (sc_to_ctx sc) f)
             (du : der (PushF (IShiftF f) (PushI (sc_to_ctx sc))) u (IShift (tsig A B)) (lmax s s'))
             (du0 : der (sc_to_ctx sc) u0 (tsig A B) (lmax s s'))
             (deq : der_eq (PushF f (sc_to_ctx sc)) u0 (applyI1 u it0) (tsig A B) (lmax s s')) :
  der_eq (sc_to_sctx d sc) (shift id (thcomp (tsig A B) f u u0))
         (shift id (tpair (thcomp A f (tp1 u) (tp1 u0))
                           (tcomp (apply1 (IShift B) (thfill A f (tp1 u) (tp1 u0))) f (tp2 u) (tp2 u0)))) (shift id (tsig A B)) (lmax s s') ≔
begin
  assume Γ sa s s' T id sc d A B u u0 f dA dB df du du0 deq;
  refine Jeq (TRefl _) (TRefl _) _
         (der_eq_hcomp_sig _ s s' (shift id A) (shift (dbsucc id) B) f (shift id u) (shift id u0)
                           (der_shift_n id sc d dA) (der_shift_n (dbsucc id) (SCSucc sc dA) d dB)
                           (der_F_shift_n id sc d df)
                           (JT (aux_teq_shift_Ishift id db0 (tsig A B)) (der_shift_n id (SCF (SCI sc) (der_Ishift0F (sc_to_dctx sc) df)) d du))
                           (der_shift_n id sc d du0) (der_eq_shift_n id (SCF sc df) d deq));
  refine Jpair (TRefl _) _;
  refine teq_trans _ (teq_shift_comp id (apply1 (IShift B) (thfill A f (tp1 u) (tp1 u0))) f (tp2 u) (tp2 u0));
  refine Jcomp [(apply1 (IShift (shift (dbsucc id) B)) (thfill (shift id A) f (tp1 (shift id u)) (tp1 (shift id u0))))]
               [(shift id (apply1 (IShift B) (thfill A f (tp1 u) (tp1 u0))))] _ (FTRefl f) (TRefl (shift id (tp2 u))) (TRefl (shift id (tp2 u0)));
  refine teq_trans (Jcong (λ t, apply1 t (thfill (shift id A) f (tp1 (shift id u)) (tp1 (shift id u0)))) (teq_inv (aux_teq_shift_Ishift (dbsucc id) db0 B))) _;
  refine Jcong [(thfill (shift id A) f (tp1 (shift id u)) (tp1 (shift id u0)))] [shift id (thfill A f (tp1 u) (tp1 u0))]
               (λ t, apply1 (shift (dbsucc id) (IShift B)) t) _;
  refine teq_shift_hfill id A f (tp1 u) (tp1 u0)
end;
print test2;
symbol der_context_shift_n [Γ : Context] [sa : Lev] [A : Term] (id i : DBId)
                           (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (lsuc sa)) :
  DBLe (dbsucc i) (len (sc_to_ctx sc)) →
  der (sc_to_sctx dA sc) (tvar (dbshift id i)) (shift id (shiftgetΓ (sc_to_ctx sc) i)) (getS (sc_to_ctx sc) i) ≔
begin
  assume Γ sa A id i sc dA h;
  refine JT (shiftget_ctx_sctx i sc dA) _;
  refine Jl (getS_ctx_sctx i sc dA) _;
  refine der_var _;
  refine len_ctx_sctx i sc dA h
end;

rule sc_to_dsctx $d (SC0 $dΓ) ↪ der_context_Push _ _ _ $d $dΓ
with sc_to_dsctx $d (SCSucc $sc $dA) ↪ der_context_Push _ _ _ (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc)
with sc_to_dsctx $d (SCI $sc) ↪ der_context_PushI _ (sc_to_dsctx $d $sc)
with sc_to_dsctx $d (SCF $sc $df) ↪ der_context_PushF _ _ (der_F_shift_n _ $sc $d $df) (sc_to_dsctx $d $sc);

// der_shift_n
rule der_shift_n $id $sc $d (der_empty_face $d1) ↪ der_empty_face (der_isOne_shift_n $id $sc $d $d1)
with der_shift_n $id $sc $d (der_union_face $df $dg $d1 $d2 $dfg) ↪
     der_union_face (der_F_shift_n $id $sc $d $df)
                    (der_F_shift_n $id $sc $d $dg)
                    (der_shift_n $id (SCF $sc $df) $d $d1)
                    (der_shift_n $id (SCF $sc $dg) $d $d2)
                    (der_isOne_shift_n $id $sc $d $dfg)
with der_shift_n $id $sc $d (@der_var _ $i $le) ↪ der_context_shift_n $id $i $sc $d $le
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
with der_shift_n $id $sc $d (@der_hcomp _ _ $A _ _ _ $dA $df $du $du0 $deq) ↪
     der_hcomp (der_shift_n $id $sc $d $dA) (der_F_shift_n $id $sc $d $df)
               (JT (aux_teq_shift_Ishift $id db0 $A) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du))
               (der_shift_n $id $sc $d $du0)
               (der_eq_shift_n $id (SCF $sc $df) $d $deq)
// der_eq_shift_n
with der_eq_shift_n $id $sc $d (der_eq_refl _ $s $u $A $du) ↪
     der_eq_refl _ $s (shift $id $u) (shift $id $A) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_trans _ $s $u $v $w $A $duv $dvw) ↪
     der_eq_trans _ $s (shift $id $u) (shift $id $v) (shift $id $w) (shift $id $A)
                       (der_eq_shift_n $id $sc $d $duv) (der_eq_shift_n $id $sc $d $dvw)
with der_eq_shift_n $id $sc $d (der_eq_sym _ $s $u $v $A $deq) ↪
     der_eq_sym _ $s (shift $id $u) (shift $id $v) (shift $id $A) (der_eq_shift_n $id $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_conv _ $s $t1 $t2 $T1 $T2 $deqt $deqT) ↪
     der_eq_conv _ $s (shift $id $t1) (shift $id $t2) (shift $id $T1) (shift $id $T2)
                      (der_eq_shift_n $id $sc $d $deqt) (der_eq_shift_n $id $sc $d $deqT)
with der_eq_shift_n $id $sc $d (der_eq_isOne_zero _ $s $A $u $v $d1) ↪
     der_eq_isOne_zero _ $s (shift $id $A) (shift $id $u) (shift $id $v)
                            (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_isOne_max _ $s $A $u $v $f $g $df $dg $deqf $deqg $d1) ↪
     der_eq_isOne_max _ $s (shift $id $A) (shift $id $u) (shift $id $v) $f $g
                      (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                      (der_eq_shift_n $id (SCF $sc $df) $d $deqf)
                      (der_eq_shift_n $id (SCF $sc $dg) $d $deqg)
                      (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du) ↪
     der_eq_beta _ $s $s' (shift $id $u) (shift $id $A) (shift (dbsucc $id) $t) (shift (dbsucc $id) $B)
                        (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                        (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dt) (der_shift_n $id $sc $d $du)
with der_eq_shift_n $id $sc $d (der_eq_eta _ $s $s' $A $B $f $dA $dB $df) ↪
     der_eq_eta _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $f)
                       (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                       (der_shift_n $id $sc $d $df)
with der_eq_shift_n $id $sc $d (der_eq_rec_zero _ $s $s' $P $z $H $dP $dz $dH) ↪
     der_eq_rec_zero _ $s $s' (shift $id $P) (shift $id $z) (shift $id $H)
                     (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dz)
                     (der_shift_n $id $sc $d $dH)
with der_eq_shift_n $id $sc $d (der_eq_rec_suc _ $s $s' $P $z $H $n $dP $dz $dH $dn) ↪
     der_eq_rec_suc _ $s $s' (shift $id $P) (shift $id $z) (shift $id $H) (shift $id $n)
                     (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dz)
                     (der_shift_n $id $sc $d $dH) (der_shift_n $id $sc $d $dn)
with der_eq_shift_n $id $sc $d (der_eq_p1 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p1 _ $s $s' (shift $id $A) (shift $id $u) (shift (dbsucc $id) $B) (shift $id $v)
                      (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
                      (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_p2 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p2 _ $s $s' (shift $id $A) (shift $id $u) (shift (dbsucc $id) $B) (shift $id $v)
                      (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $du)
                      (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB) (der_shift_n $id $sc $d $dv)
with der_eq_shift_n $id $sc $d (der_eq_pair _ $s $s' $A $B $t $u $dA $dB $dt $du $dp1 $dp2) ↪
     der_eq_pair _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $t) (shift $id $u)
                      (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                      (der_shift_n $id $sc $d $dt) (der_shift_n $id $sc $d $du)
                      (der_eq_shift_n $id $sc $d $dp1) (der_eq_shift_n $id $sc $d $dp2)
with der_eq_shift_n $id $sc $d (der_eq_case_left _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_left _ $s $s' $m (shift $id $A) (shift $id $B) (shift $id $P) (shift $id $Ha)
                                   (shift $id $Hb) (shift $id $a)
                      (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
                      (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dHa)
                      (der_shift_n $id $sc $d $dHb) (der_shift_n $id $sc $d $da)
with der_eq_shift_n $id $sc $d (der_eq_case_right _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_right _ $s $s' $m (shift $id $A) (shift $id $B) (shift $id $P) (shift $id $Ha)
                                   (shift $id $Hb) (shift $id $a)
                      (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB)
                      (der_shift_n $id $sc $d $dP) (der_shift_n $id $sc $d $dHa)
                      (der_shift_n $id $sc $d $dHb) (der_shift_n $id $sc $d $da)
with der_eq_shift_n $id $sc $d (der_eq_betaP _ $s $A $t $i $dA $dt $di) ↪
     der_eq_betaP _ $s (shift $id $A) (shift $id $t) $i
                      (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id (SCI $sc) $d $dt)
                      (der_I_shift_n $id $sc $d $di)
with der_eq_shift_n $id $sc $d (der_eq_etaP _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     Jeq (TRefl _) (Jcong (λ v, tlamP (tappP v (itvar db0))) (teq_inv (aux_teq_shift_Ishift $id db0 $t))) (TRefl _)
         (der_eq_etaP _ $s (shift $id $A) (shift $id $t) (shift $id $x) (shift $id $y)
                           (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id $sc $d $dx)
                           (der_shift_n $id $sc $d $dy) (der_shift_n $id $sc $d $dt))
with der_eq_shift_n $id $sc $d (der_eq_appP_zero _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_appP_zero _ $s (shift $id $A) (shift $id $t) (shift $id $x) (shift $id $y)
                      (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id $sc $d $dx)
                      (der_shift_n $id $sc $d $dy) (der_shift_n $id $sc $d $dt)
with der_eq_shift_n $id $sc $d (der_eq_appP_one _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_appP_one _ $s (shift $id $A) (shift $id $t) (shift $id $x) (shift $id $y)
                      (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id $sc $d $dx)
                      (der_shift_n $id $sc $d $dy) (der_shift_n $id $sc $d $dt)
with der_eq_shift_n $id $sc $d (der_eq_sys_left _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_left _ $s (shift $id $A) $f $g (shift $id $x) (shift $id $y) (der_shift_n $id $sc $d $dA)
                     (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                     (der_shift_n $id (SCF $sc $df) $d $dx) (der_shift_n $id (SCF $sc $dg) $d $dy)
                     (der_eq_shift_n $id (SCF $sc (der_F_min $df $dg)) $d $deq)
                     (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_sys_right _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_right _ $s (shift $id $A) $f $g (shift $id $x) (shift $id $y) (der_shift_n $id $sc $d $dA)
                      (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                      (der_shift_n $id (SCF $sc $df) $d $dx) (der_shift_n $id (SCF $sc $dg) $d $dy)
                      (der_eq_shift_n $id (SCF $sc (der_F_min $df $dg)) $d $deq)
                      (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_transp _ $s $A $f $u $dA $df $du $deq $d1) ↪
     der_eq_transp _ $s (shift $id $A) $f (shift $id $u) (der_shift_n $id (SCI $sc) $d $dA)
                     (der_F_shift_n $id $sc $d $df) (der_shift_n $id $sc $d $du)
                     (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                          (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deq))
                     (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_transp_pi _ $s $s' $A $B $f $u $v $dA $dB $df $deqA $deqB $du $dv) ↪
     Jeq (TRefl _) (TRefl _)
         (Jtransp (teq_trans (Jcong (λ w, apply1 (shift (dbsucc $id) $B)
                                                 (ttransp (applyI1 w (itmax (itvar db1) (itsym (itvar db0))))
                                                          (ftmax (IShiftF $f) (fteq0 db0)) (IShift (shift $id $v))))
                                    (teq_trans (Jcong IShift1 (teq_inv (aux_teq_shift_Ishift $id db1 $A)))
                                               (teq_inv (aux_teq_shift_Ishift $id db1 (IShift1 $A)))))
                             (Jcong (λ w, apply1 (shift (dbsucc $id) $B)
                                                 (ttransp (applyI1 (shift $id (IShift1 (IShift1 $A)))
                                                                   (itmax (itvar db1) (itsym (itvar db0))))
                                                          (ftmax (IShiftF $f) (fteq0 db0)) w))
                                    (teq_inv (aux_teq_shift_Ishift $id db0 $v)))) (FTRefl $f)
                  (Jcong (λ w, tapp (shift $id $u) (ttransp (applyI1 w (itsym (itvar db0))) $f (shift $id $v)))
                         (teq_inv (aux_teq_shift_Ishift $id db1 $A))))
         (der_eq_transp_pi _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u) (shift $id $v)
                           (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n (dbsucc $id) (SCSucc (SCI $sc) $dA) $d $dB)
                           (der_F_shift_n $id $sc $d $df)
                           (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                                (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqA))
                           (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift (dbsucc $id) db0 (applyI1 $B it0))
                                (der_eq_shift_n (dbsucc $id)
                                                (SCSucc (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df))
                                                        (der_weakF (pushΓI (sc_to_dctx $sc)) $dA
                                                                   (der_Ishift0F (sc_to_dctx $sc) $df)))
                                                $d $deqB))
                           (der_shift_n $id $sc $d $du)
                           (der_shift_n $id $sc $d $dv))
with der_eq_shift_n $id $sc $d (der_eq_transp_univ _ $s $f $A $df $dA) ↪
     der_eq_transp_univ _ $s $f (shift $id $A)
                       (der_F_shift_n $id $sc $d $df) (der_shift_n $id $sc $d $dA)
with der_eq_shift_n $id $sc $d (der_eq_transp_zero _ $s $f $df) ↪
     der_eq_transp_zero _ $s $f (der_F_shift_n $id $sc $d $df)
with der_eq_shift_n $id $sc $d (der_eq_transp_suc _ $s $f $n $df $dn) ↪
     der_eq_transp_suc _ $s $f (shift $id $n) (der_F_shift_n $id $sc $d $df) (der_shift_n $id $sc $d $dn)
with der_eq_shift_n $id $sc $d (der_eq_transp_sig _ $s $s' $A $B $f $u $dA $dB $df $deqA $deqB $du) ↪
     Jeq (TRefl _) (TRefl _)
         (Jpair (TRefl _)
                (Jtransp (Jcong (λ v, apply1 (shift (dbsucc $id) $B) v)
                                (Jtransp (Jcong (λ v, (applyI1 v (itmin (itvar db0) (itvar db1))))
                                                (teq_trans (Jcong IShift1 (teq_inv (aux_teq_shift_Ishift $id db1 $A)))
                                                           (teq_inv (aux_teq_shift_Ishift $id db1 (IShift1 $A)))))
                                         (FTRefl (ftmax (IshiftF db0 $f) (fteq0 db0)))
                                         (Jcong tp1 (teq_inv (aux_teq_shift_Ishift $id db0 $u)))))
                         (FTRefl _) (TRefl _)))
         (der_eq_transp_sig _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u)
                            (der_shift_n $id (SCI $sc) $d $dA)
                            (der_shift_n (dbsucc $id) (SCSucc (SCI $sc) $dA) $d $dB)
                            (der_F_shift_n $id $sc $d $df)
                            (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                                 (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqA))
                            (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift (dbsucc $id) db0 (applyI1 $B it0))
                                 (der_eq_shift_n (dbsucc $id)
                                                 (SCSucc (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df))
                                                         (der_weakF (pushΓI (sc_to_dctx $sc)) $dA
                                                                    (der_Ishift0F (sc_to_dctx $sc) $df))) $d $deqB))
                            (der_shift_n $id $sc $d $du))
with der_eq_shift_n $id $sc $d (der_eq_transp_sum_left _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     der_eq_transp_sum_left _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a)
                       (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id (SCI $sc) $d $dB)
                       (der_F_shift_n $id $sc $d $df) (der_shift_n $id $sc $d $da)
                       (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                            (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqA))
                       (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $B it0))
                            (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqB))
with der_eq_shift_n $id $sc $d (der_eq_transp_sum_right _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     der_eq_transp_sum_right _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a)
                       (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id (SCI $sc) $d $dB)
                       (der_F_shift_n $id $sc $d $df) (der_shift_n $id $sc $d $da)
                       (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $A it0))
                            (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqA))
                       (Jeq (TRefl _) (TRefl _) (aux_teq_shift_Ishift $id db0 (applyI1 $B it0))
                            (der_eq_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqB))
with der_eq_shift_n $id $sc $d (der_eq_transp_path _ $s $A $x $y $f $u $dA $dx $dy $df $du $deqA $deqx $deqy) ↪
     Jeq (Jcong (λ v, tpath v (applyI1 (shift $id $x) it1) (applyI1 (shift $id $y) it1)) (aux_teq_Isubst_shift db1 $id it1 $A))
         (TRefl _)
         (Jcong tlamP (teq_trans (Jcomp (Jcong (λ v, applyI1 (applyI1 v (itvar db2)) (itvar db0))
                                               (teq_trans (Jcong (Ishift db2) (teq_inv (aux_teq_shift_Ishift $id db2 $A)))
                                                          (teq_inv (aux_teq_shift_Ishift $id db2 (Ishift db2 $A)))))
                                        (FTRefl _)
                                        (Jsys (FTRefl _) (FTRefl _)
                                              (JappP (teq_trans (Jcong IShift (teq_inv (aux_teq_shift_Ishift $id db0 $u)))
                                                                (teq_inv (aux_teq_shift_Ishift $id db0 (IShift $u))))
                                                     (ITRefl _))
                                              (Jsys (FTRefl _) (FTRefl _)
                                                    (teq_inv (aux_teq_shift_Ishift $id db1 $x))
                                                    (teq_inv (aux_teq_shift_Ishift $id db1 $y))))
                                        (JappP (teq_inv (aux_teq_shift_Ishift $id db0 $u)) (ITRefl _)))
                                 (teq_shift_comp $id (applyI1 (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)) (itvar db0))
                                                     (ftmax (IShiftF $f) (ftmax (fteq0 db0) (fteq1 db0)))
                                                     (tsys (IShiftFN db1 $f) (ftmax (fteq0 db1) (fteq1 db1)) (tappP (IShift (IShift $u)) (itvar db1))
                                                           (tsys (fteq0 db1) (fteq1 db1) (IShift1 $x) (IShift1 $y)))
                                                     (tappP (IShift $u) (itvar db0)))))
         (der_eq_transp_path _ $s (shift $id $A) (shift $id $x) (shift $id $y) $f (shift $id $u) (der_shift_n $id (SCI (SCI $sc)) $d $dA)
                             (der_shift_n _ (SCI $sc) $d $dx) (der_shift_n _ (SCI $sc) $d $dy)
                             (der_F_shift_n _ $sc $d $df)
                             (JT (teq_inv (aux_teq_Isubst_shift db0 $id it0 (tpath $A $x $y))) (der_shift_n _ $sc $d $du))
                             (Jeq (TRefl _) (TRefl _) (teq_trans (aux_teq_shift_Ishift $id db1 (Isubst db1 it0 $A))
                                                                 (Jcong IShift1 (teq_inv (aux_teq_Isubst_shift db1 $id it0 $A))))
                                  (der_eq_shift_n _ (SCF (SCI (SCI $sc)) (der_Ishift0F (sc_to_dctx (SCI $sc)) (der_Ishift0F (sc_to_dctx $sc) $df))) $d $deqA))
                             (Jeq (TRefl _) (TRefl _) (teq_trans (aux_teq_shift_Ishift $id db0 (applyI1 $x it0))
                                                                 (Jcong IShift (teq_inv (aux_teq_Isubst_shift db0 $id it0 $x))))
                                  (der_eq_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqx))
                             (Jeq (TRefl _) (TRefl _) (teq_trans (aux_teq_shift_Ishift $id db0 (applyI1 $y it0))
                                                                 (Jcong IShift (teq_inv (aux_teq_Isubst_shift db0 $id it0 $y))))
                                  (der_eq_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $deqy)))
with der_eq_shift_n $id $sc $d (der_eq_hcomp _ $s $A $f $u $u0 $dA $df $du $du0 $deq $d1) ↪
     der_eq_hcomp _ $s (shift $id $A) $f (shift $id $u) (shift $id $u0) (der_shift_n $id $sc $d $dA)
                  (der_F_shift_n $id $sc $d $df)
                  (JT (aux_teq_shift_Ishift $id db0 $A) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du))
                  (der_shift_n $id $sc $d $du0)
                  (der_eq_shift_n $id (SCF $sc $df) $d $deq) (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_pi _ $s $s' $A $B $f $u $u0 $v $dA $dB $df $du $du0 $deq $dv) ↪
     Jeq (TRefl _) (TRefl _) (Jhcomp (TRefl _) (FTRefl _)
                                     (Japp (TRefl _) (teq_inv (aux_teq_shift_Ishift $id db0 $v))) (TRefl _))
     (der_eq_hcomp_pi _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u) (shift $id $u0) (shift $id $v)
                     (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                     (der_F_shift_n $id $sc $d $df)
                     (JT (aux_teq_shift_Ishift $id db0 (tpi $A $B)) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du))
                     (der_shift_n $id $sc $d $du0) (der_eq_shift_n $id (SCF $sc $df) $d $deq)
                     (der_shift_n $id $sc $d $dv))
with der_eq_shift_n $id $sc $d (der_eq_hcomp_zero _ $s $f $n $df $dn $deq) ↪
     der_eq_hcomp_zero _ $s $f (shift $id $n) (der_F_shift_n $id $sc $d $df)
                       (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $dn)
                       (der_eq_shift_n $id (SCF $sc $df) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_suc _ $s $f $n $n0 $df $dn $dn0 $deq) ↪
     der_eq_hcomp_suc _ $s $f (shift $id $n) (shift $id $n0) (der_F_shift_n $id $sc $d $df)
                       (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $dn)
                       (der_shift_n $id $sc $d $dn0) (der_eq_shift_n $id (SCF $sc $df) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_sig _ $s $s' $A $B $f $u $u0 $dA $dB $df $du $du0 $deq) ↪
     Jeq (TRefl _) (TRefl _)
         (Jpair (TRefl _)
                (teq_trans (Jcomp (teq_trans (Jcong (λ t, apply1 t (thfill (shift $id $A) $f (tp1 (shift $id $u)) (tp1 (shift $id $u0))))
                                                    (teq_inv (aux_teq_shift_Ishift (dbsucc $id) db0 $B)))
                                             (Jcong (λ t, apply1 (shift (dbsucc $id) (IShift $B)) t) (teq_shift_hfill $id $A $f (tp1 $u) (tp1 $u0))))
                                  (FTRefl $f) (TRefl _) (TRefl _))
                           (teq_shift_comp $id (apply1 (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))) $f (tp2 $u) (tp2 $u0))))
         (der_eq_hcomp_sig (sc_to_sctx $d $sc) $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u) (shift $id $u0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                           (der_F_shift_n $id $sc $d $df)
                           (JT (aux_teq_shift_Ishift $id db0 (tsig $A $B)) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du))
                           (der_shift_n $id $sc $d $du0) (der_eq_shift_n $id (SCF $sc $df) $d $deq))
with der_eq_shift_n $id $sc $d (der_eq_hcomp_sum_left _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_left _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a) (shift $id $a0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB) (der_F_shift_n $id $sc $d $df)
                           (JT (aux_teq_shift_Ishift $id db0 $A) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $da))
                           (der_shift_n $id $sc $d $da0) (der_eq_shift_n $id (SCF $sc $df) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_sum_right _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_right _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a) (shift $id $a0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB) (der_F_shift_n $id $sc $d $df)
                           (JT (aux_teq_shift_Ishift $id db0 $B) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $da))
                           (der_shift_n $id $sc $d $da0) (der_eq_shift_n $id (SCF $sc $df) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_path _ $s $A $x $y $f $u $u0 $dA $dx $dy $df $du $du0 $deq) ↪
     Jeq (TRefl _) (TRefl _)
         (Jcong tlamP (Jhcomp (TRefl _) (FTRefl _) (Jsys (FTRefl _) (FTRefl _) (JappP (teq_inv (aux_teq_shift_Ishift $id db1 $u)) (ITRefl _))
                                                         (Jsys (FTRefl _) (FTRefl _) (teq_trans (Jcong IShift (teq_inv (aux_teq_shift_Ishift $id db0 $x)))
                                                                                                (teq_inv (aux_teq_shift_Ishift $id db0 (IShift $x))))
                                                               (teq_trans (Jcong IShift (teq_inv (aux_teq_shift_Ishift $id db0 $y)))
                                                                          (teq_inv (aux_teq_shift_Ishift $id db0 (IShift $y))))))
                              (JappP (teq_inv (aux_teq_shift_Ishift $id db0 $u0)) (ITRefl _))))
         (der_eq_hcomp_path _ $s (shift $id $A) (shift $id $x) (shift $id $y) $f (shift $id $u) (shift $id $u0)
                            (der_shift_n $id (SCI $sc) $d $dA) (der_shift_n $id $sc $d $dx) (der_shift_n $id $sc $d $dy)
                            (der_F_shift_n $id $sc $d $df) (JT (Jpath (aux_teq_shift_Ishift $id db1 $A) (aux_teq_shift_Ishift $id db0 $x)
                                                                      (aux_teq_shift_Ishift $id db0 $y))
                                                               (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du))
                            (der_shift_n $id $sc $d $du0) (der_eq_shift_n $id (SCF $sc $df) $d $deq))
with der_eq_shift_n $id $sc $d (der_eq_cong_pi _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_pi _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                    (der_eq_shift_n $id $sc $d $deqA) (der_eq_shift_n (dbsucc $id) (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
                    (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1)
                    (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_abs _ $s $s' $A1 $A2 $B $t1 $t2 $deqA $deqt $dB1 $dB2) ↪
     der_eq_cong_abs _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B) (shift (dbsucc $id) $t1) (shift (dbsucc $id) $t2)
                     (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqt)
                     (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1)
                     (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_app _ $s $s' $A $B $f1 $f2 $a1 $a2 $deqf $deqa) ↪
     der_eq_cong_app _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $f1) (shift $id $f2) (shift $id $a1) (shift $id $a2)
                            (der_eq_shift_n _ $sc $d $deqf) (der_eq_shift_n _ $sc $d $deqa)
with der_eq_shift_n $id $sc $d (der_eq_cong_suc _ $s $n $n' $deq) ↪
     der_eq_cong_suc _ $s (shift $id $n) (shift $id $n') (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_rec _ $s $s' $P1 $P2 $z1 $z2 $H1 $H2 $n1 $n2 $deqP $deqz $deqH $deqn) ↪
     der_eq_cong_rec _ $s $s' (shift $id $P1) (shift $id $P2) (shift $id $z1) (shift $id $z2)
                     (shift $id $H1) (shift $id $H2) (shift $id $n1) (shift $id $n2)
                     (der_eq_shift_n _ $sc $d $deqP) (der_eq_shift_n _ $sc $d $deqz)
                     (der_eq_shift_n _ $sc $d $deqH) (der_eq_shift_n _ $sc $d $deqn)
with der_eq_shift_n $id $sc $d (der_eq_cong_sig _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_sig _ $s $s' (shift $id $A1) (shift $id $A2) (shift (dbsucc $id) $B1) (shift (dbsucc $id) $B2)
                            (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $deqB)
                            (der_shift_n _ (SCSucc $sc (inv_eq_t1 (sc_to_dctx $sc) $deqA)) $d $dB1)
                            (der_shift_n _ (SCSucc $sc (inv_eq_t2 (sc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_shift_n $id $sc $d (der_eq_cong_pair _ $s $s' $A $B $a1 $a2 $b1 $b2 $deqa $deqb) ↪
     der_eq_cong_pair _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
                      (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
with der_eq_shift_n $id $sc $d (der_eq_cong_p1 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p1 _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_p2 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p2 _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_sum _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB) ↪
     der_eq_cong_sum _ $s $s' (shift $id $A1) (shift $id $A2) (shift $id $B1) (shift $id $B2)
                            (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqB)
with der_eq_shift_n $id $sc $d (der_eq_cong_injl _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injl _ $s $s' (shift $id $A) (shift $id $B) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_injr _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injr _ $s $s' (shift $id $A) (shift $id $B) (shift $id $p1) (shift $id $p2)
       (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_case _ $s $s' $m $A1 $A2 $B1 $B2 $P1 $P2 $Ha1 $Ha2 $Hb1 $Hb2 $u $v $deqA $deqB $deqP $deqHa $deqHb $deq) ↪
     der_eq_cong_case _ $s $s' $m (shift $id $A1) (shift $id $A2) (shift $id $B1) (shift $id $B2) (shift $id $P1) (shift $id $P2)
                      (shift $id $Ha1) (shift $id $Ha2) (shift $id $Hb1) (shift $id $Hb2) (shift $id $u) (shift $id $v)
                      (der_eq_shift_n _ $sc $d $deqA) (der_eq_shift_n _ $sc $d $deqB) (der_eq_shift_n _ $sc $d $deqP)
                      (der_eq_shift_n _ $sc $d $deqHa) (der_eq_shift_n _ $sc $d $deqHb) (der_eq_shift_n _ $sc $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_path _ $s $A1 $A2 $a1 $a2 $b1 $b2 $deqA $deqa $deqb) ↪
     der_eq_cong_path _ $s (shift $id $A1) (shift $id $A2) (shift $id $a1) (shift $id $a2) (shift $id $b1) (shift $id $b2)
                           (der_eq_shift_n _ (SCI $sc) $d $deqA) (der_eq_shift_n _ $sc $d $deqa) (der_eq_shift_n _ $sc $d $deqb)
with der_eq_shift_n $id $sc $d (der_eq_cong_lamP _ $s $A $a1 $a2 $deq) ↪
     der_eq_cong_lamP _ $s (shift $id $A) (shift $id $a1) (shift $id $a2)
                           (der_eq_shift_n _ (SCI $sc) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_cong_appP _ $s $A $x $y $a1 $a2 $i1 $i2 $deq $deqi) ↪
     der_eq_cong_appP _ $s (shift $id $A) (shift $id $x) (shift $id $y) (shift $id $a1) (shift $id $a2) $i1 $i2
                           (der_eq_shift_n _ $sc $d $deq) (der_eq_I_shift_n _ $sc $d $deqi)
with der_eq_shift_n $id $sc $d (der_eq_cong_sys _ $s $A $f1 $f2 $g1 $g2 $u1 $u2 $v1 $v2
                                                $deqf $deqg $dequ $deqv $du1 $du2 $dv1 $dv2 $done1 $done2 $deq1 $deq2) ↪
     der_eq_cong_sys _ $s (shift $id $A) $f1 $f2 $g1 $g2 (shift $id $u1) (shift $id $u2) (shift $id $v1) (shift $id $v2)
                     (der_eq_F_shift_n $id $sc $d $deqf) (der_eq_F_shift_n $id $sc $d $deqg)
                     (der_eq_shift_n $id (SCF $sc (inv_eq_F_t1 (sc_to_dctx $sc) $deqf)) $d $dequ)
                     (der_eq_shift_n $id (SCF $sc (inv_eq_F_t1 (sc_to_dctx $sc) $deqg)) $d $deqv)
                     (der_shift_n $id (SCF $sc (inv_eq_F_t1 (sc_to_dctx $sc) $deqf)) $d $du1)
                     (der_shift_n $id (SCF $sc (inv_eq_F_t2 (sc_to_dctx $sc) $deqf)) $d $du2)
                     (der_shift_n $id (SCF $sc (inv_eq_F_t1 (sc_to_dctx $sc) $deqg)) $d $dv1)
                     (der_shift_n $id (SCF $sc (inv_eq_F_t2 (sc_to_dctx $sc) $deqg)) $d $dv2)
                     (der_isOne_shift_n $id $sc $d $done1) (der_isOne_shift_n $id $sc $d $done2)
                     (der_eq_shift_n $id (SCF $sc (der_F_min (inv_eq_F_t1 (sc_to_dctx $sc) $deqf) (inv_eq_F_t1 (sc_to_dctx $sc) $deqg))) $d $deq1)
                     (der_eq_shift_n $id (SCF $sc (der_F_min (inv_eq_F_t2 (sc_to_dctx $sc) $deqf) (inv_eq_F_t2 (sc_to_dctx $sc) $deqg))) $d $deq2)
with der_eq_shift_n $id $sc $d (der_eq_cong_transp _ $s $A1 $A2 $f1 $f2 $a1 $a2 $deqA $deqf $deqa $deqA1 $deqA2) ↪
     der_eq_cong_transp _ $s (shift $id $A1) (shift $id $A2) $f1 $f2 (shift $id $a1) (shift $id $a2)
                        (der_eq_shift_n _ (SCI $sc) $d $deqA) (der_eq_F_shift_n _ $sc $d $deqf) (der_eq_shift_n _ $sc $d $deqa)
                        (Jeq (TRefl _) (TRefl _) (teq_trans (aux_teq_shift_Ishift $id db0 (applyI1 $A1 it0)) (TRefl _)) (der_eq_shift_n _ (SCI $sc) $d $deqA1))
                        (Jeq (TRefl _) (TRefl _) (teq_trans (aux_teq_shift_Ishift $id db0 (applyI1 $A2 it0)) (TRefl _)) (der_eq_shift_n _ (SCI $sc) $d $deqA2))
with der_eq_shift_n $id $sc $d (der_eq_cong_hcomp _ $s $A1 $A2 $f1 $f2 $u1 $u2 $v1 $v2 $deqA $deqf $dequ $deqv $du1 $du2 $dequv1 $dequv2) ↪
     der_eq_cong_hcomp _ $s (shift $id $A1) (shift $id $A2) $f1 $f2 (shift $id $u1) (shift $id $u2) (shift $id $v1) (shift $id $v2)
                       (der_eq_shift_n _ $sc $d $deqA) (der_eq_F_shift_n _ $sc $d $deqf)
                       (Jeq (aux_teq_shift_Ishift $id db0 $A1) (TRefl _) (TRefl _)
                            (der_eq_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t1 (sc_to_dctx $sc) $deqf))) $d $dequ))
                       (der_eq_shift_n _ $sc $d $deqv)
                       (JT (aux_teq_shift_Ishift $id db0 $A1)
                           (der_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t1 (sc_to_dctx $sc) $deqf))) $d $du1))
                       (JT (aux_teq_shift_Ishift $id db0 $A2)
                           (der_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t2 (sc_to_dctx $sc) $deqf))) $d $du2))
                       (der_eq_shift_n _ (SCF $sc (inv_eq_F_t1 (sc_to_dctx $sc) $deqf)) $d $dequv1)
                       (der_eq_shift_n _ (SCF $sc (inv_eq_F_t2 (sc_to_dctx $sc) $deqf)) $d $dequv2)
// der_I_shift_n
with der_I_shift_n _ _ _ der_I_0 ↪ der_I_0
with der_I_shift_n _ _ _ der_I_1 ↪ der_I_1
with der_I_shift_n _ $sc $d (@der_I_var _ $i $le) ↪ der_I_var (lenI_ctx_sctx $i $sc $d $le)
with der_I_shift_n $id $sc $d (der_I_sym $di) ↪ der_I_sym (der_I_shift_n $id $sc $d $di)
with der_I_shift_n $id $sc $d (der_I_min $da $db) ↪
     der_I_min (der_I_shift_n $id $sc $d $da) (der_I_shift_n $id $sc $d $db)
with der_I_shift_n $id $sc $d (der_I_max $da $db) ↪
     der_I_max (der_I_shift_n $id $sc $d $da) (der_I_shift_n $id $sc $d $db)
// der_eq_I_shift_n
with der_eq_I_shift_n $id $sc $d (der_eq_I_refl _ _ $di) ↪ der_eq_I_refl _ _ (der_I_shift_n $id $sc $d $di)
with der_eq_I_shift_n $id $sc $d (der_eq_I_sym _ _ _ $di) ↪ der_eq_I_sym _ _ _ (der_eq_I_shift_n $id $sc $d $di)
with der_eq_I_shift_n $id $sc $d (der_eq_I_trans _ _ _ _ $deq1 $deq2) ↪
     der_eq_I_trans _ _ _ _ (der_eq_I_shift_n $id $sc $d $deq1) (der_eq_I_shift_n $id $sc $d $deq2)
with der_eq_I_shift_n $id $sc $d (der_eq_I_isOne_zero _ _ _ $done) ↪
     der_eq_I_isOne_zero _ _ _ (der_isOne_shift_n $id $sc $d $done)
with der_eq_I_shift_n $id $sc $d (der_eq_I_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_I_isOne_max _ _ _ _ _ (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                        (der_eq_I_shift_n $id (SCF $sc $df) $d $dif) (der_eq_I_shift_n $id (SCF $sc $dg) $d $dig)
                        (der_isOne_shift_n $id $sc $d $done)
with der_eq_I_shift_n $id $sc $d (der_eq_I_isOne_eq0 _ _ $done) ↪
     der_eq_I_isOne_eq0 _ _ (der_isOne_shift_n $id $sc $d $done)
with der_eq_I_shift_n $id $sc $d (der_eq_I_isOne_eq1 _ _ $done) ↪
     der_eq_I_isOne_eq1 _ _ (der_isOne_shift_n $id $sc $d $done)
with der_eq_I_shift_n _ _ _ (der_eq_I_sym_sym _ _) ↪ der_eq_I_sym_sym _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_sym_zero _) ↪ der_eq_I_sym_zero _
with der_eq_I_shift_n _ _ _ (der_eq_I_sym_one _) ↪ der_eq_I_sym_one _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_assoc _ _ _ _) ↪ der_eq_I_min_assoc _ _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_comm _ _ _) ↪ der_eq_I_min_comm _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_zero _ _) ↪ der_eq_I_min_zero _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_one _ _) ↪ der_eq_I_min_one _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_assoc _ _ _ _) ↪ der_eq_I_max_assoc _ _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_comm _ _ _) ↪ der_eq_I_max_comm _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_zero _ _) ↪ der_eq_I_max_zero _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_one _ _) ↪ der_eq_I_max_one _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_sym _ _ _) ↪ der_eq_I_min_sym _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_sym _ _ _) ↪ der_eq_I_max_sym _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_min_distrib _ _ _ _) ↪
     der_eq_I_min_distrib _ _ _ _
with der_eq_I_shift_n _ _ _ (der_eq_I_max_distrib _ _ _ _) ↪
     der_eq_I_max_distrib _ _ _ _
with der_eq_I_shift_n $id $sc $d (der_eq_I_cong_sym _ _ _ $di) ↪
     der_eq_I_cong_sym _ _ _ (der_eq_I_shift_n $id $sc $d $di)
with der_eq_I_shift_n $id $sc $d (der_eq_I_cong_min _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_min _ _ _ _ _ (der_eq_I_shift_n $id $sc $d $di) (der_eq_I_shift_n $id $sc $d $dj)
with der_eq_I_shift_n $id $sc $d (der_eq_I_cong_max _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_max _ _ _ _ _ (der_eq_I_shift_n $id $sc $d $di) (der_eq_I_shift_n $id $sc $d $dj)
// der_F_shift_n
with der_F_shift_n _ _ _ der_F_0 ↪ der_F_0
with der_F_shift_n _ _ _ der_F_1 ↪ der_F_1
with der_F_shift_n _ $sc $d (@der_F_eq0 _ $i $le)  ↪ der_F_eq0 (lenI_ctx_sctx $i $sc $d $le)
with der_F_shift_n _ $sc $d (@der_F_eq1 _ $i $le)  ↪ der_F_eq1 (lenI_ctx_sctx $i $sc $d $le)
with der_F_shift_n $id $sc $d (der_F_min $df $dg) ↪
     der_F_min (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
with der_F_shift_n $id $sc $d (der_F_max $df $dg) ↪
     der_F_max (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
// der_eq_F_shift_n
with der_eq_F_shift_n $id $sc $d (der_eq_F_refl _ _ $df) ↪
     der_eq_F_refl _ _ (der_F_shift_n $id $sc $d $df)
with der_eq_F_shift_n $id $sc $d (der_eq_F_sym _ _ _ $df) ↪
     der_eq_F_sym _ _ _ (der_eq_F_shift_n $id $sc $d $df)
with der_eq_F_shift_n $id $sc $d (der_eq_F_trans _ _ _ _ $df $dg) ↪
     der_eq_F_trans _ _ _ _ (der_eq_F_shift_n $id $sc $d $df) (der_eq_F_shift_n $id $sc $d $dg)
with der_eq_F_shift_n $id $sc $d (der_eq_F_isOne_zero _ _ _ $done) ↪
     der_eq_F_isOne_zero _ _ _ (der_isOne_shift_n $id $sc $d $done)
with der_eq_F_shift_n $id $sc $d (der_eq_F_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_F_isOne_max _ _ _ _ _ (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                        (der_eq_F_shift_n $id (SCF $sc $df) $d $dif) (der_eq_F_shift_n $id (SCF $sc $dg) $d $dig)
                        (der_isOne_shift_n $id $sc $d $done)
with der_eq_F_shift_n $id $sc $d (der_eq_F_isOne_one _ _ $done) ↪
     der_eq_F_isOne_one _ _ (der_isOne_shift_n $id $sc $d $done)
with der_eq_F_shift_n _ _ _ (der_eq_F_min_assoc _ _ _ _) ↪ der_eq_F_min_assoc _ _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_min_comm _ _ _) ↪ der_eq_F_min_comm _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_max_assoc _ _ _ _) ↪ der_eq_F_max_assoc _ _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_max_comm _ _ _) ↪ der_eq_F_max_comm _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_min_distrib _ _ _ _) ↪
     der_eq_F_min_distrib _ _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_max_distrib _ _ _ _) ↪
     der_eq_F_max_distrib _ _ _ _
with der_eq_F_shift_n _ _ _ (der_eq_F_empty _ _) ↪ der_eq_F_empty _ _
with der_eq_F_shift_n $id $sc $d (der_eq_F_cong_eq0 _ _ _ $deq) ↪
     der_eq_F_cong_eq0 _ _ _ (der_eq_I_shift_n $id $sc $d $deq)
with der_eq_F_shift_n $id $sc $d (der_eq_F_cong_eq1 _ _ _ $deq) ↪
     der_eq_F_cong_eq1 _ _ _ (der_eq_I_shift_n $id $sc $d $deq)
with der_eq_F_shift_n $id $sc $d (der_eq_F_cong_min _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_min _ _ _ _ _ (der_eq_F_shift_n $id $sc $d $deq1) (der_eq_F_shift_n $id $sc $d $deq2)
with der_eq_F_shift_n $id $sc $d (der_eq_F_cong_max _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_max _ _ _ _ _ (der_eq_F_shift_n $id $sc $d $deq1) (der_eq_F_shift_n $id $sc $d $deq2)
// der_isOne_shift_n
with der_isOne_shift_n _ _ _ (der_isOne_one _) ↪ der_isOne_one _
with der_isOne_shift_n $id $sc $d (der_isOne_zero _ _ $d0) ↪
     der_isOne_zero _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_empty _ _ $d0) ↪
     der_isOne_empty _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_min_intro _ _ _ $df $dg) ↪
     der_isOne_min_intro _ _ _ (der_isOne_shift_n $id $sc $d $df) (der_isOne_shift_n $id $sc $d $dg)
with der_isOne_shift_n $id $sc $d (der_isOne_min_elim_left _ _ _ $d0) ↪
     der_isOne_min_elim_left _ _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_min_elim_right _ _ _ $d0) ↪
     der_isOne_min_elim_right _ _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_max_intro_left _ _ _ $d0) ↪
     der_isOne_max_intro_left _ _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_max_intro_right _ _ _ $d0) ↪
     der_isOne_max_intro_right _ _ _ (der_isOne_shift_n $id $sc $d $d0)
with der_isOne_shift_n $id $sc $d (der_isOne_max_elim _ _ _ _ $df $dg $dl $dr $d1) ↪
     der_isOne_max_elim _ _ _ _ (der_F_shift_n $id $sc $d $df) (der_F_shift_n $id $sc $d $dg)
                                (der_isOne_shift_n $id (SCF $sc $df) $d $dl) (der_isOne_shift_n $id (SCF $sc $dg) $d $dr)
                                (der_isOne_shift_n $id $sc $d $d1)
with der_isOne_shift_n $id (SCF $sc _) $d (der_isOne_axiom _ _ $df) ↪
     der_isOne_axiom _ _ (der_F_shift_n $id $sc $d $df)
with der_isOne_shift_n _ (SCSucc $sc _) $d (der_isOne_weak _ _ _ _ $dt $df) ↪
     der_isOne_weak _ _ _ _ (der_shift_n _ $sc $d $dt) (der_isOne_shift_n _ $sc $d $df)
with der_isOne_shift_n _ (SCI $sc) $d (der_isOne_weakI _ _ $df) ↪
     der_isOne_weakI _ _ (der_isOne_shift_n _ $sc $d $df)
with der_isOne_shift_n _ (SCF $sc _) $d (der_isOne_weakF _ _ _ $dg $df) ↪
     der_isOne_weakF _ _ _ (der_F_shift_n _ $sc $d $dg) (der_isOne_shift_n _ $sc $d $df)
with der_isOne_shift_n _ $sc $d (der_isOne_cong _ _ _ $df $deq) ↪
     der_isOne_cong _ _ _ (der_isOne_shift_n _ $sc $d $df) (der_eq_F_shift_n _ $sc $d $deq);

// Implementation of der_shift{0,1}
rule der_shift0 $dA $dΓ $dt ↪ der_shift_n db0 (SC0 $dΓ) $dA $dt
with der_eq_shift0 $dA $dΓ $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA $deq
with der_shift1 $dA $dB $dΓ $dt ↪ der_shift_n db1 (SCSucc (SC0 $dΓ) $dA) $dB $dt;

// Implementation of der_shift
rule der_shift db0 (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ $d
with der_shift (dbsucc $id) (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ (der_shift $id $dΓ $d)
with der_shift $id (der_context_PushI _ $dΓ) $d ↪ der_Ishift0 $dΓ (der_shift $id $dΓ $d)
with der_shift $id (der_context_PushF _ _ $df $dΓ) $d ↪ der_weakF $dΓ (der_shift $id $dΓ $d) $df;

// Implementation of der_eq_shift
rule der_eq_shift db0 (der_context_Push _ _ _ $dA $dΓ) $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA $deq
with der_eq_shift (dbsucc $id) (der_context_Push _ _ _ $dA $dΓ) $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA (der_eq_shift $id $dΓ $deq)
with der_eq_shift $id (der_context_PushI _ $dΓ) $deq ↪ der_eq_Ishift0 $dΓ (der_eq_shift $id $dΓ $deq)
with der_eq_shift $id (der_context_PushF _ _ $df $dΓ) $deq ↪ der_eq_weakF $dΓ (der_eq_shift $id $dΓ $deq) $df;

// Generic der_Ishift
constant symbol IShiftContext : Context → DBId → TYPE;
symbol isc_to_ctx [Γ : Context] [id : DBId] : IShiftContext Γ id → Context;
symbol isc_to_sctx [Γ : Context] [id : DBId] : IShiftContext Γ id → Context;
symbol isc_to_dctx [Γ : Context] [id : DBId] (sc : IShiftContext Γ id) : der_context (isc_to_ctx sc);
symbol isc_to_dsctx [Γ : Context] [id : DBId] (sc : IShiftContext Γ id) : der_context (isc_to_sctx sc);
constant symbol ISC0 [Γ : Context] : der_context Γ → IShiftContext Γ db0;
constant symbol ISCSucc [Γ : Context] [s : Lev] [A : Term] [id : DBId] (sc : IShiftContext Γ id) :
  der (isc_to_ctx sc) A (tuniv s) (lsuc s) → IShiftContext Γ id;
constant symbol ISCI [Γ : Context] [id : DBId] (sc : IShiftContext Γ id) : IShiftContext Γ (dbsucc id);
constant symbol ISCF [Γ : Context] [f : FTerm] [id : DBId] (sc : IShiftContext Γ id) :
  der_F (isc_to_ctx sc) f → IShiftContext Γ id;
rule isc_to_ctx (@ISC0 $Γ _) ↪ $Γ
with isc_to_ctx (@ISCSucc _ $s $A _ $sc _) ↪ Push $A $s (isc_to_ctx $sc)
with isc_to_ctx (ISCI $sc) ↪ PushI (isc_to_ctx $sc)
with isc_to_ctx (@ISCF _ $f _ $sc _) ↪ PushF $f (isc_to_ctx $sc)
with isc_to_sctx (@ISC0 $Γ _) ↪ PushI $Γ
with isc_to_sctx (@ISCSucc _ $s $A $id $sc _) ↪ Push (Ishift $id $A) $s (isc_to_sctx $sc)
with isc_to_sctx (ISCI $sc) ↪ PushI (isc_to_sctx $sc)
with isc_to_sctx (@ISCF _ $f $id $sc _) ↪ PushF (IshiftF $id $f) (isc_to_sctx $sc);
rule isc_to_dctx (ISC0 $dΓ) ↪ $dΓ
with isc_to_dctx (ISCSucc $sc $d) ↪ der_context_Push _ _ _ $d (isc_to_dctx $sc)
with isc_to_dctx (ISCI $sc) ↪ der_context_PushI _ (isc_to_dctx $sc)
with isc_to_dctx (ISCF $sc $d) ↪ der_context_PushF _ _ $d (isc_to_dctx $sc);


symbol Ishiftget_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : IShiftContext Γ id) :
  TEq (shiftgetΓ (isc_to_sctx sc) i) (Ishift id (shiftgetΓ (isc_to_ctx sc) i));
rule Ishiftget_ctx_sctx db0 (ISC0 _) ↪ TRefl _
with Ishiftget_ctx_sctx (dbsucc _) (ISC0 _) ↪ TRefl _
with @Ishiftget_ctx_sctx _ $id db0 (@ISCSucc _ _ $A _ _ _) ↪ aux_teq_shift_Ishift db0 $id $A
with @Ishiftget_ctx_sctx _ $id (dbsucc $i) (ISCSucc $sc _) ↪
     teq_trans (Jcong Shift (Ishiftget_ctx_sctx $i $sc))
               (aux_teq_shift_Ishift db0 $id (shiftgetΓ (isc_to_ctx $sc) $i))
with @Ishiftget_ctx_sctx _ (dbsucc $id) $i (ISCI $sc) ↪
     teq_trans (Jcong IShift (Ishiftget_ctx_sctx $i $sc))
               (aux_teq_Ishift_Ishift db0 $id (shiftgetΓ (isc_to_ctx $sc) $i) (dble_0_n $id))
with Ishiftget_ctx_sctx $i (ISCF $sc _) ↪ Ishiftget_ctx_sctx $i $sc;

symbol getS_isc_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : IShiftContext Γ id) :
  LEq (getS (isc_to_sctx sc) i) (getS (isc_to_ctx sc) i);
rule getS_isc_ctx_sctx _ (ISC0 _) ↪ LRefl _
with getS_isc_ctx_sctx db0 (ISCSucc _ _) ↪ LRefl _
with getS_isc_ctx_sctx (dbsucc $i) (ISCSucc $sc _) ↪ getS_isc_ctx_sctx $i $sc
with getS_isc_ctx_sctx $i (ISCI $sc) ↪ getS_isc_ctx_sctx $i $sc
with getS_isc_ctx_sctx $i (ISCF $sc _) ↪ getS_isc_ctx_sctx $i $sc;

symbol len_isc_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : IShiftContext Γ id) :
  DBLe (dbsucc i) (len (isc_to_ctx sc)) → DBLe (dbsucc i) (len (isc_to_sctx sc));
rule len_isc_ctx_sctx _ (ISC0 _) $h ↪ $h
with len_isc_ctx_sctx db0 (ISCSucc _ _) _ ↪ dble_n_S (dble_0_n _)
with len_isc_ctx_sctx (dbsucc $i) (ISCSucc $sc _) $h ↪ dble_n_S (len_isc_ctx_sctx $i $sc (dble_S_n $h))
with len_isc_ctx_sctx $i (ISCI $sc) $h ↪ len_isc_ctx_sctx $i $sc $h
with len_isc_ctx_sctx $i (ISCF $sc _) $h ↪ len_isc_ctx_sctx $i $sc $h;

symbol lenI_isc_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : IShiftContext Γ id) :
  DBLe (dbsucc i) (lenI (isc_to_ctx sc)) → DBLe (dbsucc (dbshift id i)) (lenI (isc_to_sctx sc));
rule lenI_isc_ctx_sctx _ (ISC0 _) $h ↪ dble_n_S $h
with lenI_isc_ctx_sctx $id (ISCSucc $sc _) $h ↪ lenI_isc_ctx_sctx $id $sc $h
with lenI_isc_ctx_sctx db0 (ISCI _) _ ↪ dble_n_S (dble_0_n _)
with lenI_isc_ctx_sctx (dbsucc $i) (ISCI $sc) $h ↪ dble_n_S (lenI_isc_ctx_sctx $i $sc (dble_S_n $h))
with lenI_isc_ctx_sctx $i (ISCF $sc _) $h ↪ lenI_isc_ctx_sctx $i $sc $h;

symbol der_Ishift_n [Γ : Context] [s : Lev] [t T : Term] (id : DBId)
                   (sc : IShiftContext Γ id) (d : der (isc_to_ctx sc) t T s)
                   : der (isc_to_sctx sc) (Ishift id t) (Ishift id T) s;

symbol der_eq_Ishift_n [Γ : Context] [s : Lev] [T t1 t2 : Term] (id : DBId)
                      (sc : IShiftContext Γ id) (deq : der_eq (isc_to_ctx sc) t1 t2 T s) :
  der_eq (isc_to_sctx sc) (Ishift id t1) (Ishift id t2) (Ishift id T) s;
symbol der_I_Ishift_n [Γ : Context] [t : ITerm] (id : DBId)
                   (sc : IShiftContext Γ id) (d : der_I (isc_to_ctx sc) t)
                   : der_I (isc_to_sctx sc) (IshiftI id t);
symbol der_eq_I_Ishift_n [Γ : Context] [t1 t2 : ITerm] (id : DBId)
                      (sc : IShiftContext Γ id) (deq : der_eq_I (isc_to_ctx sc) t1 t2) :
  der_eq_I (isc_to_sctx sc) (IshiftI id t1) (IshiftI id t2);
symbol der_F_Ishift_n [Γ : Context] [f : FTerm] (id : DBId)
                   (sc : IShiftContext Γ id) (d : der_F (isc_to_ctx sc) f)
                   : der_F (isc_to_sctx sc) (IshiftF id f);
symbol der_eq_F_Ishift_n [Γ : Context] [t1 t2 : FTerm] (id : DBId)
                      (sc : IShiftContext Γ id) (deq : der_eq_F (isc_to_ctx sc) t1 t2) :
  der_eq_F (isc_to_sctx sc) (IshiftF id t1) (IshiftF id t2);
symbol der_isOne_Ishift_n [Γ : Context] [f : FTerm] (id : DBId)
                   (sc : IShiftContext Γ id) (d : der_isOne (isc_to_ctx sc) f)
                   : der_isOne (isc_to_sctx sc) (IshiftF id f);

symbol test [Γ : Context] [s s' : Lev] (id : DBId)
            (sc : IShiftContext Γ id) (f : FTerm) (id' : DBId) (i : ITerm)
            (deqi : der_eq_I (isc_to_ctx sc) (itvar id') i) :
  der_eq_F (isc_to_sctx sc) (IshiftF id (fteq0 id'))
         (IshiftF id (IsubstF id' i (fteq0 id'))) ≔
begin
  assume Γ s s' id sc f id' i deqi;
  refine FJeq (FTRefl _) _ (der_eq_F_cong_eq0 _ (dbshift id id') (IshiftI id i) (der_eq_I_Ishift_n id sc deqi));
  simplify;
  refine fteq_trans _ (fteq_inv (aux_teq_shift_dbselectF id id' id' (substeq0 i) (fteq0 id') (fteq0 (dbprev id'))));
  refine fteq_trans (aux_dbselectF_spec_eq _ _ (substeq0 (IshiftI id i)) (fteq0 (dbshift id id')) (fteq0 (dbprev (dbshift id id'))) (DBRefl (dbshift id id'))) _;
  refine fteq_trans _ (fteq_inv (aux_dbselectF_spec_eq _ _ (IshiftF id (substeq0 i)) (IshiftF id (fteq0 id')) (IshiftF id (fteq0 (dbprev id'))) (DBRefl id')));
  refine fteq_trans _ (aux_teq_Ishift_substeq0 id i);
  refine FTRefl _;
end;
print test;

symbol der_context_Ishift_n [Γ : Context] (id i : DBId)
                           (sc : IShiftContext Γ id) :
  DBLe (dbsucc i) (len (isc_to_ctx sc)) →
  der (isc_to_sctx sc) (tvar i) (Ishift id (shiftgetΓ (isc_to_ctx sc) i)) (getS (isc_to_ctx sc) i) ≔
begin
  assume Γ id i sc h;
  refine JT (Ishiftget_ctx_sctx i sc) _;
  refine Jl (getS_isc_ctx_sctx i sc) _;
  refine der_var _;
  refine len_isc_ctx_sctx i sc h
end;

rule isc_to_dsctx (ISC0 $dΓ) ↪ der_context_PushI _ $dΓ
with isc_to_dsctx (ISCSucc $sc $dA) ↪ der_context_Push _ _ _ (der_Ishift_n _ $sc $dA) (isc_to_dsctx $sc)
with isc_to_dsctx (ISCI $sc) ↪ der_context_PushI _ (isc_to_dsctx $sc)
with isc_to_dsctx (ISCF $sc $df) ↪ der_context_PushF _ _ (der_F_Ishift_n _ $sc $df) (isc_to_dsctx $sc);

// der_Ishift_n
rule der_Ishift_n $id $sc (der_empty_face $d1) ↪ der_empty_face (der_isOne_Ishift_n $id $sc $d1)
with der_Ishift_n $id $sc (der_union_face $df $dg $d1 $d2 $dfg) ↪
     der_union_face (der_F_Ishift_n $id $sc $df)
                    (der_F_Ishift_n $id $sc $dg)
                    (der_Ishift_n $id (ISCF $sc $df) $d1)
                    (der_Ishift_n $id (ISCF $sc $dg) $d2)
                    (der_isOne_Ishift_n $id $sc $dfg)
with der_Ishift_n $id $sc (@der_var _ $i $le) ↪ der_context_Ishift_n $id $i $sc $le
with der_Ishift_n _   _  der_univ ↪ der_univ
with der_Ishift_n $id $sc (der_pi $dA $dB) ↪
     der_pi (der_Ishift_n $id $sc $dA)
            (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
with der_Ishift_n $id $sc (der_abs $dA $dB $dt) ↪
     der_abs (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
             (der_Ishift_n $id (ISCSucc $sc $dA) $dt)
with der_Ishift_n $id $sc (der_app $A $t $u $B $dA $dB $dt $du) ↪
     JT (aux_teq_subst_Ishift db0 $id $u $B)
     (der_app (Ishift $id $A) (Ishift $id $t) (Ishift $id $u) (Ishift $id $B)
             (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
             (der_Ishift_n $id $sc $dt) (der_Ishift_n $id $sc $du))
with der_Ishift_n $id $sc (der_type_conv $du $deq) ↪
     der_type_conv (der_Ishift_n $id $sc $du) (der_eq_Ishift_n $id $sc $deq)
with der_Ishift_n _   _  der_nat ↪ der_nat
with der_Ishift_n _   _  der_zero ↪ der_zero
with der_Ishift_n $id $sc (der_suc $du) ↪
     der_suc (der_Ishift_n $id $sc $du)
with der_Ishift_n $id $sc (@der_rec _ _ _ $P _ _ _ $dP $dz $dH $dn) ↪
     der_rec (der_Ishift_n $id $sc $dP) (der_Ishift_n $id $sc $dz)
             (JT (Jpi (TRefl _) (Jpi (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))
                                     (Japp (teq_trans (teq_inv (aux_teq_shift_Ishift db0 $id (Shift $P)))
                                                      (Jcong Shift (teq_inv (aux_teq_shift_Ishift db0 $id $P)))) (TRefl _))))
                 (der_Ishift_n $id $sc $dH))
             (der_Ishift_n $id $sc $dn)
with der_Ishift_n $id $sc (der_sig $dA $dB) ↪
     der_sig (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
with der_Ishift_n $id $sc (der_pair $dA $dB $du $dv) ↪
     der_pair (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
              (der_Ishift_n $id $sc $du) (der_Ishift_n $id $sc $dv)
with der_Ishift_n $id $sc (der_p1 $dA $dB $dp) ↪
     der_p1 (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
            (der_Ishift_n $id $sc $dp)
with der_Ishift_n $id $sc (der_p2 $dA $dB $dp) ↪
     der_p2 (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
            (der_Ishift_n $id $sc $dp)
with der_Ishift_n $id $sc (der_sum $dA $dB) ↪
     der_sum (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
with der_Ishift_n $id $sc (der_injl $dA $dB $dp) ↪
     der_injl (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
            (der_Ishift_n $id $sc $dp)
with der_Ishift_n $id $sc (der_injr $dA $dB $dp) ↪
     der_injr (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
            (der_Ishift_n $id $sc $dp)
with der_Ishift_n $id $sc (@der_case _ _ _ _ _ _ $P _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_case (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
              (der_Ishift_n $id $sc $dP)
              (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHa))
              (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHb))
              (der_Ishift_n $id $sc $dx)
with der_Ishift_n $id $sc (@der_path _ _ $A _ _ $dA $dx $dy) ↪
     der_path (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
              (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
              (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
with der_Ishift_n $id $sc (@der_lamP _ _ _ $t $dA $dt) ↪
     JT (teq_inv (Jpath (TRefl _) (teq_Ishift_Isubst $id it0 $t)
                        (teq_Ishift_Isubst $id it1 $t)))
        (der_lamP (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dt))
with der_Ishift_n $id $sc (der_appP $A _ _ _ $i $dA $dx $dy $dt $di) ↪
     JT (teq_inv (teq_Ishift_Isubst $id $i $A))
        (der_appP _ _ _ _ _ (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                            (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
                            (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
                            (der_Ishift_n $id $sc $dt) (der_I_Ishift_n $id $sc $di))
with der_Ishift_n $id $sc (der_sys $dA $df $dg $du $dv $d1fg $deq) ↪
     der_sys (der_Ishift_n $id $sc $dA) (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
             (der_Ishift_n $id (ISCF $sc $df) $du) (der_Ishift_n $id (ISCF $sc $dg) $dv)
             (der_isOne_Ishift_n $id $sc $d1fg)
             (der_eq_Ishift_n $id (ISCF $sc (der_F_min $df $dg)) $deq)
with der_Ishift_n $id $sc (der_sys_empty $dA $d1) ↪
     der_sys_empty (der_Ishift_n $id $sc $dA) (der_isOne_Ishift_n $id $sc $d1)
with der_Ishift_n $id $sc (@der_transp _ _ $A _ _ $dA $df $du $deq) ↪
     JT (teq_inv (teq_Ishift_Isubst $id it1 $A))
        (der_transp (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_F_Ishift_n $id $sc $df)
                    (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $du))
                    (Jeq (TRefl _) (TRefl _) (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                                        (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                         (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deq)))
with der_Ishift_n $id $sc (@der_hcomp _ _ $A _ $u _ $dA $df $du $du0 $deq) ↪
     der_hcomp (der_Ishift_n $id $sc $dA) (der_F_Ishift_n $id $sc $df)
               (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $A (dble_0_n $id)))
                   (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $du))
               (der_Ishift_n $id $sc $du0)
               (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
// der_eq_Ishift_n
with der_eq_Ishift_n $id $sc (der_eq_refl _ $s $u $A $du) ↪
     der_eq_refl _ $s (Ishift $id $u) (Ishift $id $A) (der_Ishift_n $id $sc $du)
with der_eq_Ishift_n $id $sc (der_eq_trans _ $s $u $v $w $A $duv $dvw) ↪
     der_eq_trans _ $s (Ishift $id $u) (Ishift $id $v) (Ishift $id $w) (Ishift $id $A)
                       (der_eq_Ishift_n $id $sc $duv) (der_eq_Ishift_n $id $sc $dvw)
with der_eq_Ishift_n $id $sc (der_eq_sym _ $s $u $v $A $deq) ↪
     der_eq_sym _ $s (Ishift $id $u) (Ishift $id $v) (Ishift $id $A) (der_eq_Ishift_n $id $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_conv _ $s $t1 $t2 $T1 $T2 $deqt $deqT) ↪
     der_eq_conv _ $s (Ishift $id $t1) (Ishift $id $t2) (Ishift $id $T1) (Ishift $id $T2)
                      (der_eq_Ishift_n $id $sc $deqt) (der_eq_Ishift_n $id $sc $deqT)
with der_eq_Ishift_n $id $sc (der_eq_isOne_zero _ $s $A $u $v $d1) ↪
     der_eq_isOne_zero _ $s (Ishift $id $A) (Ishift $id $u) (Ishift $id $v)
                            (der_isOne_Ishift_n $id $sc $d1)
with der_eq_Ishift_n $id $sc (der_eq_isOne_max _ $s $A $u $v $f $g $df $dg $deqf $deqg $d1) ↪
     der_eq_isOne_max _ $s (Ishift $id $A) (Ishift $id $u) (Ishift $id $v) (IshiftF $id $f) (IshiftF $id $g)
                      (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                      (der_eq_Ishift_n $id (ISCF $sc $df) $deqf)
                      (der_eq_Ishift_n $id (ISCF $sc $dg) $deqg)
                      (der_isOne_Ishift_n $id $sc $d1)
with der_eq_Ishift_n $id $sc (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du) ↪
     der_eq_beta _ $s $s' (Ishift $id $u) (Ishift $id $A) (Ishift $id $t) (Ishift $id $B)
                        (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
                        (der_Ishift_n $id (ISCSucc $sc $dA) $dt) (der_Ishift_n $id $sc $du)
with der_eq_Ishift_n $id $sc (der_eq_eta _ $s $s' $A $B $f $dA $dB $df) ↪
     Jeq (TRefl _) (Jabs (TRefl _) (Japp (aux_teq_shift_Ishift db0 $id $f) (TRefl _))) (TRefl _)
         (der_eq_eta _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $f)
                     (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
                     (der_Ishift_n $id $sc $df))
with der_eq_Ishift_n $id $sc (der_eq_rec_zero _ $s $s' $P $z $H $dP $dz $dH) ↪
     der_eq_rec_zero _ $s $s' (Ishift $id $P) (Ishift $id $z) (Ishift $id $H)
                     (der_Ishift_n $id $sc $dP) (der_Ishift_n $id $sc $dz)
                     (JT (Jpi (TRefl _) (Jpi (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))
                                             (Japp (teq_inv (teq_trans (Jcong Shift (aux_teq_shift_Ishift db0 $id $P))
                                                                       (aux_teq_shift_Ishift db0 $id (Shift $P)))) (TRefl _))))
                         (der_Ishift_n $id $sc $dH))
with der_eq_Ishift_n $id $sc (der_eq_rec_suc _ $s $s' $P $z $H $n $dP $dz $dH $dn) ↪
     der_eq_rec_suc _ $s $s' (Ishift $id $P) (Ishift $id $z) (Ishift $id $H) (Ishift $id $n)
                     (der_Ishift_n $id $sc $dP) (der_Ishift_n $id $sc $dz)
                     (JT (Jpi (TRefl _) (Jpi (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))
                                             (Japp (teq_inv (teq_trans (Jcong Shift (aux_teq_shift_Ishift db0 $id $P))
                                                                       (aux_teq_shift_Ishift db0 $id (Shift $P)))) (TRefl _))))
                         (der_Ishift_n $id $sc $dH))
                     (der_Ishift_n $id $sc $dn)
with der_eq_Ishift_n $id $sc (der_eq_p1 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p1 _ $s $s' (Ishift $id $A) (Ishift $id $u) (Ishift $id $B) (Ishift $id $v)
                      (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $du)
                      (der_Ishift_n $id (ISCSucc $sc $dA) $dB) (der_Ishift_n $id $sc $dv)
with der_eq_Ishift_n $id $sc (der_eq_p2 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p2 _ $s $s' (Ishift $id $A) (Ishift $id $u) (Ishift $id $B) (Ishift $id $v)
                      (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $du)
                      (der_Ishift_n $id (ISCSucc $sc $dA) $dB) (der_Ishift_n $id $sc $dv)
with der_eq_Ishift_n $id $sc (der_eq_pair _ $s $s' $A $B $t $u $dA $dB $dt $du $dp1 $dp2) ↪
     der_eq_pair _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $t) (Ishift $id $u)
                      (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
                      (der_Ishift_n $id $sc $dt) (der_Ishift_n $id $sc $du)
                      (der_eq_Ishift_n $id $sc $dp1) (der_eq_Ishift_n $id $sc $dp2)
with der_eq_Ishift_n $id $sc (der_eq_case_left _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_left _ $s $s' $m (Ishift $id $A) (Ishift $id $B) (Ishift $id $P)
                      (Ishift $id $Ha) (Ishift $id $Hb) (Ishift $id $a)
                      (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
                      (der_Ishift_n $id $sc $dP)
                      (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHa))
                      (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHb))
                      (der_Ishift_n $id $sc $da)
with der_eq_Ishift_n $id $sc (der_eq_case_right _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_right _ $s $s' $m (Ishift $id $A) (Ishift $id $B) (Ishift $id $P)
                       (Ishift $id $Ha) (Ishift $id $Hb) (Ishift $id $a)
                      (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB)
                      (der_Ishift_n $id $sc $dP)
                      (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHa))
                      (JT (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P)) (TRefl _))) (der_Ishift_n $id $sc $dHb))
                      (der_Ishift_n $id $sc $da)
with der_eq_Ishift_n $id $sc (der_eq_betaP _ $s $A $t $i $dA $dt $di) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id $i $A)) (TRefl _) (teq_inv (teq_Ishift_Isubst $id $i $t))
         (der_eq_betaP _ $s (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $t) (IshiftI $id $i)
                      (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dt)
                      (der_I_Ishift_n $id $sc $di))
with der_eq_Ishift_n $id $sc (der_eq_etaP _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     Jeq (TRefl _) (Jcong tlamP (JappP (aux_teq_Ishift_Ishift db0 $id $t (dble_0_n _)) (ITRefl _))) (TRefl _)
         (der_eq_etaP _ $s (Ishift (dbsucc $id) $A) (Ishift $id $t) (Ishift $id $x) (Ishift $id $y)
                           (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                           (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
                           (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
                           (der_Ishift_n $id $sc $dt))
with der_eq_Ishift_n $id $sc (der_eq_appP_zero _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it0 $A)) (TRefl _) (TRefl _)
         (der_eq_appP_zero _ $s (Ishift (dbsucc $id) $A) (Ishift $id $t) (Ishift $id $x) (Ishift $id $y)
                          (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                          (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
                          (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
                          (der_Ishift_n $id $sc $dt))
with der_eq_Ishift_n $id $sc (der_eq_appP_one _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 $A)) (TRefl _) (TRefl _)
         (der_eq_appP_one _ $s (Ishift (dbsucc $id) $A) (Ishift $id $t) (Ishift $id $x) (Ishift $id $y)
                          (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                          (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
                          (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
                          (der_Ishift_n $id $sc $dt))
with der_eq_Ishift_n $id $sc (der_eq_sys_left _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_left _ $s (Ishift $id $A) (IshiftF $id $f) (IshiftF $id $g) (Ishift $id $x) (Ishift $id $y)
                     (der_Ishift_n $id $sc $dA)
                     (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                     (der_Ishift_n $id (ISCF $sc $df) $dx) (der_Ishift_n $id (ISCF $sc $dg) $dy)
                     (der_eq_Ishift_n $id (ISCF $sc (der_F_min $df $dg)) $deq)
                     (der_isOne_Ishift_n $id $sc $d1)
with der_eq_Ishift_n $id $sc (der_eq_sys_right _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_right _ $s (Ishift $id $A) (IshiftF $id $f) (IshiftF $id $g) (Ishift $id $x) (Ishift $id $y) (der_Ishift_n $id $sc $dA)
                      (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                      (der_Ishift_n $id (ISCF $sc $df) $dx) (der_Ishift_n $id (ISCF $sc $dg) $dy)
                      (der_eq_Ishift_n $id (ISCF $sc (der_F_min $df $dg)) $deq)
                      (der_isOne_Ishift_n $id $sc $d1)
with der_eq_Ishift_n $id $sc (der_eq_transp _ $s $A $f $u $dA $df $du $deq $d1) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 $A)) (TRefl _) (TRefl _)
         (der_eq_transp _ $s (Ishift (dbsucc $id) $A) (IshiftF $id $f) (Ishift $id $u)
                        (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                        (der_F_Ishift_n $id $sc $df)
                        (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $du))
                        (Jeq (TRefl _) (TRefl _) (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                                            (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                             (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deq))
                        (der_isOne_Ishift_n $id $sc $d1))
with der_eq_Ishift_n $id $sc (der_eq_transp_pi _ $s $s' $A $B $f $u $v $dA $dB $df $deqA $deqB $du $dv) ↪
     Jeq (teq_trans (Jcong (λ t, apply1 t (Ishift $id $v)) (teq_inv (teq_Ishift_Isubst $id it1 $B)))
                    (aux_teq_subst_Ishift db0 $id $v (applyI1 $B it1)))
         (TRefl _)
         (Jtransp (teq_trans (Jcong (λ t, apply1 (Ishift (dbsucc $id) $B) t)
                                    (Jtransp (teq_trans (Jcong (λ t, applyI1 t (itmax (itvar db1) (itsym (itvar db0))))
                                                               (teq_trans (Jcong IShift1 (aux_teq_Ishift_Ishift db1 (dbsucc $id) $A dble_db0))
                                                                          (aux_teq_Ishift_Ishift db1 (dbsucc (dbsucc $id)) (IShift1 $A) dble_db0)))
                                                        (teq_inv (teq_Ishift_Isubst (dbsucc (dbsucc $id)) (itmax (itvar db1) (itsym (itvar db0)))
                                                                                    (IShift1 (IShift1 $A)))))
                                             (FJmax (aux_teq_IshiftF_IshiftF db0 $id $f (dble_0_n $id)) (FTRefl (fteq0 db0)))
                                             (aux_teq_Ishift_Ishift db0 $id $v (dble_0_n $id))))
                             (aux_teq_subst_Ishift db0 (dbsucc $id) (ttransp (applyI1 (IShift1 (IShift1 $A)) (itmax (itvar db1) (itsym (itvar db0))))
                                                                             (ftmax (IShiftF $f) (fteq0 db0)) (IShift $v)) $B))
                  (FTRefl _)
                  (Japp (TRefl _) (Jtransp (teq_trans (Jcong (λ t, applyI1 t (itsym (itvar db0))) (aux_teq_Ishift_Ishift db1 (dbsucc $id) $A dble_db0))
                                                      (teq_inv (teq_Ishift_Isubst (dbsucc $id) (itsym (itvar db0)) (IShift1 $A))))
                                           (FTRefl _) (TRefl _))))
         (der_eq_transp_pi _ $s $s' (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $B) (IshiftF $id $f) (Ishift $id $u) (Ishift $id $v)
                           (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCSucc (ISCI $sc) $dA) $dB)
                           (der_F_Ishift_n $id $sc $df)
                           (Jeq (TRefl _) (TRefl _)
                                (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                           (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                                (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqA))
                           (Jeq (TRefl _) (TRefl _)
                                (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $B it0) (dble_0_n $id)))
                                           (Jcong IShift (teq_Ishift_Isubst $id it0 $B)))
                                (der_eq_Ishift_n (dbsucc $id) (ISCSucc (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df))
                                                                       (der_weakF (pushΓI (isc_to_dctx $sc)) $dA (der_Ishift0F (isc_to_dctx $sc) $df)))
                                                 $deqB))
                           (JT (teq_Ishift_Isubst $id it0 (tpi $A $B)) (der_Ishift_n $id $sc $du))
                           (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dv)))
with der_eq_Ishift_n $id $sc (der_eq_transp_univ _ $s $f $A $df $dA) ↪
     der_eq_transp_univ _ $s (IshiftF $id $f) (Ishift $id $A)
                       (der_F_Ishift_n $id $sc $df) (der_Ishift_n $id $sc $dA)
with der_eq_Ishift_n $id $sc (der_eq_transp_zero _ $s $f $df) ↪
     der_eq_transp_zero _ $s (IshiftF $id $f) (der_F_Ishift_n $id $sc $df)
with der_eq_Ishift_n $id $sc (der_eq_transp_suc _ $s $f $n $df $dn) ↪
     der_eq_transp_suc _ $s (IshiftF $id $f) (Ishift $id $n) (der_F_Ishift_n $id $sc $df) (der_Ishift_n $id $sc $dn)
with der_eq_Ishift_n $id $sc (der_eq_transp_sig _ $s $s' $A $B $f $u $dA $dB $df $deqA $deqB $du) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 (tsig $A $B)))
         (TRefl _)
         (Jpair (TRefl _) (Jtransp (teq_trans (Jcong (λ t, apply1 (Ishift (dbsucc $id) $B) t) (teq_Ishift_transpfill $id $A $f (tp1 $u)))
                                              (aux_teq_subst_Ishift db0 (dbsucc $id) (ttranspFill $A $f (tp1 $u)) $B))
                                   (FTRefl (IshiftF $id $f))
                                   (TRefl (Ishift $id (tp2 $u)))))
         (der_eq_transp_sig _ $s $s' (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $B) (IshiftF $id $f) (Ishift $id $u)
                            (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCSucc (ISCI $sc) $dA) $dB)
                            (der_F_Ishift_n $id $sc $df)
                            (Jeq (TRefl _) (TRefl _)
                                 (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                            (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                                 (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqA))
                            (Jeq (TRefl (tuniv $s')) (TRefl _)
                                 (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $B it0) (dble_0_n $id)))
                                            (Jcong IShift (teq_Ishift_Isubst $id it0 $B)))
                                 (der_eq_Ishift_n (dbsucc $id) (ISCSucc (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df))
                                                                        (der_weakF (pushΓI (isc_to_dctx $sc)) $dA (der_Ishift0F (isc_to_dctx $sc) $df))) $deqB))
                            (JT (teq_Ishift_Isubst $id it0 (tsig $A $B)) (der_Ishift_n $id $sc $du)))
with der_eq_Ishift_n $id $sc (der_eq_transp_sum_left _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 (tsum $A $B))) (TRefl _) (TRefl _)
         (der_eq_transp_sum_left _ $s $s' (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $B) (IshiftF $id $f) (Ishift $id $a)
                                 (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dB)
                                 (der_F_Ishift_n $id $sc $df)
                                 (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $da))
                                 (Jeq (TRefl _) (TRefl _)
                                      (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                                 (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                                      (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqA))
                                 (Jeq (TRefl _) (TRefl _)
                                      (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $B it0) (dble_0_n $id)))
                                                 (Jcong IShift (teq_Ishift_Isubst $id it0 $B)))
                                      (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqB)))
with der_eq_Ishift_n $id $sc (der_eq_transp_sum_right _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 (tsum $A $B))) (TRefl _) (TRefl _)
         (der_eq_transp_sum_right _ $s $s' (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $B) (IshiftF $id $f) (Ishift $id $a)
                                 (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dB)
                                 (der_F_Ishift_n $id $sc $df)
                                 (JT (teq_Ishift_Isubst $id it0 $B) (der_Ishift_n $id $sc $da))
                                 (Jeq (TRefl _) (TRefl _)
                                      (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A it0) (dble_0_n $id)))
                                                 (Jcong IShift (teq_Ishift_Isubst $id it0 $A)))
                                      (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqA))
                                 (Jeq (TRefl _) (TRefl _)
                                      (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $B it0) (dble_0_n $id)))
                                                 (Jcong IShift (teq_Ishift_Isubst $id it0 $B)))
                                      (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqB)))
with der_eq_Ishift_n $id $sc (der_eq_transp_path _ $s $A $x $y $f $u $dA $dx $dy $df $du $deqA $deqx $deqy) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 (tpath $A $x $y))) (TRefl _)
         (Jcong tlamP
                (teq_trans
                 (Jcomp (teq_trans
                         (Jcong (λ t, applyI1 t (itvar db0))
                                (teq_trans
                                 (Jcong (λ t, applyI1 t (itvar db2))
                                        (teq_trans (Jcong (Ishift db2) (aux_teq_Ishift_Ishift db2 (dbsucc (dbsucc $id)) $A
                                                                                              (dble_n_S (dble_n_S (dble_0_n $id)))))
                                                   (aux_teq_Ishift_Ishift db2 (dbsucc (dbsucc (dbsucc $id))) (Ishift db2 $A)
                                                                          (dble_n_S (dble_n_S (dble_0_n (dbsucc $id)))))))
                                 (teq_inv (teq_Ishift_Isubst (dbsucc (dbsucc (dbsucc $id))) (itvar db2) (Ishift db2 (Ishift db2 $A))))))
                         (teq_inv (teq_Ishift_Isubst (dbsucc (dbsucc $id)) (itvar db0) (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)))))
                        (FJmax (aux_teq_IshiftF_IshiftF db0 $id $f (dble_0_n $id)) (FTRefl _))
                        (Jsys (fteq_trans (FJcong IShiftF (aux_teq_IshiftF_IshiftF db0 $id $f (dble_0_n $id)))
                                          (aux_teq_IshiftF_IshiftF db0 (dbsucc $id) (IShiftF $f) (dble_0_n (dbsucc $id))))
                              (FTRefl _)
                              (JappP (teq_trans (Jcong IShift (aux_teq_Ishift_Ishift db0 $id $u (dble_0_n $id)))
                                                (aux_teq_Ishift_Ishift db0 (dbsucc $id) (IShift $u) (dble_0_n (dbsucc $id))))
                                     (ITRefl (IshiftI (dbsucc (dbsucc $id)) (itvar db1))))
                              (Jsys (FTRefl _) (FTRefl _) (aux_teq_Ishift_Ishift db1 (dbsucc $id) $x dble_db0)
                                    (aux_teq_Ishift_Ishift db1 (dbsucc $id) $y dble_db0)))
                        (JappP (aux_teq_Ishift_Ishift db0 $id $u (dble_0_n $id)) (ITRefl (IshiftI (dbsucc $id) (itvar db0)))))
                 (teq_Ishift_comp (dbsucc $id) (applyI1 (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)) (itvar db0))
                                  (ftmax (IShiftF $f) (ftmax (fteq0 db0) (fteq1 db0)))
                                  (tsys (IShiftFN db1 $f) (ftmax (fteq0 db1) (fteq1 db1))
                                        (tappP (IShift (IShift $u)) (itvar db1))
                                        (tsys (fteq0 db1) (fteq1 db1) (IShift1 $x) (IShift1 $y)))
                                  (tappP (IShift $u) (itvar db0)))))
         (der_eq_transp_path _ $s (Ishift (dbsucc (dbsucc $id)) $A) (Ishift (dbsucc $id) $x) (Ishift (dbsucc $id) $y) (IshiftF $id $f) (Ishift $id $u)
                             (der_Ishift_n (dbsucc (dbsucc $id)) (ISCI (ISCI $sc)) $dA)
                             (JT (teq_Ishift_Isubst (dbsucc $id) it0 $A) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dx))
                             (JT (teq_Ishift_Isubst (dbsucc $id) it1 $A) (der_Ishift_n (dbsucc $id) (ISCI $sc) $dy))
                             (der_F_Ishift_n $id $sc $df)
                             (JT (teq_Ishift_Isubst $id it0 (tpath $A $x $y)) (der_Ishift_n $id $sc $du))
                             (Jeq (TRefl _) (TRefl _)
                                  (teq_trans (teq_inv (aux_teq_Ishift_Ishift db1 (dbsucc $id) (Isubst db1 it0 $A) dble_db0))
                                             (Jcong IShift1 (aux_teq_Ishift_Isubst db1 (dbsucc $id) it0 $A dble_db0)))
                                  (der_eq_Ishift_n (dbsucc (dbsucc $id))
                                                   (ISCF (ISCI (ISCI $sc)) (der_Ishift0F (isc_to_dctx (ISCI $sc))
                                                                                         (der_Ishift0F (isc_to_dctx $sc) $df)))
                                                   $deqA))
                             (Jeq (teq_Ishift_Isubst (dbsucc $id) it0 $A) (TRefl _)
                                  (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $x it0) (dble_0_n $id)))
                                             (Jcong IShift (teq_Ishift_Isubst $id it0 $x)))
                                  (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqx))
                             (Jeq (teq_Ishift_Isubst (dbsucc $id) it1 $A) (TRefl _)
                                  (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $y it0) (dble_0_n $id)))
                                             (Jcong IShift (teq_Ishift_Isubst $id it0 $y)))
                                  (der_eq_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $deqy)))
with der_eq_Ishift_n $id $sc (der_eq_hcomp _ $s $A $f $u $u0 $dA $df $du $du0 $deq $d1) ↪
     Jeq (TRefl _) (TRefl _) (teq_inv (teq_Ishift_Isubst $id it1 $u))
     (der_eq_hcomp _ $s (Ishift $id $A) (IshiftF $id $f) (Ishift (dbsucc $id) $u) (Ishift $id $u0)
                  (der_Ishift_n $id $sc $dA) (der_F_Ishift_n $id $sc $df)
                  (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $A (dble_0_n _)))
                      (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $du))
                  (der_Ishift_n $id $sc $du0)
                  (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
                  (der_isOne_Ishift_n $id $sc $d1))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_pi _ $s $s' $A $B $f $u $u0 $v $dA $dB $df $du $du0 $deq $dv) ↪
     Jeq (aux_teq_subst_Ishift db0 $id $v $B) (TRefl _)
         (Jhcomp (aux_teq_subst_Ishift db0 $id $v $B) (FTRefl _)
                                     (Japp (TRefl _) (aux_teq_Ishift_Ishift db0 $id $v (dble_0_n _))) (TRefl _))
     (der_eq_hcomp_pi _ $s $s' (Ishift $id $A) (Ishift $id $B) (IshiftF $id $f) (Ishift (dbsucc $id) $u) (Ishift $id $u0) (Ishift $id $v)
                     (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
                     (der_F_Ishift_n $id $sc $df)
                     (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id (tpi $A $B) (dble_0_n _)))
                         (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $du))
                     (der_Ishift_n $id $sc $du0)
                     (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
                     (der_Ishift_n $id $sc $dv))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_zero _ $s $f $n $df $dn $deq) ↪
     der_eq_hcomp_zero _ $s (IshiftF $id $f) (Ishift (dbsucc $id) $n) (der_F_Ishift_n $id $sc $df)
                       (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $dn)
                       (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $n) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_suc _ $s $f $n $n0 $df $dn $dn0 $deq) ↪
     der_eq_hcomp_suc _ $s (IshiftF $id $f) (Ishift (dbsucc $id) $n) (Ishift $id $n0) (der_F_Ishift_n $id $sc $df)
                       (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $dn)
                       (der_Ishift_n $id $sc $dn0)
                       (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $n) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_sig _ $s $s' $A $B $f $u $u0 $dA $dB $df $du $du0 $deq) ↪
     Jeq (TRefl _) (TRefl _)
         (Jpair (TRefl _)
                (teq_trans (Jcomp (teq_trans (teq_trans (Jcong (apply1 (IShift (Ishift $id $B))) (teq_Ishift_hfill $id $A $f (tp1 $u) (tp1 $u0)))
                                                        (Jcong (λ t, apply1 t (Ishift (dbsucc $id) (thfill $A $f (tp1 $u) (tp1 $u0))))
                                                               (aux_teq_Ishift_Ishift db0 $id $B (dble_0_n $id))))
                                             (aux_teq_subst_Ishift db0 (dbsucc $id) (thfill $A $f (tp1 $u) (tp1 $u0)) (IShift $B)))
                                  (FTRefl _) (TRefl _) (TRefl _))
                           (teq_Ishift_comp $id (apply1 (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))) $f (tp2 $u) (tp2 $u0))))
         (der_eq_hcomp_sig _ $s $s' (Ishift $id $A) (Ishift $id $B) (IshiftF $id $f) (Ishift (dbsucc $id) $u) (Ishift $id $u0)
                           (der_Ishift_n $id $sc $dA) (der_Ishift_n $id (ISCSucc $sc $dA) $dB)
                           (der_F_Ishift_n $id $sc $df)
                           (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id (tsig $A $B) (dble_0_n $id)))
                               (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $du))
                           (der_Ishift_n $id $sc $du0)
                           (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u) (der_eq_Ishift_n $id (ISCF $sc $df) $deq)))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_sum_left _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_left _ $s $s' (Ishift $id $A) (Ishift $id $B) (IshiftF $id $f) (Ishift (dbsucc $id) $a) (Ishift $id $a0)
                           (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB) (der_F_Ishift_n $id $sc $df)
                           (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $A (dble_0_n $id)))
                               (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $da))
                           (der_Ishift_n $id $sc $da0)
                           (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $a) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_sum_right _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_right _ $s $s' (Ishift $id $A) (Ishift $id $B) (IshiftF $id $f) (Ishift (dbsucc $id) $a) (Ishift $id $a0)
                           (der_Ishift_n $id $sc $dA) (der_Ishift_n $id $sc $dB) (der_F_Ishift_n $id $sc $df)
                           (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $B (dble_0_n $id)))
                               (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $da))
                           (der_Ishift_n $id $sc $da0)
                           (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $a) (der_eq_Ishift_n $id (ISCF $sc $df) $deq))
with der_eq_Ishift_n $id $sc (der_eq_hcomp_path _ $s $A $x $y $f $u $u0 $dA $dx $dy $df $du $du0 $deq) ↪
     Jeq (TRefl _) (TRefl _)
         (Jcong tlamP
                (Jhcomp (TRefl _)
                        (FJmax (aux_teq_IshiftF_IshiftF db0 $id $f (dble_0_n $id))
                               (FTRefl _))
                        (Jsys (FTRefl _) (FTRefl _)
                              (JappP (aux_teq_Ishift_Ishift db1 (dbsucc $id) $u dble_db0) (ITRefl _))
                              (Jsys (FTRefl _) (FTRefl _)
                                    (teq_trans (Jcong IShift (aux_teq_Ishift_Ishift db0 $id $x (dble_0_n $id)))
                                               (aux_teq_Ishift_Ishift db0 (dbsucc $id) (IShift $x) (dble_0_n (dbsucc $id))))
                                    (teq_trans (Jcong IShift (aux_teq_Ishift_Ishift db0 $id $y (dble_0_n $id)))
                                               (aux_teq_Ishift_Ishift db0 (dbsucc $id) (IShift $y) (dble_0_n (dbsucc $id))))))
                        (JappP (aux_teq_Ishift_Ishift db0 $id $u0 (dble_0_n $id)) (ITRefl _))))
         (der_eq_hcomp_path _ $s (Ishift (dbsucc $id) $A) (Ishift $id $x) (Ishift $id $y) (IshiftF $id $f) (Ishift (dbsucc $id) $u) (Ishift $id $u0)
                            (der_Ishift_n (dbsucc $id) (ISCI $sc) $dA)
                            (JT (teq_Ishift_Isubst $id it0 $A) (der_Ishift_n $id $sc $dx))
                            (JT (teq_Ishift_Isubst $id it1 $A) (der_Ishift_n $id $sc $dy))
                            (der_F_Ishift_n $id $sc $df)
                            (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id (tpath $A $x $y) (dble_0_n $id)))
                                (der_Ishift_n (dbsucc $id) (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) $df)) $du))
                            (der_Ishift_n $id $sc $du0)
                            (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u) (der_eq_Ishift_n $id (ISCF $sc $df) $deq)))
with der_eq_Ishift_n $id $sc (der_eq_cong_pi _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_pi _ $s $s' (Ishift $id $A1) (Ishift $id $A2) (Ishift $id $B1) (Ishift $id $B2)
                    (der_eq_Ishift_n $id $sc $deqA) (der_eq_Ishift_n $id (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $deqB)
                    (der_Ishift_n _ (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $dB1)
                    (der_Ishift_n _ (ISCSucc $sc (inv_eq_t2 (isc_to_dctx $sc) $deqA)) $dB2)
with der_eq_Ishift_n $id $sc (der_eq_cong_abs _ $s $s' $A1 $A2 $B $t1 $t2 $deqA $deqt $dB1 $dB2) ↪
     der_eq_cong_abs _ $s $s' (Ishift $id $A1) (Ishift $id $A2) (Ishift $id $B) (Ishift $id $t1) (Ishift $id $t2)
                     (der_eq_Ishift_n _ $sc $deqA) (der_eq_Ishift_n _ (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $deqt)
                     (der_Ishift_n _ (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $dB1)
                     (der_Ishift_n _ (ISCSucc $sc (inv_eq_t2 (isc_to_dctx $sc) $deqA)) $dB2)
with der_eq_Ishift_n $id $sc (der_eq_cong_app _ $s $s' $A $B $f1 $f2 $a1 $a2 $deqf $deqa) ↪
     der_eq_cong_app _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $f1) (Ishift $id $f2) (Ishift $id $a1) (Ishift $id $a2)
                            (der_eq_Ishift_n _ $sc $deqf) (der_eq_Ishift_n _ $sc $deqa)
with der_eq_Ishift_n $id $sc (der_eq_cong_suc _ $s $n $n' $deq) ↪
     der_eq_cong_suc _ $s (Ishift $id $n) (Ishift $id $n') (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_rec _ $s $s' $P1 $P2 $z1 $z2 $H1 $H2 $n1 $n2 $deqP $deqz $deqH $deqn) ↪
     der_eq_cong_rec _ $s $s' (Ishift $id $P1) (Ishift $id $P2) (Ishift $id $z1) (Ishift $id $z2)
                     (Ishift $id $H1) (Ishift $id $H2) (Ishift $id $n1) (Ishift $id $n2)
                     (der_eq_Ishift_n _ $sc $deqP) (der_eq_Ishift_n _ $sc $deqz)
                     (Jeq (Jpi (TRefl _) (Jpi (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P1)) (TRefl _))
                                             (Japp (teq_inv (teq_trans (Jcong Shift (aux_teq_shift_Ishift db0 $id $P1))
                                                                       (aux_teq_shift_Ishift db0 $id (Shift $P1)))) (TRefl _))))
                          (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqH))
                     (der_eq_Ishift_n _ $sc $deqn)
with der_eq_Ishift_n $id $sc (der_eq_cong_sig _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_sig _ $s $s' (Ishift $id $A1) (Ishift $id $A2) (Ishift $id $B1) (Ishift $id $B2)
                            (der_eq_Ishift_n _ $sc $deqA) (der_eq_Ishift_n _ (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $deqB)
                            (der_Ishift_n _ (ISCSucc $sc (inv_eq_t1 (isc_to_dctx $sc) $deqA)) $dB1)
                            (der_Ishift_n _ (ISCSucc $sc (inv_eq_t2 (isc_to_dctx $sc) $deqA)) $dB2)
with der_eq_Ishift_n $id $sc (der_eq_cong_pair _ $s $s' $A $B $a1 $a2 $b1 $b2 $deqa $deqb) ↪
     der_eq_cong_pair _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $a1) (Ishift $id $a2) (Ishift $id $b1) (Ishift $id $b2)
                      (der_eq_Ishift_n _ $sc $deqa) (der_eq_Ishift_n _ $sc $deqb)
with der_eq_Ishift_n $id $sc (der_eq_cong_p1 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p1 _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $p1) (Ishift $id $p2)
       (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_p2 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p2 _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $p1) (Ishift $id $p2)
       (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_sum _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB) ↪
     der_eq_cong_sum _ $s $s' (Ishift $id $A1) (Ishift $id $A2) (Ishift $id $B1) (Ishift $id $B2)
                            (der_eq_Ishift_n _ $sc $deqA) (der_eq_Ishift_n _ $sc $deqB)
with der_eq_Ishift_n $id $sc (der_eq_cong_injl _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injl _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $p1) (Ishift $id $p2)
       (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_injr _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injr _ $s $s' (Ishift $id $A) (Ishift $id $B) (Ishift $id $p1) (Ishift $id $p2)
       (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_case _ $s $s' $m $A1 $A2 $B1 $B2 $P1 $P2 $Ha1 $Ha2 $Hb1 $Hb2 $u $v $deqA $deqB $deqP $deqHa $deqHb $deq) ↪
     der_eq_cong_case _ $s $s' $m (Ishift $id $A1) (Ishift $id $A2) (Ishift $id $B1) (Ishift $id $B2) (Ishift $id $P1) (Ishift $id $P2)
                      (Ishift $id $Ha1) (Ishift $id $Ha2) (Ishift $id $Hb1) (Ishift $id $Hb2) (Ishift $id $u) (Ishift $id $v)
                      (der_eq_Ishift_n _ $sc $deqA) (der_eq_Ishift_n _ $sc $deqB) (der_eq_Ishift_n _ $sc $deqP)
                      (Jeq (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P1)) (TRefl _)))
                           (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqHa))
                      (Jeq (Jpi (TRefl _) (Japp (teq_inv (aux_teq_shift_Ishift db0 $id $P1)) (TRefl _)))
                           (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqHb))
                      (der_eq_Ishift_n _ $sc $deq)
with der_eq_Ishift_n $id $sc (der_eq_cong_path _ $s $A1 $A2 $a1 $a2 $b1 $b2 $deqA $deqa $deqb) ↪
     der_eq_cong_path _ $s (Ishift (dbsucc $id) $A1) (Ishift (dbsucc $id) $A2) (Ishift $id $a1) (Ishift $id $a2) (Ishift $id $b1) (Ishift $id $b2)
                           (der_eq_Ishift_n _ (ISCI $sc) $deqA)
                           (Jeq (teq_Ishift_Isubst $id it0 $A1) (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqa))
                           (Jeq (teq_Ishift_Isubst $id it1 $A1) (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqb))
with der_eq_Ishift_n $id $sc (der_eq_cong_lamP _ $s $A $a1 $a2 $deq) ↪
     Jeq (Jpath (TRefl _) (teq_inv (teq_Ishift_Isubst $id it0 $a1)) (teq_inv (teq_Ishift_Isubst $id it1 $a1))) (TRefl _) (TRefl _)
         (der_eq_cong_lamP _ $s (Ishift (dbsucc $id) $A) (Ishift (dbsucc $id) $a1) (Ishift (dbsucc $id) $a2)
                           (der_eq_Ishift_n _ (ISCI $sc) $deq))
with der_eq_Ishift_n $id $sc (der_eq_cong_appP _ $s $A $x $y $a1 $a2 $i1 $i2 $deq $deqi) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id $i1 $A)) (TRefl _) (TRefl _)
         (der_eq_cong_appP _ $s (Ishift (dbsucc $id) $A) (Ishift $id $x) (Ishift $id $y)
                           (Ishift $id $a1) (Ishift $id $a2) (IshiftI $id $i1) (IshiftI $id $i2)
                           (der_eq_Ishift_n _ $sc $deq) (der_eq_I_Ishift_n _ $sc $deqi))
with der_eq_Ishift_n $id $sc (der_eq_cong_sys _ $s $A $f1 $f2 $g1 $g2 $u1 $u2 $v1 $v2
                                                $deqf $deqg $dequ $deqv $du1 $du2 $dv1 $dv2 $done1 $done2 $deq1 $deq2) ↪
     der_eq_cong_sys _ $s (Ishift $id $A) (IshiftF $id $f1) (IshiftF $id $f2) (IshiftF $id $g1) (IshiftF $id $g2)
                     (Ishift $id $u1) (Ishift $id $u2) (Ishift $id $v1) (Ishift $id $v2)
                     (der_eq_F_Ishift_n $id $sc $deqf) (der_eq_F_Ishift_n $id $sc $deqg)
                     (der_eq_Ishift_n $id (ISCF $sc (inv_eq_F_t1 (isc_to_dctx $sc) $deqf)) $dequ)
                     (der_eq_Ishift_n $id (ISCF $sc (inv_eq_F_t1 (isc_to_dctx $sc) $deqg)) $deqv)
                     (der_Ishift_n $id (ISCF $sc (inv_eq_F_t1 (isc_to_dctx $sc) $deqf)) $du1)
                     (der_Ishift_n $id (ISCF $sc (inv_eq_F_t2 (isc_to_dctx $sc) $deqf)) $du2)
                     (der_Ishift_n $id (ISCF $sc (inv_eq_F_t1 (isc_to_dctx $sc) $deqg)) $dv1)
                     (der_Ishift_n $id (ISCF $sc (inv_eq_F_t2 (isc_to_dctx $sc) $deqg)) $dv2)
                     (der_isOne_Ishift_n $id $sc $done1) (der_isOne_Ishift_n $id $sc $done2)
                     (der_eq_Ishift_n $id (ISCF $sc (der_F_min (inv_eq_F_t1 (isc_to_dctx $sc) $deqf) (inv_eq_F_t1 (isc_to_dctx $sc) $deqg))) $deq1)
                     (der_eq_Ishift_n $id (ISCF $sc (der_F_min (inv_eq_F_t2 (isc_to_dctx $sc) $deqf) (inv_eq_F_t2 (isc_to_dctx $sc) $deqg))) $deq2)
with der_eq_Ishift_n $id $sc (der_eq_cong_transp _ $s $A1 $A2 $f1 $f2 $a1 $a2 $deqA $deqf $deqa $deqA1 $deqA2) ↪
     Jeq (teq_inv (teq_Ishift_Isubst $id it1 $A1)) (TRefl _) (TRefl _)
     (der_eq_cong_transp _ $s (Ishift (dbsucc $id) $A1) (Ishift (dbsucc $id) $A2) (IshiftF $id $f1) (IshiftF $id $f2) (Ishift $id $a1) (Ishift $id $a2)
                        (der_eq_Ishift_n _ (ISCI $sc) $deqA) (der_eq_F_Ishift_n _ $sc $deqf)
                        (Jeq (teq_Ishift_Isubst $id it0 $A1)  (TRefl _) (TRefl _) (der_eq_Ishift_n _ $sc $deqa))
                        (Jeq (TRefl _) (TRefl _) (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A1 it0) (dble_0_n _)))
                                                            (Jcong IShift (teq_Ishift_Isubst $id it0 $A1)))
                             (der_eq_Ishift_n _ (ISCI $sc) $deqA1))
                        (Jeq (TRefl _) (TRefl _) (teq_trans (teq_inv (aux_teq_Ishift_Ishift db0 $id (applyI1 $A2 it0) (dble_0_n _)))
                                                            (Jcong IShift (teq_Ishift_Isubst $id it0 $A2)))
                             (der_eq_Ishift_n _ (ISCI $sc) $deqA2)))
with der_eq_Ishift_n $id $sc (der_eq_cong_hcomp _ $s $A1 $A2 $f1 $f2 $u1 $u2 $v1 $v2 $deqA $deqf $dequ $deqv $du1 $du2 $dequv1 $dequv2) ↪
     der_eq_cong_hcomp _ $s (Ishift $id $A1) (Ishift $id $A2) (IshiftF $id $f1) (IshiftF $id $f2)
                            (Ishift (dbsucc $id) $u1) (Ishift (dbsucc $id) $u2) (Ishift $id $v1) (Ishift $id $v2)
                       (der_eq_Ishift_n _ $sc $deqA) (der_eq_F_Ishift_n _ $sc $deqf)
                       (Jeq (teq_inv (aux_teq_Ishift_Ishift db0 $id $A1 (dble_0_n _))) (TRefl _) (TRefl _)
                            (der_eq_Ishift_n _ (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) (inv_eq_F_t1 (isc_to_dctx $sc) $deqf))) $dequ))
                       (der_eq_Ishift_n _ $sc $deqv)
                       (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $A1 (dble_0_n _)))
                           (der_Ishift_n _ (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) (inv_eq_F_t1 (isc_to_dctx $sc) $deqf))) $du1))
                       (JT (teq_inv (aux_teq_Ishift_Ishift db0 $id $A2 (dble_0_n _)))
                           (der_Ishift_n _ (ISCF (ISCI $sc) (der_Ishift0F (isc_to_dctx $sc) (inv_eq_F_t2 (isc_to_dctx $sc) $deqf))) $du2))
                       (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u1)
                            (der_eq_Ishift_n _ (ISCF $sc (inv_eq_F_t1 (isc_to_dctx $sc) $deqf)) $dequv1))
                       (Jeq (TRefl _) (TRefl _) (teq_Ishift_Isubst $id it0 $u2)
                            (der_eq_Ishift_n _ (ISCF $sc (inv_eq_F_t2 (isc_to_dctx $sc) $deqf)) $dequv2))
// der_I_Ishift_n
with der_I_Ishift_n _ _ der_I_0 ↪ der_I_0
with der_I_Ishift_n _ _ der_I_1 ↪ der_I_1
with der_I_Ishift_n _ $sc (@der_I_var _ $i $le) ↪ der_I_var (lenI_isc_ctx_sctx $i $sc $le)
with der_I_Ishift_n $id $sc (der_I_sym $di) ↪ der_I_sym (der_I_Ishift_n $id $sc $di)
with der_I_Ishift_n $id $sc (der_I_min $da $db) ↪
     der_I_min (der_I_Ishift_n $id $sc $da) (der_I_Ishift_n $id $sc $db)
with der_I_Ishift_n $id $sc (der_I_max $da $db) ↪
     der_I_max (der_I_Ishift_n $id $sc $da) (der_I_Ishift_n $id $sc $db)
// der_eq_I_Ishift_n
with der_eq_I_Ishift_n $id $sc (der_eq_I_refl _ _ $di) ↪ der_eq_I_refl _ _ (der_I_Ishift_n $id $sc $di)
with der_eq_I_Ishift_n $id $sc (der_eq_I_sym _ _ _ $di) ↪ der_eq_I_sym _ _ _ (der_eq_I_Ishift_n $id $sc $di)
with der_eq_I_Ishift_n $id $sc (der_eq_I_trans _ _ _ _ $deq1 $deq2) ↪
     der_eq_I_trans _ _ _ _ (der_eq_I_Ishift_n $id $sc $deq1) (der_eq_I_Ishift_n $id $sc $deq2)
with der_eq_I_Ishift_n $id $sc (der_eq_I_isOne_zero _ _ _ $done) ↪
     der_eq_I_isOne_zero _ _ _ (der_isOne_Ishift_n $id $sc $done)
with der_eq_I_Ishift_n $id $sc (der_eq_I_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_I_isOne_max _ _ _ _ _ (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                        (der_eq_I_Ishift_n $id (ISCF $sc $df) $dif) (der_eq_I_Ishift_n $id (ISCF $sc $dg) $dig)
                        (der_isOne_Ishift_n $id $sc $done)
with der_eq_I_Ishift_n $id $sc (der_eq_I_isOne_eq0 _ _ $done) ↪
     der_eq_I_isOne_eq0 _ _ (der_isOne_Ishift_n $id $sc $done)
with der_eq_I_Ishift_n $id $sc (der_eq_I_isOne_eq1 _ _ $done) ↪
     der_eq_I_isOne_eq1 _ _ (der_isOne_Ishift_n $id $sc $done)
with der_eq_I_Ishift_n _ _ (der_eq_I_sym_sym _ _) ↪ der_eq_I_sym_sym _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_sym_zero _) ↪ der_eq_I_sym_zero _
with der_eq_I_Ishift_n _ _ (der_eq_I_sym_one _) ↪ der_eq_I_sym_one _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_assoc _ _ _ _) ↪ der_eq_I_min_assoc _ _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_comm _ _ _) ↪ der_eq_I_min_comm _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_zero _ _) ↪ der_eq_I_min_zero _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_one _ _) ↪ der_eq_I_min_one _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_assoc _ _ _ _) ↪ der_eq_I_max_assoc _ _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_comm _ _ _) ↪ der_eq_I_max_comm _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_zero _ _) ↪ der_eq_I_max_zero _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_one _ _) ↪ der_eq_I_max_one _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_sym _ _ _) ↪ der_eq_I_min_sym _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_sym _ _ _) ↪ der_eq_I_max_sym _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_min_distrib _ _ _ _) ↪
     der_eq_I_min_distrib _ _ _ _
with der_eq_I_Ishift_n _ _ (der_eq_I_max_distrib _ _ _ _) ↪
     der_eq_I_max_distrib _ _ _ _
with der_eq_I_Ishift_n $id $sc (der_eq_I_cong_sym _ _ _ $di) ↪
     der_eq_I_cong_sym _ _ _ (der_eq_I_Ishift_n $id $sc $di)
with der_eq_I_Ishift_n $id $sc (der_eq_I_cong_min _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_min _ _ _ _ _ (der_eq_I_Ishift_n $id $sc $di) (der_eq_I_Ishift_n $id $sc $dj)
with der_eq_I_Ishift_n $id $sc (der_eq_I_cong_max _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_max _ _ _ _ _ (der_eq_I_Ishift_n $id $sc $di) (der_eq_I_Ishift_n $id $sc $dj)
// der_F_Ishift_n
with der_F_Ishift_n _ _ der_F_0 ↪ der_F_0
with der_F_Ishift_n _ _ der_F_1 ↪ der_F_1
with der_F_Ishift_n _ $sc (@der_F_eq0 _ $i $le)  ↪ der_F_eq0 (lenI_isc_ctx_sctx $i $sc $le)
with der_F_Ishift_n _ $sc (@der_F_eq1 _ $i $le)  ↪ der_F_eq1 (lenI_isc_ctx_sctx $i $sc $le)
with der_F_Ishift_n $id $sc (der_F_min $df $dg) ↪
     der_F_min (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
with der_F_Ishift_n $id $sc (der_F_max $df $dg) ↪
     der_F_max (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
// der_eq_F_Ishift_n
with der_eq_F_Ishift_n $id $sc (der_eq_F_refl _ _ $df) ↪
     der_eq_F_refl _ _ (der_F_Ishift_n $id $sc $df)
with der_eq_F_Ishift_n $id $sc (der_eq_F_sym _ _ _ $df) ↪
     der_eq_F_sym _ _ _ (der_eq_F_Ishift_n $id $sc $df)
with der_eq_F_Ishift_n $id $sc (der_eq_F_trans _ _ _ _ $df $dg) ↪
     der_eq_F_trans _ _ _ _ (der_eq_F_Ishift_n $id $sc $df) (der_eq_F_Ishift_n $id $sc $dg)
with der_eq_F_Ishift_n $id $sc (der_eq_F_isOne_zero _ _ _ $done) ↪
     der_eq_F_isOne_zero _ _ _ (der_isOne_Ishift_n $id $sc $done)
with der_eq_F_Ishift_n $id $sc (der_eq_F_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_F_isOne_max _ _ _ _ _ (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                        (der_eq_F_Ishift_n $id (ISCF $sc $df) $dif) (der_eq_F_Ishift_n $id (ISCF $sc $dg) $dig)
                        (der_isOne_Ishift_n $id $sc $done)
with der_eq_F_Ishift_n $id $sc (der_eq_F_isOne_one _ _ $done) ↪
     der_eq_F_isOne_one _ _ (der_isOne_Ishift_n $id $sc $done)
with der_eq_F_Ishift_n _ _ (der_eq_F_min_assoc _ _ _ _) ↪ der_eq_F_min_assoc _ _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_min_comm _ _ _) ↪ der_eq_F_min_comm _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_max_assoc _ _ _ _) ↪ der_eq_F_max_assoc _ _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_max_comm _ _ _) ↪ der_eq_F_max_comm _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_min_distrib _ _ _ _) ↪
     der_eq_F_min_distrib _ _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_max_distrib _ _ _ _) ↪
     der_eq_F_max_distrib _ _ _ _
with der_eq_F_Ishift_n _ _ (der_eq_F_empty _ _) ↪ der_eq_F_empty _ _
with der_eq_F_Ishift_n $id $sc (der_eq_F_cong_eq0 _ $id' $i $deq) ↪
     FJeq (FTRefl _) (fteq_trans (fteq_trans (aux_dbselectF_spec_eq (dbshift $id $id') (dbshift $id $id')
                                                                    (substeq0 (IshiftI $id $i)) (fteq0 (dbshift $id $id'))
                                                                    (fteq0 (dbprev (dbshift $id $id'))) (DBRefl (dbshift $id $id')))
                                             (fteq_trans (fteq_trans (FTRefl (substeq0 (IshiftI $id $i)))
                                                                     (aux_teq_Ishift_substeq0 $id $i))
                                                         (fteq_inv (aux_dbselectF_spec_eq $id' $id' (IshiftF $id (substeq0 $i)) (IshiftF $id (fteq0 $id'))
                                                                                          (IshiftF $id (fteq0 (dbprev $id'))) (DBRefl $id')))))
                                 (fteq_inv (aux_teq_shift_dbselectF $id $id' $id' (substeq0 $i) (fteq0 $id') (fteq0 (dbprev $id')))))
          (der_eq_F_cong_eq0 (isc_to_sctx $sc) (dbshift $id $id') (IshiftI $id $i) (der_eq_I_Ishift_n $id $sc $deq))
with der_eq_F_Ishift_n $id $sc (der_eq_F_cong_eq1 _ $id' $i $deq) ↪
     FJeq (FTRefl _) (fteq_trans (fteq_trans (aux_dbselectF_spec_eq (dbshift $id $id') (dbshift $id $id')
                                                                    (substeq1 (IshiftI $id $i)) (fteq1 (dbshift $id $id'))
                                                                    (fteq1 (dbprev (dbshift $id $id'))) (DBRefl (dbshift $id $id')))
                                             (fteq_trans (fteq_trans (FTRefl (substeq1 (IshiftI $id $i)))
                                                                     (aux_teq_Ishift_substeq1 $id $i))
                                                         (fteq_inv (aux_dbselectF_spec_eq $id' $id' (IshiftF $id (substeq1 $i)) (IshiftF $id (fteq1 $id'))
                                                                                          (IshiftF $id (fteq1 (dbprev $id'))) (DBRefl $id')))))
                                 (fteq_inv (aux_teq_shift_dbselectF $id $id' $id' (substeq1 $i) (fteq1 $id') (fteq1 (dbprev $id')))))
          (der_eq_F_cong_eq1 (isc_to_sctx $sc) (dbshift $id $id') (IshiftI $id $i) (der_eq_I_Ishift_n $id $sc $deq))
with der_eq_F_Ishift_n $id $sc (der_eq_F_cong_min _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_min _ _ _ _ _ (der_eq_F_Ishift_n $id $sc $deq1) (der_eq_F_Ishift_n $id $sc $deq2)
with der_eq_F_Ishift_n $id $sc (der_eq_F_cong_max _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_max _ _ _ _ _ (der_eq_F_Ishift_n $id $sc $deq1) (der_eq_F_Ishift_n $id $sc $deq2)
// der_isOne_Ishift_n
with der_isOne_Ishift_n _ _ (der_isOne_one _) ↪ der_isOne_one _
with der_isOne_Ishift_n $id $sc (der_isOne_zero _ _ $d0) ↪
     der_isOne_zero _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_empty _ _ $d0) ↪
     der_isOne_empty _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_min_intro _ _ _ $df $dg) ↪
     der_isOne_min_intro _ _ _ (der_isOne_Ishift_n $id $sc $df) (der_isOne_Ishift_n $id $sc $dg)
with der_isOne_Ishift_n $id $sc (der_isOne_min_elim_left _ _ _ $d0) ↪
     der_isOne_min_elim_left _ _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_min_elim_right _ _ _ $d0) ↪
     der_isOne_min_elim_right _ _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_max_intro_left _ _ _ $d0) ↪
     der_isOne_max_intro_left _ _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_max_intro_right _ _ _ $d0) ↪
     der_isOne_max_intro_right _ _ _ (der_isOne_Ishift_n $id $sc $d0)
with der_isOne_Ishift_n $id $sc (der_isOne_max_elim _ _ _ _ $df $dg $dl $dr $d1) ↪
     der_isOne_max_elim _ _ _ _ (der_F_Ishift_n $id $sc $df) (der_F_Ishift_n $id $sc $dg)
                                (der_isOne_Ishift_n $id (ISCF $sc $df) $dl) (der_isOne_Ishift_n $id (ISCF $sc $dg) $dr)
                                (der_isOne_Ishift_n $id $sc $d1)
with der_isOne_Ishift_n $id (ISCF $sc _) (der_isOne_axiom _ _ $df) ↪
     der_isOne_axiom _ _ (der_F_Ishift_n $id $sc $df)
with der_isOne_Ishift_n _ (ISCSucc $sc _) (der_isOne_weak _ _ _ _ $dt $df) ↪
     der_isOne_weak _ _ _ _ (der_Ishift_n _ $sc $dt) (der_isOne_Ishift_n _ $sc $df)
with der_isOne_Ishift_n _ (ISCI $sc) (der_isOne_weakI _ _ $df) ↪
     der_isOne_weakI _ _ (der_isOne_Ishift_n _ $sc $df)
with der_isOne_Ishift_n _ (ISCF $sc _) (der_isOne_weakF _ _ _ $dg $df) ↪
     der_isOne_weakF _ _ _ (der_F_Ishift_n _ $sc $dg) (der_isOne_Ishift_n _ $sc $df)
with der_isOne_Ishift_n _ $sc (der_isOne_cong _ _ _ $df $deq) ↪
     der_isOne_cong _ _ _ (der_isOne_Ishift_n _ $sc $df) (der_eq_F_Ishift_n _ $sc $deq);

// definition of der_Ishift*
rule der_Ishift0 $dΓ $d ↪ der_Ishift_n db0 (ISC0 $dΓ) $d;
rule der_Ishift0F $dΓ $d ↪ der_F_Ishift_n db0 (ISC0 $dΓ) $d;
rule der_eq_Ishift0 $dΓ $d ↪ der_eq_Ishift_n db0 (ISC0 $dΓ) $d;
rule der_Ishift1 $dΓ $d ↪ der_Ishift_n db1 (ISCI (ISC0 $dΓ)) $d;

// Generic der_weakF
constant symbol FShiftContext : Context → TYPE;
symbol fsc_to_ctx [Γ : Context] : FShiftContext Γ → Context;
symbol fsc_to_sctx [Γ : Context] [f : FTerm] : der_F Γ f → FShiftContext Γ → Context;
symbol fsc_to_dctx [Γ : Context] (sc : FShiftContext Γ) : der_context (fsc_to_ctx sc);
symbol fsc_to_dsctx [Γ : Context] [f : FTerm] (df : der_F Γ f) (sc : FShiftContext Γ) : der_context (fsc_to_sctx df sc);
constant symbol FSC0 [Γ : Context] : der_context Γ → FShiftContext Γ;
constant symbol FSCSucc [Γ : Context] [s : Lev] [A : Term] (sc : FShiftContext Γ) :
  der (fsc_to_ctx sc) A (tuniv s) (lsuc s) → FShiftContext Γ;
constant symbol FSCI [Γ : Context] (sc : FShiftContext Γ) : FShiftContext Γ;
constant symbol FSCF [Γ : Context] [f : FTerm] (sc : FShiftContext Γ) :
  der_F (fsc_to_ctx sc) f → FShiftContext Γ;
rule fsc_to_ctx (@FSC0 $Γ _) ↪ $Γ
with fsc_to_ctx (@FSCSucc _ $s $A $sc _) ↪ Push $A $s (fsc_to_ctx $sc)
with fsc_to_ctx (FSCI $sc) ↪ PushI (fsc_to_ctx $sc)
with fsc_to_ctx (@FSCF _ $f $sc _) ↪ PushF $f (fsc_to_ctx $sc)
with @fsc_to_sctx _ $f _ (@FSC0 $Γ _) ↪ PushF $f $Γ
with fsc_to_sctx $df (@FSCSucc _ $s $A $sc _) ↪ Push $A $s (fsc_to_sctx $df $sc)
with fsc_to_sctx $df (FSCI $sc) ↪ PushI (fsc_to_sctx $df $sc)
with fsc_to_sctx $df (@FSCF _ $f $sc _) ↪ PushF $f (fsc_to_sctx $df $sc);
rule fsc_to_dctx (FSC0 $dΓ) ↪ $dΓ
with fsc_to_dctx (FSCSucc $sc $d) ↪ der_context_Push _ _ _ $d (fsc_to_dctx $sc)
with fsc_to_dctx (FSCI $sc) ↪ der_context_PushI _ (fsc_to_dctx $sc)
with fsc_to_dctx (FSCF $sc $d) ↪ der_context_PushF _ _ $d (fsc_to_dctx $sc);


symbol Fshiftget_ctx_sctx [Γ : Context] (i : DBId) (sc : FShiftContext Γ) [f : FTerm] (df : der_F Γ f) :
  TEq (shiftgetΓ (fsc_to_sctx df sc) i) (shiftgetΓ (fsc_to_ctx sc) i);
rule Fshiftget_ctx_sctx db0 (FSC0 _) _ ↪ TRefl _
with Fshiftget_ctx_sctx (dbsucc _) (FSC0 _) _ ↪ TRefl _
with Fshiftget_ctx_sctx db0 (FSCSucc _ _) _ ↪ TRefl _
with Fshiftget_ctx_sctx (dbsucc $i) (FSCSucc $sc _) $df ↪
     Jcong Shift (Fshiftget_ctx_sctx $i $sc $df)
with Fshiftget_ctx_sctx $i (FSCI $sc) $df ↪
     Jcong IShift (Fshiftget_ctx_sctx $i $sc $df)
with Fshiftget_ctx_sctx $i (FSCF $sc _) $df ↪ Fshiftget_ctx_sctx $i $sc $df;

symbol getS_fsc_ctx_sctx [Γ : Context] (i : DBId) (sc : FShiftContext Γ) [f : FTerm] (df : der_F Γ f) :
  LEq (getS (fsc_to_sctx df sc) i) (getS (fsc_to_ctx sc) i);
rule getS_fsc_ctx_sctx _ (FSC0 _) _ ↪ LRefl _
with getS_fsc_ctx_sctx db0 (FSCSucc _ _) _ ↪ LRefl _
with getS_fsc_ctx_sctx (dbsucc $i) (FSCSucc $sc _) $df ↪ getS_fsc_ctx_sctx $i $sc $df
with getS_fsc_ctx_sctx $i (FSCI $sc) $df ↪ getS_fsc_ctx_sctx $i $sc $df
with getS_fsc_ctx_sctx $i (FSCF $sc _) $df ↪ getS_fsc_ctx_sctx $i $sc $df;

symbol len_fsc_ctx_sctx [Γ : Context] (i : DBId) (sc : FShiftContext Γ) [f : FTerm] (df : der_F Γ f) :
  DBLe (dbsucc i) (len (fsc_to_ctx sc)) → DBLe (dbsucc i) (len (fsc_to_sctx df sc));
rule len_fsc_ctx_sctx _ (FSC0 _) _ $h ↪ $h
with len_fsc_ctx_sctx db0 (FSCSucc _ _) _ _ ↪ dble_n_S (dble_0_n _)
with len_fsc_ctx_sctx (dbsucc $i) (FSCSucc $sc _) $df $h ↪ dble_n_S (len_fsc_ctx_sctx $i $sc $df (dble_S_n $h))
with len_fsc_ctx_sctx $i (FSCI $sc) $df $h ↪ len_fsc_ctx_sctx $i $sc $df $h
with len_fsc_ctx_sctx $i (FSCF $sc _) $df $h ↪ len_fsc_ctx_sctx $i $sc $df $h;

symbol lenI_fsc_ctx_sctx [Γ : Context] (i : DBId) (sc : FShiftContext Γ) [f : FTerm] (df : der_F Γ f) :
  DBLe (dbsucc i) (lenI (fsc_to_ctx sc)) → DBLe (dbsucc i) (lenI (fsc_to_sctx df sc));
rule lenI_fsc_ctx_sctx _ (FSC0 _) _ $h ↪ $h
with lenI_fsc_ctx_sctx $id (FSCSucc $sc _) $df $h ↪ lenI_fsc_ctx_sctx $id $sc $df $h
with lenI_fsc_ctx_sctx db0 (FSCI _) _ _ ↪ dble_n_S (dble_0_n _)
with lenI_fsc_ctx_sctx (dbsucc $i) (FSCI $sc) $df $h ↪ dble_n_S (lenI_fsc_ctx_sctx $i $sc $df (dble_S_n $h))
with lenI_fsc_ctx_sctx $i (FSCF $sc _) $df $h ↪ lenI_fsc_ctx_sctx $i $sc $df $h;

symbol der_Fshift_n [Γ : Context] [s : Lev] [t T : Term] [f : FTerm]
                   (sc : FShiftContext Γ) (df : der_F Γ f)
                   (d : der (fsc_to_ctx sc) t T s)
                   : der (fsc_to_sctx df sc) t T s;

symbol der_eq_Fshift_n  [Γ : Context] [s : Lev] [t1 t2 T : Term] [f : FTerm]
                        (sc : FShiftContext Γ) (df : der_F Γ f)
                        (deq : der_eq (fsc_to_ctx sc) t1 t2 T s) :
  der_eq (fsc_to_sctx df sc) t1 t2 T s;
symbol der_I_Fshift_n [Γ : Context] [t : ITerm] [f : FTerm]
                   (sc : FShiftContext Γ) (df : der_F Γ f) (d : der_I (fsc_to_ctx sc) t)
                   : der_I (fsc_to_sctx df sc) t;
symbol der_eq_I_Fshift_n [Γ : Context] [t1 t2 : ITerm] [f : FTerm]
                      (sc : FShiftContext Γ) (df : der_F Γ f) (deq : der_eq_I (fsc_to_ctx sc) t1 t2) :
  der_eq_I (fsc_to_sctx df sc) t1 t2;
symbol der_F_Fshift_n [Γ : Context] [f : FTerm] [g : FTerm]
                   (sc : FShiftContext Γ) (df : der_F Γ g) (d : der_F (fsc_to_ctx sc) f)
                   : der_F (fsc_to_sctx df sc) f;
symbol der_eq_F_Fshift_n [Γ : Context] [t1 t2 : FTerm] [f : FTerm]
                      (sc : FShiftContext Γ) (df : der_F Γ f) (deq : der_eq_F (fsc_to_ctx sc) t1 t2) :
  der_eq_F (fsc_to_sctx df sc) t1 t2;
symbol der_isOne_Fshift_n [Γ : Context] [f g : FTerm]
                   (sc : FShiftContext Γ) (df : der_F Γ g) (d : der_isOne (fsc_to_ctx sc) f)
                   : der_isOne (fsc_to_sctx df sc) f;

symbol test3 [Γ : Context] [s s' : Lev] (id : DBId)
            (sc : IShiftContext Γ id) (f : FTerm) (id' : DBId) (i : ITerm)
            (deqi : der_eq_I (isc_to_ctx sc) (itvar id') i) :
  der_eq_F (isc_to_sctx sc) (IshiftF id (fteq0 id'))
         (IshiftF id (IsubstF id' i (fteq0 id'))) ≔
begin
  assume Γ s s' id sc f id' i deqi;
  refine FJeq (FTRefl _) _ (der_eq_F_cong_eq0 _ (dbshift id id') (IshiftI id i) (der_eq_I_Ishift_n id sc deqi));
  simplify;
  refine fteq_trans _ (fteq_inv (aux_teq_shift_dbselectF id id' id' (substeq0 i) (fteq0 id') (fteq0 (dbprev id'))));
  refine fteq_trans (aux_dbselectF_spec_eq _ _ (substeq0 (IshiftI id i)) (fteq0 (dbshift id id')) (fteq0 (dbprev (dbshift id id'))) (DBRefl (dbshift id id'))) _;
  refine fteq_trans _ (fteq_inv (aux_dbselectF_spec_eq _ _ (IshiftF id (substeq0 i)) (IshiftF id (fteq0 id')) (IshiftF id (fteq0 (dbprev id'))) (DBRefl id')));
  refine fteq_trans _ (aux_teq_Ishift_substeq0 id i);
  refine FTRefl _;
end;
print test3;

symbol der_context_Fshift_n [Γ : Context] (i : DBId)
                           (sc : FShiftContext Γ) [f : FTerm] (df : der_F Γ f) :
  DBLe (dbsucc i) (len (fsc_to_ctx sc)) →
  der (fsc_to_sctx df sc) (tvar i) (shiftgetΓ (fsc_to_ctx sc) i) (getS (fsc_to_ctx sc) i) ≔
begin
  assume Γ i sc f df h;
  refine JT (Fshiftget_ctx_sctx i sc df) _;
  refine Jl (getS_fsc_ctx_sctx i sc df) _;
  refine der_var _;
  refine len_fsc_ctx_sctx i sc df h
end;

rule fsc_to_dsctx $df (FSC0 $dΓ) ↪ der_context_PushF _ _ $df $dΓ
with fsc_to_dsctx $df (FSCSucc $sc $dA) ↪ der_context_Push _ _ _ (der_Fshift_n $sc $df $dA) (fsc_to_dsctx $df $sc)
with fsc_to_dsctx $df (FSCI $sc) ↪ der_context_PushI _ (fsc_to_dsctx $df $sc)
with fsc_to_dsctx $df (FSCF $sc $dg) ↪ der_context_PushF _ _ (der_F_Fshift_n $sc $df $dg) (fsc_to_dsctx $df $sc);

// der_Fshift_n
rule der_Fshift_n $sc $df (der_empty_face $d1) ↪ der_empty_face (der_isOne_Fshift_n $sc $df $d1)
with der_Fshift_n $sc $d (der_union_face $df $dg $d1 $d2 $dfg) ↪
     der_union_face (der_F_Fshift_n $sc $d $df)
                    (der_F_Fshift_n $sc $d $dg)
                    (der_Fshift_n (FSCF $sc $df) $d $d1)
                    (der_Fshift_n (FSCF $sc $dg) $d $d2)
                    (der_isOne_Fshift_n $sc $d $dfg)
with der_Fshift_n $sc $df (@der_var _ $i $le) ↪ der_context_Fshift_n $i $sc $df $le
with der_Fshift_n _   _  der_univ ↪ der_univ
with der_Fshift_n $sc $df (der_pi $dA $dB) ↪
     der_pi (der_Fshift_n $sc $df $dA)
            (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
with der_Fshift_n $sc $df (der_abs $dA $dB $dt) ↪
     der_abs (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
             (der_Fshift_n (FSCSucc $sc $dA) $df $dt)
with der_Fshift_n $sc $df (der_app $A $t $u $B $dA $dB $dt $du) ↪
     der_app $A $t $u $B
             (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
             (der_Fshift_n $sc $df $dt) (der_Fshift_n $sc $df $du)
with der_Fshift_n $sc $df (der_type_conv $du $deq) ↪
     der_type_conv (der_Fshift_n $sc $df $du) (der_eq_Fshift_n $sc $df $deq)
with der_Fshift_n _   _  der_nat ↪ der_nat
with der_Fshift_n _   _  der_zero ↪ der_zero
with der_Fshift_n $sc $df (der_suc $du) ↪
     der_suc (der_Fshift_n $sc $df $du)
with der_Fshift_n $sc $df (der_rec $dP $dz $dH $dn) ↪
     der_rec (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dz)
             (der_Fshift_n $sc $df $dH) (der_Fshift_n $sc $df $dn)
with der_Fshift_n $sc $df (der_sig $dA $dB) ↪
     der_sig (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
with der_Fshift_n $sc $df (der_pair $dA $dB $du $dv) ↪
     der_pair (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
              (der_Fshift_n $sc $df $du) (der_Fshift_n $sc $df $dv)
with der_Fshift_n $sc $df (der_p1 $dA $dB $dp) ↪
     der_p1 (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
            (der_Fshift_n $sc $df $dp)
with der_Fshift_n $sc $df (der_p2 $dA $dB $dp) ↪
     der_p2 (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
            (der_Fshift_n $sc $df $dp)
with der_Fshift_n $sc $df (der_sum $dA $dB) ↪
     der_sum (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
with der_Fshift_n $sc $df (der_injl $dA $dB $dp) ↪
     der_injl (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
            (der_Fshift_n $sc $df $dp)
with der_Fshift_n $sc $df (der_injr $dA $dB $dp) ↪
     der_injr (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
            (der_Fshift_n $sc $df $dp)
with der_Fshift_n $sc $df (der_case $dA $dB $dP $dHa $dHb $dx) ↪
     der_case (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
              (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dHa)
              (der_Fshift_n $sc $df $dHb) (der_Fshift_n $sc $df $dx)
with der_Fshift_n $sc $df (der_path $dA $dx $dy) ↪
     der_path (der_Fshift_n (FSCI $sc) $df $dA)
              (der_Fshift_n $sc $df $dx) (der_Fshift_n $sc $df $dy)
with der_Fshift_n $sc $df (der_lamP $dA $dt) ↪
     der_lamP (der_Fshift_n (FSCI $sc) $df $dA) (der_Fshift_n (FSCI $sc) $df $dt)
with der_Fshift_n $sc $df (der_appP _ _ _ _ _ $dA $dx $dy $dt $di) ↪
     der_appP _ _ _ _ _ (der_Fshift_n (FSCI $sc) $df $dA)
                        (der_Fshift_n $sc $df $dx) (der_Fshift_n $sc $df $dy)
                        (der_Fshift_n $sc $df $dt) (der_I_Fshift_n $sc $df $di)
with der_Fshift_n $sc $d (der_sys $dA $df $dg $du $dv $d1fg $deq) ↪
     der_sys (der_Fshift_n $sc $d $dA) (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
             (der_Fshift_n (FSCF $sc $df) $d $du) (der_Fshift_n (FSCF $sc $dg) $d $dv)
             (der_isOne_Fshift_n $sc $d $d1fg)
             (der_eq_Fshift_n (FSCF $sc (der_F_min $df $dg)) $d $deq)
with der_Fshift_n $sc $df (der_sys_empty $dA $d1) ↪
     der_sys_empty (der_Fshift_n $sc $df $dA) (der_isOne_Fshift_n $sc $df $d1)
with der_Fshift_n $sc $d (der_transp $dA $df $du $deq) ↪
     der_transp (der_Fshift_n (FSCI $sc) $d $dA) (der_F_Fshift_n $sc $d $df)
                (der_Fshift_n $sc $d $du)
                (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deq)
with der_Fshift_n $sc $d (der_hcomp $dA $df $du $du0 $deq) ↪
     der_hcomp (der_Fshift_n $sc $d $dA) (der_F_Fshift_n $sc $d $df)
               (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $du)
               (der_Fshift_n $sc $d $du0)
               (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
// der_eq_Fshift_n
with der_eq_Fshift_n $sc $df (der_eq_refl _ $s $u $A $du) ↪
     der_eq_refl _ $s $u $A (der_Fshift_n $sc $df $du)
with der_eq_Fshift_n $sc $df (der_eq_trans _ $s $u $v $w $A $duv $dvw) ↪
     der_eq_trans _ $s $u $v $w $A
                       (der_eq_Fshift_n $sc $df $duv) (der_eq_Fshift_n $sc $df $dvw)
with der_eq_Fshift_n $sc $df (der_eq_sym _ $s $u $v $A $deq) ↪
     der_eq_sym _ $s $u $v $A (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_conv _ $s $t1 $t2 $T1 $T2 $deqt $deqT) ↪
     der_eq_conv _ $s $t1 $t2 $T1 $T2
                      (der_eq_Fshift_n $sc $df $deqt) (der_eq_Fshift_n $sc $df $deqT)
with der_eq_Fshift_n $sc $df (der_eq_isOne_zero _ $s $A $u $v $d1) ↪
     der_eq_isOne_zero _ $s $A $u $v
                            (der_isOne_Fshift_n $sc $df $d1)
with der_eq_Fshift_n $sc $d (der_eq_isOne_max _ $s $A $u $v $f $g $df $dg $deqf $deqg $d1) ↪
     der_eq_isOne_max _ $s $A $u $v $f $g
                      (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                      (der_eq_Fshift_n (FSCF $sc $df) $d $deqf)
                      (der_eq_Fshift_n (FSCF $sc $dg) $d $deqg)
                      (der_isOne_Fshift_n $sc $d $d1)
with der_eq_Fshift_n $sc $df (der_eq_beta _ $s $s' $u $A $t $B $dA $dB $dt $du) ↪
     der_eq_beta _ $s $s' $u $A $t $B
                        (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
                        (der_Fshift_n (FSCSucc $sc $dA) $df $dt) (der_Fshift_n $sc $df $du)
with der_eq_Fshift_n $sc $d (der_eq_eta _ $s $s' $A $B $f $dA $dB $df) ↪
     der_eq_eta _ $s $s' $A $B $f
                (der_Fshift_n $sc $d $dA) (der_Fshift_n (FSCSucc $sc $dA) $d $dB)
                (der_Fshift_n $sc $d $df)
with der_eq_Fshift_n $sc $df (der_eq_rec_zero _ $s $s' $P $z $H $dP $dz $dH) ↪
     der_eq_rec_zero _ $s $s' $P $z $H
                     (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dz)
                     (der_Fshift_n $sc $df $dH)
with der_eq_Fshift_n $sc $df (der_eq_rec_suc _ $s $s' $P $z $H $n $dP $dz $dH $dn) ↪
     der_eq_rec_suc _ $s $s' $P $z $H $n
                     (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dz)
                     (der_Fshift_n $sc $df $dH) (der_Fshift_n $sc $df $dn)
with der_eq_Fshift_n $sc $df (der_eq_p1 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p1 _ $s $s' $A $u $B $v
                      (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $du)
                      (der_Fshift_n (FSCSucc $sc $dA) $df $dB) (der_Fshift_n $sc $df $dv)
with der_eq_Fshift_n $sc $df (der_eq_p2 _ $s $s' $A $u $B $v $dA $du $dB $dv) ↪
     der_eq_p2 _ $s $s' $A $u $B $v
                      (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $du)
                      (der_Fshift_n (FSCSucc $sc $dA) $df $dB) (der_Fshift_n $sc $df $dv)
with der_eq_Fshift_n $sc $df (der_eq_pair _ $s $s' $A $B $t $u $dA $dB $dt $du $dp1 $dp2) ↪
     der_eq_pair _ $s $s' $A $B $t $u
                      (der_Fshift_n $sc $df $dA) (der_Fshift_n (FSCSucc $sc $dA) $df $dB)
                      (der_Fshift_n $sc $df $dt) (der_Fshift_n $sc $df $du)
                      (der_eq_Fshift_n $sc $df $dp1) (der_eq_Fshift_n $sc $df $dp2)
with der_eq_Fshift_n $sc $df (der_eq_case_left _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_left _ $s $s' $m $A $B $P
                      $Ha $Hb $a
                      (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
                      (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dHa)
                      (der_Fshift_n $sc $df $dHb) (der_Fshift_n $sc $df $da)
with der_eq_Fshift_n $sc $df (der_eq_case_right _ $s $s' $m $A $B $P $Ha $Hb $a $dA $dB $dP $dHa $dHb $da) ↪
     der_eq_case_right _ $s $s' $m $A $B $P
                       $Ha $Hb $a
                      (der_Fshift_n $sc $df $dA) (der_Fshift_n $sc $df $dB)
                      (der_Fshift_n $sc $df $dP) (der_Fshift_n $sc $df $dHa)
                      (der_Fshift_n $sc $df $dHb) (der_Fshift_n $sc $df $da)
with der_eq_Fshift_n $sc $df (der_eq_betaP _ $s $A $t $i $dA $dt $di) ↪
     der_eq_betaP _ $s $A $t $i
                  (der_Fshift_n (FSCI $sc) $df $dA) (der_Fshift_n (FSCI $sc) $df $dt)
                  (der_I_Fshift_n $sc $df $di)
with der_eq_Fshift_n $sc $df (der_eq_etaP _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_etaP _ $s $A $t $x $y
                 (der_Fshift_n (FSCI $sc) $df $dA)
                 (der_Fshift_n $sc $df $dx)
                 (der_Fshift_n $sc $df $dy)
                 (der_Fshift_n $sc $df $dt)
with der_eq_Fshift_n $sc $df (der_eq_appP_zero _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_appP_zero _ $s $A $t $x $y
                      (der_Fshift_n (FSCI $sc) $df $dA)
                      (der_Fshift_n $sc $df $dx)
                      (der_Fshift_n $sc $df $dy)
                      (der_Fshift_n $sc $df $dt)
with der_eq_Fshift_n $sc $df (der_eq_appP_one _ $s $A $t $x $y $dA $dx $dy $dt) ↪
     der_eq_appP_one _ $s $A $t $x $y
                     (der_Fshift_n (FSCI $sc) $df $dA)
                     (der_Fshift_n $sc $df $dx)
                     (der_Fshift_n $sc $df $dy)
                     (der_Fshift_n $sc $df $dt)
with der_eq_Fshift_n $sc $d (der_eq_sys_left _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_left _ $s $A $f $g $x $y
                     (der_Fshift_n $sc $d $dA)
                     (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                     (der_Fshift_n (FSCF $sc $df) $d $dx) (der_Fshift_n (FSCF $sc $dg) $d $dy)
                     (der_eq_Fshift_n (FSCF $sc (der_F_min $df $dg)) $d $deq)
                     (der_isOne_Fshift_n $sc $d $d1)
with der_eq_Fshift_n $sc $d (der_eq_sys_right _ $s $A $f $g $x $y $dA $df $dg $dx $dy $deq $d1) ↪
     der_eq_sys_right _ $s $A $f $g $x $y (der_Fshift_n $sc $d $dA)
                      (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                      (der_Fshift_n (FSCF $sc $df) $d $dx) (der_Fshift_n (FSCF $sc $dg) $d $dy)
                      (der_eq_Fshift_n (FSCF $sc (der_F_min $df $dg)) $d $deq)
                      (der_isOne_Fshift_n $sc $d $d1)
with der_eq_Fshift_n $sc $d (der_eq_transp _ $s $A $f $u $dA $df $du $deq $d1) ↪
     der_eq_transp _ $s $A $f $u
                   (der_Fshift_n (FSCI $sc) $d $dA)
                   (der_F_Fshift_n $sc $d $df)
                   (der_Fshift_n $sc $d $du)
                   (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deq)
                   (der_isOne_Fshift_n $sc $d $d1)
with der_eq_Fshift_n $sc $d (der_eq_transp_pi _ $s $s' $A $B $f $u $v $dA $dB $df $deqA $deqB $du $dv) ↪
         der_eq_transp_pi _ $s $s' $A $B $f $u $v
                           (der_Fshift_n (FSCI $sc) $d $dA) (der_Fshift_n (FSCSucc (FSCI $sc) $dA) $d $dB)
                           (der_F_Fshift_n $sc $d $df)
                           (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqA)
                           (der_eq_Fshift_n (FSCSucc (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df))
                                                     (der_weakF (pushΓI (fsc_to_dctx $sc)) $dA (der_Ishift0F (fsc_to_dctx $sc) $df)))
                                            $d $deqB)
                           (der_Fshift_n $sc $d $du)
                           (der_Fshift_n $sc $d $dv)
with der_eq_Fshift_n $sc $d (der_eq_transp_univ _ $s $f $A $df $dA) ↪
     der_eq_transp_univ _ $s $f $A
                       (der_F_Fshift_n $sc $d $df) (der_Fshift_n $sc $d $dA)
with der_eq_Fshift_n $sc $d (der_eq_transp_zero _ $s $f $df) ↪
     der_eq_transp_zero _ $s $f (der_F_Fshift_n $sc $d $df)
with der_eq_Fshift_n $sc $d (der_eq_transp_suc _ $s $f $n $df $dn) ↪
     der_eq_transp_suc _ $s $f $n (der_F_Fshift_n $sc $d $df) (der_Fshift_n $sc $d $dn)
with der_eq_Fshift_n $sc $d (der_eq_transp_sig _ $s $s' $A $B $f $u $dA $dB $df $deqA $deqB $du) ↪
     der_eq_transp_sig _ $s $s' $A $B $f $u
                       (der_Fshift_n (FSCI $sc) $d $dA) (der_Fshift_n (FSCSucc (FSCI $sc) $dA) $d $dB)
                       (der_F_Fshift_n $sc $d $df)
                       (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqA)
                       (der_eq_Fshift_n (FSCSucc (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df))
                                                 (der_weakF (pushΓI (fsc_to_dctx $sc)) $dA (der_Ishift0F (fsc_to_dctx $sc) $df)))
                                        $d $deqB)
                       (der_Fshift_n $sc $d $du)
with der_eq_Fshift_n $sc $d (der_eq_transp_sum_left _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     der_eq_transp_sum_left _ $s $s' $A $B $f $a
                            (der_Fshift_n (FSCI $sc) $d $dA) (der_Fshift_n (FSCI $sc) $d $dB)
                                 (der_F_Fshift_n $sc $d $df) (der_Fshift_n $sc $d $da)
                                 (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqA)
                                 (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqB)
with der_eq_Fshift_n $sc $d (der_eq_transp_sum_right _ $s $s' $A $B $f $a $dA $dB $df $da $deqA $deqB) ↪
     der_eq_transp_sum_right _ $s $s' $A $B $f $a
                                 (der_Fshift_n (FSCI $sc) $d $dA) (der_Fshift_n (FSCI $sc) $d $dB)
                                 (der_F_Fshift_n $sc $d $df) (der_Fshift_n $sc $d $da)
                                 (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqA)
                                 (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqB)
with der_eq_Fshift_n $sc $d (der_eq_transp_path _ $s $A $x $y $f $u $dA $dx $dy $df $du $deqA $deqx $deqy) ↪
     der_eq_transp_path _ $s $A $x $y $f $u
                        (der_Fshift_n (FSCI (FSCI $sc)) $d $dA)
                        (der_Fshift_n (FSCI $sc) $d $dx) (der_Fshift_n (FSCI $sc) $d $dy)
                        (der_F_Fshift_n $sc $d $df)
                        (der_Fshift_n $sc $d $du)
                        (der_eq_Fshift_n (FSCF (FSCI (FSCI $sc)) (der_Ishift0F (fsc_to_dctx (FSCI $sc))
                                                                               (der_Ishift0F (fsc_to_dctx $sc) $df)))
                                         $d $deqA)
                        (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqx)
                        (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $deqy)
with der_eq_Fshift_n $sc $d (der_eq_hcomp _ $s $A $f $u $u0 $dA $df $du $du0 $deq $d1) ↪
     der_eq_hcomp _ $s $A $f $u $u0
                  (der_Fshift_n $sc $d $dA) (der_F_Fshift_n $sc $d $df)
                  (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $du)
                  (der_Fshift_n $sc $d $du0)
                  (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
                  (der_isOne_Fshift_n $sc $d $d1)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_pi _ $s $s' $A $B $f $u $u0 $v $dA $dB $df $du $du0 $deq $dv) ↪
     der_eq_hcomp_pi _ $s $s' $A $B $f $u $u0 $v
                    (der_Fshift_n $sc $d $dA) (der_Fshift_n (FSCSucc $sc $dA) $d $dB)
                    (der_F_Fshift_n $sc $d $df)
                    (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $du)
                    (der_Fshift_n $sc $d $du0)
                    (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
                    (der_Fshift_n $sc $d $dv)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_zero _ $s $f $n $df $dn $deq) ↪
     der_eq_hcomp_zero _ $s $f $n (der_F_Fshift_n $sc $d $df)
                       (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $dn)
                       (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_suc _ $s $f $n $n0 $df $dn $dn0 $deq) ↪
     der_eq_hcomp_suc _ $s $f $n $n0 (der_F_Fshift_n $sc $d $df)
                       (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $dn)
                       (der_Fshift_n $sc $d $dn0)
                       (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_sig _ $s $s' $A $B $f $u $u0 $dA $dB $df $du $du0 $deq) ↪
     der_eq_hcomp_sig _ $s $s' $A $B $f $u $u0
                      (der_Fshift_n $sc $d $dA) (der_Fshift_n (FSCSucc $sc $dA) $d $dB)
                      (der_F_Fshift_n $sc $d $df)
                      (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $du)
                      (der_Fshift_n $sc $d $du0)
                      (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_sum_left _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_left _ $s $s' $A $B $f $a $a0
                           (der_Fshift_n $sc $d $dA) (der_Fshift_n $sc $d $dB) (der_F_Fshift_n $sc $d $df)
                           (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $da)
                           (der_Fshift_n $sc $d $da0)
                           (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_sum_right _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_right _ $s $s' $A $B $f $a $a0
                           (der_Fshift_n $sc $d $dA) (der_Fshift_n $sc $d $dB) (der_F_Fshift_n $sc $d $df)
                           (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $da)
                           (der_Fshift_n $sc $d $da0)
                           (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_hcomp_path _ $s $A $x $y $f $u $u0 $dA $dx $dy $df $du $du0 $deq) ↪
     der_eq_hcomp_path _ $s $A $x $y $f $u $u0
                       (der_Fshift_n (FSCI $sc) $d $dA)
                       (der_Fshift_n $sc $d $dx) (der_Fshift_n $sc $d $dy)
                       (der_F_Fshift_n $sc $d $df)
                       (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) $df)) $d $du)
                       (der_Fshift_n $sc $d $du0)
                       (der_eq_Fshift_n (FSCF $sc $df) $d $deq)
with der_eq_Fshift_n $sc $d (der_eq_cong_pi _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_pi _ $s $s' $A1 $A2 $B1 $B2
                    (der_eq_Fshift_n $sc $d $deqA) (der_eq_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $d $deqB)
                    (der_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $d $dB1)
                    (der_Fshift_n (FSCSucc $sc (inv_eq_t2 (fsc_to_dctx $sc) $deqA)) $d $dB2)
with der_eq_Fshift_n $sc $df (der_eq_cong_abs _ $s $s' $A1 $A2 $B $t1 $t2 $deqA $deqt $dB1 $dB2) ↪
     der_eq_cong_abs _ $s $s' $A1 $A2 $B $t1 $t2
                     (der_eq_Fshift_n $sc $df $deqA) (der_eq_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $df $deqt)
                     (der_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $df $dB1)
                     (der_Fshift_n (FSCSucc $sc (inv_eq_t2 (fsc_to_dctx $sc) $deqA)) $df $dB2)
with der_eq_Fshift_n $sc $df (der_eq_cong_app _ $s $s' $A $B $f1 $f2 $a1 $a2 $deqf $deqa) ↪
     der_eq_cong_app _ $s $s' $A $B $f1 $f2 $a1 $a2
                            (der_eq_Fshift_n $sc $df $deqf) (der_eq_Fshift_n $sc $df $deqa)
with der_eq_Fshift_n $sc $df (der_eq_cong_suc _ $s $n $n' $deq) ↪
     der_eq_cong_suc _ $s $n $n' (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_rec _ $s $s' $P1 $P2 $z1 $z2 $H1 $H2 $n1 $n2 $deqP $deqz $deqH $deqn) ↪
     der_eq_cong_rec _ $s $s' $P1 $P2 $z1 $z2
                     $H1 $H2 $n1 $n2
                     (der_eq_Fshift_n $sc $df $deqP) (der_eq_Fshift_n $sc $df $deqz)
                     (der_eq_Fshift_n $sc $df $deqH) (der_eq_Fshift_n $sc $df $deqn)
with der_eq_Fshift_n $sc $df (der_eq_cong_sig _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB $dB1 $dB2) ↪
     der_eq_cong_sig _ $s $s' $A1 $A2 $B1 $B2
                     (der_eq_Fshift_n $sc $df $deqA) (der_eq_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $df $deqB)
                     (der_Fshift_n (FSCSucc $sc (inv_eq_t1 (fsc_to_dctx $sc) $deqA)) $df $dB1)
                     (der_Fshift_n (FSCSucc $sc (inv_eq_t2 (fsc_to_dctx $sc) $deqA)) $df $dB2)
with der_eq_Fshift_n $sc $df (der_eq_cong_pair _ $s $s' $A $B $a1 $a2 $b1 $b2 $deqa $deqb) ↪
     der_eq_cong_pair _ $s $s' $A $B $a1 $a2 $b1 $b2
                      (der_eq_Fshift_n $sc $df $deqa) (der_eq_Fshift_n $sc $df $deqb)
with der_eq_Fshift_n $sc $df (der_eq_cong_p1 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p1 _ $s $s' $A $B $p1 $p2
       (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_p2 _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_p2 _ $s $s' $A $B $p1 $p2
       (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_sum _ $s $s' $A1 $A2 $B1 $B2 $deqA $deqB) ↪
     der_eq_cong_sum _ $s $s' $A1 $A2 $B1 $B2
                            (der_eq_Fshift_n $sc $df $deqA) (der_eq_Fshift_n $sc $df $deqB)
with der_eq_Fshift_n $sc $df (der_eq_cong_injl _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injl _ $s $s' $A $B $p1 $p2
       (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_injr _ $s $s' $A $B $p1 $p2 $deq) ↪
     der_eq_cong_injr _ $s $s' $A $B $p1 $p2
       (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_case _ $s $s' $m $A1 $A2 $B1 $B2 $P1 $P2 $Ha1 $Ha2 $Hb1 $Hb2 $u $v $deqA $deqB $deqP $deqHa $deqHb $deq) ↪
     der_eq_cong_case _ $s $s' $m $A1 $A2 $B1 $B2 $P1 $P2 $Ha1 $Ha2 $Hb1 $Hb2 $u $v
                      (der_eq_Fshift_n $sc $df $deqA) (der_eq_Fshift_n $sc $df $deqB) (der_eq_Fshift_n $sc $df $deqP)
                      (der_eq_Fshift_n $sc $df $deqHa)
                      (der_eq_Fshift_n $sc $df $deqHb)
                      (der_eq_Fshift_n $sc $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_path _ $s $A1 $A2 $a1 $a2 $b1 $b2 $deqA $deqa $deqb) ↪
     der_eq_cong_path _ $s $A1 $A2 $a1 $a2 $b1 $b2
                           (der_eq_Fshift_n (FSCI $sc) $df $deqA)
                           (der_eq_Fshift_n $sc $df $deqa)
                           (der_eq_Fshift_n $sc $df $deqb)
with der_eq_Fshift_n $sc $df (der_eq_cong_lamP _ $s $A $a1 $a2 $deq) ↪
     der_eq_cong_lamP _ $s $A $a1 $a2
                      (der_eq_Fshift_n (FSCI $sc) $df $deq)
with der_eq_Fshift_n $sc $df (der_eq_cong_appP _ $s $A $x $y $a1 $a2 $i1 $i2 $deq $deqi) ↪
     der_eq_cong_appP _ $s $A $x $y $a1 $a2 $i1 $i2
                      (der_eq_Fshift_n $sc $df $deq) (der_eq_I_Fshift_n $sc $df $deqi)
with der_eq_Fshift_n $sc $df (der_eq_cong_sys _ $s $A $f1 $f2 $g1 $g2 $u1 $u2 $v1 $v2
                                                $deqf $deqg $dequ $deqv $du1 $du2 $dv1 $dv2 $done1 $done2 $deq1 $deq2) ↪
     der_eq_cong_sys _ $s $A $f1 $f2 $g1 $g2 $u1 $u2 $v1 $v2
                     (der_eq_F_Fshift_n $sc $df $deqf) (der_eq_F_Fshift_n $sc $df $deqg)
                     (der_eq_Fshift_n (FSCF $sc (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf)) $df $dequ)
                     (der_eq_Fshift_n (FSCF $sc (inv_eq_F_t1 (fsc_to_dctx $sc) $deqg)) $df $deqv)
                     (der_Fshift_n (FSCF $sc (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf)) $df $du1)
                     (der_Fshift_n (FSCF $sc (inv_eq_F_t2 (fsc_to_dctx $sc) $deqf)) $df $du2)
                     (der_Fshift_n (FSCF $sc (inv_eq_F_t1 (fsc_to_dctx $sc) $deqg)) $df $dv1)
                     (der_Fshift_n (FSCF $sc (inv_eq_F_t2 (fsc_to_dctx $sc) $deqg)) $df $dv2)
                     (der_isOne_Fshift_n $sc $df $done1) (der_isOne_Fshift_n $sc $df $done2)
                     (der_eq_Fshift_n (FSCF $sc (der_F_min (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf) (inv_eq_F_t1 (fsc_to_dctx $sc) $deqg))) $df $deq1)
                     (der_eq_Fshift_n (FSCF $sc (der_F_min (inv_eq_F_t2 (fsc_to_dctx $sc) $deqf) (inv_eq_F_t2 (fsc_to_dctx $sc) $deqg))) $df $deq2)
with der_eq_Fshift_n $sc $df (der_eq_cong_transp _ $s $A1 $A2 $f1 $f2 $a1 $a2 $deqA $deqf $deqa $deqA1 $deqA2) ↪
     der_eq_cong_transp _ $s $A1 $A2 $f1 $f2 $a1 $a2
                        (der_eq_Fshift_n (FSCI $sc) $df $deqA) (der_eq_F_Fshift_n $sc $df $deqf)
                        (der_eq_Fshift_n $sc $df $deqa)
                        (der_eq_Fshift_n (FSCI $sc) $df $deqA1)
                        (der_eq_Fshift_n (FSCI $sc) $df $deqA2)
with der_eq_Fshift_n $sc $df (der_eq_cong_hcomp _ $s $A1 $A2 $f1 $f2 $u1 $u2 $v1 $v2 $deqA $deqf $dequ $deqv $du1 $du2 $dequv1 $dequv2) ↪
     der_eq_cong_hcomp _ $s $A1 $A2 $f1 $f2 $u1 $u2 $v1 $v2
                       (der_eq_Fshift_n $sc $df $deqA) (der_eq_F_Fshift_n $sc $df $deqf)
                       (der_eq_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf))) $df $dequ)
                       (der_eq_Fshift_n $sc $df $deqv)
                       (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf))) $df $du1)
                       (der_Fshift_n (FSCF (FSCI $sc) (der_Ishift0F (fsc_to_dctx $sc) (inv_eq_F_t2 (fsc_to_dctx $sc) $deqf))) $df $du2)
                       (der_eq_Fshift_n (FSCF $sc (inv_eq_F_t1 (fsc_to_dctx $sc) $deqf)) $df $dequv1)
                       (der_eq_Fshift_n (FSCF $sc (inv_eq_F_t2 (fsc_to_dctx $sc) $deqf)) $df $dequv2)
// der_I_Fshift_n
with der_I_Fshift_n _ _ der_I_0 ↪ der_I_0
with der_I_Fshift_n _ _ der_I_1 ↪ der_I_1
with der_I_Fshift_n $sc $df (@der_I_var _ $i $le) ↪ der_I_var (lenI_fsc_ctx_sctx $i $sc $df $le)
with der_I_Fshift_n $sc $df (der_I_sym $di) ↪ der_I_sym (der_I_Fshift_n $sc $df $di)
with der_I_Fshift_n $sc $df (der_I_min $da $db) ↪
     der_I_min (der_I_Fshift_n $sc $df $da) (der_I_Fshift_n $sc $df $db)
with der_I_Fshift_n $sc $df (der_I_max $da $db) ↪
     der_I_max (der_I_Fshift_n $sc $df $da) (der_I_Fshift_n $sc $df $db)
// der_eq_I_Fshift_n
with der_eq_I_Fshift_n $sc $df (der_eq_I_refl _ _ $di) ↪ der_eq_I_refl _ _ (der_I_Fshift_n $sc $df $di)
with der_eq_I_Fshift_n $sc $df (der_eq_I_sym _ _ _ $di) ↪ der_eq_I_sym _ _ _ (der_eq_I_Fshift_n $sc $df $di)
with der_eq_I_Fshift_n $sc $df (der_eq_I_trans _ _ _ _ $deq1 $deq2) ↪
     der_eq_I_trans _ _ _ _ (der_eq_I_Fshift_n $sc $df $deq1) (der_eq_I_Fshift_n $sc $df $deq2)
with der_eq_I_Fshift_n $sc $df (der_eq_I_isOne_zero _ _ _ $done) ↪
     der_eq_I_isOne_zero _ _ _ (der_isOne_Fshift_n $sc $df $done)
with der_eq_I_Fshift_n $sc $d (der_eq_I_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_I_isOne_max _ _ _ _ _ (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                        (der_eq_I_Fshift_n (FSCF $sc $df) $d $dif) (der_eq_I_Fshift_n (FSCF $sc $dg) $d $dig)
                        (der_isOne_Fshift_n $sc $d $done)
with der_eq_I_Fshift_n $sc $df (der_eq_I_isOne_eq0 _ _ $done) ↪
     der_eq_I_isOne_eq0 _ _ (der_isOne_Fshift_n $sc $df $done)
with der_eq_I_Fshift_n $sc $df (der_eq_I_isOne_eq1 _ _ $done) ↪
     der_eq_I_isOne_eq1 _ _ (der_isOne_Fshift_n $sc $df $done)
with der_eq_I_Fshift_n _ _ (der_eq_I_sym_sym _ _) ↪ der_eq_I_sym_sym _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_sym_zero _) ↪ der_eq_I_sym_zero _
with der_eq_I_Fshift_n _ _ (der_eq_I_sym_one _) ↪ der_eq_I_sym_one _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_assoc _ _ _ _) ↪ der_eq_I_min_assoc _ _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_comm _ _ _) ↪ der_eq_I_min_comm _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_zero _ _) ↪ der_eq_I_min_zero _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_one _ _) ↪ der_eq_I_min_one _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_assoc _ _ _ _) ↪ der_eq_I_max_assoc _ _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_comm _ _ _) ↪ der_eq_I_max_comm _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_zero _ _) ↪ der_eq_I_max_zero _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_one _ _) ↪ der_eq_I_max_one _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_sym _ _ _) ↪ der_eq_I_min_sym _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_sym _ _ _) ↪ der_eq_I_max_sym _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_min_distrib _ _ _ _) ↪
     der_eq_I_min_distrib _ _ _ _
with der_eq_I_Fshift_n _ _ (der_eq_I_max_distrib _ _ _ _) ↪
     der_eq_I_max_distrib _ _ _ _
with der_eq_I_Fshift_n $sc $df (der_eq_I_cong_sym _ _ _ $di) ↪
     der_eq_I_cong_sym _ _ _ (der_eq_I_Fshift_n $sc $df $di)
with der_eq_I_Fshift_n $sc $df (der_eq_I_cong_min _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_min _ _ _ _ _ (der_eq_I_Fshift_n $sc $df $di) (der_eq_I_Fshift_n $sc $df $dj)
with der_eq_I_Fshift_n $sc $df (der_eq_I_cong_max _ _ _ _ _ $di $dj) ↪
     der_eq_I_cong_max _ _ _ _ _ (der_eq_I_Fshift_n $sc $df $di) (der_eq_I_Fshift_n $sc $df $dj)
// der_F_Fshift_n
with der_F_Fshift_n _ _ der_F_0 ↪ der_F_0
with der_F_Fshift_n _ _ der_F_1 ↪ der_F_1
with der_F_Fshift_n $sc $d (@der_F_eq0 _ $i $le)  ↪ der_F_eq0 (lenI_fsc_ctx_sctx $i $sc $d $le)
with der_F_Fshift_n $sc $d (@der_F_eq1 _ $i $le)  ↪ der_F_eq1 (lenI_fsc_ctx_sctx $i $sc $d $le)
with der_F_Fshift_n $sc $d (der_F_min $df $dg) ↪
     der_F_min (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
with der_F_Fshift_n $sc $d (der_F_max $df $dg) ↪
     der_F_max (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
// der_eq_F_Fshift_n
with der_eq_F_Fshift_n $sc $d (der_eq_F_refl _ _ $df) ↪
     der_eq_F_refl _ _ (der_F_Fshift_n $sc $d $df)
with der_eq_F_Fshift_n $sc $d (der_eq_F_sym _ _ _ $df) ↪
     der_eq_F_sym _ _ _ (der_eq_F_Fshift_n $sc $d $df)
with der_eq_F_Fshift_n $sc $d (der_eq_F_trans _ _ _ _ $df $dg) ↪
     der_eq_F_trans _ _ _ _ (der_eq_F_Fshift_n $sc $d $df) (der_eq_F_Fshift_n $sc $d $dg)
with der_eq_F_Fshift_n $sc $d (der_eq_F_isOne_zero _ _ _ $done) ↪
     der_eq_F_isOne_zero _ _ _ (der_isOne_Fshift_n $sc $d $done)
with der_eq_F_Fshift_n $sc $d (der_eq_F_isOne_max _ _ _ _ _ $df $dg $dif $dig $done) ↪
     der_eq_F_isOne_max _ _ _ _ _ (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                        (der_eq_F_Fshift_n (FSCF $sc $df) $d $dif) (der_eq_F_Fshift_n (FSCF $sc $dg) $d $dig)
                        (der_isOne_Fshift_n $sc $d $done)
with der_eq_F_Fshift_n $sc $d (der_eq_F_isOne_one _ _ $done) ↪
     der_eq_F_isOne_one _ _ (der_isOne_Fshift_n $sc $d $done)
with der_eq_F_Fshift_n _ _ (der_eq_F_min_assoc _ _ _ _) ↪ der_eq_F_min_assoc _ _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_min_comm _ _ _) ↪ der_eq_F_min_comm _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_max_assoc _ _ _ _) ↪ der_eq_F_max_assoc _ _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_max_comm _ _ _) ↪ der_eq_F_max_comm _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_min_distrib _ _ _ _) ↪
     der_eq_F_min_distrib _ _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_max_distrib _ _ _ _) ↪
     der_eq_F_max_distrib _ _ _ _
with der_eq_F_Fshift_n _ _ (der_eq_F_empty _ _) ↪ der_eq_F_empty _ _
with der_eq_F_Fshift_n $sc $d (der_eq_F_cong_eq0 _ $id' $i $deq) ↪
     der_eq_F_cong_eq0 (fsc_to_sctx $d $sc) $id' $i (der_eq_I_Fshift_n $sc $d $deq)
with der_eq_F_Fshift_n $sc $d (der_eq_F_cong_eq1 _ $id' $i $deq) ↪
     der_eq_F_cong_eq1 (fsc_to_sctx $d $sc) $id' $i (der_eq_I_Fshift_n $sc $d $deq)
with der_eq_F_Fshift_n $sc $d (der_eq_F_cong_min _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_min _ _ _ _ _ (der_eq_F_Fshift_n $sc $d $deq1) (der_eq_F_Fshift_n $sc $d $deq2)
with der_eq_F_Fshift_n $sc $d (der_eq_F_cong_max _ _ _ _ _ $deq1 $deq2) ↪
     der_eq_F_cong_max _ _ _ _ _ (der_eq_F_Fshift_n $sc $d $deq1) (der_eq_F_Fshift_n $sc $d $deq2)
// der_isOne_Fshift_n
with der_isOne_Fshift_n _ _ (der_isOne_one _) ↪ der_isOne_one _
with der_isOne_Fshift_n $sc $d (der_isOne_zero _ _ $d0) ↪
     der_isOne_zero _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_empty _ _ $d0) ↪
     der_isOne_empty _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_min_intro _ _ _ $df $dg) ↪
     der_isOne_min_intro _ _ _ (der_isOne_Fshift_n $sc $d $df) (der_isOne_Fshift_n $sc $d $dg)
with der_isOne_Fshift_n $sc $d (der_isOne_min_elim_left _ _ _ $d0) ↪
     der_isOne_min_elim_left _ _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_min_elim_right _ _ _ $d0) ↪
     der_isOne_min_elim_right _ _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_max_intro_left _ _ _ $d0) ↪
     der_isOne_max_intro_left _ _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_max_intro_right _ _ _ $d0) ↪
     der_isOne_max_intro_right _ _ _ (der_isOne_Fshift_n $sc $d $d0)
with der_isOne_Fshift_n $sc $d (der_isOne_max_elim _ _ _ _ $df $dg $dl $dr $d1) ↪
     der_isOne_max_elim _ _ _ _ (der_F_Fshift_n $sc $d $df) (der_F_Fshift_n $sc $d $dg)
                                (der_isOne_Fshift_n (FSCF $sc $df) $d $dl) (der_isOne_Fshift_n (FSCF $sc $dg) $d $dr)
                                (der_isOne_Fshift_n $sc $d $d1)
with der_isOne_Fshift_n (FSCF $sc _) $d (der_isOne_axiom _ _ $df) ↪
     der_isOne_axiom _ _ (der_F_Fshift_n $sc $d $df)
with der_isOne_Fshift_n (FSCSucc $sc _) $d (der_isOne_weak _ _ _ _ $dt $df) ↪
     der_isOne_weak _ _ _ _ (der_Fshift_n $sc $d $dt) (der_isOne_Fshift_n $sc $d $df)
with der_isOne_Fshift_n (FSCI $sc) $d (der_isOne_weakI _ _ $df) ↪
     der_isOne_weakI _ _ (der_isOne_Fshift_n $sc $d $df)
with der_isOne_Fshift_n (FSCF $sc _) $d (der_isOne_weakF _ _ _ $dg $df) ↪
     der_isOne_weakF _ _ _ (der_F_Fshift_n $sc $d $dg) (der_isOne_Fshift_n $sc $d $df)
with der_isOne_Fshift_n $sc $d (der_isOne_cong _ _ _ $df $deq) ↪
     der_isOne_cong _ _ _ (der_isOne_Fshift_n $sc $d $df) (der_eq_F_Fshift_n $sc $d $deq);

// Definition of exported lemmas
rule der_weakF $dΓ $d $df ↪ der_Fshift_n (FSC0 $dΓ) $df $d
with der_weakFF $dΓ $dg $df ↪ der_F_Fshift_n (FSC0 $dΓ) $df $dg
with der_eq_weakF $dΓ $deq $df ↪ der_eq_Fshift_n (FSC0 $dΓ) $df $deq
with der_weakF1 $dΓ $dA $dt $df ↪ der_Fshift_n (FSCSucc (FSC0 $dΓ) $dA) $df $dt;
