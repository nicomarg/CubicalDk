
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.derived;
require open ctt.Typing;
require open ctt.TermEquality;
require open ctt.Lemmas;

// Exported lemmas TODO : define them
// Shifting derivation
symbol der_Ishift0 [Γ : Context] [t T : Term] [l : Lev]
                  (_ : der_context Γ) (_ : der Γ t T l) :
  der (PushI Γ) (IShift t) (IShift T) l;
symbol der_Ishift0F [Γ : Context] [f : FTerm]
                  (_ : der_context Γ) (_ : der_F Γ f) :
  der_F (PushI Γ) (IShiftF f);
symbol der_eq_Ishift0 [Γ : Context] [t1 t2 T : Term] [l : Lev]
                      (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) :
  der_eq (PushI Γ) (IShift t1) (IShift t2) (IShift T) l;
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
symbol der_eq_weakF [Γ : Context] [t1 t2 T : Term] [l : Lev] [f : FTerm]
                    (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) (_ : der_F Γ f) :
  der_eq (PushF f Γ) t1 t2 T l;
symbol der_weakF1 [Γ : Context] [t A T : Term] [f : FTerm] [l l' : Lev]
                 (_ : der_context Γ) (_ : der Γ A (tuniv l') (lsuc l')) (_ : der (Push A l' Γ) t T l) (_ : der_F Γ f) :
  der (Push A l' (PushF f Γ)) t T l;

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
with der_shift_n $id $sc $d (der_hcomp $dA $df $du $du0 $deq) ↪
     der_hcomp (der_shift_n $id $sc $d $dA) (der_F_shift_n $id $sc $d $df)
               (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du)
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
                  (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du)
                  (der_shift_n $id $sc $d $du0)
                  (der_eq_shift_n $id (SCF $sc $df) $d $deq) (der_isOne_shift_n $id $sc $d $d1)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_pi _ $s $s' $A $B $f $u $u0 $v $dA $dB $df $du $du0 $deq $dv) ↪
     Jeq (TRefl _) (TRefl _) (Jhcomp (TRefl _) (FTRefl _)
                                     (Japp (TRefl _) (teq_inv (aux_teq_shift_Ishift $id db0 $v))) (TRefl _))
     (der_eq_hcomp_pi _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u) (shift $id $u0) (shift $id $v)
                     (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                     (der_F_shift_n $id $sc $d $df)
                     (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du)
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
                (Jhcomp (Jcong (λ v, applyI1 (apply1 (shift (dbsucc $id) $B) v) it1)
                               (teq_shift_hfill $id $A $f (tp1 $u) (tp1 $u0))) (FTRefl $f)
                        (Jtransp (Jcong (λ v, applyI1 v (itmax (itvar db0) (itvar db0)))
                                        (teq_trans (teq_trans (Jcong (λ v, IShift1 (IShift1 v))
                                                                     (Jcong (apply1 (shift (dbsucc $id) $B))
                                                                            (teq_shift_hfill $id $A $f (tp1 $u) (tp1 $u0))))
                                                              (Jcong IShift1
                                                                     (teq_inv (aux_teq_shift_Ishift $id db1 (apply1 $B (thfill $A $f (tp1 $u) (tp1 $u0)))))))
                                                   (teq_inv (aux_teq_shift_Ishift $id db1 (IShift1 (apply1 $B (thfill $A $f (tp1 $u) (tp1 $u0))))))))
                                 (FTRefl (fteq1 db0)) (TRefl (tp2 (shift $id $u))))
                        (Jtransp (Jcong (λ v, applyI1 v (itmax (itvar db0) it0))
                                        (teq_trans (Jcong (λ v, IShift1 (apply1 (shift (dbsucc $id) $B) v))
                                                          (teq_shift_hfill $id $A $f (tp1 $u) (tp1 $u0)))
                                                   (teq_inv (aux_teq_shift_Ishift $id db1 (apply1 $B (thfill $A $f (tp1 $u) (tp1 $u0))))))) (FTRefl ft0)
                                 (TRefl (tp2 (shift $id $u0))))))
         (der_eq_hcomp_sig _ $s $s' (shift $id $A) (shift (dbsucc $id) $B) $f (shift $id $u) (shift $id $u0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n (dbsucc $id) (SCSucc $sc $dA) $d $dB)
                           (der_F_shift_n $id $sc $d $df) (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $du)
                           (der_shift_n $id $sc $d $du0) (der_eq_shift_n $id (SCF $sc $df) $d $deq))
with der_eq_shift_n $id $sc $d (der_eq_hcomp_sum_left _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_left _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a) (shift $id $a0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB) (der_F_shift_n $id $sc $d $df)
                           (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $da)
                           (der_shift_n $id $sc $d $da0) (der_eq_shift_n $id (SCF $sc $df) $d $deq)
with der_eq_shift_n $id $sc $d (der_eq_hcomp_sum_right _ $s $s' $A $B $f $a $a0 $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_right _ $s $s' (shift $id $A) (shift $id $B) $f (shift $id $a) (shift $id $a0)
                           (der_shift_n $id $sc $d $dA) (der_shift_n $id $sc $d $dB) (der_F_shift_n $id $sc $d $df)
                           (der_shift_n $id (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $d $da)
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
                       (der_eq_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t1 (sc_to_dctx $sc) $deqf))) $d $dequ)
                       (der_eq_shift_n _ $sc $d $deqv)
                       (der_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t1 (sc_to_dctx $sc) $deqf))) $d $du1)
                       (der_shift_n _ (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) (inv_eq_F_t2 (sc_to_dctx $sc) $deqf))) $d $du2)
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
