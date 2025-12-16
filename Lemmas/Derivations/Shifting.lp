require open ctt.Contexts.Shift;
require open ctt.Contexts.Typing;
require open ctt.Lemmas.Commutations;

// Generic der_shift
constant symbol ShiftContext : Context → DBId → TYPE;
symbol sc_to_ctx [Γ : Context] [id : DBId] : ShiftContext Γ id → Context;
symbol sc_to_sctx [Γ : Context] [id : DBId] [s : Sort] [A : Term] :
  der Γ A (tuniv s) (tlsuc s) → ShiftContext Γ id → Context;
symbol sc_to_dctx [Γ : Context] [id : DBId] (sc : ShiftContext Γ id) : der_context (sc_to_ctx sc);
symbol sc_to_dsctx [Γ : Context] [id : DBId] [s : Sort] [A : Term] (dA : der Γ A (tuniv s) (tlsuc s))
                   (sc : ShiftContext Γ id) : der_context (sc_to_sctx dA sc);
constant symbol SC0 [Γ : Context] : der_context Γ → ShiftContext Γ db0;
constant symbol SCSucc [Γ : Context] [s : Sort] [A : Term] [id : DBId] (sc : ShiftContext Γ id) :
  der (sc_to_ctx sc) A (tuniv s) (tlsuc s) → ShiftContext Γ (dbsucc id);
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

symbol shiftget_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id) [l : Sort] [A : Term]
                         (dA : der Γ A (tuniv l) (tlsuc l)) :
  TEq (shiftgetΓ (sc_to_sctx dA sc) (dbshift id i)) (shift id (shiftgetΓ (sc_to_ctx sc) i));
rule shiftget_ctx_sctx db0 (SC0 _) _ ↪ TRefl _
with shiftget_ctx_sctx (dbsucc _) (SC0 _) _ ↪ TRefl _
with shiftget_ctx_sctx db0 (@SCSucc _ _ $t $id _ _) _ ↪ swap_Shift_shift $id $t
with @shiftget_ctx_sctx _ (dbsucc $id) (dbsucc $i) (SCSucc $sc _) _ _ $dA ↪
     teq_trans  (Jcong Shift (shiftget_ctx_sctx $i $sc $dA))
                (swap_Shift_shift $id (shiftgetΓ (sc_to_ctx $sc) $i))
with @shiftget_ctx_sctx _ $id $i (SCI $sc) _ _ $dA ↪
     teq_trans (Jcong IShift (shiftget_ctx_sctx $i $sc $dA))
               (teq_inv (swap_shift_Ishift $id db0 (shiftgetΓ (sc_to_ctx $sc) $i)))
with shiftget_ctx_sctx $i (SCF $sc _) $dA ↪ shiftget_ctx_sctx $i $sc $dA;

symbol getS_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                     [l : Sort] [A : Term] (dA : der Γ A (tuniv l) (tlsuc l)) :
  LEq (getS (sc_to_sctx dA sc) (dbshift id i)) (getS (sc_to_ctx sc) i);
rule getS_ctx_sctx _ (SC0 _) _ ↪ LRefl _
with getS_ctx_sctx db0 (SCSucc _ _) _ ↪ LRefl _
with getS_ctx_sctx (dbsucc $i) (SCSucc $sc _) $dA ↪ getS_ctx_sctx $i $sc $dA
with getS_ctx_sctx $i (SCI $sc) $dA ↪ getS_ctx_sctx $i $sc $dA
with getS_ctx_sctx $i (SCF $sc _) $dA ↪ getS_ctx_sctx $i $sc $dA;

symbol len_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                    [l : Sort] [A : Term] (dA : der Γ A (tuniv l) (tlsuc l)) :
  DBLe (dbsucc i) (len (sc_to_ctx sc)) → DBLe (dbsucc (dbshift id i)) (len (sc_to_sctx dA sc));
rule len_ctx_sctx _ (SC0 _) _ $h ↪ dble_n_S $h
with len_ctx_sctx db0 (SCSucc _ _) _ _ ↪ dble_n_S (dble_0_n _)
with len_ctx_sctx (dbsucc $i) (SCSucc $sc _) $dA $h ↪ dble_n_S (len_ctx_sctx $i $sc $dA (dble_S_n $h))
with len_ctx_sctx $i (SCI $sc) $dA $h ↪ len_ctx_sctx $i $sc $dA $h
with len_ctx_sctx $i (SCF $sc _) $dA $h ↪ len_ctx_sctx $i $sc $dA $h;

symbol lenI_ctx_sctx [Γ : Context] [id : DBId] (i : DBId) (sc : ShiftContext Γ id)
                     [l : Sort] [A : Term] (dA : der Γ A (tuniv l) (tlsuc l)) :
  DBLe (dbsucc i) (lenI (sc_to_ctx sc)) → DBLe (dbsucc i) (lenI (sc_to_sctx dA sc));
rule lenI_ctx_sctx _ (SC0 _) _ $h ↪ $h
with lenI_ctx_sctx $id (SCSucc $sc _) $d $h ↪ lenI_ctx_sctx $id $sc $d $h
with lenI_ctx_sctx db0 (SCI _) _ _ ↪ dble_n_S (dble_0_n _)
with lenI_ctx_sctx (dbsucc $i) (SCI $sc) $dA $h ↪ dble_n_S (lenI_ctx_sctx $i $sc $dA (dble_S_n $h))
with lenI_ctx_sctx $i (SCF $sc _) $dA $h ↪ lenI_ctx_sctx $i $sc $dA $h;

symbol der_shift_n [Γ : Context] [sa s : Sort] [A t T : Term] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                   (d : der (sc_to_ctx sc) t T s)
                   : der (sc_to_sctx dA sc) (shift id t) (shift id T) s;
symbol der_eq_shift_n [Γ : Context] [sa s : Sort] [A T t1 t2 : Term] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                      (deq : der_eq (sc_to_ctx sc) t1 t2 T s) :
  der_eq (sc_to_sctx dA sc) (shift id t1) (shift id t2) (shift id T) s;
symbol der_I_shift_n [Γ : Context] [sa : Sort] [A : Term] [t : ITerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                   (d : der_I (sc_to_ctx sc) t)
                   : der_I (sc_to_sctx dA sc) t;
symbol der_eq_I_shift_n [Γ : Context] [sa : Sort] [A : Term] [t1 t2 : ITerm] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                      (deq : der_eq_I (sc_to_ctx sc) t1 t2) :
  der_eq_I (sc_to_sctx dA sc) t1 t2;
symbol der_F_shift_n [Γ : Context] [sa : Sort] [A : Term] [f : FTerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                   (d : der_F (sc_to_ctx sc) f)
                   : der_F (sc_to_sctx dA sc) f;
symbol der_eq_F_shift_n [Γ : Context] [sa : Sort] [A : Term] [t1 t2 : FTerm] (id : DBId)
                      (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                      (deq : der_eq_F (sc_to_ctx sc) t1 t2) :
  der_eq_F (sc_to_sctx dA sc) t1 t2;
symbol der_isOne_shift_n [Γ : Context] [sa : Sort] [A : Term] [f : FTerm] (id : DBId)
                   (sc : ShiftContext Γ id) (dA : der Γ A (tuniv sa) (tlsuc sa))
                   (d : der_isOne (sc_to_ctx sc) f)
                   : der_isOne (sc_to_sctx dA sc) f;

require open ctt.Univ.Subst;
rule sc_to_dsctx $d (SC0 $dΓ) ↪ der_context_Push _ _ _ $d $dΓ
with sc_to_dsctx $d (SCSucc $sc $dA) ↪ der_context_Push _ _ _ (der_shift_n _ $sc $d $dA) (sc_to_dsctx $d $sc)
with sc_to_dsctx $d (SCI $sc) ↪ der_context_PushI _ (sc_to_dsctx $d $sc)
with sc_to_dsctx $d (SCF $sc $df) ↪ der_context_PushF _ _ (der_F_shift_n _ $sc $d $df) (sc_to_dsctx $d $sc);

require open ctt.Lemmas.Derivations;
// Implementation of der_shift{0,1}
rule der_shift0 $dA $dΓ $dt ↪ der_shift_n db0 (SC0 $dΓ) $dA $dt
with der_eq_shift0 $dA $dΓ $deq ↪ der_eq_shift_n db0 (SC0 $dΓ) $dA $deq
with der_shift1 $dA $dB $dΓ $dt ↪ der_shift_n db1 (SCSucc (SC0 $dΓ) $dA) $dB $dt;
