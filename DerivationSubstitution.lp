require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.derived;
require open ctt.Typing;
require open ctt.TermEquality;
require open ctt.Lemmas;

// exported lemmas, TODO define them
// Congruence for replacement
symbol der_eq_cong_apply [Γ : Context] [l l' : Lev] [A1 A2 B1 B2 t1 t2 : Term]
                         (_ : der_context Γ)
                         (_ : der_eq Γ A1 A2 (tuniv l) (lsuc l)) (_ : der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l'))
                         (_ : der_eq Γ t1 t2 A1 l)
                         (_ : der (Push A1 l Γ) B1 (tuniv l') (lsuc l'))
                         (_ : der (Push A2 l Γ) B2 (tuniv l') (lsuc l'))
                         (_ : der Γ t1 A1 l) (_ : der Γ t2 A2 l)
                         : der_eq Γ (apply1 B1 t1) (apply1 B2 t2) (tuniv l') (lsuc l');
symbol der_eq_cong_Iapply [Γ : Context] [l' : Lev] [B1 B2 : Term] [t1 t2 : ITerm]
                         (_ : der_context Γ)
                         (_ : der_eq (PushI Γ) B1 B2 (tuniv l') (lsuc l'))
                         (_ : der_eq_I Γ t1 t2)
                         (_ : der_I Γ t1) (_ : der_I Γ t2)
                         : der_eq Γ (applyI1 B1 t1) (applyI1 B2 t2) (tuniv l') (lsuc l');

symbol Isubstitution [Γ : Context] [l : Lev] [B C : Term] :
  der_context Γ → der (PushI Γ) C B l → Π [i : ITerm], der_I Γ i → der Γ (applyI1 C i) (applyI1 B i) l;
symbol Isubstitution1 [Γ : Context] [l l' : Lev] [A B C : Term] :
  der_context Γ → der (PushI Γ) A (tuniv l') (lsuc l') → der (Push A l' (PushI Γ)) C B l →
  Π [i : ITerm], der_I Γ i → der (Push (applyI1 A i) l' Γ) (applyI1 C i) (applyI1 B i) l;
symbol Isubstitution_eq [Γ : Context] [l : Lev] [A B C : Term] :
  der_context Γ → der_eq (PushI Γ) A B C l → Π [i : ITerm], der_I Γ i →
  der_eq Γ (applyI1 A i) (applyI1 B i) (applyI1 C i) l;
symbol Fsubstitution [Γ : Context] [l : Lev] [B C : Term] [f : FTerm] :
  der_context Γ → der (PushF f Γ) C B l → der_F Γ f → der_isOne Γ f → der Γ C B l;
symbol Fsubstitution_eq [Γ : Context] [l : Lev] [A B C : Term] [f : FTerm] :
  der_context Γ → der_eq (PushF f Γ) A B C l → der_F Γ f → der_isOne Γ f → der_eq Γ A B C l;

// SubstContext
constant symbol SubstContext [Γ : Context] [A : Term] [s : Lev] : der Γ A (tuniv s) (lsuc s) → DBId → TYPE;
symbol sc_to_ctx [Γ : Context] [A : Term] [s : Lev] [d : der Γ A (tuniv s) (lsuc s)] [id : DBId]
                 : SubstContext d id → Context;
symbol sc_to_dctx [Γ : Context] [A : Term] [s : Lev] [d : der Γ A (tuniv s) (lsuc s)] [id : DBId]
                  (sc : SubstContext d id) : der_context (sc_to_ctx sc);
symbol sc_to_sctx [Γ : Context] [A t : Term] [s : Lev] [id : DBId]
                  (d : der Γ t A s) (dΓ : der_context Γ) : SubstContext (inv_type dΓ d) id → Context;
symbol sc_to_dsctx [Γ : Context] [A t : Term] [s : Lev] [id : DBId]
                   (dt : der Γ t A s) (dΓ : der_context Γ) (sc : SubstContext (inv_type dΓ dt) id) : der_context (sc_to_sctx dt dΓ sc);

constant symbol SC0 [Γ : Context] [s : Lev] [A : Term]
                    (d : der Γ A (tuniv s) (lsuc s)) (_ : der_context Γ) : SubstContext d db0;
constant symbol SCPush [Γ : Context] [s s' : Lev] [A B : Term] [d : der Γ A (tuniv s) (lsuc s)] [id : DBId]
                       (sc : SubstContext d id) : der (sc_to_ctx sc) B (tuniv s') (lsuc s') → SubstContext d (dbsucc id);
constant symbol SCI [Γ : Context] [s : Lev] [A : Term] [d : der Γ A (tuniv s) (lsuc s)] [id : DBId]
                    (sc : SubstContext d id) : SubstContext d id;
constant symbol SCF [Γ : Context] [s : Lev] [A : Term] [f : FTerm] [d : der Γ A (tuniv s) (lsuc s)] [id : DBId]
                    (sc : SubstContext d id) (df : der_F (sc_to_ctx sc) f) : SubstContext d id;

symbol shift_sctx [Γ : Context] [A : Term] [s : Lev] [dA : der Γ A (tuniv s) (lsuc s)] [id : DBId] (sc : SubstContext dA id) (t : Term) : Term;
rule shift_sctx (SC0 _ _) $t ↪ $t
with shift_sctx (SCPush $sc _) $t ↪ Shift (shift_sctx $sc $t)
with shift_sctx (SCI $sc) $t ↪ IShift (shift_sctx $sc $t)
with shift_sctx (SCF $sc _) $t ↪ shift_sctx $sc $t;

symbol sctx_to_ss [Γ : Context] [A : Term] [s : Lev] [dA : der Γ A (tuniv s) (lsuc s)] [id : DBId] (sc : SubstContext dA id) : ShiftSequence id;
rule sctx_to_ss (SC0 _ _) ↪ SS0
with sctx_to_ss (SCPush $sc _) ↪ SSP (sctx_to_ss $sc)
with sctx_to_ss (SCI $sc) ↪ SSI (sctx_to_ss $sc)
with sctx_to_ss (SCF $sc _) ↪ (sctx_to_ss $sc);

symbol shift_sctx_ss_compat [Γ : Context] [A : Term] [s : Lev] [dA : der Γ A (tuniv s) (lsuc s)] [id : DBId] (sc : SubstContext dA id) (t : Term) :
  TEq (shift_sctx sc t) (shift_seq (sctx_to_ss sc) t);
rule shift_sctx_ss_compat (SC0 _ _) $t ↪ TRefl $t
with shift_sctx_ss_compat (SCPush $sc _) $t ↪ Jcong Shift (shift_sctx_ss_compat $sc $t)
with shift_sctx_ss_compat (SCI $sc) $t ↪ Jcong IShift (shift_sctx_ss_compat $sc $t)
with shift_sctx_ss_compat (SCF $sc _) $t ↪ (shift_sctx_ss_compat $sc $t);

rule sc_to_ctx (@SC0 $Γ $s $A _ _) ↪ Push $A $s $Γ
with sc_to_ctx (@SCPush _ _ $s _ $B _ _ $sc _) ↪ Push $B $s (sc_to_ctx $sc)
with sc_to_ctx (SCI $sc) ↪ PushI (sc_to_ctx $sc)
with sc_to_ctx (@SCF _ _ _ $f _ _ $sc _) ↪ PushF $f (sc_to_ctx $sc)
with sc_to_sctx _ _ (@SC0 $Γ _ _ _ _) ↪ $Γ
with @sc_to_sctx _ _ $t _ _ $dt $dΓ (@SCPush _ _ $s _ $B _ $id $sc _) ↪ Push (subst $id (shift_sctx $sc $t) $B) $s (sc_to_sctx $dt $dΓ $sc)
with sc_to_sctx $dt $dΓ (SCI $sc) ↪ PushI (sc_to_sctx $dt $dΓ $sc)
with sc_to_sctx $dt $dΓ (@SCF _ _ _ $f _ _ $sc _) ↪ PushF $f (sc_to_sctx $dt $dΓ $sc);
rule sc_to_dctx (SC0 $d $dΓ) ↪ pushΓ $d $dΓ
with sc_to_dctx (SCPush $sc $dB) ↪ pushΓ $dB (sc_to_dctx $sc)
with sc_to_dctx (SCI $sc) ↪ pushΓI (sc_to_dctx $sc)
with sc_to_dctx (SCF $sc $df) ↪ pushΓF $df (sc_to_dctx $sc);

symbol len_ctx_sctx [Γ : Context] [A t : Term] [s : Lev] [id : DBId] (d : der Γ t A s) (dΓ : der_context Γ)
                    (sc : SubstContext (inv_type dΓ d) id) (i : DBId) : DBLe (dbsucc i) (len (sc_to_ctx sc)) → DBLe i (len (sc_to_sctx d dΓ sc));
rule len_ctx_sctx _ _ _ db0 _ ↪ dble_0_n _
with len_ctx_sctx _ _ (SC0 _ _) (dbsucc _) $h ↪ dble_S_n $h
with len_ctx_sctx $d $dΓ (SCPush $sc _) (dbsucc $i) $h ↪ dble_n_S (len_ctx_sctx $d $dΓ $sc $i (dble_S_n $h))
with len_ctx_sctx $d $dΓ (SCI $sc) (dbsucc $i) $h ↪ len_ctx_sctx $d $dΓ $sc (dbsucc $i) $h
with len_ctx_sctx $d $dΓ (SCF $sc _) (dbsucc $i) $h ↪ len_ctx_sctx $d $dΓ $sc (dbsucc $i) $h;

symbol lenI_ctx_sctx [Γ : Context] [A t : Term] [s : Lev] [id : DBId] (d : der Γ t A s) (dΓ : der_context Γ)
                    (sc : SubstContext (inv_type dΓ d) id) (i : DBId) : DBLe i (lenI (sc_to_ctx sc)) → DBLe i (lenI (sc_to_sctx d dΓ sc));
rule lenI_ctx_sctx _ _ _ db0 _ ↪ dble_0_n _
with lenI_ctx_sctx _ _ (SC0 _ _) (dbsucc _) $h ↪ $h
with lenI_ctx_sctx $d $dΓ (SCPush $sc _) (dbsucc $i) $h ↪ lenI_ctx_sctx $d $dΓ $sc (dbsucc $i) $h
with lenI_ctx_sctx $d $dΓ (SCI $sc) (dbsucc $i) $h ↪ dble_n_S (lenI_ctx_sctx $d $dΓ $sc $i (dble_S_n $h))
with lenI_ctx_sctx $d $dΓ (SCF $sc _) (dbsucc $i) $h ↪ lenI_ctx_sctx $d $dΓ $sc (dbsucc $i) $h;

// EqSubstContext
constant symbol EqSubstContext [Γ : Context] [A1 A2 : Term] [s : Lev]
                               : der Γ A1 (tuniv s) (lsuc s)
                               → der Γ A2 (tuniv s) (lsuc s)
                               → DBId → TYPE;
symbol esc_to_sc1 [Γ : Context] [A1 A2 : Term] [s : Lev] [id : DBId]
                  [d1 : der Γ A1 (tuniv s) (lsuc s)]
                  [d2 : der Γ A2 (tuniv s) (lsuc s)]
                  : EqSubstContext d1 d2 id → SubstContext d1 id;
symbol esc_to_sc2 [Γ : Context] [A1 A2 : Term] [s : Lev] [id : DBId]
                  [d1 : der Γ A1 (tuniv s) (lsuc s)]
                  [d2 : der Γ A2 (tuniv s) (lsuc s)]
                  : EqSubstContext d1 d2 id → SubstContext d2 id;
constant symbol ESC0 [Γ : Context] [A1 A2 : Term] [s : Lev]
                     (dΓ : der_context Γ)
                     (d1 : der Γ A1 (tuniv s) (lsuc s))
                     (d2 : der Γ A2 (tuniv s) (lsuc s))
                     : der_eq Γ A1 A2 (tuniv s) (lsuc s)
                     → EqSubstContext d1 d2 db0;
constant symbol ESCPush [Γ : Context] [A1 A2 B : Term] [s s' : Lev] [id : DBId]
                        [d1 : der Γ A1 (tuniv s) (lsuc s)]
                        [d2 : der Γ A2 (tuniv s) (lsuc s)]
                        (esc : EqSubstContext d1 d2 id)
                        (dB1 : der (sc_to_ctx (esc_to_sc1 esc)) B (tuniv s') (lsuc s'))
                        (dB2 : der (sc_to_ctx (esc_to_sc2 esc)) B (tuniv s') (lsuc s'))
                        : EqSubstContext d1 d2 (dbsucc id);
constant symbol ESCPushI [Γ : Context] [A1 A2 : Term] [s : Lev] [id : DBId]
                         [d1 : der Γ A1 (tuniv s) (lsuc s)]
                         [d2 : der Γ A2 (tuniv s) (lsuc s)]
                         (esc : EqSubstContext d1 d2 id)
                         : EqSubstContext d1 d2 id;
constant symbol ESCPushF [Γ : Context] [A1 A2 : Term] [s : Lev] [f : FTerm] [id : DBId]
                         [d1 : der Γ A1 (tuniv s) (lsuc s)]
                         [d2 : der Γ A2 (tuniv s) (lsuc s)]
                         (esc : EqSubstContext d1 d2 id)
                         (df1 : der_F (sc_to_ctx (esc_to_sc1 esc)) f)
                         (df2 : der_F (sc_to_ctx (esc_to_sc2 esc)) f)
                         : EqSubstContext d1 d2 id;

rule esc_to_sc1 (ESC0 $dΓ $d1 _ _) ↪ SC0 $d1 $dΓ
with esc_to_sc1 (ESCPush $esc $d1 _) ↪ SCPush (esc_to_sc1 $esc) $d1
with esc_to_sc1 (ESCPushI $esc) ↪ SCI (esc_to_sc1 $esc)
with esc_to_sc1 (ESCPushF $esc $df1 _) ↪ SCF (esc_to_sc1 $esc) $df1
with esc_to_sc2 (ESC0 $dΓ _ $d2 _) ↪ SC0 $d2 $dΓ
with esc_to_sc2 (ESCPush $esc _ $d2) ↪ SCPush (esc_to_sc2 $esc) $d2
with esc_to_sc2 (ESCPushI $esc) ↪ SCI (esc_to_sc2 $esc)
with esc_to_sc2 (ESCPushF $esc _ $df2) ↪ SCF (esc_to_sc2 $esc) $df2;


// Conversion
symbol deq_subst_convert [Γ : Context] (id : DBId)
                         [s s' : Lev] [A1 A2 B f : Term] (t1 t2 : Term)
                         (dΓ : der_context Γ)
                         (deqA : der_eq Γ A1 A2 (tuniv s) (lsuc s))
                         (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                         (esc : EqSubstContext (inv_type dΓ dt1) (inv_type dΓ dt2) id)
                         (_ : der (sc_to_ctx (esc_to_sc1 esc)) f B s') (_ : der_eq Γ t1 t2 A1 s)
                         : der_eq (sc_to_sctx dt1 dΓ (esc_to_sc1 esc))
                                  (subst id (shift_sctx (esc_to_sc1 esc) t1) f)
                                  (subst id (shift_sctx (esc_to_sc2 esc) t2) f)
                                  (subst id (shift_sctx (esc_to_sc1 esc) t1) B) s';
symbol deq_convert_var [Γ : Context] (id : DBId)
                       [s : Lev] [A1 A2 : Term] (t1 t2 : Term)
                       (dΓ : der_context Γ)
                       (deqA : der_eq Γ A1 A2 (tuniv s) (lsuc s))
                       (dt1 : der Γ t1 A1 s) (dt2 : der Γ t2 A2 s)
                       (esc : EqSubstContext (inv_type dΓ dt1) (inv_type dΓ dt2) id)
                       (i : DBId) (_ : der_eq Γ t1 t2 A1 s)
                       : der_eq (sc_to_sctx dt1 dΓ (esc_to_sc1 esc))
                                (dbselect id i (shift_sctx (esc_to_sc1 esc) t1) (tvar i) (tvar (dbprev i)))
                                (dbselect id i (shift_sctx (esc_to_sc2 esc) t2) (tvar i) (tvar (dbprev i)))
                                (subst id (shift_sctx (esc_to_sc1 esc) t1) (shiftgetΓ (sc_to_ctx (esc_to_sc1 esc)) i))
                                (getS (sc_to_ctx (esc_to_sc1 esc)) i);

symbol der_subst [Γ : Context] (id : DBId)
                 [s s' : Lev] [A B C u : Term]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der (sc_to_ctx sc) C B s')
                 : der (sc_to_sctx du dΓ sc) (subst id (shift_sctx sc u) C) (subst id (shift_sctx sc u) B) s';
symbol der_context_subst
       [Γ : Context] (id : DBId)
       [s : Lev] [A u : Term]
       (dΓ : der_context Γ)
       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id)
       (i : DBId)
       (h : DBLe (dbsucc i) (len (sc_to_ctx sc)))
       : der (sc_to_sctx d dΓ sc) (dbselect id i (shift_sctx sc u) (tvar i) (tvar (dbprev i)))
             (subst id (shift_sctx sc u) (shiftgetΓ (sc_to_ctx sc) i))
             (getS (sc_to_ctx sc) i);
symbol der_eq_subst [Γ : Context] (id : DBId)
                    [s s' : Lev] [A B C1 C2 : Term] (u : Term)
                    (dΓ : der_context Γ)
                    (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                    (_ : der_eq (sc_to_ctx sc) C1 C2 B s')
                    : der_eq (sc_to_sctx du dΓ sc) (subst id (shift_sctx sc u) C1) (subst id (shift_sctx sc u) C2) (subst id (shift_sctx sc u) B) s';
symbol der_I_subst [Γ : Context] (id : DBId)
                 [s : Lev] [A u : Term] [i : ITerm]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der_I (sc_to_ctx sc) i)
                 : der_I (sc_to_sctx du dΓ sc) i;
symbol der_eq_I_subst [Γ : Context] (id : DBId)
                 [s : Lev] [A u : Term] [i j : ITerm]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der_eq_I (sc_to_ctx sc) i j)
                 : der_eq_I (sc_to_sctx du dΓ sc) i j;
symbol der_F_subst [Γ : Context] (id : DBId)
                 [s : Lev] [A u : Term] [f : FTerm]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der_F (sc_to_ctx sc) f)
                 : der_F (sc_to_sctx du dΓ sc) f;
symbol der_eq_F_subst [Γ : Context] (id : DBId)
                 [s : Lev] [A u : Term] [f g : FTerm]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der_eq_F (sc_to_ctx sc) f g)
                 : der_eq_F (sc_to_sctx du dΓ sc) f g;
symbol der_isOne_subst [Γ : Context] (id : DBId)
                 [s : Lev] [A u : Term] [f : FTerm]
                 (dΓ : der_context Γ)
                 (du : der Γ u A s) (sc : SubstContext (inv_type dΓ du) id)
                 (_ : der_isOne (sc_to_ctx sc) f)
                 : der_isOne (sc_to_sctx du dΓ sc) f;

symbol der_subst_apply [Γ : Context] (id : DBId) [s : Lev] [A u : Term] (dΓ : der_context Γ)
                       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id) (B C : Term) :
  TEq (apply1 (subst (dbsucc id) (Shift (shift_sctx sc u)) B) (subst id (shift_sctx sc u) C)) (subst id (shift_sctx sc u) (apply1 B C)) ≔
  (teq_trans (Jcong (λ v, apply1 (subst (dbsucc id) (Shift v) B) (subst id v C)) (shift_sctx_ss_compat sc u))
             (teq_trans (teq_inv (teq_subst_apply' id (sctx_to_ss sc) u C B))
                        (Jcong (λ v, subst id v (apply1 B C)) (teq_inv (shift_sctx_ss_compat sc u)))));

symbol der_subst_Iapply [Γ : Context] (id : DBId) [s : Lev] [A u : Term] (dΓ : der_context Γ)
                       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id) (B : Term) (C : ITerm) :
  TEq (applyI1 (subst id (IShift (shift_sctx sc u)) B) C) (subst id (shift_sctx sc u) (applyI1 B C)) ≔
begin
  assume Γ id s A u dΓ d sc B C;
  refine teq_trans (Jcong (λ v, applyI1 (subst id (IShift v) B) C) (shift_sctx_ss_compat sc u)) _;
  refine teq_trans _ (Jcong (λ v, subst id v (applyI1 B C)) (teq_inv (shift_sctx_ss_compat sc u)));
  refine teq_inv (teq_subst_Iapply id (sctx_to_ss sc) C u B);
end;
  // (teq_trans (Jcong (λ v, applyI1 (subst (dbsucc id) (Shift v) B) C) (shift_sctx_ss_compat sc u))
  //            (teq_trans (teq_subst_Iapply id (sctx_to_ss sc) C u B)
  //                       (Jcong (λ v, subst id v (applyI1 B C)) (teq_inv (shift_sctx_ss_compat sc u)))));

symbol der_subst_shift [Γ : Context] (id : DBId) [s : Lev] [A u : Term] (dΓ : der_context Γ)
                       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id) (B : Term) :
  TEq (subst (dbsucc id) (Shift (shift_sctx sc u)) (Shift B)) (Shift (subst id (shift_sctx sc u) B)) ≔
  teq_subst_shift id (shift_sctx sc u) B;
symbol der_subst_Ishift [Γ : Context] (id : DBId) [s : Lev] [A u : Term] (dΓ : der_context Γ)
                       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id) (B : Term) :
  TEq (subst id (IShift (shift_sctx sc u)) (IShift B)) (IShift (subst id (shift_sctx sc u) B)) ≔
  aux_teq_subst_Ishift id db0 (shift_sctx sc u) B;

rule substitution $dΓ $dB $du ↪ der_subst db0 $dΓ $du (SC0 (inv_type $dΓ $du) $dΓ) $dB;

rule sc_to_dsctx _ _ (SC0 _ $dΓ) ↪ $dΓ
with sc_to_dsctx $d $dΓ (SCPush $sc $dA) ↪ pushΓ (der_subst _ $dΓ $d $sc $dA) (sc_to_dsctx $d $dΓ $sc)
with sc_to_dsctx $d $dΓ (SCI $sc) ↪ pushΓI (sc_to_dsctx $d $dΓ $sc)
with sc_to_dsctx $d $dΓ (SCF $sc $df) ↪ pushΓF (der_F_subst _ $dΓ $d $sc $df) (sc_to_dsctx $d $dΓ $sc);

// der_eq_cong_apply
rule der_eq_cong_apply $dΓ $deqA $deqB $deqt _ _ $dt1 $dt2
  ↪ der_eq_trans _ _ _ _ _ _
       (der_eq_subst db0 _ $dΓ $dt1 (SC0 (inv_type $dΓ $dt1) $dΓ) $deqB)
       (deq_subst_convert db0 _ _ $dΓ $deqA $dt1 $dt2 (ESC0 $dΓ (inv_type $dΓ $dt1) (inv_type $dΓ $dt2) $deqA) (inv_eq_t2 (pushIΓ $dΓ $dt1) $deqB) $deqt);
symbol test
       [Γ : Context] (id : DBId)
       [s l l': Lev] [A' u' A x y u u0 : Term] [f : FTerm]
       (dΓ : der_context Γ) (d : der Γ u' A' s) (sc : SubstContext (inv_type dΓ d) id)
       (dA : der (PushI (sc_to_ctx sc)) A (tuniv l) (lsuc l)) (dx : der (sc_to_ctx sc) x (applyI1 A it0) l)
       (dy : der (sc_to_ctx sc) y (applyI1 A it1) l) (df : der_F (sc_to_ctx sc) f)
       (du : der (PushF (IShiftF f) (PushI (sc_to_ctx sc))) u (IShift (tpath A x y)) l) (du0 : der (sc_to_ctx sc) u0 (tpath A x y) l)
       (deq : der_eq (PushF f (sc_to_ctx sc)) u0 (applyI1 u it0) (tpath A x y) l) :
  der_eq (sc_to_sctx d dΓ sc) (subst id (shift_sctx sc u') (thcomp (tpath A x y) f u u0))
         (subst id (shift_sctx sc u') (tlamP (thcomp A (ftmax (IShiftF f) (ftmax (fteq0 db0) (fteq1 db0)))
                        (tsys (IShiftFN db1 f) (ftmax (fteq0 db1) (fteq1 db1)) (tappP (IShift1 u) (itvar db1))
                              (tsys (fteq0 db1) (fteq1 db1) (IShiftN db1 x) (IShiftN db1 y)))
                        (tappP (IShift u0) (itvar db0)))))
         (subst id (shift_sctx sc u') (tpath A x y)) l ≔
begin
  assume Γ id s l l'  A' u' A x y u u0 f dΓ d sc dA dx dy df du du0 deq;
  refine Jeq (TRefl _) (TRefl _) _ (der_eq_hcomp_path _ _ _ _ _ _ _ _
          (der_subst id dΓ d (SCI sc) dA)
          (JT (teq_inv (der_subst_Iapply id dΓ d sc A it0)) (der_subst id dΓ d sc dx))
          (JT (teq_inv (der_subst_Iapply id dΓ d sc A it1)) (der_subst id dΓ d sc dy))
          (der_F_subst id dΓ d sc df)
          (JT (der_subst_Ishift id dΓ d sc (tpath A x y)) (der_subst id dΓ d (SCF (SCI sc) (der_Ishift0F (sc_to_dctx sc) df)) du))
          (der_subst id dΓ d sc du0)
          (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply id dΓ d sc u it0))
               (der_eq_subst id _ dΓ d (SCF sc df) deq)));
  refine Jcong tlamP _;
  refine Jhcomp (TRefl _) (FTRefl _) _ _
{
    refine Jsys (FTRefl _) (FTRefl _) _ _
    {
        refine JappP _ (ITRefl _);
        refine teq_trans (teq_inv (aux_teq_subst_Ishift id db1 (shift_sctx (SCI sc) u') u)) _;
        refine Jcong (λ t, subst id t (IShift1 u)) (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx sc u')))
    }
    {
        refine Jsys (FTRefl _) (FTRefl _) _ _
        {
            refine teq_inv (teq_trans (der_subst_Ishift id dΓ d (SCI sc) (IShift x)) (Jcong IShift (der_subst_Ishift id dΓ d sc x)))
        }
        {
            refine teq_inv (teq_trans (der_subst_Ishift id dΓ d (SCI sc) (IShift y)) (Jcong IShift (der_subst_Ishift id dΓ d sc y)))
        }
    }
}
{
    refine JappP _ (ITRefl _);
    refine teq_inv (der_subst_Ishift id dΓ d sc u0)
}
end;
print test;

// Variable case
rule der_context_subst db0 _ $d (SC0 _ _) db0 _ ↪ $d
with der_context_subst db0 _ _ (SC0 _ _) (dbsucc _) $h ↪
        (der_var (dble_S_n $h))
with @der_context_subst _ $id _ _ $x $dΓ $d (SCI $sc) $i $h ↪
     JtT (aux_teq_Ishift_dbselect db0 $id $i (shift_sctx $sc $x) (tvar $i) (tvar (dbprev $i)))
     (teq_inv (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $x) (shiftgetΓ (sc_to_ctx $sc) $i)))
     (der_Ishift0 (sc_to_dsctx $d $dΓ $sc) (der_context_subst $id $dΓ $d $sc $i $h))
with der_context_subst $id $dΓ $d (SCF $sc $df) $i $h ↪
     der_weakF (sc_to_dsctx $d $dΓ $sc) (der_context_subst $id $dΓ $d $sc $i $h) (der_F_subst $id $dΓ $d $sc $df)
with @der_context_subst _ (dbsucc $id) _ _ $x _ _ (@SCPush _ _ _ _ $A _ _ $sc _) db0 _ ↪
     JT (teq_inv (teq_subst_shift $id (shift_sctx $sc $x) $A))
        (der_var dble_db0)
with @der_context_subst _ (dbsucc $id) _ _ $x $dΓ $d (SCPush $sc $dA) (dbsucc $i) $h ↪
     JtT (teq_inv (teq_select_shift $id $i (shift_sctx $sc $x)))
         (teq_inv (teq_subst_shift $id (shift_sctx $sc $x) (shiftgetΓ (sc_to_ctx $sc) $i)))
         (der_shift0
           (der_subst _ $dΓ $d $sc $dA)
           (sc_to_dsctx $d $dΓ $sc)
           (der_context_subst $id $dΓ $d $sc $i (dble_S_n $h)));

// Structural
rule der_subst $id $dΓ $d $sc (der_empty_face $done) ↪ der_empty_face (der_isOne_subst $id $dΓ $d $sc $done)
with der_subst $id $dΓ $d $sc (der_union_face $df $dg $dtf $dtg $done) ↪
     der_union_face (der_F_subst $id $dΓ $d $sc $df)
                    (der_F_subst $id $dΓ $d $sc $dg)
                    (der_subst $id $dΓ $d (SCF $sc $df) $dtf)
                    (der_subst $id $dΓ $d (SCF $sc $dg) $dtg)
                    (der_isOne_subst $id $dΓ $d $sc $done)
with der_subst $id $dΓ $d $sc (@der_var _ $i $h) ↪ der_context_subst $id $dΓ $d $sc $i $h
with der_subst _ _ _ _ (der_univ) ↪ der_univ
with der_subst _ $dΓ $d $sc (der_type_conv $du $deq) ↪
     der_type_conv (der_subst _ $dΓ $d $sc $du)
                   (der_eq_subst _ _ $dΓ $d $sc $deq)

// Pi-types
with der_subst $id $dΓ $d $sc (der_pi $dA $dB) ↪
     der_pi (der_subst $id $dΓ $d $sc $dA)
            (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
with der_subst $id $dΓ $d $sc (der_abs $dA $dB $dt) ↪
     der_abs (der_subst $id $dΓ $d $sc $dA)
             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dt)
with der_subst $id $dΓ $d $sc (der_app _ _ $u $B $dA $dB $dt $du) ↪
      JT (der_subst_apply $id $dΓ $d $sc $B $u)
         (der_app _ _ _ _ (der_subst $id $dΓ $d $sc $dA) (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                          (der_subst $id $dΓ $d $sc $dt) (der_subst $id $dΓ $d $sc $du))
// integers
with der_subst _ _ _ _ (der_nat) ↪ der_nat
with der_subst _ _ _ _ (der_zero) ↪ der_zero
with der_subst $id $sc $d $dΓ (der_suc $dn) ↪ der_suc (der_subst $id $sc $d $dΓ $dn)
with der_subst $id $dΓ $d $sc (@der_rec _ $s _ $P _ _ _ $dP $dz $dH $dn) ↪
      der_rec (der_subst $id $dΓ $d $sc $dP) (der_subst $id $dΓ $d $sc $dz)
              (JT (Jcong (tpi tnat) (Jpi (Jcong (λ v, tapp v (tvar db0)) (der_subst_shift $id $dΓ $d $sc $P))
                                         (Jcong (λ v, tapp v (tsuc (tvar db1)))
                                                (teq_trans (der_subst_shift (dbsucc $id) $dΓ $d (SCPush $sc (@der_nat _ $s)) (Shift $P))
                                                           (Jcong Shift (der_subst_shift $id $dΓ $d $sc $P ))))))
                  (der_subst $id $dΓ $d $sc $dH))
              (der_subst $id $dΓ $d $sc $dn)
// Sigma types
with der_subst $id $dΓ $d $sc (der_sig $dA $dB) ↪
     der_sig (der_subst $id $dΓ $d $sc $dA)
             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
with der_subst $id $dΓ $d $sc (@der_pair _ _ _ _ $B $a _ $dA $dB $da $db) ↪
      der_pair (der_subst $id $dΓ $d $sc $dA) (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
               (der_subst $id $dΓ $d $sc $da) (JT (teq_inv (der_subst_apply $id $dΓ $d $sc $B $a)) (der_subst $id $dΓ $d $sc $db))
with der_subst $id $dΓ $d $sc (der_p1 $dA $dB $dp) ↪
      der_p1 (der_subst $id $dΓ $d $sc $dA) (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
               (der_subst $id $dΓ $d $sc $dp)
with der_subst $id $dΓ $d $sc (@der_p2 _ _ _ _ $B $p $dA $dB $dp) ↪
      JT (der_subst_apply $id $dΓ $d $sc $B (tp1 $p))
         (der_p2 (der_subst $id $dΓ $d $sc $dA) (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                 (der_subst $id $dΓ $d $sc $dp))
// Sum types
with der_subst $id $dΓ $d $sc (der_sum $dA $dB) ↪
     der_sum (der_subst $id $dΓ $d $sc $dA)
             (der_subst $id $dΓ $d $sc $dB)
with der_subst $id $dΓ $d $sc (der_injl $dA $dB $da) ↪
     der_injl (der_subst $id $dΓ $d $sc $dA)
             (der_subst $id $dΓ $d $sc $dB)
             (der_subst $id $dΓ $d $sc $da)
with der_subst $id $dΓ $d $sc (der_injr $dA $dB $da) ↪
     der_injr (der_subst $id $dΓ $d $sc $dA)
             (der_subst $id $dΓ $d $sc $dB)
             (der_subst $id $dΓ $d $sc $da)
with der_subst $id $dΓ $d $sc (@der_case _ _ _ _ _ _ $P _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_case (der_subst $id $dΓ $d $sc $dA)
              (der_subst $id $dΓ $d $sc $dB)
              (der_subst $id $dΓ $d $sc $dP)
              (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHa))
              (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHb))
              (der_subst $id $dΓ $d $sc $dx)
// Path types
with der_subst $id $dΓ $d $sc (@der_path _ _ $A _ _ $dA $dx $dy) ↪
     der_path (der_subst $id $dΓ $d (SCI $sc) $dA)
              (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $dx))
              (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it1)) (der_subst $id $dΓ $d $sc $dy))
with der_subst $id $dΓ $d $sc (@der_lamP _ _ _ $t $dA $dt) ↪
     JT (Jpath (TRefl _) (der_subst_Iapply $id $dΓ $d $sc $t it0) (der_subst_Iapply $id $dΓ $d $sc $t it1))
        (der_lamP (der_subst $id $dΓ $d (SCI $sc) $dA)
                  (der_subst $id $dΓ $d (SCI $sc) $dt))
with der_subst $id $dΓ $d $sc (der_appP $A _ _ _ $i $dA $dx $dy $dt $di) ↪
     JT (der_subst_Iapply $id $dΓ $d $sc $A $i)
        (der_appP _ _ _ _ _ (der_subst $id $dΓ $d (SCI $sc) $dA)
              (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $dx))
              (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it1)) (der_subst $id $dΓ $d $sc $dy))
                  (der_subst $id $dΓ $d $sc $dt)
                  (der_I_subst $id $dΓ $d $sc $di))
// Systems
with der_subst $id $dΓ $d $sc (der_sys $dA $df $dg $du $dv $done $deq) ↪
     der_sys (der_subst $id $dΓ $d $sc $dA)
             (der_F_subst $id $dΓ $d $sc $df)
             (der_F_subst $id $dΓ $d $sc $dg)
             (der_subst $id $dΓ $d (SCF $sc $df) $du)
             (der_subst $id $dΓ $d (SCF $sc $dg) $dv)
             (der_isOne_subst $id $dΓ $d $sc $done)
             (der_eq_subst $id _ $dΓ $d (SCF $sc (der_F_min $df $dg)) $deq)
with der_subst $id $dΓ $d $sc (der_sys_empty $dA $done) ↪
     der_sys_empty (der_subst $id $dΓ $d $sc $dA)
                   (der_isOne_subst $id $dΓ $d $sc $done)
// Transport
with @der_subst _ $id _ _ _ _ _ $u $dΓ $d $sc (@der_transp _ _ $A _ _ $dA $df $du $deq) ↪
     JT (der_subst_Iapply $id $dΓ $d $sc $A it1)
        (der_transp (der_subst $id $dΓ $d (SCI $sc) $dA)
                    (der_F_subst $id $dΓ $d $sc $df)
                    (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $du))
                    (Jeq (TRefl _) (TRefl _)
                         (teq_trans (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $u) (applyI1 $A it0))
                                    (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
                         (der_eq_subst $id _ $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deq)))
// hcomp
with @der_subst _ $id _ _ _ _ _ $u $dΓ $d $sc (@der_hcomp _ _ $A _ $u' _ $dA $df $du $du0 $deq) ↪
     der_hcomp (der_subst $id $dΓ $d $sc $dA)
               (der_F_subst $id $dΓ $d $sc $df)
               (JT (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $u) $A) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $du))
               (der_subst $id $dΓ $d $sc $du0)
               (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $u' it0)) (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
// Structural (conversion)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_refl _ _ _ _ $du) ↪ der_eq_refl _ _ _ _ (der_subst $id $dΓ $d $sc $du)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_trans _ _ _ _ _ _ $d1 $d2) ↪
     der_eq_trans _ _ _ _ _ _ (der_eq_subst $id _ $dΓ $d $sc $d1) (der_eq_subst $id _ $dΓ $d $sc $d2)
with der_eq_subst _ _ $dΓ $d $sc (der_eq_sym _ _ _ _ _ $deq) ↪
     der_eq_sym _ _ _ _ _ (der_eq_subst _ _ $dΓ $d $sc $deq)
with der_eq_subst _ _ $dΓ $d $sc (der_eq_conv _ _ _ _ _ _ $du $deq) ↪
     der_eq_conv _ _ _ _ _ _ (der_eq_subst _ _ $dΓ $d $sc $du)
                             (der_eq_subst _ _ $dΓ $d $sc $deq)
with der_eq_subst _ _ $dΓ $d $sc (der_eq_isOne_zero _ _ _ _ _ $done) ↪
     der_eq_isOne_zero _ _ _ _ _ (der_isOne_subst _ $dΓ $d $sc $done)
with der_eq_subst _ _ $dΓ $d $sc (der_eq_isOne_max _ _ _ _ _ _ _ $df $dg $d1 $d2 $done) ↪
     der_eq_isOne_max _ _ _ _ _ _ _
                      (der_F_subst _ $dΓ $d $sc $df)
                      (der_F_subst _ $dΓ $d $sc $dg)
                      (der_eq_subst _ _ $dΓ $d (SCF $sc $df) $d1)
                      (der_eq_subst _ _ $dΓ $d (SCF $sc $dg) $d2)
                      (der_isOne_subst _ $dΓ $d $sc $done)
// Computation rules
with der_eq_subst _ _ $dΓ $d $sc (der_eq_beta _ _ _ $u _ $t $B $dA $dB $dt $du) ↪
     Jeq (der_subst_apply _ $dΓ $d $sc $B $u) (TRefl _) (der_subst_apply _ $dΓ $d $sc $t $u)
         (der_eq_beta _ _ _ _ _ _ _ (der_subst _ $dΓ $d $sc $dA)
                      (der_subst _ $dΓ $d (SCPush $sc $dA) $dB)
                      (der_subst _ $dΓ $d (SCPush $sc $dA) $dt) (der_subst _ $dΓ $d $sc $du))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_eta _ _ _ _ _ $f $dA $dB $df) ↪
     Jeq (TRefl _) (Jabs (TRefl _) (Japp (teq_inv (der_subst_shift $id $dΓ $d $sc $f)) (TRefl _))) (TRefl _)
         (der_eq_eta _ _ _ _ _ _ (der_subst _ $dΓ $d $sc $dA)
                      (der_subst _ $dΓ $d (SCPush $sc $dA) $dB)
                      (der_subst _ $dΓ $d $sc $df))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_rec_zero _ $s _ $P _ _ $dP $dz $dH) ↪
      der_eq_rec_zero _ $s _ _ _ _ (der_subst $id $dΓ $d $sc $dP) (der_subst $id $dΓ $d $sc $dz)
              (JT (Jcong (tpi tnat) (Jpi (Jcong (λ v, tapp v (tvar db0)) (der_subst_shift $id $dΓ $d $sc $P))
                                         (Jcong (λ v, tapp v (tsuc (tvar db1)))
                                                (teq_trans (der_subst_shift (dbsucc $id) $dΓ $d (SCPush $sc (@der_nat _ $s)) (Shift $P))
                                                           (Jcong Shift (der_subst_shift $id $dΓ $d $sc $P ))))))
                  (der_subst $id $dΓ $d $sc $dH))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_rec_suc _ $s _ $P _ _ _ $dP $dz $dH $dn) ↪
      der_eq_rec_suc _ $s _ _ _ _ _ (der_subst $id $dΓ $d $sc $dP) (der_subst $id $dΓ $d $sc $dz)
              (JT (Jcong (tpi tnat) (Jpi (Jcong (λ v, tapp v (tvar db0)) (der_subst_shift $id $dΓ $d $sc $P))
                                         (Jcong (λ v, tapp v (tsuc (tvar db1)))
                                                (teq_trans (der_subst_shift (dbsucc $id) $dΓ $d (SCPush $sc (@der_nat _ $s)) (Shift $P))
                                                           (Jcong Shift (der_subst_shift $id $dΓ $d $sc $P ))))))
                  (der_subst $id $dΓ $d $sc $dH))
              (der_subst _ $dΓ $d $sc $dn)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_p1 _ _ _ _ $u $B _ $dA $du $dB $dv) ↪
      der_eq_p1 _ _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA) (der_subst _ $dΓ $d $sc $du)
                              (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                              (JT (teq_inv (der_subst_apply $id $dΓ $d $sc $B $u)) (der_subst $id $dΓ $d $sc $dv))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_p2 _ _ _ _ $u $B _ $dA $du $dB $dv) ↪
      Jeq (der_subst_apply $id $dΓ $d $sc $B $u) (TRefl _) (TRefl _)
          (der_eq_p2 _ _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA) (der_subst _ $dΓ $d $sc $du)
                     (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                     (JT (teq_inv (der_subst_apply $id $dΓ $d $sc $B $u)) (der_subst $id $dΓ $d $sc $dv)))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_pair _ _ _ _ $B $t _ $dA $dB $dt $du $de1 $de2) ↪
     der_eq_pair _ _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA)
                 (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
                 (der_subst _ $dΓ $d $sc $dt) (der_subst _ $dΓ $d $sc $du)
                 (der_eq_subst _ _ $dΓ $d $sc $de1)
                 (Jeq (teq_inv (der_subst_apply $id $dΓ $d $sc $B (tp1 $t))) (TRefl _) (TRefl _) (der_eq_subst _ _ $dΓ $d $sc $de2))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_case_left _ _ _ _ _ _ $P _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_eq_case_left _ _ _ _ _ _ _ _ _ _
                      (der_subst $id $dΓ $d $sc $dA)
                      (der_subst $id $dΓ $d $sc $dB)
                      (der_subst $id $dΓ $d $sc $dP)
                      (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHa))
                      (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHb))
                      (der_subst $id $dΓ $d $sc $dx)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_case_right _ _ _ _ _ _ $P _ _ _ $dA $dB $dP $dHa $dHb $dx) ↪
     der_eq_case_right _ _ _ _ _ _ _ _ _ _
                      (der_subst $id $dΓ $d $sc $dA)
                      (der_subst $id $dΓ $d $sc $dB)
                      (der_subst $id $dΓ $d $sc $dP)
                      (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHa))
                      (JT (Jpi (TRefl _) (Japp (der_subst_shift $id $dΓ $d $sc $P) (TRefl _))) (der_subst $id $dΓ $d $sc $dHb))
                      (der_subst $id $dΓ $d $sc $dx)
with der_eq_subst _ _ $dΓ $d $sc (der_eq_betaP _ _ $A $t $i $dA $dt $di) ↪
     Jeq (der_subst_Iapply _ $dΓ $d $sc $A $i) (TRefl _) (der_subst_Iapply _ $dΓ $d $sc $t $i)
         (der_eq_betaP _ _ _ _ _
                       (der_subst _ $dΓ $d (SCI $sc) $dA)
                       (der_subst _ $dΓ $d (SCI $sc) $dt) (der_I_subst _ $dΓ $d $sc $di))
with der_eq_subst _ _ $dΓ $d $sc (der_eq_etaP _ _ $A $t _ _ $dA $dx $dy $dt) ↪
     Jeq (TRefl _) (Jcong tlamP (JappP (teq_inv (der_subst_Ishift _ $dΓ $d $sc $t)) (ITRefl _))) (TRefl _)
         (der_eq_etaP _ _ _ _ _ _
                       (der_subst _ $dΓ $d (SCI $sc) $dA)
                       (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it0)) (der_subst _ $dΓ $d $sc $dx))
                       (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it1)) (der_subst _ $dΓ $d $sc $dy))
                       (der_subst _ $dΓ $d $sc $dt))
with der_eq_subst _ _ $dΓ $d $sc (der_eq_appP_zero _ _ $A _ _ _ $dA $dx $dy $dt) ↪
     Jeq (der_subst_Iapply _ $dΓ $d $sc $A it0) (TRefl _) (TRefl _)
         (der_eq_appP_zero _ _ _ _ _ _
                           (der_subst _ $dΓ $d (SCI $sc) $dA)
                           (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it0)) (der_subst _ $dΓ $d $sc $dx))
                           (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it1)) (der_subst _ $dΓ $d $sc $dy))
                           (der_subst _ $dΓ $d $sc $dt))
with der_eq_subst _ _ $dΓ $d $sc (der_eq_appP_one _ _ $A _ _ _ $dA $dx $dy $dt) ↪
     Jeq (der_subst_Iapply _ $dΓ $d $sc $A it1) (TRefl _) (TRefl _)
         (der_eq_appP_one _ _ _ _ _ _
                           (der_subst _ $dΓ $d (SCI $sc) $dA)
                           (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it0)) (der_subst _ $dΓ $d $sc $dx))
                           (JT (teq_inv (der_subst_Iapply _ $dΓ $d $sc $A it1)) (der_subst _ $dΓ $d $sc $dy))
                           (der_subst _ $dΓ $d $sc $dt))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_sys_left _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq $done) ↪
     der_eq_sys_left _ _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA)
                                   (der_F_subst $id $dΓ $d $sc $df)
                                   (der_F_subst $id $dΓ $d $sc $dg)
                                   (der_subst $id $dΓ $d (SCF $sc $df) $du)
                                   (der_subst $id $dΓ $d (SCF $sc $dg) $dv)
                                   (der_eq_subst $id _ $dΓ $d (SCF $sc (der_F_min $df $dg)) $deq)
                                   (der_isOne_subst $id $dΓ $d $sc $done)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_sys_right _ _ _ _ _ _ _ $dA $df $dg $du $dv $deq $done) ↪
     der_eq_sys_right _ _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA)
                                   (der_F_subst $id $dΓ $d $sc $df)
                                   (der_F_subst $id $dΓ $d $sc $dg)
                                   (der_subst $id $dΓ $d (SCF $sc $df) $du)
                                   (der_subst $id $dΓ $d (SCF $sc $dg) $dv)
                                   (der_eq_subst $id _ $dΓ $d (SCF $sc (der_F_min $df $dg)) $deq)
                                   (der_isOne_subst $id $dΓ $d $sc $done)
with der_eq_subst $id $u $dΓ $d $sc (der_eq_transp _ _ $A _ _ $dA $df $du $deq $done) ↪
     Jeq (der_subst_Iapply $id $dΓ $d $sc $A it1) (TRefl _) (TRefl _)
         (der_eq_transp _ _ _ _ _ (der_subst $id $dΓ $d (SCI $sc) $dA)
                        (der_F_subst $id $dΓ $d $sc $df)
                        (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $du))
                        (Jeq (TRefl _) (TRefl _)
                             (teq_trans (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $u) (applyI1 $A it0))
                                        (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
                             (der_eq_subst $id _ $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deq))
                        (der_isOne_subst $id $dΓ $d $sc $done))
with der_eq_subst $id $u $dΓ $d $sc (der_eq_transp_pi _ _ _ $A $B $f _ $v $dA $dB $df $deqA $deqB $du $dv) ↪
     Jeq (teq_trans (Jcong (λ v', apply1 v' (subst $id (shift_sctx $sc $u) $v))
                           (teq_trans (Jcong (λ v1, applyI1 (subst (dbsucc $id) v1 $B) it1) (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u)))
                                      (der_subst_Iapply (dbsucc $id) $dΓ $d (SCPush $sc (Isubstitution (sc_to_dctx $sc) $dA der_I_1)) $B it1)))
                    (der_subst_apply $id $dΓ $d $sc (applyI1 $B it1) $v))
         (TRefl _)
         (Jtransp (teq_trans
                   (Jcong (λ w, apply1 (subst (dbsucc $id) (Shift (shift_sctx (SCI $sc) $u)) $B) w)
                          (Jtransp (teq_trans
                                    (Jcong (λ w, applyI1 w (itmax (itvar db1) (itsym (itvar db0))))
                                           (teq_trans (teq_trans
                                                       (Jcong IShift1 (teq_trans
                                                                       (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u) $A))
                                                                       (Jcong (λ w, subst $id w (IShift1 $A))
                                                                              (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u))))))
                                                       (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI (SCI $sc)) $u) (IShift1 $A))))
                                                      (Jcong (λ w, subst $id w (IShift1 (IShift1 $A)))
                                                             (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx (SCI $sc) $u))))))
                                    (der_subst_Iapply $id $dΓ $d (SCI (SCI $sc)) (IShift1 (IShift1 $A)) (itmax (itvar db1) (itsym (itvar db0)))))
                                   (FTRefl (ftmax (IshiftF db0 $f) (fteq0 db0)))
                                   (teq_inv (der_subst_Ishift $id $dΓ $d $sc $v))))
                   (der_subst_apply $id $dΓ $d (SCI $sc) $B (ttransp (applyI1 (IShift1 (IShift1 $A)) (itmax (itvar db1) (itsym (itvar db0))))
                                                                     (ftmax (IShiftF $f) (fteq0 db0)) (IShift $v))))
                  (FTRefl _)
                  (Japp (TRefl _) (Jtransp (teq_trans
                                            (Jcong (λ w, applyI1 w (itsym (itvar db0)))
                                                   (teq_trans (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u) $A))
                                                              (Jcong (λ w, subst $id w (IShift1 $A))
                                                                     (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u))))))
                                            (der_subst_Iapply $id $dΓ $d (SCI $sc) (IShift1 $A) (itsym (itvar db0))))
                                           (FTRefl _) (TRefl _))))
         (der_eq_transp_pi _ _ _ _ _ _ _ _ (der_subst $id $dΓ $d (SCI $sc) $dA) (der_subst (dbsucc $id) $dΓ $d (SCPush (SCI $sc) $dA) $dB)
                           (der_F_subst $id $dΓ $d $sc $df)
                           (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $A it0))
                                                               (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
                                (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqA))
                           (Jeq (TRefl _) (TRefl _)
                                (teq_trans (Jcong (λ w, subst (dbsucc $id) w (IShift (applyI1 $B it0))) (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u)))
                                           (teq_trans (der_subst_Ishift (dbsucc $id) $dΓ $d (SCPush $sc (Isubstitution (sc_to_dctx $sc) $dA der_I_0))
                                                                                            (applyI1 $B it0))
                                                      (Jcong IShift (teq_trans (teq_inv (der_subst_Iapply (dbsucc $id) $dΓ $d (SCPush $sc (Isubstitution (sc_to_dctx $sc) $dA der_I_0)) $B it0))
                                                                               (Jcong (λ w, applyI1 (subst (dbsucc $id) w $B) it0) (teq_inv (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u))))))))
                                (der_eq_subst (dbsucc $id) $u $dΓ $d (SCPush (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df))
                                                                             (der_weakF (pushΓI (sc_to_dctx $sc)) $dA (der_Ishift0F (sc_to_dctx $sc) $df))) $deqB))
                           (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc (tpi $A $B) it0)) (der_subst $id $dΓ $d $sc $du))
                           (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it1)) (der_subst $id $dΓ $d $sc $dv)))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_transp_univ _ _ _ _ $df $dA) ↪ der_eq_transp_univ _ _ _ _ (der_F_subst $id $dΓ $d $sc $df)
                                                                                                      (der_subst $id $dΓ $d $sc $dA)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_transp_zero _ _ _ $df) ↪ der_eq_transp_zero _ _ _ (der_F_subst $id $dΓ $d $sc $df)
with der_eq_subst $id _ $dΓ $d $sc (der_eq_transp_suc _ _ _ _ $df $dn) ↪ der_eq_transp_suc _ _ _ _ (der_F_subst $id $dΓ $d $sc $df)
                                                                                                   (der_subst $id $dΓ $d $sc $dn)
with der_eq_subst $id $u $dΓ $d $sc (der_eq_transp_sig _ _ _ $A $B $f $v $dA $dB $df $deqA $deqB $du) ↪
     Jeq (der_subst_Iapply $id $dΓ $d $sc (tsig $A $B) it1) (TRefl _)
         (Jpair (TRefl _) (Jtransp (teq_trans (Jcong (λ t, apply1 (subst (dbsucc $id) (Shift (shift_sctx (SCI $sc) $u)) $B) t)
                                                     (teq_trans (Jcong (λ v1, ttranspFill (subst $id (IShift v1) $A) $f (tp1 (subst $id v1 $v)))
                                                                       (shift_sctx_ss_compat $sc $u))
                                                                (teq_trans (teq_subst_transpFill $id (sctx_to_ss $sc) $u $A $f (tp1 $v))
                                                                           (Jcong (λ v1, subst $id (IShift v1) (ttranspFill $A $f (tp1 $v)))
                                                                                  (teq_inv (shift_sctx_ss_compat $sc $u))))))
                                              (der_subst_apply $id $dΓ $d (SCI $sc) $B (ttranspFill $A $f (tp1 $v)))) (FTRefl _) (TRefl _)))
         (der_eq_transp_sig _ _ _ _ _ _ _
          (der_subst $id $dΓ $d (SCI $sc) $dA)
          (der_subst (dbsucc $id) $dΓ $d (SCPush (SCI $sc) $dA) $dB)
          (der_F_subst $id $dΓ $d $sc $df)
          (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $A it0))
                                              (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
               (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqA))
          (Jeq (TRefl _) (TRefl _)
               (teq_trans (Jcong (λ w, subst (dbsucc $id) w (IShift (applyI1 $B it0))) (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u)))
                          (teq_trans (der_subst_Ishift (dbsucc $id) $dΓ $d (SCPush $sc (Isubstitution (sc_to_dctx $sc) $dA der_I_0)) (applyI1 $B it0))
                                     (Jcong IShift (teq_trans (teq_inv (der_subst_Iapply (dbsucc $id) $dΓ $d (SCPush $sc (Isubstitution (sc_to_dctx $sc) $dA der_I_0)) $B it0))
                                                              (Jcong (λ w, applyI1 (subst (dbsucc $id) w $B) it0)
                                                                     (teq_inv (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u))))))))
               (der_eq_subst (dbsucc $id) $u $dΓ $d (SCPush (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df))
                                                            (der_weakF (pushΓI (sc_to_dctx $sc)) $dA (der_Ishift0F (sc_to_dctx $sc) $df))) $deqB))
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc (tsig $A $B) it0)) (der_subst $id $dΓ $d $sc $du)))
with der_eq_subst $id $u $dΓ $d $sc (der_eq_transp_sum_left _ _ _ $A $B _ _ $dA $dB $df $du $deqA $deqB) ↪
     Jeq (der_subst_Iapply $id $dΓ $d $sc (tsum $A $B) it1) (TRefl _) (TRefl _)
         (der_eq_transp_sum_left _ _ _ _ _ _ _
          (der_subst $id $dΓ $d (SCI $sc) $dA)
          (der_subst $id $dΓ $d (SCI $sc) $dB)
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $du))
          (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $A it0))
                                              (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
               (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqA))
          (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $B it0))
                                              (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $B it0))))
               (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqB)))
with der_eq_subst $id $u $dΓ $d $sc (der_eq_transp_sum_right _ _ _ $A $B _ _ $dA $dB $df $du $deqA $deqB) ↪
     Jeq (der_subst_Iapply $id $dΓ $d $sc (tsum $A $B) it1) (TRefl _) (TRefl _)
         (der_eq_transp_sum_right _ _ _ _ _ _ _
          (der_subst $id $dΓ $d (SCI $sc) $dA)
          (der_subst $id $dΓ $d (SCI $sc) $dB)
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $B it0)) (der_subst $id $dΓ $d $sc $du))
          (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $A it0))
                                              (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0))))
               (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqA))
          (Jeq (TRefl _) (TRefl _) (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $B it0))
                                              (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $B it0))))
               (der_eq_subst $id $u $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqB)))
with der_eq_subst $id $u' $dΓ $d $sc (der_eq_transp_path _ _ $A $x $y $f $u $dA $dx $dy $df $du $deqA $deqx $deqy) ↪
     Jeq (der_subst_Iapply $id $dΓ $d $sc (tpath $A $x $y) it1) (TRefl _)
         (Jcong tlamP (teq_trans (teq_trans (Jcomp (teq_trans (Jcong (λ t, applyI1 t (itvar db0)) (teq_trans (Jcong (λ t, applyI1 t (itvar db2)) (teq_trans //
                       (Jcong (Ishift db2) (teq_inv (aux_teq_subst_Ishift $id db2 (shift_sctx (SCI (SCI $sc)) $u') $A)))
                       (teq_trans (teq_inv (aux_teq_subst_Ishift $id db2 (Ishift db2 (shift_sctx (SCI (SCI $sc)) $u')) (Ishift db2 $A)))
                                  (Jcong (λ t, subst $id t (Ishift db2 (Ishift db2 $A))) (teq_trans (teq_trans (Jcong (Ishift db2) (teq_trans //
                                   (teq_inv (aux_teq_Ishift_Ishift0 db1 (IShift (shift_sctx $sc $u'))))
                                   (Jcong IShift (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u'))))))
                                   (teq_trans (teq_inv (aux_teq_Ishift_Ishift0 db1 (IShift (IShift (shift_sctx $sc $u')))))
                                              (Jcong IShift (teq_inv (aux_teq_Ishift_Ishift0 db0 (IShift (shift_sctx $sc $u')))))))
                                   (Jcong (λ t, IShift (IShift (IShift (IShift t)))) (shift_sctx_ss_compat $sc $u')))))))
                       (teq_inv (teq_subst_Iapply $id (SSI (SSI (SSI (sctx_to_ss $sc)))) (itvar db2) $u' (Ishift db2 (Ishift db2 $A))))))
                       (teq_inv (teq_subst_Iapply $id (SSI (SSI (sctx_to_ss $sc))) (itvar db0) $u' (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)))))
                         (FTRefl _)
                         (Jsys (FTRefl _) (FTRefl _)
                               (JappP (teq_trans (Jcong IShift (teq_inv (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $u') $u)))
                                                 (teq_trans (teq_inv (aux_teq_subst_Ishift $id db0 (IShift (shift_sctx $sc $u')) (IShift $u)))
                                                            (Jcong (λ t, subst $id (IShift t) (IShift (IShift $u))) (shift_sctx_ss_compat (SCI $sc) $u'))))
                                      (ITRefl (itvar db1)))
                               (Jsys (FTRefl (fteq0 db1)) (FTRefl (fteq1 db1))
                                     (teq_trans (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u') $x))
                                                (teq_trans (Jcong (λ t, subst $id t (IShift1 $x)) (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u'))))
                                                           (Jcong (λ t, subst $id (IShift t) (IShift1 $x)) (shift_sctx_ss_compat (SCI $sc) $u'))))
                                     (teq_trans (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u') $y))
                                                (teq_trans (Jcong (λ t, subst $id t (IShift1 $y)) (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u'))))
                                                           (Jcong (λ t, subst $id (IShift t) (IShift1 $y)) (shift_sctx_ss_compat (SCI $sc) $u'))))))
                         (JappP (teq_trans (teq_inv (aux_teq_subst_Ishift $id db0 (shift_sctx $sc $u') $u))
                                           (Jcong (λ t, subst $id t (IShift $u)) (shift_sctx_ss_compat (SCI $sc) $u')))
                                (ITRefl (itvar db0))))
                  (teq_subst_comp $id (sctx_to_ss (SCI $sc)) $u' (applyI1 (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)) (itvar db0))
                                  (ftmax (IShiftF $f) (ftmax (fteq0 db0) (fteq1 db0)))
                                  (tsys (IShiftFN db1 $f) (ftmax (fteq0 db1) (fteq1 db1))
                                        (tappP (IShift (IShift $u)) (itvar db1)) (tsys (fteq0 db1) (fteq1 db1) (IShift1 $x) (IShift1 $y)))
                                  (tappP (IShift $u) (itvar db0))))
                 (Jcong (λ t, subst $id (IShift t) (tcomp (applyI1 (applyI1 (Ishift db2 (Ishift db2 $A)) (itvar db2)) (itvar db0))
                                                          (ftmax (IShiftF $f) (ftmax (fteq0 db0) (fteq1 db0)))
                                                          (tsys (IShiftFN db1 $f) (ftmax (fteq0 db1) (fteq1 db1))
                                                                (tappP (IShift (IShift $u)) (itvar db1))
                                                                (tsys (fteq0 db1) (fteq1 db1) (IShift1 $x) (IShift1 $y)))
                                                          (tappP (IShift $u) (itvar db0))))
                        (teq_inv (shift_sctx_ss_compat $sc $u')))))
         (der_eq_transp_path _ _ _ _ _ _ _
          (der_subst $id $dΓ $d (SCI (SCI $sc)) $dA)
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d (SCI $sc) $A it0)) (der_subst $id $dΓ $d (SCI $sc) $dx))
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d (SCI $sc) $A it1)) (der_subst $id $dΓ $d (SCI $sc) $dy))
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc (tpath $A $x $y) it0)) (der_subst $id $dΓ $d $sc $du))
          (Jeq (TRefl _) (TRefl _)
               (teq_trans (Jcong (λ t, subst $id t (IShift1 (Isubst db1 it0 $A))) (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u')))
                          (teq_trans (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u') (Isubst db1 it0 $A))
                                     (Jcong IShift1 (teq_trans (Jcong (λ v, subst $id v (Isubst db1 it0 $A)) (shift_sctx_ss_compat (SCI $sc) $u'))
                                                               (teq_trans (teq_trans
                                                                           (aux_teq_subst_Isubst' (IMI (IM0 (sctx_to_ss $sc))) it0 $u' $A)
                                                                           (Jcong (λ t, Isubst db1 it0 (subst $id t $A))
                                                                                  (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_seq (sctx_to_ss $sc) $u')))))
                                                                          (Jcong (λ v, Isubst db1 it0 (subst $id (IShift (IShift v)) $A))
                                                                                 (teq_inv (shift_sctx_ss_compat $sc $u'))))))))
               (der_eq_subst $id $u' $dΓ $d (SCF (SCI (SCI $sc)) (der_Ishift0F (sc_to_dctx (SCI $sc)) (der_Ishift0F (sc_to_dctx $sc) $df))) $deqA))
          (Jeq (teq_inv (der_subst_Iapply $id $dΓ $d (SCI $sc) $A it0)) (TRefl _)
               (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $x it0))
                          (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $x it0))))
               (der_eq_subst $id $u' $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqx))
          (Jeq (teq_inv (der_subst_Iapply $id $dΓ $d (SCI $sc) $A it1)) (TRefl _)
               (teq_trans (der_subst_Ishift $id $dΓ $d $sc (applyI1 $y it0))
                          (Jcong IShift (teq_inv (der_subst_Iapply $id $dΓ $d $sc $y it0))))
               (der_eq_subst $id $u' $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $deqy)))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp _ _ $A _ $u _ $dA $df $du $du0 $deq $done) ↪
     Jeq (TRefl _) (TRefl _) (der_subst_Iapply $id $dΓ $d $sc $u it1)
         (der_eq_hcomp _ _ _ _ _ _ (der_subst $id $dΓ $d $sc $dA)
                       (der_F_subst $id $dΓ $d $sc $df)
                       (JT (der_subst_Ishift $id $dΓ $d $sc $A) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $du))
                       (der_subst $id $dΓ $d $sc $du0)
                       (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $u it0))
                            (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
                       (der_isOne_subst $id $dΓ $d $sc $done))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp_pi _ _ _ $A $B _ $u _ $v $dA $dB $df $du $du0 $deq $dv) ↪
     Jeq (der_subst_apply $id $dΓ $d $sc $B $v) (TRefl _)
         (Jhcomp (der_subst_apply $id $dΓ $d $sc $B $v) (FTRefl _) (Japp (TRefl _) (teq_inv (der_subst_Ishift $id $dΓ $d $sc $v))) (TRefl _))
         (der_eq_hcomp_pi _ _ _ _ _ _ _ _ _
          (der_subst $id $dΓ $d $sc $dA)
          (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (der_subst_Ishift $id $dΓ $d $sc (tpi $A $B)) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $du))
          (der_subst $id $dΓ $d $sc $du0)
          (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $u it0))
               (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
          (der_subst $id $dΓ $d $sc $dv))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp_zero _ _ _ $n $df $dn $deq) ↪
     der_eq_hcomp_zero _ _ _ _ (der_F_subst $id $dΓ $d $sc $df)
                               (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $dn)
                               (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $n it0)) (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp_suc _ _ _ $n _ $df $dn $dn0 $deq) ↪
     der_eq_hcomp_suc _ _ _ _ _ (der_F_subst $id $dΓ $d $sc $df)
                                (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $dn)
                                (der_subst $id $dΓ $d $sc $dn0)
                                (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $n it0)) (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
with der_eq_subst $id $u' $dΓ $d $sc (der_eq_hcomp_sig _ _ _ $A $B $f $u $u0 $dA $dB $df $du $du0 $deq ) ↪
     Jeq (TRefl _) (TRefl _)
         (Jpair (TRefl _)
                (teq_trans (teq_trans (teq_trans (Jcomp (teq_trans (teq_trans //
                 (Jcong (λ t, apply1 (IShift (subst (dbsucc $id) (Shift (shift_sctx $sc $u')) $B)) t)
                        (teq_trans (teq_trans (Jcong (λ t, thfill (subst $id t $A) $f (tp1 (subst $id (IShift t) $u)) (tp1 (subst $id t $u0)))
                                                     (shift_sctx_ss_compat $sc $u'))
                                              (teq_subst_hfill $id (sctx_to_ss $sc) $u' $A $f (tp1 $u) (tp1 $u0)))
                                   (Jcong (λ t, subst $id t (thfill $A $f (tp1 $u) (tp1 $u0))) (teq_inv (shift_sctx_ss_compat (SCI $sc) $u')))))
                 (Jcong (λ t, apply1 t (subst $id (shift_sctx (SCI $sc) $u') (thfill $A $f (tp1 $u) (tp1 $u0))))
                        (teq_trans (teq_inv (der_subst_Ishift (dbsucc $id) $dΓ $d (SCPush $sc $dA) $B))
                                   (Jcong (λ t, subst (dbsucc $id) t (IShift $B)) (teq_inv (aux_teq_shift_Ishift db0 db0 (shift_sctx $sc $u')))))))
                 (der_subst_apply $id $dΓ $d (SCI $sc) (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))))
                 (FTRefl _) (TRefl _) (TRefl _))
                 (Jcong (λ t, tcomp (subst $id (IShift t) (apply1 (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))))
                                    $f (subst $id (IShift t) (tp2 $u)) (subst $id t (tp2 $u0))) (shift_sctx_ss_compat $sc $u')))
                 (teq_subst_comp $id (sctx_to_ss $sc) $u' (apply1 (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))) $f (tp2 $u) (tp2 $u0)))
                 (Jcong (λ t, subst $id t (tcomp (apply1 (IShift $B) (thfill $A $f (tp1 $u) (tp1 $u0))) $f (tp2 $u) (tp2 $u0)))
                        (teq_inv (shift_sctx_ss_compat $sc $u')))))
         (der_eq_hcomp_sig _ _ _ _ _ _ _ _
          (der_subst $id $dΓ $d $sc $dA)
          (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (der_subst_Ishift $id $dΓ $d $sc (tsig $A $B)) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $du))
          (der_subst $id $dΓ $d $sc $du0)
          (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $u it0))
               (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq)))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp_sum_left _ _ _ $A _ _ $a _ $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_left _ _ _ _ _ _ _ _
                           (der_subst $id $dΓ $d $sc $dA)
                           (der_subst $id $dΓ $d $sc $dB)
                           (der_F_subst $id $dΓ $d $sc $df)
                           (JT (der_subst_Ishift $id $dΓ $d $sc $A) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $da))
                           (der_subst $id $dΓ $d $sc $da0)
                           (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $a it0)) (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
with der_eq_subst $id _ $dΓ $d $sc (der_eq_hcomp_sum_right _ _ _ _ $B _ $a _ $dA $dB $df $da $da0 $deq) ↪
     der_eq_hcomp_sum_right _ _ _ _ _ _ _ _
                           (der_subst $id $dΓ $d $sc $dA)
                           (der_subst $id $dΓ $d $sc $dB)
                           (der_F_subst $id $dΓ $d $sc $df)
                           (JT (der_subst_Ishift $id $dΓ $d $sc $B) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $da))
                           (der_subst $id $dΓ $d $sc $da0)
                           (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $a it0)) (der_eq_subst $id _ $dΓ $d (SCF $sc $df) $deq))
with der_eq_subst $id $u' $dΓ $d $sc (der_eq_hcomp_path _ _ $A $x $y $f $u $u0 $dA $dx $dy $df $du $du0 $deq) ↪
     Jeq (TRefl _) (TRefl _)
         (Jcong tlamP (Jhcomp (TRefl _) (FTRefl _)
                              (Jsys (FTRefl _) (FTRefl _)
                                    (JappP (teq_trans (teq_inv (aux_teq_subst_Ishift $id db1 (shift_sctx (SCI $sc) $u') $u))
                                                      (Jcong (λ t, subst $id t (IShift1 $u)) (teq_inv (aux_teq_Ishift_Ishift0 db0 (shift_sctx $sc $u')))))
                                           (ITRefl (itvar db1)))
                                    (Jsys (FTRefl (fteq0 db1)) (FTRefl (fteq1 db1))
                                          (teq_inv (teq_trans (der_subst_Ishift $id $dΓ $d (SCI $sc) (IShift $x))
                                                              (Jcong IShift (der_subst_Ishift $id $dΓ $d $sc $x))))
                                          (teq_inv (teq_trans (der_subst_Ishift $id $dΓ $d (SCI $sc) (IShift $y))
                                                              (Jcong IShift (der_subst_Ishift $id $dΓ $d $sc $y))))))
                              (JappP (teq_inv (der_subst_Ishift $id $dΓ $d $sc $u0)) (ITRefl (itvar db0)))))
         (der_eq_hcomp_path _ _ _ _ _ _ _ _
          (der_subst $id $dΓ $d (SCI $sc) $dA)
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it0)) (der_subst $id $dΓ $d $sc $dx))
          (JT (teq_inv (der_subst_Iapply $id $dΓ $d $sc $A it1)) (der_subst $id $dΓ $d $sc $dy))
          (der_F_subst $id $dΓ $d $sc $df)
          (JT (der_subst_Ishift $id $dΓ $d $sc (tpath $A $x $y)) (der_subst $id $dΓ $d (SCF (SCI $sc) (der_Ishift0F (sc_to_dctx $sc) $df)) $du))
          (der_subst $id $dΓ $d $sc $du0)
          (Jeq (TRefl _) (TRefl _) (teq_inv (der_subst_Iapply $id $dΓ $d $sc $u it0)) (der_eq_subst $id $u' $dΓ $d (SCF $sc $df) $deq)))
;
