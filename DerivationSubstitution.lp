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
       [s s': Lev] [A B u : Term]
       (dΓ : der_context Γ)
       (d : der Γ u A s) (sc : SubstContext (inv_type dΓ d) id)
       (dA : der (sc_to_ctx sc) B (tuniv s') (lsuc s'))
       (i : DBId)
       (h : DBLe (dbsucc (dbsucc i)) (len (sc_to_ctx (SCPush sc dA))))
       : der (sc_to_sctx d dΓ (SCPush sc dA)) (dbselect (dbsucc id) (dbsucc i) (shift_sctx (SCPush sc dA) u) (tvar (dbsucc i)) (tvar i))
             (subst (dbsucc id) (shift_sctx (SCPush sc dA) u) (shiftgetΓ (sc_to_ctx (SCPush sc dA)) (dbsucc i)))
             (getS (sc_to_ctx (SCPush sc dA)) (dbsucc i)) ≔
begin
  assume Γ id s s' A B u dΓ d sc dA i h;
  refine JtT _ _ (der_shift0 (der_subst _ dΓ d sc dA) (sc_to_dsctx d dΓ sc) (der_context_subst id dΓ d sc i (dble_S_n h)))
  {
    refine teq_inv _;
    refine teq_select_shift id i (shift_sctx sc u);
  }
  {
    refine teq_inv _;
    refine teq_subst_shift id (shift_sctx sc u) (shiftgetΓ (sc_to_ctx sc) i);
  }
end;
// Types
rule der_subst $id $dΓ $d $sc (der_empty_face $done) ↪ der_empty_face (der_isOne_subst $id $dΓ $d $sc $done)
with der_subst $id $dΓ $d $sc (der_union_face $df $dg $dtf $dtg $done) ↪
     der_union_face (der_F_subst $id $dΓ $d $sc $df)
                    (der_F_subst $id $dΓ $d $sc $dg)
                    (der_subst $id $dΓ $d (SCF $sc $df) $dtf)
                    (der_subst $id $dΓ $d (SCF $sc $dg) $dtg)
                    (der_isOne_subst $id $dΓ $d $sc $done)
with der_subst $id $dΓ $d $sc (@der_var _ $i $h) ↪ der_context_subst $id $dΓ $d $sc $i $h
// Structural
with der_context_subst db0 _ $d (SC0 _ _) db0 _ ↪ $d
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

// with der_subst _ $dΓ $d $sc (der_type_conv _ _ _ _ $s $du $deq)
//   ↪ der_type_conv _ _ _ _ $s
//                    (der_subst _ $dΓ $d $sc $du)
//                    (der_eq_subst _ _ $dΓ $d $sc $deq)

// with der_subst _ $dΓ $d $sc (der_univ _ $s) ↪ der_univ (sc_to_sctx $d $dΓ $sc) $s
// with der_subst $id $dΓ $d $sc (der_prod _ $s $s' _ _ $dA $dB)
//   ↪ der_prod (sc_to_sctx $d $dΓ $sc) $s $s' _ _
//               (der_subst $id $dΓ $d $sc $dA)
//               (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
// with der_subst $id $dΓ $d $sc (der_sigma _ $s $s' _ _ $dA $dB)
//   ↪ der_sigma (sc_to_sctx $d $dΓ $sc) $s $s' _ _
//                (der_subst $id $dΓ $d $sc $dA)
//                (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
// with der_subst $id $dΓ $d $sc (der_prop_type_eq _ $s _ _ _ $dA $du $dv)
//   ↪ der_prop_type_eq _ $s _ _ _
//                       (der_subst $id $dΓ $d $sc $dA)
//                       (der_subst $id $dΓ $d $sc $du)
//                       (der_subst $id $dΓ $d $sc $dv)

// // λ-calculus
// with der_subst $id $dΓ $d $sc (der_abs _ $s $s' _ _ _ $dA $dB $dt)
//   ↪ der_abs _ $s $s' _ _ _
//              (der_subst $id $dΓ $d $sc $dA)
//              (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
//              (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dt)
// with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_app _ $s $s' _ _ $a $B $dA $dB $df $da)
//   ↪ JT (teq_inv (teq_subst_apply $id $x $a $B))
//         (der_app _ $s $s' _ _ _ _
//                  (der_subst $id $dΓ $d $sc $dA)
//                  (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
//                  (der_subst $id $dΓ $d $sc $df)
//                  (der_subst $id $dΓ $d $sc $da))
// with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_pair _ $s $s' $u _ _ $B $dA $du $dB $dv)
//   ↪ der_pair _ $s $s' _ _ _ _
//               (der_subst $id $dΓ $d $sc $dA)
//               (der_subst $id $dΓ $d $sc $du)
//               (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
//               (JT (teq_subst_apply $id $x $u $B)
//                   (der_subst $id $dΓ $d $sc $dv))
// with der_subst $id $dΓ $d $sc (der_π1 _ $s $s' _ _ _ $dA $dB $dp)
//   ↪ der_π1 _ $s $s' _ _ _
//             (der_subst $id $dΓ $d $sc $dA)
//             (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
//             (der_subst $id $dΓ $d $sc $dp)
// with @der_subst _ $id _ _ _ _ _ $x $dΓ $d $sc (der_π2 _ $s $s' $p $A $B $dA $dB $dp)
//   ↪ JT (teq_inv (teq_subst_apply $id $x (ETT.π1 $A $B $p) $B))
//         (der_π2 _ $s $s' _ _ _
//                 (der_subst $id $dΓ $d $sc $dA)
//                 (der_subst (dbsucc $id) $dΓ $d (SCPush $sc $dA) $dB)
//                 (der_subst $id $dΓ $d $sc $dp))
// // Equality
// with der_subst $id $dΓ $d $sc (der_refl _ $s _ _ $dA $du)
//   ↪ der_refl _ $s _ _
//               (der_subst $id $dΓ $d $sc $dA)
//               (der_subst $id $dΓ $d $sc $du)
// with der_subst $id $dΓ $d $sc (der_K _ $s _ _ _ $dA $da $dp)
//   ↪ der_K _ $s _ _ _
//            (der_subst $id $dΓ $d $sc $dA)
//            (der_subst $id $dΓ $d $sc $da)
//            (der_subst $id $dΓ $d $sc $dp)
// ;
