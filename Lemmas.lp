
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;


// der_context accessors
// Might get expanded for other constructor when needed
symbol der_getΓ [Γ : Context] (id : DBId) (_ : der_context Γ) :
  der (getΓ Γ id) (get Γ id) (tuniv (getS Γ id)) (lsuc (getS Γ id));
symbol der_subΓ [Γ : Context] (id : DBId) (_ : der_context Γ) : der_context (getΓ Γ id);
rule der_getΓ db0 (der_context_Push _ _ _ $dA _) ↪ $dA
with der_getΓ (dbsucc $id) (der_context_Push _ _ _ _ $dt) ↪ der_getΓ $id $dt
with der_getΓ $id (der_context_PushI _ $dt) ↪ der_getΓ $id $dt
with der_getΓ $id (der_context_PushF _ _ $dt _) ↪ der_getΓ $id $dt
with der_subΓ db0 (der_context_Push _ _ _ _ $dΓ) ↪ $dΓ
with der_subΓ (dbsucc $id) (der_context_Push _ _ _ _ $dΓ) ↪ der_subΓ $id $dΓ
with der_subΓ $id (der_context_PushI _ $dt) ↪ der_subΓ $id $dt
with der_subΓ $id (der_context_PushF _ _ $dt _) ↪ der_subΓ $id $dt
;

// Better der_context_push
symbol pushΓ [Γ : Context] [l : Lev] [T : Term] (d : der Γ T (tuniv l) (lsuc l)) (dΓ : der_context Γ) :
  der_context (Push T l Γ) ≔ der_context_Push Γ l T d dΓ;
symbol pushΓF [Γ : Context] [f : FTerm] (df : der_F Γ f) (dΓ : der_context Γ) :
  der_context (PushF f Γ) ≔ der_context_PushF Γ f dΓ df;
symbol pushΓI [Γ : Context] (dΓ : der_context Γ) :
  der_context (PushI Γ) ≔ der_context_PushI Γ dΓ;

symbol dble_db0 [n : DBId] : DBLe (dbsucc db0) (dbsucc n) ≔
  dble_n_S (dble_0_n n);
symbol dble_db1 [n : DBId] : DBLe (dbsucc (dbsucc db0)) (dbsucc (dbsucc n)) ≔
  dble_n_S (dble_n_S (dble_0_n n));

// TODO : Prove all lemmas below
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

// Congruence for replacement
symbol der_eq_cong_apply [Γ : Context] [l l' : Lev] [A1 A2 B1 B2 t1 t2 : Term]
                         (_ : der_context Γ)
                         (_ : der_eq Γ A1 A2 (tuniv l) (lsuc l)) (_ : der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l'))
                         (_ : der_eq Γ t1 t2 A1 l)
                         (_ : der (Push A1 l Γ) B1 (tuniv l') (lsuc l'))
                         (_ : der (Push A2 l Γ) B2 (tuniv l') (lsuc l'))
                         (_ : der Γ t1 A1 l) (_ : der Γ t2 A2 l)
                         : der_eq Γ (apply1 B1 t1) (apply1 B2 t2) (tuniv l') (lsuc l');

symbol substitution [Γ : Context] [l l' : Lev] [A B C : Term] :
  der_context Γ → der (Push A l Γ) C B l' → Π[u : Term], der Γ u A l → der Γ (apply1 C u) (apply1 B u) l';
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
