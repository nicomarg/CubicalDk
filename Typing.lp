
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.derived;

// Typing context
constant symbol Context : TYPE;
constant symbol Push : Term → Lev → Context → Context;
constant symbol PushI : Context → Context;
constant symbol PushF : FTerm → Context → Context;
constant symbol Empty : Context;

symbol get : Context → DBId → Term;
symbol getS : Context → DBId → Lev;
symbol getΓ : Context → DBId → Context;
symbol IgetΓ : Context → DBId → Context;
rule get (Push $t _ _) db0 ↪ $t
with get (Push _ _ $t) (dbsucc $i) ↪ get $t $i
with get (PushF _ $t) $i ↪ get $t $i
with get (PushI $t) $i ↪ get $t $i
with getS (Push _ $s _) db0 ↪ $s
with getS (Push _ _ $t) (dbsucc $i) ↪ getS $t $i
with getS (PushI $t) $i ↪ getS $t $i
with getS (PushF _ $t) $i ↪ getS $t $i
with getΓ (Push _ _ $t) db0 ↪ $t
with getΓ (Push _ _ $t) (dbsucc $i) ↪ getΓ $t $i
with getΓ (PushI $t) $i ↪ getΓ $t $i
with getΓ (PushF _ $t) $i ↪ getΓ $t $i
with getΓ (getΓ $Γ $n) $m ↪ getΓ $Γ (dbsucc (dbadd $n $m))
with IgetΓ (Push _ _ $t) $i ↪ IgetΓ $t $i
with IgetΓ (PushI $t) db0 ↪ $t
with IgetΓ (PushI $t) (dbsucc $i) ↪ IgetΓ $t $i
with IgetΓ (PushF _ $t) $i ↪ IgetΓ $t $i
with IgetΓ (IgetΓ $Γ $n) $m ↪ IgetΓ $Γ (dbsucc (dbadd $n $m));

// Computes the 'length' (or maximum defined index + 1) of a context
symbol len : Context → DBId;
symbol lenI : Context → DBId;
rule len Empty ↪ db0
with len (Push _ _ $t) ↪ dbsucc (len $t)
with len (PushI $t) ↪ len $t
with len (PushF _ $t) ↪ len $t
with lenI Empty ↪ db0
with lenI (Push _ _ $t) ↪ lenI $t
with lenI (PushI $t) ↪ dbsucc (lenI $t)
with lenI (PushF _ $t) ↪ lenI $t;

// Shifts the term t valid in context (getΓ id Γ) to context Γ
symbol shiftΓ (Γ : Context) (id : DBId) (t : Term) : Term;
rule shiftΓ (Push _ _ _) db0 $t ↪ Shift $t
with shiftΓ (Push _ _ $Γ) (dbsucc $i) $t ↪ Shift (shiftΓ $Γ $i $t)
with shiftΓ (PushF _ $Γ) $i $t ↪ shiftΓ $Γ $i $t
with shiftΓ (PushI $Γ) $i $t ↪ IShift (shiftΓ $Γ $i $t)
// Universes aren't changed by shifting, useful for later
with shiftΓ _ _ (tuniv $s) ↪ tuniv $s;
// Shifts the type (get Γ id) to a valid type in context Γ
symbol shiftgetΓ (Γ : Context) (id : DBId) : Term;
// rule shiftgetΓ (Push $t _ _) db0 ↪ Shift $t
// with shiftgetΓ (Push _ _ $t) (dbsucc $i) ↪ Shift (shiftgetΓ $t $i)
// with shiftgetΓ (PushF _ $t) $i ↪ shiftgetΓ $t $i
// with shiftgetΓ (PushI $t) $i ↪ IShift (shiftgetΓ $t $i)
rule shiftgetΓ $Γ $id ↪ shiftΓ $Γ $id (get $Γ $id);

// Judgments definition
constant symbol der : Context → Term → Term → Lev → TYPE;
constant symbol der_eq : Context → Term → Term → Term → Lev → TYPE;
constant symbol der_I : Context → ITerm → TYPE;
constant symbol der_eq_I : Context → ITerm → ITerm → TYPE;
constant symbol der_F : Context → FTerm → TYPE;
constant symbol der_eq_F : Context → FTerm → FTerm → TYPE;
constant symbol der_isOne : Context → FTerm → TYPE;
// Typing derivation
// The derivation is only truly valid with a proof of the validity of the context
// Face reasoning
constant symbol der_empty_face : Π [Γ : Context] [l : Lev] [t A : Term],
  der_isOne Γ ft0 → der Γ t A l;
constant symbol der_union_face : Π [Γ : Context] [l : Lev] [t A : Term] [f g : FTerm],
  der_F Γ f → der_F Γ g → der (PushF f Γ) t A l → der (PushF g Γ) t A l → der_isOne Γ (ftmax f g) → der Γ t A l;
// Dependent λ-calculus
constant symbol der_var : Π[Γ : Context] [id : DBId], DBLe (dbsucc id) (len Γ) →
  der Γ (tvar id) (shiftgetΓ Γ id) (getS Γ id);
constant symbol der_univ : Π [Γ : Context] [l : Lev], der Γ (tuniv l) (tuniv (lsuc l)) (lsuc (lsuc l));
constant symbol der_pi : Π[Γ : Context] [l l' : Lev] [A B : Term],
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ (tpi A B) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_abs : Π[Γ : Context] [s s' : Lev], Π[A t B : Term],
  der Γ A (tuniv s) (lsuc s) → der (Push A s Γ) B (tuniv s') (lsuc s') → der (Push A s Γ) t B s' →
  der Γ (tabs A t) (tpi A B) (lmax s s');
constant symbol der_app : Π[Γ : Context] [s s' : Lev] (A t u B : Term),
  der Γ A (tuniv s) (lsuc s) → der (Push A s Γ) B (tuniv s') (lsuc s') →
  der Γ t (tpi A B) (lmax s s') → der Γ u A s → der Γ (tapp t u) (apply1 B u) s';
constant symbol der_type_conv : Π [Γ : Context] [l : Lev] [u A B : Term],
  der Γ u A l → der_eq Γ A B (tuniv l) (lsuc l) → der Γ u B l;
// Integers
constant symbol der_nat : Π [Γ : Context] [l : Lev], der Γ tnat (tuniv l) (lsuc l);
constant symbol der_zero : Π [Γ : Context] [l : Lev], der Γ tzero tnat l;
constant symbol der_suc : Π [Γ : Context] [l : Lev] [n : Term], der Γ n tnat l → der Γ (tsuc n) tnat l;
constant symbol der_rec : Π [Γ : Context] [l l' : Lev] [P z H n : Term],
  der Γ P (tpi tnat (tuniv l')) (lmax l (lsuc l')) → der Γ z (tapp P tzero) l' →
  der Γ H (tpi tnat (tpi (tapp (Shift P) (tvar db0)) (tapp (Shift (Shift P)) (tsuc (tvar db1))))) (lmax l l') →
  der Γ n tnat l → der Γ (trec P z H n) (tapp P n) l';
// Dependent pairs
constant symbol der_sig : Π[Γ : Context] [l l' : Lev] [A B : Term],
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ (tsig A B) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_pair : Π [Γ : Context] [l l' : Lev] [A B a b : Term],
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ a A l → der Γ b (apply1 B a) l' → der Γ (tpair a b) (tsig A B) (lmax l l');
constant symbol der_p1 : Π [Γ : Context] [l l' : Lev] [A B p : Term],
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ p (tsig A B) (lmax l l') → der Γ (tp1 p) A l;
constant symbol der_p2 : Π [Γ : Context] [l l' : Lev] [A B p : Term],
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ p (tsig A B) (lmax l l') → der Γ (tp2 p) (apply1 B (tp1 p)) l';
// Sum type
constant symbol der_sum : Π [Γ : Context] [l l' : Lev] [A B : Term],
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ (tsum A B) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_injl : Π [Γ : Context] [l l' : Lev] [A B a : Term],
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ a A l → der Γ (tinjl a) (tsum A B) (lmax l l');
constant symbol der_injr : Π [Γ : Context] [l l' : Lev] [A B b : Term],
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ b B l' → der Γ (tinjr b) (tsum A B) (lmax l l');
constant symbol der_case : Π [Γ : Context] [l l' m : Lev] [A B P Ha Hb x : Term],
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ P (tpi (tsum A B) (tuniv m)) (lmax (lmax l l') (lsuc m)) →
  der Γ Ha (tpi A (tapp (Shift P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (tapp (Shift P) (tinjr (tvar db0)))) (lmax l' m) →
  der Γ x (tsum A B) (lmax l l') → der Γ (tcase A B P Ha Hb x) (tapp P x) m;
// Path types
constant symbol der_path : Π [Γ : Context] [l : Lev] [A x y : Term],
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ (tpath A x y) (tuniv l) (lsuc l);
constant symbol der_lamP : Π [Γ : Context] [l : Lev] [A t : Term],
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) t A l →
  der Γ (tlamP t) (tpath A (applyI1 t it0) (applyI1 t it1)) l;
constant symbol der_appP : Π [Γ : Context] [l : Lev] (A t x y : Term) (i : ITerm),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_I Γ i → der Γ (tappP t i) (applyI1 A i) l;
// Systems
constant symbol der_sys : Π [Γ : Context] [l : Lev] [A : Term] [f g : FTerm] [u v : Term],
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_isOne Γ (ftmax f g) → der_eq (PushF (ftmin f g) Γ) u v A l → der Γ (tsys f g u v) A l;
constant symbol der_sys_empty : Π [Γ : Context] [l : Lev] [A : Term],
  der Γ A (tuniv l) (lsuc l) → der_isOne Γ ft0 → der Γ temptysys A l;
// Transport
constant symbol der_transp : Π [Γ : Context] [l : Lev] [A : Term] [f : FTerm] [u : Term],
  der (PushI Γ) A (tuniv l) (lsuc l) → der_F Γ f → der Γ u (applyI1 A it0) l →
  der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der Γ (ttransp A f u) (applyI1 A it1) l;
// Homogeneous composition
constant symbol der_hcomp : Π [Γ : Context] [l : Lev] [A : Term] [f : FTerm] [u u0 : Term],
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der (PushF (IShiftF f) (PushI Γ)) u (IShift A) l → der Γ u0 A l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) A l → der Γ (thcomp A f u u0) A l;
// TODO : glue
// Term conversion judgment
// Structural rules
constant symbol der_eq_refl : Π(Γ : Context) (l : Lev) (u A : Term), der Γ u A l → der_eq Γ u u A l;
constant symbol der_eq_trans : Π (Γ : Context) (l : Lev) (u v w A : Term),
  der_eq Γ u v A l → der_eq Γ v w A l → der_eq Γ u w A l;
constant symbol der_eq_sym : Π (Γ : Context) (l : Lev) (u v A : Term),
  der_eq Γ u v A l → der_eq Γ v u A l;
// Type conversion
constant symbol der_eq_conv : Π (Γ : Context) (l : Lev) (u v A B : Term),
  der_eq Γ u v A l → der_eq Γ A B (tuniv l) (lsuc l) → der_eq Γ u v B l;
// Face reasoning
constant symbol der_eq_isOne_zero : Π (Γ : Context) (l : Lev) (A u v : Term),
  der_isOne Γ ft0 → der_eq Γ u v A l;
constant symbol der_eq_isOne_max : Π (Γ : Context) (l : Lev) (A u v : Term) (f g : FTerm),
  der_F Γ f → der_F Γ g → der_eq (PushF f Γ) u v A l → der_eq (PushF g Γ) u v A l → der_isOne Γ (ftmax f g) →
  der_eq Γ u v A l;
// Computation rules
// λ-calculus
constant symbol der_eq_beta : Π (Γ : Context) (l l' : Lev) (u A t B : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der (Push A l Γ) t B l' → der Γ u A l → der_eq Γ (tapp (tabs A t) u) (apply1 t u) (apply1 B u) l';
constant symbol der_eq_eta : Π (Γ : Context) (l l' : Lev) (A B f : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ f (tpi A B) (lmax l l') →
  der_eq Γ (tabs A (tapp (Shift f) (tvar db0))) f (tpi A B) (lmax l l');
// Integers
constant symbol der_eq_rec_zero : Π (Γ : Context) (l l' : Lev) (P z H : Term),
  der Γ P (tpi tnat (tuniv l')) (lmax l (lsuc l')) → der Γ z (tapp P tzero) l' →
  der Γ H (tpi tnat (tpi (tapp (Shift P) (tvar db0)) (tapp (Shift (Shift P)) (tsuc (tvar db1))))) (lmax l l') →
  der_eq Γ (trec P z H tzero) z (tapp P tzero) l';
constant symbol der_eq_rec_suc : Π (Γ : Context) (l l' : Lev) (P z H n : Term),
  der Γ P (tpi tnat (tuniv l')) (lmax l (lsuc l')) → der Γ z (tapp P tzero) l' →
  der Γ H (tpi tnat (tpi (tapp (Shift P) (tvar db0)) (tapp (Shift (Shift P)) (tsuc (tvar db1))))) (lmax l l') →
  der Γ n tnat l → der_eq Γ (trec P z H (tsuc n)) (tapp (tapp H n) (trec P z H n)) (tapp P (tsuc n)) l';
// Σ-types
constant symbol der_eq_p1 : Π (Γ : Context) (l l' : Lev) (A u B v : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ u A l → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ v (apply1 B u) l' →
  der_eq Γ (tp1 (tpair u v)) u A l;
constant symbol der_eq_p2 : Π (Γ : Context) (l l' : Lev) (A u B v : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ u A l → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ v (apply1 B u) l' →
  der_eq Γ (tp2 (tpair u v)) v (apply1 B u) l';
constant symbol der_eq_pair : Π (Γ : Context) (l l' : Lev) (A B t u : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ t (tsig A B) (lmax l l') →
  der Γ u (tsig A B) (lmax l l') → der_eq Γ (tp1 t) (tp1 u) A l → der_eq Γ (tp2 t) (tp2 u) (apply1 B (tp1 t)) l' →
  der_eq Γ t u (tsig A B) (lmax l l');
// Sum types
constant symbol der_eq_case_left : Π (Γ : Context) (l l' m : Lev) (A B P Ha Hb a : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ P (tpi (tsum A B) (tuniv m)) (lmax (lmax l l') (lsuc m)) →
  der Γ Ha (tpi A (tapp (Shift P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (tapp (Shift P) (tinjr (tvar db0)))) (lmax l' m) →
  der Γ a A l → der_eq Γ (tcase A B P Ha Hb (tinjl a)) (tapp Ha a) (tapp P (tinjl a)) m;
constant symbol der_eq_case_right : Π (Γ : Context) (l l' m : Lev) (A B P Ha Hb b : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ P (tpi (tsum A B) (tuniv m)) (lmax (lmax l l') (lsuc m)) →
  der Γ Ha (tpi A (tapp (Shift P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (tapp (Shift P) (tinjr (tvar db0)))) (lmax l' m) →
  der Γ b B l' → der_eq Γ (tcase A B P Ha Hb (tinjr b)) (tapp Hb b) (tapp P (tinjr b)) m;
// Path types
constant symbol der_eq_betaP : Π (Γ : Context) (l : Lev) (A t : Term) (i : ITerm),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) t A l → der_I Γ i →
  der_eq Γ (tappP (tlamP t) i) (applyI1 t i) (applyI1 A i) l;
constant symbol der_eq_etaP : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tlamP (tappP (IShift t) (itvar db0))) t (tpath A x y) l;
constant symbol der_eq_appP_zero : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tappP t it0) x (applyI1 A it0) l;
constant symbol der_eq_appP_one : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tappP t it1) y (applyI1 A it1) l;
// Systems
constant symbol der_eq_sys_left : Π (Γ : Context) (l : Lev) (A : Term) (f g : FTerm) (u v : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_eq (PushF (ftmin f g) Γ) u v A l → der_isOne Γ f → der_eq Γ (tsys f g u v) u A l;
constant symbol der_eq_sys_right : Π (Γ : Context) (l : Lev) (A : Term) (f g : FTerm) (u v : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_eq (PushF (ftmin f g) Γ) u v A l → der_isOne Γ g → der_eq Γ (tsys f g u v) v A l;
// Transport, general rule first when transporting on the whole space,
constant symbol der_eq_transp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der_F Γ f → der Γ u (applyI1 A it0) l →
  der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_isOne Γ f → der_eq Γ (ttransp A f u) u (applyI1 A it1) l;
// then computing rules by case analysis on the type
// (transpⁱ (Π (x:A) B) φ u) v = transpⁱ B(x/transpFill⁻ⁱ A φ v) φ (u (transpʲ A(i/~j) φ v))
constant symbol der_eq_transp_pi : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u v : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (Push A l (PushI Γ)) B (tuniv l') (lsuc l') →
  der_F Γ f → der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (Push A l (PushF (IShiftF f) (PushI Γ))) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l') →
  der Γ u (applyI1 (tpi A B) it0) (lmax l l') → der Γ v (applyI1 A it1) l →
  der_eq Γ (tapp (ttransp (tpi A B) f u) v)
         (ttransp (apply1 B (ttransp (applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0))))
                                     (ftmax (IShiftF f) (fteq0 db0)) (IShift v)))
                  f (tapp u (ttransp (applyI1 (IShift1 A) (itsym (itvar db0))) f v)))
         (apply1 (applyI1 B it1) v) l';
constant symbol der_eq_transp_univ : Π (Γ : Context) (l : Lev) (f : FTerm) (A : Term),
  der_F Γ f → der Γ A (tuniv l) (lsuc l) → der_eq Γ (ttransp (tuniv l) f A) A (tuniv l) (lsuc l);
constant symbol der_eq_transp_zero : Π (Γ : Context) (l : Lev) (f : FTerm),
  der_F Γ f → der_eq Γ (ttransp tnat f tzero) tzero tnat l;
constant symbol der_eq_transp_suc : Π (Γ : Context) (l : Lev) (f : FTerm) (n : Term),
  der_F Γ f → der Γ n tnat l → der_eq Γ (ttransp tnat f (tsuc n)) (tsuc (ttransp tnat f n)) tnat l;
// transpⁱ (Σ (x : A) B) φ u = (transpⁱ A φ u.1, transpⁱ B(x/transpFillⁱ A φ u.1) φ u.2)
constant symbol der_eq_transp_sig : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (Push A l (PushI Γ)) B (tuniv l') (lsuc l') →
  der_F Γ f → der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (Push A l (PushF (IShiftF f) (PushI Γ))) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l') →
  der Γ u (applyI1 (tsig A B) it0) (lmax l l') →
  der_eq Γ (ttransp (tsig A B) f u)
         (tpair (ttransp A f (tp1 u))
                (ttransp (apply1 B (ttranspFill A f (tp1 u))) f (tp2 u)))
         (tsig (applyI1 A it1) (applyI1 B it1)) (lmax l l');
// transpⁱ (A + B) φ (injl a) = injl (transpⁱ A φ a)
constant symbol der_eq_transp_sum_left : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (a : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) B (tuniv l') (lsuc l') → der_F Γ f →
  der Γ a (applyI1 A it0) l → der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (PushF (IShiftF f) (PushI Γ)) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l') →
  der_eq Γ (ttransp (tsum A B) f (tinjl a)) (tinjl (ttransp A f a)) (applyI1 (tsum A B) it1) (lmax l l');
// transpⁱ (A + B) φ (injr b) = injr (transpⁱ B φ b)
constant symbol der_eq_transp_sum_right : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (b : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) B (tuniv l') (lsuc l') → der_F Γ f →
  der Γ b (applyI1 B it0) l' → der_eq (PushF (IShiftF f) (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (PushF (IShiftF f) (PushI Γ)) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l) →
  der_eq Γ (ttransp (tsum A B) f (tinjr b)) (tinjr (ttransp B f b)) (applyI1 (tsum A B) it1) (lmax l l');
// transpⁱ (Pathʲ A v w) φ u = λ j, compⁱ A [φ ↦ u j, (j = 0) ↦ v, (j = 1) ↦ w] (u j)
// The ugly subst/shift is swapping the two interval variables in A's context
constant symbol der_eq_transp_path : Π (Γ : Context) (l : Lev) (A x y : Term) (f : FTerm) (u : Term),
  der (PushI (PushI Γ)) A (tuniv l) (lsuc l) → der (PushI Γ) x (applyI1 A it0) l →
  der (PushI Γ) y (applyI1 A it1) l → der_F Γ f → der Γ u (applyI1 (tpath A x y) it0) l →
  der_eq (PushF (IShiftF (IShiftF f)) (PushI (PushI Γ))) A (IShift1 (Isubst db1 it0 A)) (tuniv l) (lsuc l) →
  der_eq (PushF (IShiftF f) (PushI Γ)) x (IShift (applyI1 x it0)) (applyI1 A it0) l →
  der_eq (PushF (IShiftF f) (PushI Γ)) y (IShift (applyI1 y it0)) (applyI1 A it1) l →
  der_eq Γ (ttransp (tpath A x y) f u)
         (tlamP (tcomp (applyI1 (applyI1 (Ishift db2 (Ishift db2 A)) (itvar db2)) (itvar db0))
                       (ftmax (IShiftF f) (ftmax (fteq0 db0) (fteq1 db0)))
                       (tsys (IShiftFN db1 f) (ftmax (fteq0 db1) (fteq1 db1))
                             (tappP (IShift (IShift u)) (itvar db1))
                             (tsys (fteq0 db1) (fteq1 db1) (IShift1 x) (IShift1 y)))
                       (tappP (IShift u) (itvar db0)))) (applyI1 (tpath A x y) it1) l;
// TODO : Glue types transport
// hcomp, general rule first when composing on the whole space,
constant symbol der_eq_hcomp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u u0 : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der (PushF (IShiftF f) (PushI Γ)) u (IShift A) l → der Γ u0 A l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) A l → der_isOne Γ f → der_eq Γ (thcomp A f u u0) (applyI1 u it1) A l;
// then computing rules by case analysis on the type
// hcompⁱ (Π (x : A), B) [φ ↦ u] u0 v = hcompⁱ B(x/v) [φ ↦ u v] (u0 v)
constant symbol der_eq_hcomp_pi : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u u0 v : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF (IShiftF f) (PushI Γ)) u (IShift (tpi A B)) (lmax l l') → der Γ u0 (tpi A B) (lmax l l') →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tpi A B) (lmax l l') → der Γ v A l →
  der_eq Γ (tapp (thcomp A f u u0) v) (thcomp (apply1 B v) f (tapp u (IShift v)) (tapp u0 v)) (apply1 B v) l';
// TODO : universe hcomp
// hcomp (U l) [φ ↦ E] A = Glue [φ ↦ (E(i/1), (equivⁱ E(i/1-i)))] A
constant symbol der_eq_hcomp_zero : Π (Γ : Context) (l : Lev) (f : FTerm) (n : Term),
  der_F Γ f → der (PushF (IShiftF f) (PushI Γ)) n tnat l → der_eq (PushF f Γ) tzero (applyI1 n it0) tnat l →
  der_eq Γ (thcomp tnat f n tzero) tzero tnat l;
constant symbol der_eq_hcomp_suc : Π (Γ : Context) (l : Lev) (f : FTerm) (n n0 : Term),
  der_F Γ f → der (PushF (IShiftF f) (PushI Γ)) n tnat l → der Γ n0 tnat l →
  der_eq (PushF f Γ) n0 (applyI1 n it0) tnat l →
  der_eq Γ (thcomp tnat f (tsuc n) (tsuc n0)) (tsuc (thcomp tnat f n n0)) tnat l;
// hcompⁱ (Σ (x : A), B) [φ ↦ u] u0 = (hcompⁱ A [φ ↦ u.1] u0.1, compⁱ B(x/hfillⁱ A [φ ↦ u.1] u0.1) [φ ↦ u.2] u0.2)
constant symbol der_eq_hcomp_sig : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u u0 : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF (IShiftF f) (PushI Γ)) u (IShift (tsig A B)) (lmax l l') → der Γ u0 (tsig A B) (lmax l l') →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tsig A B) (lmax l l') →
  der_eq Γ (thcomp (tsig A B) f u u0) (tpair (thcomp A f (tp1 u) (tp1 u0))
                                             (tcomp (apply1 (IShift B) (thfill A f (tp1 u) (tp1 u0))) f (tp2 u) (tp2 u0)))
         (tsig A B) (lmax l l');
constant symbol der_eq_hcomp_sum_left : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (a a0 : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF (IShiftF f) (PushI Γ)) a (IShift A) l → der Γ a0 A l → der_eq (PushF f Γ) a0 (applyI1 a it0) A l →
  der_eq Γ (thcomp (tsum A B) f (tinjl a) (tinjl a0)) (tinjl (thcomp A f a a0)) (tsum A B) (lmax l l');
constant symbol der_eq_hcomp_sum_right : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (b b0 : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF (IShiftF f) (PushI Γ)) b (IShift B) l' → der Γ b0 B l' → der_eq (PushF f Γ) b0 (applyI1 b it0) B l' →
  der_eq Γ (thcomp (tsum A B) f (tinjr b) (tinjr b0)) (tinjr (thcomp B f b b0)) (tsum A B) (lmax l l');
// hcompⁱ (Pathʲ A v w) [φ ↦ u] u0 = λ j, hcompⁱ A [φ ↦ u j, (j = 0) ↦ v, (j = 1) ↦ w] (u0 j)
constant symbol der_eq_hcomp_path : Π (Γ : Context) (l : Lev) (A x y : Term) (f : FTerm) (u u0 : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der_F Γ f → der (PushF (IShiftF f) (PushI Γ)) u (IShift (tpath A x y)) l → der Γ u0 (tpath A x y) l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tpath A x y) l →
  der_eq Γ (thcomp (tpath A x y) f u u0)
         (tlamP (thcomp A (ftmax (IShiftF f) (ftmax (fteq0 db0) (fteq1 db0)))
                        (tsys (IShiftFN db1 f) (ftmax (fteq0 db1) (fteq1 db1)) (tappP (IShift1 u) (itvar db1))
                              (tsys (fteq0 db1) (fteq1 db1) (IShiftN db1 x) (IShiftN db1 y)))
                        (tappP (IShift u0) (itvar db0))))
         (tpath A x y) l;
// TODO : Glue types hcomp
// TODO : Glue types conversions
// Congruence rules
constant symbol der_eq_cong_pi : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l') →
  der (Push A1 l Γ) B1 (tuniv l') (lsuc l') → der (Push A2 l Γ) B2 (tuniv l') (lsuc l') →
  der_eq Γ (tpi A1 B1) (tpi A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_eq_cong_abs : Π (Γ : Context) (l l' : Lev) (A1 A2 B t1 t2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) t1 t2 B l' →
  der (Push A1 l Γ) t1 B l' → der (Push A2 l Γ) t2 B l' →
  der_eq Γ (tabs A1 t1) (tabs A2 t2) (tpi A1 B) (lmax l l');
constant symbol der_eq_cong_app : Π (Γ : Context) (l l' : Lev) (A B t1 t2 u1 u2 : Term),
  der_eq Γ t1 t2 (tpi A B) (lmax l l') → der_eq Γ u1 u2 A l →
  der_eq Γ (tapp t1 u1) (tapp t2 u2) (apply1 B u1) l';
constant symbol der_eq_cong_suc : Π (Γ : Context) (l : Lev) (n n' : Term),
  der_eq Γ n n' tnat l → der_eq Γ (tsuc n) (tsuc n') tnat l;
constant symbol der_eq_cong_rec : Π (Γ : Context) (l l' : Lev) (P1 P2 z1 z2 H1 H2 n1 n2 : Term),
  der_eq Γ P1 P2 (tpi tnat (tuniv l')) (lmax l (lsuc l')) → der_eq Γ z1 z2 (tapp P1 tzero) l' →
  der_eq Γ H1 H2 (tpi tnat (tpi (tapp (Shift P1) (tvar db0)) (tapp (Shift (Shift P1)) (tsuc (tvar db1))))) l' →
  der_eq Γ n1 n2 tnat l →
  der_eq Γ (trec P1 z1 H1 n1) (trec P2 z2 H2 n2) (tapp P1 n1) l';
constant symbol der_eq_cong_sig : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l') →
  der (Push A1 l Γ) B1 (tuniv l') (lsuc l') → der (Push A2 l Γ) B2 (tuniv l') (lsuc l') →
  der_eq Γ (tsig A1 B1) (tsig A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_eq_cong_pair : Π (Γ : Context) (l l' : Lev) (A B u1 u2 v1 v2 : Term),
  der_eq Γ u1 u2 A l → der_eq Γ v1 v2 (apply1 B u1) l' →
  der_eq Γ (tpair u1 v1) (tpair u2 v2) (tsig A B) (lmax l l');
constant symbol der_eq_cong_p1 : Π (Γ : Context) (l l' : Lev) (A B u v : Term),
  der_eq Γ u v (tsig A B) (lmax l l') →
  der_eq Γ (tp1 u) (tp1 v) A l;
constant symbol der_eq_cong_p2 : Π (Γ : Context) (l l' : Lev) (A B u v : Term),
  der_eq Γ u v (tsig A B) (lmax l l') →
  der_eq Γ (tp2 u) (tp2 v) (apply1 B (tp1 u)) l';
constant symbol der_eq_cong_sum : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq Γ B1 B2 (tuniv l') (lsuc l') →
  der_eq Γ (tsum A1 B1) (tsum A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'));
constant symbol der_eq_cong_injl : Π (Γ : Context) (l l' : Lev) (A B a1 a2 : Term),
  der_eq Γ a1 a2 A l → der_eq Γ (tinjl a1) (tinjl a2) (tsum A B) (lmax l l');
constant symbol der_eq_cong_injr : Π (Γ : Context) (l l' : Lev) (A B b1 b2 : Term),
  der_eq Γ b1 b2 B l' → der_eq Γ (tinjr b1) (tinjr b2) (tsum A B) (lmax l l');
constant symbol der_eq_cong_case : Π (Γ : Context) (l l' m : Lev) (A1 A2 B1 B2 P1 P2 Ha1 Ha2 Hb1 Hb2 u v : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq Γ B1 B2 (tuniv l') (lsuc l') →
  der_eq Γ P1 P2 (tpi (tsum A1 B1) (tuniv m)) (lmax (lmax l l') (lsuc m)) →
  der_eq Γ Ha1 Ha2 (tpi A1 (tapp (Shift P1) (tinjl (tvar db0)))) (lmax l m) →
  der_eq Γ Hb1 Hb2 (tpi B1 (tapp (Shift P1) (tinjr (tvar db0)))) (lmax l' m) →
  der_eq Γ u v (tsum A1 B1) (lmax l l') →
  der_eq Γ (tcase A1 B1 P1 Ha1 Hb1 u) (tcase A2 B2 P2 Ha2 Hb2 v) (tapp P1 u) m;
constant symbol der_eq_cong_path : Π (Γ : Context) (l : Lev) (A1 A2 x1 x2 y1 y2 : Term),
  der_eq (PushI Γ) A1 A2 (tuniv l) (lsuc l) →
  der_eq Γ x1 x2 (applyI1 A1 it0) l → der_eq Γ y1 y2 (applyI1 A1 it1) l →
  der_eq Γ (tpath A1 x1 y1) (tpath A2 x2 y2) (tuniv l) (lsuc l);
constant symbol der_eq_cong_lamP : Π (Γ : Context) (l : Lev) (A t1 t2 : Term),
  der_eq (PushI Γ) t1 t2 A l →
  der_eq Γ (tlamP t1) (tlamP t2) (tpath A (applyI1 t1 it0) (applyI1 t1 it1)) l;
constant symbol der_eq_cong_appP : Π (Γ : Context) (l : Lev) (A x y u v : Term) (i1 i2 : ITerm),
  der_eq Γ u v (tpath A x y) l → der_eq_I Γ i1 i2 →
  der_eq Γ (tappP u i1) (tappP v i2) (applyI1 A i1) l;
constant symbol der_eq_cong_sys : Π (Γ : Context) (l : Lev) (A : Term) (f1 f2 g1 g2 : FTerm) (u1 u2 v1 v2 : Term),
  der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq (PushF f1 Γ) u1 u2 A l → der_eq (PushF g1 Γ) v1 v2 A l →
  der (PushF f1 Γ) u1 A l → der (PushF f2 Γ) u2 A l → der (PushF g1 Γ) v1 A l → der (PushF g2 Γ) v2 A l →
  der_isOne Γ (ftmax f1 g1) → der_isOne Γ (ftmax f2 g2) → der_eq (PushF (ftmin f1 g1) Γ) u1 v1 A l →
  der_eq (PushF (ftmin f2 g2) Γ) u2 v2 A l → der_eq Γ (tsys f1 g1 u1 v1) (tsys f2 g2 u2 v2) A l;
constant symbol der_eq_cong_transp : Π (Γ : Context) (l : Lev) (A1 A2 : Term) (f1 f2 : FTerm) (a1 a2 : Term),
  der_eq (PushI Γ) A1 A2 (tuniv l) (lsuc l) → der_eq_F Γ f1 f2 → der_eq Γ a1 a2 (applyI1 A1 it0) l →
  der_eq (PushI Γ) A1 (IShift (applyI1 A1 it0)) (tuniv l) (lsuc l) →
  der_eq (PushI Γ) A2 (IShift (applyI1 A2 it0)) (tuniv l) (lsuc l) →
  der_eq Γ (ttransp A1 f1 a1) (ttransp A2 f2 a2) (applyI1 A1 it1) l;
constant symbol der_eq_cong_hcomp : Π (Γ : Context) (l : Lev) (A1 A2 : Term) (f1 f2 : FTerm) (u1 u2 v1 v2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq_F Γ f1 f2 → der_eq (PushF (IShiftF f1) (PushI Γ)) u1 u2 (IShift A1) l →
  der_eq Γ v1 v2 A1 l → der (PushF (IShiftF f1) (PushI Γ)) u1 (IShift A1) l →
  der (PushF (IShiftF f2) (PushI Γ)) u2 (IShift A2) l →
  der_eq (PushF f1 Γ) v1 (applyI1 u1 it0) A1 l →
  der_eq (PushF f2 Γ) v2 (applyI1 u2 it0) A2 l →
  der_eq Γ (thcomp A1 f1 u1 v1) (thcomp A2 f2 u2 v2) A1 l;
// TODO : Glue types congruences
// Interval terms typing judgment
constant symbol der_I_0 : Π [Γ : Context], der_I Γ it0;
constant symbol der_I_1 : Π [Γ : Context], der_I Γ it1;
constant symbol der_I_var : Π [Γ : Context] [id : DBId], DBLe (dbsucc id) (lenI Γ) → der_I Γ (itvar id);
constant symbol der_I_sym : Π [Γ : Context] [i : ITerm], der_I Γ i → der_I Γ (itsym i);
constant symbol der_I_min : Π [Γ : Context] [i j : ITerm], der_I Γ i → der_I Γ j → der_I Γ (itmin i j);
constant symbol der_I_max : Π [Γ : Context] [i j : ITerm], der_I Γ i → der_I Γ j → der_I Γ (itmax i j);
// Interval terms conversion judgment
// Structural rules
constant symbol der_eq_I_refl : Π (Γ : Context) (i : ITerm), der_I Γ i → der_eq_I Γ i i;
constant symbol der_eq_I_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ i j → der_eq_I Γ j i;
constant symbol der_eq_I_trans : Π (Γ : Context) (i j k : ITerm), der_eq_I Γ i j → der_eq_I Γ j k → der_eq_I Γ i k;
// Face reasoning
constant symbol der_eq_I_isOne_zero : Π (Γ : Context) (i j : ITerm), der_isOne Γ ft0 → der_eq_I Γ i j;
constant symbol der_eq_I_isOne_max : Π (Γ : Context) (i j : ITerm) (f g : FTerm),
  der_F Γ f → der_F Γ g → der_eq_I (PushF f Γ) i j → der_eq_I (PushF g Γ) i j → der_isOne Γ (ftmax f g) →
  der_eq_I Γ i j;
constant symbol der_eq_I_isOne_eq0 : Π (Γ : Context) (id : DBId), der_isOne Γ (fteq0 id) → der_eq_I Γ (itvar id) it0;
constant symbol der_eq_I_isOne_eq1 : Π (Γ : Context) (id : DBId), der_isOne Γ (fteq1 id) → der_eq_I Γ (itvar id) it1;
// Computation rules for interval operations
constant symbol der_eq_I_sym_sym : Π (Γ : Context) (i : ITerm), der_eq_I Γ i (itsym (itsym i));
constant symbol der_eq_I_sym_zero : Π (Γ : Context), der_eq_I Γ (itsym it0) it1;
constant symbol der_eq_I_sym_one : Π (Γ : Context), der_eq_I Γ (itsym it1) it0;
constant symbol der_eq_I_min_assoc : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmin i (itmin j k)) (itmin (itmin i j) k);
constant symbol der_eq_I_min_comm : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itmin i j) (itmin j i);
constant symbol der_eq_I_min_zero : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmin i it0) it0;
constant symbol der_eq_I_min_one : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmin i it1) i;
constant symbol der_eq_I_max_assoc : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmax i (itmax j k)) (itmax (itmax i j) k);
constant symbol der_eq_I_max_comm : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itmax i j) (itmax j i);
constant symbol der_eq_I_max_zero : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmax i it0) i;
constant symbol der_eq_I_max_one : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmax i it1) it1;
constant symbol der_eq_I_min_sym : Π (Γ : Context) (i j : ITerm),
  der_eq_I Γ (itsym (itmin i j)) (itmax (itsym i) (itsym j));
constant symbol der_eq_I_max_sym : Π (Γ : Context) (i j : ITerm),
  der_eq_I Γ (itsym (itmax i j)) (itmin (itsym i) (itsym j));
constant symbol der_eq_I_min_distrib : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmin i (itmax j k)) (itmax (itmin i j) (itmin i k));
constant symbol der_eq_I_max_distrib : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmax i (itmin j k)) (itmin (itmax i j) (itmax i k));
// Congruence rules
constant symbol der_eq_I_cong_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ i j → der_eq_I Γ (itsym i) (itsym j);
constant symbol der_eq_I_cong_min : Π (Γ : Context) (i1 i2 j1 j2 : ITerm),
  der_eq_I Γ i1 i2 → der_eq_I Γ j1 j2 → der_eq_I Γ (itmin i1 j1) (itmin i2 j2);
constant symbol der_eq_I_cong_max : Π (Γ : Context) (i1 i2 j1 j2 : ITerm),
  der_eq_I Γ i1 i2 → der_eq_I Γ j1 j2 → der_eq_I Γ (itmax i1 j1) (itmax i2 j2);
// Face terms typing judgment
constant symbol der_F_0 : Π [Γ : Context], der_F Γ ft0;
constant symbol der_F_1 : Π [Γ : Context], der_F Γ ft1;
constant symbol der_F_eq0 : Π [Γ : Context] [id : DBId], DBLe (dbsucc id) (lenI Γ) → der_F Γ (fteq0 id);
constant symbol der_F_eq1 : Π [Γ : Context] [id : DBId], DBLe (dbsucc id) (lenI Γ) → der_F Γ (fteq1 id);
constant symbol der_F_min : Π [Γ : Context] [f g : FTerm], der_F Γ f → der_F Γ g → der_F Γ (ftmin f g);
constant symbol der_F_max : Π [Γ : Context] [f g : FTerm], der_F Γ f → der_F Γ g → der_F Γ (ftmax f g);
// Face terms conversion judgment
// Structural rules
constant symbol der_eq_F_refl : Π (Γ : Context) (f : FTerm), der_F Γ f → der_eq_F Γ f f;
constant symbol der_eq_F_sym : Π (Γ : Context) (f g : FTerm), der_eq_F Γ f g → der_eq_F Γ g f;
constant symbol der_eq_F_trans : Π (Γ : Context) (f g h : FTerm), der_eq_F Γ f g → der_eq_F Γ g h → der_eq_F Γ f h;
// Face reasoning
constant symbol der_eq_F_isOne_zero : Π (Γ : Context) (f g : FTerm), der_isOne Γ ft0 → der_eq_F Γ f g;
constant symbol der_eq_F_isOne_max : Π (Γ : Context) (f g f' g' : FTerm),
  der_F Γ f' → der_F Γ g' →
  der_eq_F (PushF f' Γ) f g → der_eq_F (PushF g' Γ) f g → der_isOne Γ (ftmax f g) → der_eq_F Γ f g;
constant symbol der_eq_F_isOne_one : Π (Γ : Context) (f : FTerm), der_isOne Γ f → der_eq_F Γ f ft1;
// Computation rules for face operations
constant symbol der_eq_F_min_assoc : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmin f (ftmin g h)) (ftmin (ftmin f g) h);
constant symbol der_eq_F_min_comm : Π (Γ : Context) (f g : FTerm), der_eq_F Γ (ftmin f g) (ftmin g f);
constant symbol der_eq_F_max_assoc : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmax f (ftmax g h)) (ftmax (ftmax f g) h);
constant symbol der_eq_F_max_comm : Π (Γ : Context) (f g : FTerm), der_eq_F Γ (ftmax f g) (ftmax g f);
constant symbol der_eq_F_min_distrib : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmin f (ftmax g h)) (ftmax (ftmin f g) (ftmin f h));
constant symbol der_eq_F_max_distrib : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmax f (ftmin g h)) (ftmin (ftmax f g) (ftmax f h));
constant symbol der_eq_F_empty : Π (Γ : Context) (id : DBId), der_eq_F Γ (ftmin (fteq0 id) (fteq1 id)) ft0;
// Congruence rules
constant symbol der_eq_F_cong_eq0 : Π (Γ : Context) (id : DBId) (i : ITerm),
  der_eq_I Γ (itvar id) i → der_eq_F Γ (fteq0 id) (IsubstF id i (fteq0 id));
constant symbol der_eq_F_cong_eq1 : Π (Γ : Context) (id : DBId) (i : ITerm),
  der_eq_I Γ (itvar id) i → der_eq_F Γ (fteq1 id) (IsubstF id i (fteq1 id));
constant symbol der_eq_F_cong_min : Π (Γ : Context) (f1 f2 g1 g2 : FTerm),
  der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq_F Γ (ftmin f1 g1) (ftmin f2 g2);
constant symbol der_eq_F_cong_max : Π (Γ : Context) (f1 f2 g1 g2 : FTerm),
  der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq_F Γ (ftmax f1 g1) (ftmax f2 g2);
// Judgment expressing that the context currently restricts to (a subface of) the face f.
// All reasoning about the faces in the context goes through this judgment
constant symbol der_isOne_one : Π (Γ : Context), der_isOne Γ (ft1);
constant symbol der_isOne_zero : Π (Γ : Context) (t : FTerm), der_isOne Γ ft0 → der_isOne Γ t;
constant symbol der_isOne_empty : Π (Γ : Context) (id : DBId),
  der_isOne Γ (ftmin (fteq0 id) (fteq1 id)) → der_isOne Γ ft0;
constant symbol der_isOne_min_intro : Π (Γ : Context) (f g : FTerm),
  der_isOne Γ f → der_isOne Γ g → der_isOne Γ (ftmin f g);
constant symbol der_isOne_min_elim_left : Π (Γ : Context) (f g : FTerm), der_isOne Γ (ftmin f g) → der_isOne Γ f;
constant symbol der_isOne_min_elim_right : Π (Γ : Context) (f g : FTerm), der_isOne Γ (ftmin f g) → der_isOne Γ g;
constant symbol der_isOne_max_intro_left : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_isOne Γ (ftmax f g);
constant symbol der_isOne_max_intro_right : Π (Γ : Context) (f g : FTerm), der_isOne Γ g → der_isOne Γ (ftmax f g);
constant symbol der_isOne_max_elim : Π (Γ : Context) (f g t : FTerm), der_F Γ f → der_F Γ g →
  der_isOne (PushF f Γ) t → der_isOne (PushF g Γ) t → der_isOne Γ (ftmax f g) → der_isOne Γ t;
constant symbol der_isOne_axiom : Π (Γ : Context) (f : FTerm), der_F Γ f → der_isOne (PushF f Γ) f;
constant symbol der_isOne_weak : Π (Γ : Context) (t : Term) (l : Lev) (f : FTerm),
  der Γ t (tuniv l) (lsuc l) → der_isOne Γ f → der_isOne (Push t l Γ) f;
constant symbol der_isOne_weakI : Π (Γ : Context) (f : FTerm), der_isOne Γ f → der_isOne (PushI Γ) (IShiftF f);
constant symbol der_isOne_weakF : Π (Γ : Context) (f g : FTerm), der_F Γ g → der_isOne Γ f → der_isOne (PushF g Γ) f;
constant symbol der_isOne_cong : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_eq_F Γ f g → der_isOne Γ g;

// Independent der_context expressing context validity
constant symbol der_context : Context → TYPE;
constant symbol der_context_empty : der_context Empty;
constant symbol der_context_Push : Π (Γ : Context) (l : Lev) (A : Term),
  der Γ A (tuniv l) (lsuc l) → der_context Γ → der_context (Push A l Γ);
constant symbol der_context_PushI : Π (Γ : Context), der_context Γ → der_context (PushI Γ);
constant symbol der_context_PushF : Π (Γ : Context) (f : FTerm), der_F Γ f → der_context Γ → der_context (PushF f Γ);
