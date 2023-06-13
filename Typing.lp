
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
// symbol getΓ : Context → DBId → Context;
rule get (Push $t _ _) db0 ↪ $t
with get (Push _ _ $t) (dbsucc $i) ↪ get $t $i
with get (PushF _ $t) $i ↪ get $t $i
with get (PushI $t) $i ↪ get $t $i
with getS (Push _ $s _) db0 ↪ $s
with getS (Push _ _ $t) (dbsucc $i) ↪ getS $t $i
with getS (PushI $t) $i ↪ getS $t $i
with getS (PushF _ $t) $i ↪ getS $t $i;
// with getΓ (Push _ _ $t) db0 ↪ $t
// with getΓ (Push _ _ $t) (dbsucc $i) ↪ getΓ $t $i
// with getΓ (getΓ $Γ $n) $m ↪ getΓ $Γ (dbsucc (dbadd $n $m));

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

// Typing derivation
// The derivation is only truly valid with a proof of the validity of the context
inductive der : Context → Term → Term → Lev → TYPE ≔
// Dependent λ-calculus
| der_var : Π(Γ : Context) (id : DBId), DBLe (dbsucc id) (len Γ) →
  der Γ (tvar id) (ShiftN id (get Γ id)) (getS Γ id)
| der_pi : Π(Γ : Context) (l l' : Lev) (A B : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ (tpi A B) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_abs : Π(Γ : Context) (s s' : Lev), Π(A t B : Term),
  der Γ A (tuniv s) (lsuc s) → der (Push A s Γ) B (tuniv s') (lsuc s') → der (Push A s Γ) t B s' →
  der Γ (tabs A t) (tpi A B) (lmax s s')
| der_app : Π(Γ : Context) (s s' : Lev) (A t u B : Term),
  der Γ A (tuniv s) (lsuc s) → der (Push A s Γ) B (tuniv s') (lsuc s') →
  der Γ t (tpi A B) (lmax s s') → der Γ u A s → der Γ (tapp t u) (apply1 B u) s'
| der_univ : Π (Γ : Context) (l : Lev), der Γ (tuniv l) (tuniv (lsuc l)) (lsuc (lsuc l))
| der_type_conv : Π (Γ : Context) (l : Lev) (u A B : Term),
  der Γ u A l → der_eq Γ A B (tuniv l) (lsuc l) → der Γ u B l
// Integers
| der_nat : Π (Γ : Context) (l : Lev), der Γ tnat (tuniv l) (lsuc l)
| der_zero : Π (Γ : Context) (l : Lev), der Γ tzero tnat l
| der_suc : Π (Γ : Context) (l : Lev) (n : Term), der Γ n tnat l → der Γ (tsuc n) tnat l
| der_rec : Π (Γ : Context) (l l' : Lev) (P z H n : Term),
  der (Push tnat l Γ) P (tuniv l') (lsuc l') → der Γ z (apply1 P tzero) l' →
  der Γ H (tpi tnat (tpi P (apply1 (Shift1 (Shift1 P)) (tsuc (tvar db1))))) (lmax l l') →
  der Γ n tnat l → der Γ (trec P z H n) (apply1 P n) l'
// Dependent pairs
| der_sig : Π(Γ : Context) (l l' : Lev) (A B : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ (tsig A B) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_pair : Π (Γ : Context) (l l' : Lev) (A B a b : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ a A l → der Γ b (apply1 B a) l' → der Γ (tpair a b) (tsig A B) (lmax l l')
| der_p1 : Π (Γ : Context) (l l' : Lev) (A B p : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ p (tsig A B) (lmax l l') → der Γ (tp1 p) A l
| der_p2 : Π (Γ : Context) (l l' : Lev) (A B p : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der Γ p (tsig A B) (lmax l l') → der Γ (tp2 p) (apply1 B (tp1 p)) l
// Sum type
| der_sum : Π (Γ : Context) (l l' : Lev) (A B : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ A (tuniv l') (lsuc l') →
  der Γ (tsum A B) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_injl : Π (Γ : Context) (l l' : Lev) (A B a : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ a A l → der Γ (tinjl a) (tsum A B) (lmax l l')
| der_injr : Π (Γ : Context) (l l' : Lev) (A B b : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der Γ b B l → der Γ (tinjr b) (tsum A B) (lmax l l')
| der_case : Π (Γ : Context) (l l' m : Lev) (A B P Ha Hb x : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') →
  der (Push (tsum A B) (lmax l l') Γ) P (tuniv m) (lsuc m) →
  der Γ Ha (tpi A (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l' m) →
  der Γ x (tsum A B) (lmax l l') → der Γ (tcase A B P Ha Hb x) (apply1 P x) (lmax l (lmax l' m))
// Path types
| der_path : Π (Γ : Context) (l : Lev) (A x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ (tpath A x y) (tuniv l) (lsuc l)
| der_lamP : Π (Γ : Context) (l : Lev) (A t : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) t A l →
  der Γ (tlamP t) (tpath A (applyI1 t it0) (applyI1 t it1)) l
| der_appP : Π (Γ : Context) (l : Lev) (A t x y : Term) (i : ITerm),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_I Γ i → der Γ (tappP t i) (applyI1 A i) l
// Systems
| der_sys : Π (Γ : Context) (l : Lev) (A : Term) (f g : FTerm) (u v : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_isOne Γ (ftmax f g) → der_eq (PushF (ftmin f g) Γ) u v A l → der Γ (tsys f g u v) A l
| der_sys_empty : Π (Γ : Context) (l : Lev) (A : Term),
  der Γ A (tuniv l) (lsuc l) → der_isOne Γ ft0 → der Γ temptysys A l
// Transport
| der_transp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der_F Γ f → der Γ u (applyI1 A it0) l →
  der_eq (PushF f (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der Γ (ttransp A f u) (applyI1 A it1) l
// Homogeneous composition
| der_hcomp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u u0 : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der (PushF f (PushI Γ)) u A l → der Γ u0 A l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) A l → der Γ (thcomp A f u u0) A l
// glue
with der_eq : Context → Term → Term → Term → Lev → TYPE ≔
// Structural rules
| der_eq_refl : Π(Γ : Context) (l : Lev) (u A : Term), der Γ u A l → der_eq Γ u u A l
| der_eq_trans : Π (Γ : Context) (l : Lev) (u v w A : Term), der_eq Γ u v A l → der_eq Γ v w A l → der_eq Γ u w A l
| der_eq_sym : Π (Γ : Context) (l : Lev) (u v A : Term), der_eq Γ u v A l → der_eq Γ v u A l
// Type conversion
| der_eq_conv : Π (Γ : Context) (l : Lev) (u v A B : Term), der_eq Γ u v A l → der_eq Γ A B (tuniv l) (lsuc l) →
                                                            der_eq Γ u v B l
// Face reasoning
| der_eq_isOne_zero : Π (Γ : Context) (l : Lev) (A u v : Term),
  der_isOne Γ ft0 → der_eq Γ u v A l
| der_eq_isOne_max : Π (Γ : Context) (l : Lev) (A u v : Term) (f g : FTerm),
  der_eq (PushF f Γ) u v A l → der_eq (PushF g Γ) u v A l → der_isOne Γ (ftmax f g) → der_eq Γ u v A l
// Computation rules
// λ-calculus
| der_eq_beta : Π (Γ : Context) (l l' : Lev) (u A t B : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') →
  der (Push A l Γ) t B l' → der Γ u A l → der_eq Γ (tapp (tabs A t) u) (apply1 t u) (apply1 B u) l'
| der_eq_eta : Π (Γ : Context) (l l' : Lev) (A B f : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ f (tpi A B) (lmax l l') →
  der_eq Γ (tabs A (tapp (Shift f) (tvar db0))) f (tpi A B) (lmax l l')
// Integers
| der_eq_rec_zero : Π (Γ : Context) (l l' : Lev) (P z H : Term),
  der (Push tnat l Γ) P (tuniv l') (lsuc l') → der Γ z (apply1 P tzero) l' →
  der Γ H (tpi tnat (tpi P (apply1 (Shift1 (Shift1 P)) (tsuc (tvar db1))))) (lmax l l') →
  der_eq Γ (trec P z H tzero) z (apply1 P tzero) l'
| der_eq_rec_suc : Π (Γ : Context) (l l' : Lev) (P z H n : Term),
  der (Push tnat l Γ) P (tuniv l') (lsuc l') → der Γ z (apply1 P tzero) l' →
  der Γ H (tpi tnat (tpi P (apply1 (Shift1 (Shift1 P)) (tsuc (tvar db1))))) (lmax l l') →
  der Γ n tnat l → der_eq Γ (trec P z H (tsuc n)) (tapp (tapp H n) (trec P z H n)) (apply1 P (tsuc n)) l'
// Σ-types
| der_eq_p1 : Π (Γ : Context) (l l' : Lev) (A u B v : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ u A l → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ v (apply1 B u) l' →
  der_eq Γ (tp1 (tpair u v)) u A l
| der_eq_p2 : Π (Γ : Context) (l l' : Lev) (A u B v : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ u A l → der (Push A l Γ) B (tuniv l') (lsuc l') → der Γ v (apply1 B u) l' →
  der_eq Γ (tp2 (tpair u v)) v (apply1 B u) l
| der_eq_pair : Π (Γ : Context) (l l' : Lev) (A B t u : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') → der Γ t (tsig A B) (lmax l l') →
  der Γ u (tsig A B) (lmax l l') → der_eq Γ (tp1 t) (tp1 u) A l → der_eq Γ (tp2 t) (tp2 u) (apply1 B (tp1 t)) l' →
  der_eq Γ t u (tsig A B) (lmax l l')
// Sum types
| der_eq_case_left : Π (Γ : Context) (l l' m : Lev) (A B P Ha Hb a : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l) (lsuc l) →
  der (Push (tsum A B) (lmax l l') Γ) P (tuniv m) (lsuc m) →
  der Γ Ha (tpi A (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l' m) →
  der Γ a A l → der_eq Γ (tcase A B P Ha Hb (tinjl a)) (tapp Ha a) (apply1 P (tinjl a)) (lmax l (lmax l' m))
| der_eq_case_right : Π (Γ : Context) (l l' m : Lev) (A B P Ha Hb b : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l) (lsuc l) →
  der (Push (tsum A B) (lmax l l') Γ) P (tuniv m) (lsuc m) →
  der Γ Ha (tpi A (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb (tpi B (apply1 (Shift1 P) (tinjl (tvar db0)))) (lmax l' m) →
  der Γ b B l' → der_eq Γ (tcase A B P Ha Hb (tinjr b)) (tapp Hb b) (apply1 P (tinjr b)) (lmax l (lmax l' m))
// Path types
| der_eq_betaP : Π (Γ : Context) (l : Lev) (A t : Term) (i : ITerm),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) t A l → der_I Γ i →
  der_eq Γ (tappP (tlamP t) i) (applyI1 t i) (applyI1 A i) l
| der_eq_etaP : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tlamP (tappP (IShift t) (itvar db0))) t (tpath A x y) l
| der_eq_appP_zero : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tappP t it0) x (applyI1 A it0) l
| der_eq_appP_one : Π (Γ : Context) (l : Lev) (A t x y : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der Γ t (tpath A x y) l → der_eq Γ (tappP t it1) y (applyI1 A it1) l
// Systems
| der_eq_sys_left : Π (Γ : Context) (l : Lev) (A : Term) (f g : FTerm) (u v : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_eq (PushF (ftmin f g) Γ) u v A l → der_isOne Γ f → der_eq Γ (tsys f g u v) u A l
| der_eq_sys_right : Π (Γ : Context) (l : Lev) (A : Term) (f g : FTerm) (u v : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der_F Γ g → der (PushF f Γ) u A l → der (PushF g Γ) v A l →
  der_eq (PushF (ftmin f g) Γ) u v A l → der_isOne Γ g → der_eq Γ (tsys f g u v) v A l
// Transport, general rule first when transporting on the whole space,
| der_eq_transp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ u (applyI1 A it0) l →
  der_eq (PushF f (PushI Γ)) A (Shift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_isOne Γ f → der_eq Γ (ttransp A f u) u (applyI1 A it1) l
// then computing rules by case analysis on the type
// (transpⁱ (Π (x:A) B) φ u) v = transpⁱ B(x/transpFill⁻ⁱ A φ v) φ (u (transpʲ A(i/~j) φ v))
| der_eq_transp_pi : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u v : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (Push A l (PushI Γ)) B (tuniv l') (lsuc l') →
  der_F Γ f → der_eq (PushF f (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (Push A l (PushF f (PushI Γ))) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l') →
  der_eq Γ (tapp (ttransp (tpi A B) f u) v)
         (ttransp (apply1 B (ttransp (applyI1 (IShift1 (IShift1 A)) (itmax (itvar db1) (itsym (itvar db0))))
                                     (ftmax f (fteq0 db0)) v))
                  f (tapp u (ttransp (applyI1 (IShift1 A) (itsym (itvar db0))) f v)))
         (tpi (applyI1 A it1) (applyI1 B it1)) (lmax l l')
| der_eq_transp_univ : Π (Γ : Context) (l : Lev) (f : FTerm) (A : Term),
  der Γ A (tuniv l) (lsuc l) → der_eq Γ (ttransp (tuniv l) f A) A (tuniv l) (lsuc l)
| der_eq_transp_zero : Π (Γ : Context) (l : Lev) (f : FTerm),
  der_F Γ f → der_eq Γ (ttransp tnat f tzero) tzero tnat l
| der_eq_transp_suc : Π (Γ : Context) (l : Lev) (f : FTerm) (n : Term),
  der_F Γ f → der Γ n tnat l → der_eq Γ (ttransp tnat f (tsuc n)) (tsuc (ttransp tnat f n)) tnat l
// transpⁱ (Σ (x : A) B) φ u = (transpⁱ A φ u.1, transpⁱ B(x/transpFillⁱ A φ u.1) φ u.2)
| der_eq_transp_sig : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (Push A l (PushI Γ)) B (tuniv l') (lsuc l') →
  der_F Γ f → der_eq (PushF f (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (Push A l (PushF f (PushI Γ))) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l') →
  der_eq Γ (ttransp (tsig A B) f u)
         (tpair (ttransp A f (tp1 u))
                (ttransp (apply1 B (ttranspFill A f (tp1 u))) f (tp2 u)))
         (tsig (applyI1 A it1) (applyI1 B it0)) l
// transpⁱ (A + B) φ (injl a) = injl (transpⁱ A φ a)
| der_eq_transp_sum_left : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (a : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) B (tuniv l') (lsuc l') →
  der Γ a (applyI1 A it0) l → der_eq (PushF f (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (PushF f (PushI Γ)) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l) →
  der_eq Γ (ttransp (tsum A B) f (tinjl a)) (tinjl (ttransp A f a)) (applyI1 (tsum A B) it1) (lmax l l')
// transpⁱ (A + B) φ (injr b) = injr (transpⁱ B φ b)
| der_eq_transp_sum_right : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (b : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der (PushI Γ) B (tuniv l') (lsuc l') →
  der Γ b (applyI1 B it0) l' → der_eq (PushF f (PushI Γ)) A (IShift (applyI1 A it0)) (tuniv l) (lsuc l) →
  der_eq (PushF f (PushI Γ)) B (IShift (applyI1 B it0)) (tuniv l') (lsuc l) →
  der_eq Γ (ttransp (tsum A B) f (tinjr b)) (tinjr (ttransp B f b)) (applyI1 (tsum A B) it1) (lmax l l')
// transpⁱ (Pathʲ A v w) φ u = λ j, compⁱ A [φ ↦ u j, (j = 0) ↦ v, (j = 1) ↦ w] (u j)
// The ugly subst/shift is swapping the two interval variables in A's context
| der_eq_transp_path : Π (Γ : Context) (l : Lev) (A x y : Term) (f : FTerm) (u : Term),
  der (PushI (PushI Γ)) A (tuniv l) (lsuc l) → der (PushI Γ) x (applyI1 A it0) l →
  der (PushI Γ) y (applyI1 A it1) l → der Γ u (applyI1 (tpath A x y) it0) l →
  der_eq (PushF f (PushI (PushI Γ))) A (IShift1 (Isubst db1 it0 A)) (tuniv l) (lsuc l) →
  der_eq (PushF f (PushI Γ)) x (IShift (applyI1 x it0)) (applyI1 A it0) l →
  der_eq (PushF f (PushI Γ)) y (IShift (applyI1 y it0)) (applyI1 A it1) l →
  der_eq Γ (ttransp (tpath A x y) f u)
         (tlamP (tcomp (applyI1 (applyI1 (Ishift db2 (Ishift db2 A)) (itvar db2)) (itvar db0))
                       (ftmax (IShiftF f) (ftmax (fteq0 db0) (fteq1 db0)))
                       (tsys (IShiftFN db1 f) (ftmax (fteq0 db1) (fteq1 db1))
                             (ttranspFill (applyI1 (applyI1 (Ishift db2 (Ishift db2 A)) (itvar db2)) (itvar db1))
                                          (IShiftF (IShiftF f)) (tappP u (itvar db1)))
                             (tsys (fteq0 db1) (fteq1 db1) (IShift1 x) (IShift1 y)))
                       (tappP u (itvar db0)))) (tpath A x y) l
// Glue types
// hcomp, general rule first when composing on the whole space,
| der_eq_hcomp : Π (Γ : Context) (l : Lev) (A : Term) (f : FTerm) (u u0 : Term),
  der Γ A (tuniv l) (lsuc l) → der_F Γ f → der (PushF f (PushI Γ)) u A l → der Γ u0 A l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) A l → der_isOne Γ f → der_eq Γ (thcomp A f u u0) (applyI1 u it1) A l
// then computing rules by case analysis on the type
// hcompⁱ (Π (x : A), B) [φ ↦ u] u0 v = hcompⁱ B(x/v) [φ ↦ u v] (u0 v)
| der_eq_hcomp_pi : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u u0 v : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF f (PushI Γ)) u (tpi A B) (lmax l l') → der Γ u0 (tpi A B) (lmax l l') →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tpi A B) (lmax l l') → der_isOne Γ f →
  der_eq Γ (tapp (thcomp A f u u0) v) (thcomp (apply1 B v) f (tapp u v) (tapp u0 v)) (apply1 B v) l
// hcomp (U l) [φ ↦ E] A = Glue [φ ↦ (E(i/1), (equivⁱ E(i/1-i)))] A
| der_eq_hcomp_zero : Π (Γ : Context) (l : Lev) (f : FTerm) (n : Term),
  der_F Γ f → der (PushF f (PushI Γ)) n tnat l → der_eq (PushF f Γ) tzero (applyI1 n it0) tnat l →
  der_eq Γ (thcomp tnat f n tzero) tzero tnat l
| der_eq_hcomp_suc : Π (Γ : Context) (l : Lev) (f : FTerm) (n n0 : Term),
  der_F Γ f → der (PushF f (PushI Γ)) n tnat l → der Γ n0 tnat l → der_eq (PushF f Γ) n0 (applyI1 n it0) tnat l →
  der_eq Γ (thcomp tnat f (tsuc n) (tsuc n0)) (tsuc (thcomp tnat f n n0)) tnat l
// hcompⁱ (Σ (x : A), B) [φ ↦ u] u0 = (hcompⁱ A [φ ↦ u.1] u0.1, compⁱ B(x/hfillⁱ A [φ ↦ u.1] u0.1) [φ ↦ u.2] u0.2)
| der_eq_hcomp_sig : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (u u0 : Term),
  der Γ A (tuniv l) (lsuc l) → der (Push A l Γ) B (tuniv l) (lsuc l) → der_F Γ f →
  der (PushF f (PushI Γ)) u (tsig A B) (lmax l l') → der Γ u0 (tsig A B) (lmax l l') →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tsig A B) (lmax l l') →
  der_eq Γ (thcomp (tsig A B) f u u0) (tpair (thcomp A f (tp1 u) (tp1 u0))
                                             (tcomp (apply1 B (thfill A f (tp1 u) (tp1 u0))) f (tp2 u) (tp2 u0)))
         (tsig A B) (lmax l l')
| der_eq_hcomp_sum_left : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (a a0 : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF f (PushI Γ)) a A l → der Γ a0 A l → der_eq (PushF f Γ) a0 (applyI1 a it0) A l →
  der_eq Γ (thcomp (tsum A B) f (tinjl a) (tinjl a0)) (tinjl (thcomp A f a a0)) (tsum A B) (lmax l l')
| der_eq_hcomp_sum_right : Π (Γ : Context) (l l' : Lev) (A B : Term) (f : FTerm) (b b0 : Term),
  der Γ A (tuniv l) (lsuc l) → der Γ B (tuniv l') (lsuc l') → der_F Γ f →
  der (PushF f (PushI Γ)) b B l' → der Γ b0 B l' → der_eq (PushF f Γ) b0 (applyI1 b it0) B l' →
  der_eq Γ (thcomp (tsum A B) f (tinjr b) (tinjr b0)) (tinjr (thcomp B f b b0)) (tsum A B) (lmax l l')
// hcompⁱ (Pathʲ A v w) [φ ↦ u] u0 = λ j, hcompⁱ A [φ ↦ u j, (j = 0) ↦ v, (j = 1) ↦ w] (u0 j)
| der_eq_hcomp_path : Π (Γ : Context) (l : Lev) (A x y : Term) (f : FTerm) (u u0 : Term),
  der (PushI Γ) A (tuniv l) (lsuc l) → der Γ x (applyI1 A it0) l → der Γ y (applyI1 A it1) l →
  der_F Γ f → der (PushF f (PushI Γ)) u (tpath A x y) l → der Γ u0 (tpath A x y) l →
  der_eq (PushF f Γ) u0 (applyI1 u it0) (tpath A x y) l →
  der_eq Γ (thcomp (tpath A x y) f u u0)
         (tlamP (thcomp A (ftmax (IShiftF f) (ftmax (fteq0 db0) (fteq1 db0)))
                        (tsys (IShiftFN db1 f) (ftmax (fteq0 db1) (fteq1 db1)) (tappP (IShift1 u) (itvar db1))
                              (tsys (fteq0 db1) (fteq1 db1) (IShiftN db1 x) (IShiftN db1 y)))
                        (tappP (IShift u0) (itvar db0))))
         (tpath A x y) l
// Glue types
// Congruence rules
| der_eq_cong_pi : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l') →
  der (Push A1 l Γ) B1 (tuniv l') (lsuc l') → der (Push A2 l Γ) B2 (tuniv l') (lsuc l') →
  der_eq Γ (tpi A1 B1) (tpi A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_eq_cong_abs : Π (Γ : Context) (l l' : Lev) (A1 A2 B t1 t2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) t1 t2 B l' →
  der (Push A1 l Γ) t1 B l' → der (Push A2 l Γ) t2 B l' →
  der_eq Γ (tabs A1 t1) (tabs A2 t2) (tpi A1 B) (lmax l l')
| der_eq_cong_app : Π (Γ : Context) (l l' : Lev) (A B t1 t2 u1 u2 : Term),
  der_eq Γ t1 t2 (tpi A B) (lmax l l') → der_eq Γ u1 u2 A l →
  der_eq Γ (tapp t1 u1) (tapp t2 u2) (apply1 B u1) l'
| der_eq_cong_suc : Π (Γ : Context) (l : Lev) (n n' : Term),
  der_eq Γ n n' tnat l → der_eq Γ (tsuc n) (tsuc n') tnat l
| der_eq_cong_rec : Π (Γ : Context) (l l' : Lev) (P1 P2 z1 z2 H1 H2 n1 n2 : Term),
  der_eq (Push tnat l Γ) P1 P2 (tuniv l') (lsuc l') → der_eq Γ z1 z2 (apply1 P1 tzero) l' →
  der_eq Γ H1 H2 (tpi tnat (tpi P1 (apply1 (Shift1 (Shift1 P1)) (tsuc (tvar db1))))) l' →
  der_eq Γ n1 n2 tnat l → der Γ z1 (apply1 P1 tzero) l' → der Γ z2 (apply1 P2 tzero) l' →
  der Γ H1 (tpi tnat (tpi P1 (apply1 (Shift1 (Shift1 P1)) (tsuc (tvar db1))))) l' →
  der Γ H2 (tpi tnat (tpi P2 (apply1 (Shift1 (Shift1 P2)) (tsuc (tvar db1))))) l' →
  der_eq Γ (trec P1 z1 H1 n1) (trec P2 z2 H2 n2) (apply1 P1 n1) l'
| der_eq_cong_sig : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq (Push A1 l Γ) B1 B2 (tuniv l') (lsuc l') →
  der (Push A1 l Γ) B1 (tuniv l') (lsuc l') → der (Push A2 l Γ) B2 (tuniv l') (lsuc l') →
  der_eq Γ (tsig A1 B1) (tsig A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_eq_cong_pair : Π (Γ : Context) (l l' : Lev) (A B u1 u2 v1 v2 : Term),
  der_eq Γ u1 u2 A l → der_eq Γ v1 v2 (apply1 B u1) l' →
  der Γ v1 (apply1 B u1) l' → der Γ v2 (apply1 B u2) l' →
  der_eq Γ (tpair u1 v1) (tpair u2 v2) (tsig A B) (lmax l l')
| der_eq_cong_p1 : Π (Γ : Context) (l l' : Lev) (A B u v : Term),
  der_eq Γ u v (tsig A B) (lmax l l') →
  der_eq Γ (tp1 u) (tp1 v) A l
| der_eq_cong_p2 : Π (Γ : Context) (l l' : Lev) (A B u v : Term),
  der_eq Γ u v (tsig A B) (lmax l l') →
  der_eq Γ (tp2 u) (tp2 v) (apply1 B (tp1 u)) l'
| der_eq_cong_sum : Π (Γ : Context) (l l' : Lev) (A1 A2 B1 B2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq Γ B1 B2 (tuniv l') (lsuc l') →
  der_eq Γ (tsum A1 B1) (tsum A2 B2) (tuniv (lmax l l')) (lsuc (lmax l l'))
| der_eq_cong_injl : Π (Γ : Context) (l l' : Lev) (A B a1 a2 : Term),
  der_eq Γ a1 a2 A l → der_eq Γ (tinjl a1) (tinjl a2) (tsum A B) (lmax l l')
| der_eq_cong_injr : Π (Γ : Context) (l l' : Lev) (A B b1 b2 : Term),
  der_eq Γ b1 b2 B l' → der_eq Γ (tinjr b1) (tinjr b2) (tsum A B) (lmax l l')
| der_eq_cong_case : Π (Γ : Context) (l l' m : Lev) (A1 A2 B1 B2 P1 P2 Ha1 Ha2 Hb1 Hb2 u v : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq Γ B1 B2 (tuniv l') (lsuc l') →
  der_eq (Push (tsum A1 B1) (lmax l l') Γ) P1 P2 (tuniv m) (lsuc m) →
  der_eq Γ Ha1 Ha2 (tpi A1 (apply1 (Shift1 P1) (tinjl (tvar db0)))) (lmax l m) →
  der_eq Γ Hb1 Hb2 (tpi B1 (apply1 (Shift1 P1) (tinjr (tvar db0)))) (lmax l' m) →
  der_eq Γ u v (tsum A1 B1) (lmax l l') →
  der (Push (tsum A1 A2) (lmax l l') Γ) P1 (tuniv m) (lsuc m) →
  der (Push (tsum A2 B2) (lmax l l') Γ) P2 (tuniv m) (lsuc m) →
  der Γ Ha1 (tpi A1 (apply1 (Shift1 P1) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Ha2 (tpi A2 (apply1 (Shift1 P2) (tinjl (tvar db0)))) (lmax l m) →
  der Γ Hb1 (tpi B1 (apply1 (Shift1 P1) (tinjr (tvar db0)))) (lmax l' m) →
  der Γ Hb2 (tpi B2 (apply1 (Shift1 P1) (tinjr (tvar db0)))) (lmax l' m) →
  der_eq Γ (tcase A1 B1 P1 Ha1 Hb1 u) (tcase A2 B2 P2 Ha2 Hb2 v) (apply1 P1 u) m
| der_eq_cong_path : Π (Γ : Context) (l : Lev) (A1 A2 x1 x2 y1 y2 : Term),
  der_eq (PushI Γ) A1 A2 (tuniv l) (lsuc l) →
  der_eq Γ x1 x2 (applyI1 A1 it0) l → der_eq Γ y1 y2 (applyI1 A1 it1) l →
  der Γ x1 (applyI1 A1 it0) l → der Γ x2 (applyI1 A2 it1) l →
  der Γ y1 (applyI1 A1 it0) l → der Γ y2 (applyI1 A2 it1) l →
  der_eq Γ (tpath A1 x1 y1) (tpath A2 x2 y2) (tuniv l) (lsuc l)
| der_eq_cong_lamP : Π (Γ : Context) (l : Lev) (A t1 t2 : Term),
  der_eq (PushI Γ) t1 t2 A l →
  der_eq Γ (applyI1 t1 it0) (applyI1 t2 it0) (applyI1 A it0) l →
  der_eq Γ (applyI1 t1 it1) (applyI1 t2 it1) (applyI1 A it1) l →
  der_eq Γ (tlamP t1) (tlamP t2) (tpath A (applyI1 t1 it0) (applyI1 t1 it1)) l
| der_eq_cong_appP : Π (Γ : Context) (l : Lev) (A x y u v : Term) (i1 i2 : ITerm),
  der_eq Γ u v (tpath A x y) l → der_eq_I Γ i1 i2 →
  der_eq Γ (tappP u i1) (tappP v i2) (applyI1 A i1) l
| der_eq_cong_sys : Π (Γ : Context) (l : Lev) (A : Term) (f1 f2 g1 g2 : FTerm) (u1 u2 v1 v2 : Term),
  // der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq (PushF f1 Γ) u1 u2 A l → der_eq (PushF g1 Γ) v1 v2 A l →
  der (PushF f1 Γ) u1 A l → der (PushF f2 Γ) u2 A l → der (PushF g1 Γ) v1 A l → der (PushF g2 Γ) v2 A l →
  der_isOne Γ (ftmax f1 g1) → der_isOne Γ (ftmax f2 g2) → der_eq (PushF (ftmin f1 g1) Γ) u1 v1 A l →
  der_eq (PushF (ftmin f2 g2) Γ) u2 v2 A l → der_eq Γ (tsys f1 g1 u1 v1) (tsys f2 g2 u2 v2) A l
| der_eq_cong_transp : Π (Γ : Context) (l : Lev) (A1 A2 : Term) (f1 f2 : FTerm) (a1 a2 : Term),
  der_eq (PushI Γ) A1 A2 (tuniv l) (lsuc l) → der_eq_F Γ f1 f2 → der_eq Γ a1 a2 (applyI1 A1 it0) l →
  der Γ a1 (applyI1 A1 it0) l → der Γ a2 (applyI1 A2 it0) l →
  der_eq (PushI Γ) A1 (IShift (applyI1 A1 it0)) (tuniv l) (lsuc l) →
  der_eq (PushI Γ) A2 (IShift (applyI1 A2 it0)) (tuniv l) (lsuc l) →
  der_eq Γ (ttransp A1 f1 a1) (ttransp A2 f2 a2) (applyI1 A1 it1) l
| der_eq_cong_hcomp : Π (Γ : Context) (l : Lev) (A1 A2 : Term) (f1 f2 : FTerm) (u1 u2 v1 v2 : Term),
  der_eq Γ A1 A2 (tuniv l) (lsuc l) → der_eq_F Γ f1 f2 → der_eq (PushF f1 (PushI Γ)) u1 u2 A1 l →
  der_eq Γ v1 v2 A1 l → der (PushF f1 (PushI Γ)) u1 A1 l → der (PushF f2 (PushI Γ)) u2 A2 l →
  der Γ u1 A1 l → der Γ u2 A2 l → der_eq (PushF f1 Γ) v1 (applyI1 u1 it0) A1 l →
  der_eq (PushF f2 Γ) v2 (applyI1 u2 it0) A2 l →
  der_eq Γ (thcomp A1 f1 u1 v1) (thcomp A2 f2 u2 v2) A1 l
with der_I : Context → ITerm → TYPE ≔
| der_I_0 : Π (Γ : Context), der_I Γ it0
| der_I_1 : Π (Γ : Context), der_I Γ it1
| der_I_var : Π (Γ : Context) (id : DBId), DBLe (dbsucc id) (lenI Γ) → der_I Γ (itvar id)
| der_I_sym : Π (Γ : Context) (i : ITerm), der_I Γ i → der_I Γ (itsym i)
| der_I_min : Π (Γ : Context) (i j : ITerm), der_I Γ i → der_I Γ j → der_I Γ (itmin i j)
| der_I_max : Π (Γ : Context) (i j : ITerm), der_I Γ i → der_I Γ j → der_I Γ (itmax i j)
with der_eq_I : Context → ITerm → ITerm → TYPE ≔
// Structural rules
| der_eq_I_refl : Π (Γ : Context) (i : ITerm), der_I Γ i → der_eq_I Γ i i
| der_eq_I_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ i j → der_eq_I Γ j i
| der_eq_I_trans : Π (Γ : Context) (i j k : ITerm), der_eq_I Γ i j → der_eq_I Γ j k → der_eq_I Γ i k
// Face reasoning
| der_eq_I_isOne_zero : Π (Γ : Context) (i j : ITerm), der_isOne Γ ft0 → der_eq_I Γ i j
| der_eq_I_isOne_max : Π (Γ : Context) (i j : ITerm) (f g : FTerm),
  der_eq_I (PushF f Γ) i j → der_eq_I (PushF g Γ) i j → der_isOne Γ (ftmax f g) → der_eq_I Γ i j
| der_eq_I_isOne_eq0 : Π (Γ : Context) (id : DBId), der_isOne Γ (fteq0 id) → der_eq_I Γ (itvar id) it0
| der_eq_I_isOne_eq1 : Π (Γ : Context) (id : DBId), der_isOne Γ (fteq1 id) → der_eq_I Γ (itvar id) it1
// Computation rules for interval operations
| der_eq_I_sym_sym : Π (Γ : Context) (i : ITerm), der_eq_I Γ i (itsym (itsym i))
| der_eq_I_min_assoc : Π (Γ : Context) (i j k : ITerm), der_eq_I Γ (itmin i (itmin j k)) (itmin (itmin i j) k)
| der_eq_I_min_comm : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itmin i j) (itmin j i)
| der_eq_I_min_zero : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmin i it0) it0
| der_eq_I_min_one : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmin i it1) i
| der_eq_I_max_assoc : Π (Γ : Context) (i j k : ITerm), der_eq_I Γ (itmax i (itmax j k)) (itmax (itmax i j) k)
| der_eq_I_max_comm : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itmax i j) (itmax j i)
| der_eq_I_max_zero : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmax i it0) i
| der_eq_I_max_one : Π (Γ : Context) (i : ITerm), der_eq_I Γ (itmax i it1) it1
| der_eq_I_min_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itsym (itmin i j)) (itmax (itsym i) (itsym j))
| der_eq_I_max_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ (itsym (itmax i j)) (itmin (itsym i) (itsym j))
| der_eq_I_min_distrib : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmin i (itmax j k)) (itmax (itmin i j) (itmin i k))
| der_eq_I_max_distrib : Π (Γ : Context) (i j k : ITerm),
  der_eq_I Γ (itmax i (itmin j k)) (itmin (itmax i j) (itmax i k))
// Congruence rules
| der_eq_I_cong_sym : Π (Γ : Context) (i j : ITerm), der_eq_I Γ i j → der_eq_I Γ (itsym i) (itsym j)
| der_eq_I_cong_min : Π (Γ : Context) (i1 i2 j1 j2 : ITerm), der_eq_I Γ i1 i2 → der_eq_I Γ j1 j2 →
                                                             der_eq_I Γ (itmin i1 j1) (itmin i2 j2)
| der_eq_I_cong_max : Π (Γ : Context) (i1 i2 j1 j2 : ITerm), der_eq_I Γ i1 i2 → der_eq_I Γ j1 j2 →
                                                             der_eq_I Γ (itmax i1 j1) (itmax i2 j2)
with der_F : Context → FTerm → TYPE ≔
| der_F_0 : Π (Γ : Context), der_F Γ ft0
| der_F_1 : Π (Γ : Context), der_F Γ ft1
| der_F_eq0 : Π (Γ : Context) (id : DBId), DBLe (dbsucc id) (lenI Γ) → der_F Γ (fteq0 id)
| der_F_eq1 : Π (Γ : Context) (id : DBId), DBLe (dbsucc id) (lenI Γ) → der_F Γ (fteq1 id)
| der_F_min : Π (Γ : Context) (f g : FTerm), der_F Γ f → der_F Γ g → der_F Γ (ftmin f g)
| der_F_max : Π (Γ : Context) (f g : FTerm), der_F Γ f → der_F Γ g → der_F Γ (ftmax f g)
with der_eq_F : Context → FTerm → FTerm → TYPE ≔
// Structural rules
| der_eq_F_refl : Π (Γ : Context) (f : FTerm), der_F Γ f → der_eq_F Γ f f
| der_eq_F_sym : Π (Γ : Context) (f g : FTerm), der_eq_F Γ f g → der_eq_F Γ g f
| der_eq_F_assoc : Π (Γ : Context) (f g h : FTerm), der_eq_F Γ f g → der_eq_F Γ g h → der_eq_F Γ f h
// Face reasoning
| der_eq_F_isOne_zero : Π (Γ : Context) (f g : FTerm), der_isOne Γ ft0 → der_eq_F Γ f g
| der_eq_F_isOne_max : Π (Γ : Context) (f g f' g' : FTerm),
  der_eq_F (PushF f' Γ) f g → der_eq_F (PushF g' Γ) f g → der_isOne Γ (ftmax f g) → der_eq_F Γ f g
| der_eq_F_isOne_one : Π (Γ : Context) (f : FTerm), der_isOne Γ f → der_eq_F Γ f ft1
// Computation rules for face operations
| der_eq_F_min_assoc : Π (Γ : Context) (f g h : FTerm), der_eq_F Γ (ftmin f (ftmin g h)) (ftmin (ftmin f g) h)
| der_eq_F_min_comm : Π (Γ : Context) (f g : FTerm), der_eq_F Γ (ftmin f g) (ftmin g f)
| der_eq_F_max_assoc : Π (Γ : Context) (f g h : FTerm), der_eq_F Γ (ftmax f (ftmax g h)) (ftmax (ftmax f g) h)
| der_eq_F_max_comm : Π (Γ : Context) (f g : FTerm), der_eq_F Γ (ftmax f g) (ftmax g f)
| der_eq_F_min_distrib : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmin f (ftmax g h)) (ftmax (ftmin f g) (ftmin f h))
| der_eq_F_max_distrib : Π (Γ : Context) (f g h : FTerm),
  der_eq_F Γ (ftmax f (ftmin g h)) (ftmin (ftmax f g) (ftmax f h))
| der_eq_F_empty : Π (Γ : Context) (id : DBId), der_eq_F Γ (ftmin (fteq0 id) (fteq1 id)) ft0
// Congruence rules
| der_eq_F_cong_eq0 : Π (Γ : Context) (id : DBId) (i : ITerm),
  der_eq_I Γ (itvar id) i → der_eq_F Γ (fteq0 id) (IsubstF id i (fteq0 id))
| der_eq_F_cong_eq1 : Π (Γ : Context) (id : DBId) (i : ITerm),
  der_eq_I Γ (itvar id) i → der_eq_F Γ (fteq1 id) (IsubstF id i (fteq1 id))
| der_eq_F_cong_min : Π (Γ : Context) (f1 f2 g1 g2 : FTerm),
  der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq_F Γ (ftmin f1 g1) (ftmin f2 g2)
| der_eq_F_cong_max : Π (Γ : Context) (f1 f2 g1 g2 : FTerm),
  der_eq_F Γ f1 f2 → der_eq_F Γ g1 g2 → der_eq_F Γ (ftmax f1 g1) (ftmax f2 g2)
with der_isOne : Context → FTerm → TYPE ≔
| der_isOne_one : Π (Γ : Context), der_isOne Γ (ft1)
| der_isOne_zero : Π (Γ : Context) (t : FTerm), der_isOne Γ ft0 → der_isOne Γ t
| der_isOne_empty : Π (Γ : Context) (id : DBId), der_isOne Γ (ftmin (fteq0 id) (fteq1 id)) → der_isOne Γ ft0
| der_isOne_min_intro : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_isOne Γ g → der_isOne Γ (ftmin f g)
| der_isOne_min_elim_left : Π (Γ : Context) (f g : FTerm), der_isOne Γ (ftmin f g) → der_isOne Γ f
| der_isOne_min_elim_right : Π (Γ : Context) (f g : FTerm), der_isOne Γ (ftmin f g) → der_isOne Γ g
| der_isOne_max_intro_left : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_isOne Γ (ftmax f g)
| der_isOne_max_intro_right : Π (Γ : Context) (f g : FTerm), der_isOne Γ g → der_isOne Γ (ftmax f g)
| der_isOne_max_elim : Π (Γ : Context) (f g t : FTerm),
  der_isOne (PushF f Γ) t → der_isOne (PushF g Γ) t → der_isOne Γ (ftmax f g) → der_isOne Γ t
| der_isOne_axiom : Π (Γ : Context) (f : FTerm), der_isOne (PushF f Γ) f
| der_isOne_weak : Π (Γ : Context) (t : Term) (l : Lev) (f : FTerm), der_isOne Γ f → der_isOne (Push t l Γ) f
| der_isOne_weakI : Π (Γ : Context) (f : FTerm), der_isOne Γ f → der_isOne (PushI Γ) (IShiftF f)
| der_isOne_weakF : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_isOne (PushF g Γ) f
| der_isOne_cong : Π (Γ : Context) (f g : FTerm), der_isOne Γ f → der_eq_F Γ f g → der_isOne Γ g;