// TODO sort imports ctt vs derivations, avoid name clashes ?
require ctt.ctt as ctt;

// heterogeneous equality for cubical conversion TODO move this
symbol Hconv (l : ctt.Lev) (A B : ctt.T l) (a : ctt.eps A) (b : ctt.eps B) : ctt.xT ≔
  ctt.xSig (ctt.conv A B) (λ p, ctt.conv (ctt.convtransp p a) b);
symbol tHconv (l : ctt.Lev) (A B : ctt.T l) (a : ctt.eps A) (b : ctt.eps B) : TYPE ≔
  ctt.xeps (Hconv l A B a b);
symbol H [l : ctt.Lev] [A B : ctt.T l] (a : ctt.eps A) (b : ctt.eps B) ≔ Hconv l A B a b;
symbol tH [l : ctt.Lev] [A B : ctt.T l] (a : ctt.eps A) (b : ctt.eps B)  ≔ tHconv  l A B a b;
symbol heq_to_eq [l : ctt.Lev] [A : ctt.T l] [a b : ctt.eps A] (h : tHconv l A A a b) : ctt.tconv a b ≔
  ctt.xJ (λ p _, ctt.conv (ctt.convtransp p a) b) (ctt.xp2 h)
     ctt.xrefl (ctt.xK (λ p, ctt.xEq p ctt.xrefl) (ctt.xrefl) (ctt.xp1 h));

// Syntax types
constant symbol Lev : TYPE;
constant symbol lsuc : Lev → Lev;

constant symbol Term : TYPE;
constant symbol ITerm : TYPE;
constant symbol FTerm : TYPE;
constant symbol tuniv : Lev → Term;
constant symbol Context : TYPE;

// Typing
constant symbol der : Context → Term → Term → Lev → TYPE;
constant symbol der_eq : Context → Term → Term → Term → Lev → TYPE;
constant symbol der_I : Context → ITerm → TYPE;
constant symbol der_eq_I : Context → ITerm → ITerm → TYPE;
constant symbol der_F : Context → FTerm → TYPE;
constant symbol der_eq_F : Context → FTerm → FTerm → TYPE;
constant symbol der_isOne : Context → FTerm → TYPE;

constant symbol der_context : Context → TYPE;

// Lemmas
symbol inv_type [Γ : Context] [l : Lev] [t T : Term] : der_context Γ → der Γ t T l → der Γ T (tuniv l) (lsuc l);
symbol inv_eq_t1   [Γ : Context] [l : Lev] [T t1 t2 : Term] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t1 T l;
symbol inv_eq_t2   [Γ : Context] [l : Lev] [T t1 t2 : Term] : der_context Γ → der_eq Γ t1 t2 T l → der Γ t2 T l;

symbol inv_eq_I_t1 [Γ : Context] [t1 t2 : ITerm] : der_context Γ → der_eq_I Γ t1 t2 → der_I Γ t1;
symbol inv_eq_I_t2 [Γ : Context] [t1 t2 : ITerm] : der_context Γ → der_eq_I Γ t1 t2 → der_I Γ t2;

symbol inv_eq_F_t1 [Γ : Context] [t1 t2 : FTerm] : der_context Γ → der_eq_F Γ t1 t2 → der_F Γ t1;
symbol inv_eq_F_t2 [Γ : Context] [t1 t2 : FTerm] : der_context Γ → der_eq_F Γ t1 t2 → der_F Γ t2;

symbol inv_isOne [Γ : Context] [t1 : FTerm] : der_context Γ → der_isOne Γ t1 → der_F Γ t1;

// Translation, levels first (which is trivial)
symbol τ_lev : Lev → ctt.Lev;
rule τ_lev (lsuc $l) ↪ ctt.lsuc (τ_lev $l);

// Translation context
constant symbol TContext : TYPE;
constant symbol PContext : TContext → TYPE;
symbol projΓ1 [Γ : TContext] : PContext Γ → TContext;
symbol projΓ2 [Γ : TContext] : PContext Γ → TContext;

symbol τ_Γ : TContext → Context;
symbol τ_dΓ (Γ : TContext) : der_context (τ_Γ Γ);

// The translation itself, terms and types first
symbol τ_T (Γ : TContext) [T : Term] [l : Lev] :
  der (τ_Γ Γ) T (tuniv l) (lsuc l) → ctt.T (τ_lev l);
symbol τ (Γ : TContext) [l : Lev] [t T : Term] (d : der (τ_Γ Γ) t T l) :
  ctt.eps (τ_T Γ (inv_type (τ_dΓ Γ) d));

// For things to type, we need to know that the translation of a universe always is one
rule @τ_T _ (tuniv $s) (lsuc $s) _ ↪ ctt.t (τ_lev $s);
rule @τ _ (lsuc (lsuc $s)) (tuniv $s) (tuniv (lsuc $s)) _ ↪ ctt.t (τ_lev $s);

symbol τ_inv (Γ : TContext) [l : Lev] [t T : Term] :
  der (τ_Γ Γ) t T l → ctt.T (τ_lev l) ≔ λ d, τ Γ (inv_type (τ_dΓ Γ) d);

// Translation of equality derivation
symbol τ_eq_type (Γ : TContext) [l : Lev] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : ctt.xT ≔
  let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
  let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
  let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
  let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
  Hconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);
symbol τ_eq (Γ : TContext) [l : Lev] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : ctt.xeps (τ_eq_type Γ d);
symbol τ_eqT (Γ : TContext) [l : Lev] [T1 T2 : Term] (d : der_eq (τ_Γ Γ) T1 T2 (tuniv l) (lsuc l)) :
  let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
  let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
  ctt.tconvtype (τ_T Γ d1) (τ_T Γ d2);

// Translation of interval terms and equalities
symbol τ_I (Γ : TContext) [i : ITerm] : der_I (τ_Γ Γ) i → ctt.tI;
symbol τ_eq_I (Γ : TContext) [i j : ITerm] (d : der_eq_I (τ_Γ Γ) i j) :
  ctt.xtEq (τ_I Γ (inv_eq_I_t1 (τ_dΓ Γ) d))
           (τ_I Γ (inv_eq_I_t2 (τ_dΓ Γ) d));

// Translation of face terms and equalities
symbol τ_F (Γ : TContext) [i : FTerm] : der_F (τ_Γ Γ) i → ctt.tF;
symbol τ_eq_F (Γ : TContext) [i j : FTerm] (d : der_eq_F (τ_Γ Γ) i j) :
  ctt.xtEq (τ_F Γ (inv_eq_F_t1 (τ_dΓ Γ) d))
           (τ_F Γ (inv_eq_F_t2 (τ_dΓ Γ) d));

// Translation of isOne derivations
symbol τ_isOne (Γ : TContext) [f : FTerm] (d : der_isOne (τ_Γ Γ) f) : ctt.tisOne (τ_F Γ (inv_isOne (τ_dΓ Γ) d));

// Conversion of translations TODO move this ?
symbol convert_T (Γ : TContext) [T : Term] [l : Lev] (d1 d2 : der (τ_Γ Γ) T (tuniv l) (lsuc l)) :
  ctt.tconvtype (τ_T Γ d1) (τ_T Γ d2);
symbol convertR (Γ : TContext) (h : PContext Γ) [l : Lev] [t T1 T2 : Term]
                (d1 : der (τ_Γ (projΓ1 h)) t T1 l)
                (d2 : der (τ_Γ (projΓ2 h)) t T2 l) :
  let ds1 ≔ inv_type (τ_dΓ (projΓ1 h)) d1 in
  let ds2 ≔ inv_type (τ_dΓ (projΓ2 h)) d2 in
  tHconv (τ_lev l) (τ_T (projΓ1 h) ds1) (τ_T (projΓ2 h) ds2) (τ (projΓ1 h) d1) (τ (projΓ2 h) d2);
symbol convert (Γ : TContext) [l : Lev] [t T : Term] (d1 d2 : der (τ_Γ Γ) t T l) :
  let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
  let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
  tHconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);

// Translation of types is the same as the one for terms
rule τ_T $Γ $d ↪ τ $Γ $d;
rule τ_eqT $Γ $d ↪ heq_to_eq (τ_eq $Γ $d);

// TODO move this to variables part
constant symbol Empty : Context;
constant symbol Push : Term → Lev → Context → Context;
// Translation context constructors
constant symbol TEmpty : TContext;
constant symbol TPush
  (Γ : TContext) (l : Lev) (A : Term) (dA : der (τ_Γ Γ) A (tuniv l) (lsuc l))
  : ctt.eps (τ_T Γ dA) → TContext;

// Translation of context
rule τ_Γ TEmpty ↪ Empty
with τ_Γ (TPush $t $s $A _ _) ↪ Push $A $s (τ_Γ $t);
