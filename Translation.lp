require open ctt.CTT.HEq;
require open ctt.CTT.IsOne;
require open ctt.Lemmas.Inversions;
require open ctt.Contexts.Definition;

// Translation, levels first (which is trivial)
symbol τ_lev : tLev → Lev;
rule τ_lev (tlsuc $l) ↪ lsuc (τ_lev $l);

// Translation context
constant symbol TContext : TYPE;
constant symbol PContext : TContext → TYPE;
symbol projΓ1 [Γ : TContext] : PContext Γ → TContext;
symbol projΓ2 [Γ : TContext] : PContext Γ → TContext;

symbol τ_Γ : TContext → Context;
symbol τ_dΓ (Γ : TContext) : der_context (τ_Γ Γ);

// The translation itself, terms and types first
symbol τ_T (Γ : TContext) [t : Term] [l : tLev] :
  der (τ_Γ Γ) t (tuniv l) (tlsuc l) → T (τ_lev l);
symbol τ (Γ : TContext) [l : tLev] [t T : Term] (d : der (τ_Γ Γ) t T l) :
  eps (τ_T Γ (inv_type (τ_dΓ Γ) d));

// For things to type, we need to know that the translation of a universe always is one
rule @τ_T _ (tuniv $s) (tlsuc $s) _ ↪ t (τ_lev $s);
rule @τ _ (tlsuc (tlsuc $s)) (tuniv $s) (tuniv (tlsuc $s)) _ ↪ t (τ_lev $s);

symbol τ_inv (Γ : TContext) [l : tLev] [t A : Term] :
  der (τ_Γ Γ) t A l → T (τ_lev l) ≔ λ d, τ Γ (inv_type (τ_dΓ Γ) d);

// Translation of equality derivation
symbol τ_eq_type (Γ : TContext) [l : tLev] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : xT ≔
  let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
  let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
  let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
  let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
  Hconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);
symbol τ_eq (Γ : TContext) [l : tLev] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : xeps (τ_eq_type Γ d);
symbol τ_eqT (Γ : TContext) [l : tLev] [T1 T2 : Term] (d : der_eq (τ_Γ Γ) T1 T2 (tuniv l) (tlsuc l)) :
  let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
  let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
  tconvtype (τ_T Γ d1) (τ_T Γ d2);

// Translation of interval terms and equalities
symbol τ_I (Γ : TContext) [i : ITerm] : der_I (τ_Γ Γ) i → tI;
symbol τ_eq_I (Γ : TContext) [i j : ITerm] (d : der_eq_I (τ_Γ Γ) i j) :
  xtEq (τ_I Γ (inv_eq_I_t1 (τ_dΓ Γ) d))
           (τ_I Γ (inv_eq_I_t2 (τ_dΓ Γ) d));

// Translation of face terms and equalities
symbol τ_F (Γ : TContext) [i : FTerm] : der_F (τ_Γ Γ) i → tF;
symbol τ_eq_F (Γ : TContext) [i j : FTerm] (d : der_eq_F (τ_Γ Γ) i j) :
  xtEq (τ_F Γ (inv_eq_F_t1 (τ_dΓ Γ) d))
           (τ_F Γ (inv_eq_F_t2 (τ_dΓ Γ) d));

// Translation of isOne derivations
symbol τ_isOne (Γ : TContext) [f : FTerm] (d : der_isOne (τ_Γ Γ) f) : tisOne (τ_F Γ (inv_isOne (τ_dΓ Γ) d));

// Conversion of translations TODO move this ?
symbol convert_T (Γ : TContext) [A : Term] [l : tLev] (d1 d2 : der (τ_Γ Γ) A (tuniv l) (tlsuc l)) :
  tconvtype (τ_T Γ d1) (τ_T Γ d2);
symbol convertR (Γ : TContext) (h : PContext Γ) [l : tLev] [t T1 T2 : Term]
                (d1 : der (τ_Γ (projΓ1 h)) t T1 l)
                (d2 : der (τ_Γ (projΓ2 h)) t T2 l) :
  let ds1 ≔ inv_type (τ_dΓ (projΓ1 h)) d1 in
  let ds2 ≔ inv_type (τ_dΓ (projΓ2 h)) d2 in
  tHconv (τ_lev l) (τ_T (projΓ1 h) ds1) (τ_T (projΓ2 h) ds2) (τ (projΓ1 h) d1) (τ (projΓ2 h) d2);
symbol convert (Γ : TContext) [l : tLev] [t T : Term] (d1 d2 : der (τ_Γ Γ) t T l) :
  let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
  let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
  tHconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);

// Translation of types is the same as the one for terms
rule τ_T $Γ $d ↪ τ $Γ $d;
rule τ_eqT $Γ $d ↪ heq_to_eq (τ_eq $Γ $d);

// Translation context constructors
constant symbol TEmpty : TContext;
constant symbol TPush
  (Γ : TContext) (l : tLev) (A : Term) (dA : der (τ_Γ Γ) A (tuniv l) (tlsuc l))
  : eps (τ_T Γ dA) → TContext;
constant symbol TPushI (Γ : TContext) : tI → TContext;
constant symbol TPushF (Γ : TContext) (f : FTerm) (df : der_F (τ_Γ Γ) f) : tisOne (τ_F Γ df) → TContext;

// Translation of context
rule τ_Γ TEmpty ↪ Empty
with τ_Γ (TPush $t $s $A _ _) ↪ Push $A $s (τ_Γ $t)
with τ_Γ (TPushI $t _) ↪ PushI (τ_Γ $t)
with τ_Γ (TPushF $t $f _ _) ↪ PushF $f (τ_Γ $t);
