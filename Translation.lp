require open ctt.CTT.HEq;
require open ctt.CTT.IsOne;
require open ctt.Lemmas.Inversions;
// require open ctt.Contexts.Definition;

// Translation, levels first (which is trivial)
symbol τ_lev : Sort → Lev;
rule τ_lev (tlsuc $l) ↪ lsuc (τ_lev $l);

// Translation context
constant symbol TContext : TYPE;

symbol τ_Γ : TContext → Context;
symbol τ_dΓ (Γ : TContext) : der_context (τ_Γ Γ);

// The translation itself, terms and types first
symbol τ_T (Γ : TContext) [t : Typ] [l : Sort] :
  der_type (τ_Γ Γ) t l → T (τ_lev l);

// Following translations will need to define their return type as well. Indeed, when translating Γ ⊢ t ≡ u
// we need to create an equality between translations of t and u. Some approaches extracted derivations for t and u
// from the conversion derivation and applied term translation to those, however the termination of such a process is unclear.
// Thus, we will instead explicitly provide the terms we need to prove equal, and prove with an irrelevance lemma that they are
// indeed translations of any derivation of t and u
symbol τ_eqT_t1 (Γ : TContext) [t u : Typ] [l : Sort] :
  der_eqT (τ_Γ Γ) t u l → T (τ_lev l);
symbol τ_eqT_t2 (Γ : TContext) [t u : Typ] [l : Sort] :
  der_eqT (τ_Γ Γ) t u l → T (τ_lev l);
symbol τ_eqT (Γ : TContext) [t u : Typ] [l : Sort] (d : der_eqT (τ_Γ Γ) t u l) :
  tconvtype (τ_eqT_t1 Γ d) (τ_eqT_t2 Γ d);

symbol τ_type (Γ : TContext) [t : Term] [A : Typ] [l : Sort] :
  der (τ_Γ Γ) t A l → T (τ_lev l);
symbol τ (Γ : TContext) [t : Term] [A : Typ] [l : Sort] (d : der (τ_Γ Γ) t A l) :
  eps (τ_type Γ d);

// TODO one type for both sides or directly the heterogeneous one ?
symbol τ_eq_type (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  T (τ_lev l);
symbol τ_eq_t1 (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  eps (τ_eq_type Γ d);
symbol τ_eq_t2 (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  eps (τ_eq_type Γ d);
symbol τ_eq (Γ : TContext) [t u : Term] [A : Typ] [l : Sort] (d : der_eq (τ_Γ Γ) t u A l) :
  tconv (τ_eq_t1 Γ d) (τ_eq_t2 Γ d);

// For things to type, we need to know that the translation of a universe always is one
// rule @τ_T _ (tuniv $s) (tlsuc $s) _ ↪ t (τ_lev $s);
// rule @τ _ (tlsuc (tlsuc $s)) (tuniv $s) (tuniv (tlsuc $s)) _ ↪ t (τ_lev $s);

// symbol τ_inv (Γ : TContext) [l : Sort] [t A : Term] :
//   der (τ_Γ Γ) t A l → T (τ_lev l) ≔ λ d, τ Γ (inv_type (τ_dΓ Γ) d);

// Translation of equality derivation
// symbol τ_eq_type (Γ : TContext) [l : Sort] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : xT ≔
//   let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
//   let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
//   let ds1 ≔ inv_type (τ_dΓ Γ) d1 in
//   let ds2 ≔ inv_type (τ_dΓ Γ) d2 in
//   Hconv (τ_lev l) (τ_T Γ ds1) (τ_T Γ ds2) (τ Γ d1) (τ Γ d2);
// symbol τ_eq (Γ : TContext) [l : Sort] [T t1 t2 : Term] (d : der_eq (τ_Γ Γ) t1 t2 T l) : xeps (τ_eq_type Γ d);
// symbol τ_eqT (Γ : TContext) [l : Sort] [T1 T2 : Term] (d : der_eq (τ_Γ Γ) T1 T2 (tuniv l) (tlsuc l)) :
//   let d1 ≔ inv_eq_t1 (τ_dΓ Γ) d in
//   let d2 ≔ inv_eq_t2 (τ_dΓ Γ) d in
//   tconvtype (τ_T Γ d1) (τ_T Γ d2);

// Translation of interval terms and equalities
symbol τ_I (Γ : TContext) [i : ITerm] : der_I (τ_Γ Γ) i → tI;

symbol τ_eq_I_t1 (Γ : TContext) [i j : ITerm] (d : der_eq_I (τ_Γ Γ) i j) : tI;
symbol τ_eq_I_t2 (Γ : TContext) [i j : ITerm] (d : der_eq_I (τ_Γ Γ) i j) : tI;
symbol τ_eq_I (Γ : TContext) [i j : ITerm] (d : der_eq_I (τ_Γ Γ) i j) :
  xtEq (τ_eq_I_t1 Γ d) (τ_eq_I_t2 Γ d);

// Translation of face terms and equalities
symbol τ_F (Γ : TContext) [i : FTerm] : der_F (τ_Γ Γ) i → tF;
symbol τ_eq_F_t1 (Γ : TContext) [i j : FTerm] (d : der_eq_F (τ_Γ Γ) i j) : tF;
symbol τ_eq_F_t2 (Γ : TContext) [i j : FTerm] (d : der_eq_F (τ_Γ Γ) i j) : tF;
symbol τ_eq_F (Γ : TContext) [i j : FTerm] (d : der_eq_F (τ_Γ Γ) i j) :
  xtEq (τ_eq_F_t1 Γ d) (τ_eq_F_t2 Γ d);

// Translation of isOne derivations
symbol τ_isOne_t (Γ : TContext) [f : FTerm] (d : der_isOne (τ_Γ Γ) f) : tF;
symbol τ_isOne (Γ : TContext) [f : FTerm] (d : der_isOne (τ_Γ Γ) f) : tisOne (τ_isOne_t Γ d);

// Translation of types is the same as the one for terms
// rule τ_T $Γ $d ↪ τ $Γ $d;
// rule τ_eqT $Γ $d ↪ heq_to_eq (τ_eq $Γ $d);
