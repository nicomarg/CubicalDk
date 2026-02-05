# File structure

## TODOs

- Be clear about which lemma is needed for which feature
- Replace tH being injective by the proper unif_rule on transport
- Remove the need for universes to define well-formedness of types
- Make translation not depend on a specific typing derivation of the considered term

## New stuff
* Symbols (definition of syntax and typing types)
* DeBruijn (DeBruijn indices algebra)
* Contexts (Notions of variables) (will be moved)
  * Definition (define contexts)
  * Typing (valid contexts derivations)
  * Shift (def of shifting operation)
  * Subst (def of substitution operation)
* Lemmas (definition of lemmas and generic wrappers)
  * TermEquality (definition of term equality notions)
  * Commutations (commutation of shifts/substs)
  * Translation (translation properties)
  * Inversions (inversion lemmas for derivations)
  * Irrel (irrelevance of translation)
  * Derivations
    - Lemmas about derivations, exported variants
    * Shifting (Lemmas about shifting derivations)
* Translation
  - defines translation (and Heq and inversion lemmas, TODO move them)
  * Context (translation context constructors and accessors)
  * Conversion (conversion of translation of != derivations)
* Var/IVar/FVar (extension of contexts and syntax)
  * Context (context extension with derivation)
  * LContext (lemma contexts extension)
  * TContext (translation context extension)
* Var/IVar
  * Shift
  * Subst
* Constructions
  - Structural (conversion rule and equality equivalence rules)
  - Univ
  - Var
  - IVar
  * Syntax (includes term formers and typing rules)
  * Subst (or Subst_def for variable constructions) (definition of shifting and substitution for that type former)
  * Proofs (proofs of lemma cases relevant to this construction)
  * Translation (proof of translation and its associated lemmas for this construction)
* Main (place for testing stuff)
* All (TODO, imports everything)
* ctt (target model of ctt in 2LTTs)
  * Internal (MLTT part of cubical type theory)
  * External (external 1 universe layer along with a few datatypes)
  * 2LTT (external view on internal, along with conversion macros)
  * Interval
  * Faces 
  * IsOne
  * Paths
  * Derived (some computed stuff)
  * TODO glue
  * Composition (partial elements, syntax and computation due to protected symbols limitations)
  * HEq (Definition of heterogeneous equality and lemmas about it)

## Old stuff
* ast S
* DeBruijn S
* Typing S
* TermEquality S
* Lemmas (file) S
* Inversions S
* DerivationShifting S
* DerivationSubstitution
* ContextCongruence
* derived
* ctt.dk X

## Temp stuff
* tests
* ctt2.dk

# Lemmas to prove/define for each type

For derivations, sorted first by the file the lemma is defined in
* Lemmas/Derivations
  * der_type : der_type_shift_n
  * der_eqT : der_eqT_shift_n
  * der : der_shift_n
  * der_eq : der_eq_shift_n
* Lemmas/Inversions
  * der_eqT : inv_eqT_t1 & t2
  * der : inv_type
  * der_eq : inv_eq_type t1 & t2
  * der_eq_I : inv_eq_I_t1 & t2
  * der_eq_F : inv_eq_F_t1 & t2
  * der_isOne : inv_isOne
* Translation
  * der_type : tau
  * der_eqT : t1 t2 tau
  * der : type tau
  * der_eq : type1/2 t1 t2 tau
  * der_I : tau
  * der_eq_I : t1 t2 tau
  * der_F : tau
  * der_eq_F : t1 t2 tau
  * der_isOne : t
* Lemmas/Irrel
  * der_type : tau_T_irrel_rec
  * der_eqT : tau_eqT_t1 t2 compat
  * der : tau_type_compat tau_irrel_rec
  * der_eq : tau_eq_type1/2 t1 t2 compat
* Lemmas/Translation
  * der_type : der_shiftT_n
  * der : der_shift_n

For contexts, sorted by context type
* Context
  * get getS getGamma len
* TContext
  * tau_Gamma
  * tau_dGamma
  * tgetS tgetA tgetD tgetGamma
  * tget tgetShift
* PContext
  * projGamma1 / 2
  * pgetH pgetHShift
* der_context
 * der_getGamma der_subGamma

For Terms
* Typ
  * tshift
  * Itshift
  * tsubst
  * Itsubst
  * TyEq congruences
  * swap_tshift_tshift
* Term
  * shift
  * Ishift
  * subst
  * Isubst
  * TEq congruences
  * swap_shift_shift
  * swap_shift_Ishift
* ITerm
  * IshiftI
  * IsubstI
  * substeq0
  * substeq1
  * ITEq congruences
* FTerm
  * IshiftF
  * IsubstF
  * FTEq congruences
* all_der
  * shift_n
  * (Ishift_n)
  * (weakF)
  * tau
* der_type
* der_eqT
  * inv_eqT_t1
  * inv_eqT_t2
* der
  * inv_type
  * tau_shift0T_eq
  * (tau_Ishift0T_eq)
  * (tau_Fshift0T_eq)
* der_eq
  * inv_eq_type
  * inv_eq_t1
  * inv_eq_t2
* der_I
* der_eq_I
  * inv_eq_I_t1
  * inv_eq_I_t2
* der_F
* der_eq_F
  * inv_eq_F_t1
  * inv_eq_F_t2
* der_isOne
  * inv_isOne
