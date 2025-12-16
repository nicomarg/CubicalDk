# File structure

## TODOs

- Be clear about which lemma is needed for which feature
- Replace tH being injective by the proper unif_rule on transport
- Remove the need for universes to define well-formedness of types
- Make translation not depend on a specific typing derivation of the considered term

## New stuff
* Symbols (definition of syntax and typing types)
* Contexts (Notions of variables)
  * DeBruijn (DeBruijn indices algebra)
  * Definition (define contexts)
  * Typing (valid contexts derivations)
  * Shift (def of shifting operation)
  * Subst (def of substitution operation)
* Lemmas (definition of lemmas and generic wrappers)
  * TermEquality (definition of term equality notions)
  * Commutations (commutation of shifts/substs)
  * Translation (translation properties)
  * Derivations
    - Lemmas about derivations, exported variants
    * Shifting (Lemmas about shifting derivations)
* Translation
  - defines translation (and Heq and inversion lemmas, TODO move them)
  * Context (translation context constructors and accessors)
  * Conversion (conversion of translation of != derivations)
* Constructions
  - Univ
  - Var
  * Syntax (includes term formers and typing rules)
  * Subst (definition of shifting and substitution for that type former)
  * Proofs (proofs of cases relevant to this construction)
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

* Inversions
  * der_eqT : inv_eqT_t1 & t2
  * der : inv_type
  * der_eq : inv_eq_type t1 & t2
  * der_eq_I : inv_eq_I_t1 & t2
  * der_eq_F : inv_eq_F_t1 & t2
  * der_isOne : inv_isOne
* Translation
  * der_type : tau
  * der_eqT : t1 t2 tau
  * der : type t1 t2 tau
  * der_eq : type (s?) t1 t2 tau
  * der_I : tau
  * der_eq_I : t1 t2 tau
  * der_F : tau
  * der_eq_F : t1 t2 tau
  * der_isOne : t
* Translation/Irrel
  * der_type : tau_T_irrel
  * der_eqT : tau_eqT_t1 t2 compat
  * der : tau_type_compat tau_irrel
  * der_eq : tau_eq_type t1 t2 compat
  * der_I : tau_I_irrel
  * der_eq_I : tau_eq_I_t1 t2 compat
  * der_F : tau_F_irrel
  * der_eq_F : tau_eq_F_t1 t2 compat
  * der_isOne : tau_isOne_t_compat

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
