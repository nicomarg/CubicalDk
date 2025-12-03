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
  * tau_I
* der_eq_I
  * inv_eq_I_t1
  * inv_eq_I_t2
* der_F
* der_eq_F
  * inv_eq_F_t1
  * inv_eq_F_t2
* der_isOne
  * inv_isOne
