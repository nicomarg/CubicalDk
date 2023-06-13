require ctt.ctt as ctt;

symbol Prop : TYPE ≔ ctt.xT;
builtin "Prop" ≔ Prop;
symbol π ≔ ctt.xeps;
builtin "P" ≔ π;

symbol Lev : TYPE;
constant symbol lzero : Lev;
constant symbol lsuc : Lev → Lev;
symbol lmax : Lev → Lev → Lev;
rule lmax lzero $n ↪ $n
with lmax $n lzero ↪ $n
with lmax (lsuc $n) (lsuc $m) ↪ lsuc (lmax $n $m)
with lmax $s $s ↪ $s;
constant symbol DBId : TYPE;

inductive Term : TYPE ≔
// dependent λ-calculus
| tvar : DBId → Term
| tpi : Term → // Domain
         Term → // Codomain
         Term
| tabs : Term → // Domain
         // Term → // Codomain
         Term → // Body
         Term
| tapp : // Term → // Domain
         // Term → // Codomain
         // Might need domain/codomain. was crucial for ETT → ITT, but not sure it's needed for cubical
         Term → // Function
         Term → // Argument
         Term
| tuniv : Lev → Term
// Integers
| tnat : Term
| tzero : Term
| tsuc : Term → Term
| trec : Term → // Predicate
         Term → // zero case
         Term → // heredity
         Term → // Argument
         Term
// Dependent pairs
| tsig : Term → // Type of the first element
         Term → // Type of the second element
         Term
| tpair : // Term → // Type of the first element
          // Term → // Type of the second element
          Term → // First element
          Term → // Second element
          Term
| tp1 : // Term → // Type of the first element
        // Term → // Type of the second element
        Term → // The pair
        Term
| tp2 : // Term → // Type of the first element
        // Term → // Type of the second element
        Term → // The pair
        Term
// Sum type
| tsum : Term → // First type
         Term → // Second type
         Term
| tinjl : // Term → // First type
          // Term → // Second type
          Term → // Argument
          Term
| tinjr : // Term → // First type
          // Term → // Second type
          Term → // Argument
          Term
| tcase : Term → // First type
          Term → // Second type
          Term → // Predicate
          Term → // First case
          Term → // Second case
          Term → // Argument
          Term
// Path types
| tpath : Term → // Codomain
          Term → // Start point
          Term → // End point
          Term
| tlamP : // Term → // Codomain
          Term → // Body
          Term
| tappP : // Term → // Codomain
          // Term → // Start point
          // Term → // End point
          Term → // path
          ITerm → // argument
          Term
// Systems
| tsys : // Term → // Type
         FTerm → // First face
         FTerm → // Second face
         Term → // First subterm
         Term → // Second subterm
         Term
| temptysys : Term
// Primitive transport
| ttransp : Term → // Type
            FTerm → // Face
            Term → // Argument
            Term
// Hcomp operation
| thcomp : Term → // Type
           FTerm → // Face
           Term → // Partial element
           Term → // Base
           Term
// Glue types
| tgluety : FTerm → // Face
            Term → // Partial Type
            Term → // Partial equivalence
            Term → // Type
            Term
| tglue : FTerm → // Face
          // Term → // Partial Type
          // Term → // Partial equivalence
          // Term → // Type
          Term → // Preimage
          Term → // Argument
          Term
| tunglue : FTerm → // Face
            // Term → // Partial Type
            Term → // Partial equivalence
            // Term → // Type
            Term → // Argument
            Term
with ITerm : TYPE ≔
| it0 : ITerm
| it1 : ITerm
| itvar : DBId → ITerm
| itsym : ITerm → ITerm
| itmin : ITerm → ITerm → ITerm
| itmax : ITerm → ITerm → ITerm
with FTerm : TYPE ≔
| ft0 : FTerm
| ft1 : FTerm
| fteq0 : DBId → FTerm
| fteq1 : DBId → FTerm
| ftmin : FTerm → FTerm → FTerm
| ftmax : FTerm → FTerm → FTerm
;
