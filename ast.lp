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

constant symbol Term : TYPE;
constant symbol ITerm : TYPE;
constant symbol FTerm : TYPE;
// dependent λ-calculus
constant symbol tvar : DBId → Term;
constant symbol tuniv : Lev → Term;
constant symbol tpi :
          Term → // Domain
          Term → // Codomain
          Term;
constant symbol tabs :
          Term → // Domain
          // Term → // Codomain
          Term → // Body
          Term;
constant symbol tapp :
          // Term → // Domain
          // Term → // Codomain
          // Might need domain/codomain. was crucial for ETT → ITT, but not sure it's needed for cubical
          Term → // Function
          Term → // Argument
          Term;
// Integers
constant symbol tnat : Term;
constant symbol tzero : Term;
constant symbol tsuc : Term → Term;
constant symbol trec :
          Term → // Predicate
          Term → // zero case
          Term → // heredity
          Term → // Argument
          Term;
// Dependent pairs
constant symbol tsig :
          Term → // Type of the first element
          Term → // Type of the second element
          Term;
constant symbol tpair :
          // Term → // Type of the first element
          // Term → // Type of the second element
          Term → // First element
          Term → // Second element
          Term;
constant symbol tp1 :
          // Term → // Type of the first element
          // Term → // Type of the second element
          Term → // The pair
          Term;
constant symbol tp2 :
          // Term → // Type of the first element
          // Term → // Type of the second element
          Term → // The pair
          Term;
// Sum type
constant symbol tsum :
          Term → // First type
          Term → // Second type
          Term;
constant symbol tinjl :
          // Term → // First type
          // Term → // Second type
          Term → // Argument
          Term;
constant symbol tinjr :
          // Term → // First type
          // Term → // Second type
          Term → // Argument
          Term;
constant symbol tcase :
          Term → // First type
          Term → // Second type
          Term → // Predicate
          Term → // First case
          Term → // Second case
          Term → // Argument
          Term;
// Path types
constant symbol tpath :
          Term → // Codomain
          Term → // Start point
          Term → // End point
          Term;
constant symbol tlamP :
          // Term → // Codomain
          Term → // Body
          Term;
constant symbol tappP :
          // Term → // Codomain
          // Term → // Start point
          // Term → // End point
          Term → // path
          ITerm → // argument
          Term;
// Systems
constant symbol tsys :
          // Term → // Type
          FTerm → // First face
          FTerm → // Second face
          Term → // First subterm
          Term → // Second subterm
          Term;
constant symbol temptysys : Term;
// Primitive transport
constant symbol ttransp :
          Term → // Type
          FTerm → // Face
          Term → // Argument
          Term;
// Hcomp operation
constant symbol thcomp :
          Term → // Type
          FTerm → // Face
          Term → // Partial element
          Term → // Base
          Term;
// Glue types
constant symbol tgluety :
          FTerm → // Face
          Term → // Partial Type
          Term → // Partial equivalence
          Term → // Type
          Term;
constant symbol tglue :
          FTerm → // Face
          // Term → // Partial Type
          // Term → // Partial equivalence
          // Term → // Type
          Term → // Preimage
          Term → // Argument
          Term;
constant symbol tunglue :
          FTerm → // Face
          // Term → // Partial Type
          Term → // Partial equivalence
          // Term → // Type
          Term → // Argument
          Term;
// Interval terms
constant symbol it0 : ITerm;
constant symbol it1 : ITerm;
constant symbol itvar : DBId → ITerm;
constant symbol itsym : ITerm → ITerm;
constant symbol itmin : ITerm → ITerm → ITerm;
constant symbol itmax : ITerm → ITerm → ITerm;
// Face terms
constant symbol ft0 : FTerm;
constant symbol ft1 : FTerm;
constant symbol fteq0 : DBId → FTerm;
constant symbol fteq1 : DBId → FTerm;
constant symbol ftmin : FTerm → FTerm → FTerm;
constant symbol ftmax : FTerm → FTerm → FTerm;
