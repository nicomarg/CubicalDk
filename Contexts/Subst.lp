require open ctt.Contexts.DeBruijn;

// Select a term depending on whether two indices are equal, the first one is greater, or lower
symbol dbselect : DBId → DBId → Term → Term → Term → Term;
rule dbselect db0 db0 $eq _ _ ↪ $eq
with dbselect (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪ dbselect $i $j $eq $gt $lt
with dbselect db0 (dbsucc _) _ _ $lt ↪ $lt
with dbselect (dbsucc _) db0 _ $gt _ ↪ $gt;

// Substitution (and shift down everything above the substituted index)
// When substituting by a Term, interfal and face terms can't be affected
// However, interval variables can appear in the substituted term and thus need to be shifted
symbol subst : DBId → Term → Term → Term;

symbol apply1 (t u : Term) : Term ≔ subst db0 u t;

symbol dbselectI : DBId → DBId → ITerm → ITerm → ITerm → ITerm;
rule dbselectI db0 db0 $eq _ _ ↪ $eq
with dbselectI (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪ dbselectI $i $j $eq $gt $lt
with dbselectI db0 (dbsucc _) _ _ $lt ↪ $lt
with dbselectI (dbsucc _) db0 _ $gt _ ↪ $gt;

symbol dbselectF : DBId → DBId → FTerm → FTerm → FTerm → FTerm;
rule dbselectF db0 db0 $eq _ _ ↪ $eq
with dbselectF (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪ dbselectF $i $j $eq $gt $lt
with dbselectF db0 (dbsucc _) _ _ $lt ↪ $lt
with dbselectF (dbsucc _) db0 _ $gt _ ↪ $gt;

// Substitution of an interval variable
symbol IsubstI : DBId → ITerm → ITerm → ITerm;

// The computation of the face formula equivalent to having substituted a term for the variable
// in an fteq0 or fteq1
symbol substeq0 : ITerm → FTerm;
symbol substeq1 : ITerm → FTerm;

symbol IsubstF : DBId → ITerm → FTerm → FTerm;
symbol Isubst : DBId → ITerm → Term → Term;

symbol applyI1 (u : Term) (t : ITerm) ≔ Isubst db0 t u;
