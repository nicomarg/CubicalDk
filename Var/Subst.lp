require open ctt.DeBruijn;

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

symbol tsubst : DBId → Term → Typ → Typ;

symbol Tapply1 (t : Typ) (u : Term) : Typ ≔ tsubst db0 u t;
