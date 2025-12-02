require open ctt.Contexts.Definition;

// Increments the second argument if it is (not strictly) greater than the
// first, otherwise is the identity
symbol dbshift : DBId → DBId → DBId;

rule dbshift (dbsucc $i) (dbsucc $j) ↪ dbsucc (dbshift $i $j)
with dbshift db0 $d ↪ dbsucc $d
with dbshift (dbsucc _) db0 ↪ db0;

// Increases all free variable by one, assuming all the variable strictly lower
// than the first argument to be bound
symbol shift : DBId → Term → Term;

// Top-level shift
symbol Shift : Term → Term ≔ shift db0;
symbol Shift1 : Term → Term ≔ shift db1;
// Iterated shifts
symbol Shift* : DBId → Term → Term;
symbol ShiftN : DBId → Term → Term;

rule Shift* db0 $t ↪ $t
with Shift* (dbsucc $n) $t ↪ Shift (Shift* $n $t)
with ShiftN $i $t ↪ Shift (Shift* $i $t);

// Interval variables will use disjoint DeBruijn indices, and will thus need their own shift and substitution.
// As the work is obvious on terms once these functions have been defined on interval terms, the
// versions for these kind of terms will be obtained by lifting the definition on the interval.

// Interval variables shift
symbol IshiftI : DBId → ITerm → ITerm;
symbol IshiftF : DBId → FTerm → FTerm;
// Top-level interval variables shift
symbol IShiftI : ITerm → ITerm ≔ IshiftI db0;
symbol IShiftF : FTerm → FTerm ≔ IshiftF db0;
symbol IShiftI1 : ITerm → ITerm ≔ IshiftI db1;
symbol IShiftF1 : FTerm → FTerm ≔ IshiftF db1;
// Iterated shifts
symbol IShiftI* : DBId → ITerm → ITerm;
symbol IShiftF* : DBId → FTerm → FTerm;
symbol IShiftIN : DBId → ITerm → ITerm;
symbol IShiftFN : DBId → FTerm → FTerm;

rule IShiftI* db0 $t ↪ $t
with IShiftI* (dbsucc $n) $t ↪ IShiftI (IShiftI* $n $t)
with IShiftIN $i $t ↪ IShiftI (IShiftI* $i $t)
with IShiftF* db0 $t ↪ $t
with IShiftF* (dbsucc $n) $t ↪ IShiftF (IShiftF* $n $t)
with IShiftFN $i $t ↪ IShiftF (IShiftF* $i $t);

symbol Ishift : DBId → Term → Term;
symbol IShift : Term → Term ≔ Ishift db0;
symbol IShift1 : Term → Term ≔ Ishift db1;
symbol IShift* : DBId → Term → Term;
symbol IShiftN : DBId → Term → Term;
rule IShift* db0 $t ↪ $t
with IShift* (dbsucc $n) $t ↪ IShift (IShift* $n $t)
with IShiftN $i $t ↪ IShift (IShift* $i $t);

// Shifts the term t valid in context (getΓ id Γ) to context Γ
symbol shiftΓ (Γ : Context) (id : DBId) (t : Term) : Term;
rule shiftΓ (Push _ _ _) db0 $t ↪ Shift $t
with shiftΓ (Push _ _ $Γ) (dbsucc $i) $t ↪ Shift (shiftΓ $Γ $i $t)
with shiftΓ (PushF _ $Γ) $i $t ↪ shiftΓ $Γ $i $t
with shiftΓ (PushI $Γ) $i $t ↪ IShift (shiftΓ $Γ $i $t);
// Universes aren't changed by shifting, useful for later
// Shifts the type (get Γ id) to a valid type in context Γ
symbol shiftgetΓ (Γ : Context) (id : DBId) : Term;
// rule shiftgetΓ (Push $t _ _) db0 ↪ Shift $t
// with shiftgetΓ (Push _ _ $t) (dbsucc $i) ↪ Shift (shiftgetΓ $t $i)
// with shiftgetΓ (PushF _ $t) $i ↪ shiftgetΓ $t $i
// with shiftgetΓ (PushI $t) $i ↪ IShift (shiftgetΓ $t $i)
rule shiftgetΓ $Γ $id ↪ shiftΓ $Γ $id (get $Γ $id);
