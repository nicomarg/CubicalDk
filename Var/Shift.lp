require open ctt.DeBruijn;

// Increments the second argument if it is (not strictly) greater than the
// first, otherwise is the identity
symbol dbshift : DBId → DBId → DBId;

rule dbshift (dbsucc $i) (dbsucc $j) ↪ dbsucc (dbshift $i $j)
with dbshift db0 $d ↪ dbsucc $d
with dbshift (dbsucc _) db0 ↪ db0;

// Increases all free variable by one, assuming all the variable strictly lower
// than the first argument to be bound
symbol shift : DBId → Term → Term;
symbol tshift : DBId → Typ → Typ;

// Top-level shift
symbol Shift : Term → Term ≔ shift db0;
symbol TShift : Typ → Typ ≔ tshift db0;
symbol Shift1 : Term → Term ≔ shift db1;
symbol TShift1 : Typ → Typ ≔ tshift db1;
// Iterated shifts
symbol Shift* : DBId → Term → Term;
symbol TShift* : DBId → Typ → Typ;
symbol ShiftN : DBId → Term → Term;
symbol TShiftN : DBId → Typ → Typ;

rule Shift* db0 $t ↪ $t
with Shift* (dbsucc $n) $t ↪ Shift (Shift* $n $t)
with TShift* db0 $t ↪ $t
with TShift* (dbsucc $n) $t ↪ TShift (TShift* $n $t)
with ShiftN $i $t ↪ Shift (Shift* $i $t)
with TShiftN $i $t ↪ TShift (TShift* $i $t);

require open ctt.Var.Context;
// Shifts the term t valid in context (getΓ id Γ) to context Γ
symbol shiftΓ (Γ : Context) (id : DBId) (t : Term) : Term;
rule shiftΓ (Push _ _ _) db0 $t ↪ Shift $t
with shiftΓ (Push _ _ $Γ) (dbsucc $i) $t ↪ Shift (shiftΓ $Γ $i $t);
symbol tshiftΓ (Γ : Context) (id : DBId) (t : Typ) : Typ;
rule tshiftΓ (Push _ _ _) db0 $t ↪ TShift $t
with tshiftΓ (Push _ _ $Γ) (dbsucc $i) $t ↪ TShift (tshiftΓ $Γ $i $t);
// Universes aren't changed by shifting, useful for later
// Shifts the type (get Γ id) to a valid type in context Γ
symbol shiftgetΓ (Γ : Context) (id : DBId) : Typ;
// rule shiftgetΓ (Push $t _ _) db0 ↪ Shift $t
// with shiftgetΓ (Push _ _ $t) (dbsucc $i) ↪ Shift (shiftgetΓ $t $i)
// with shiftgetΓ (PushF _ $t) $i ↪ shiftgetΓ $t $i
// with shiftgetΓ (PushI $t) $i ↪ IShift (shiftgetΓ $t $i)
rule shiftgetΓ $Γ $id ↪ tshiftΓ $Γ $id (get $Γ $id);
