
require open  ctt.ast;

// De Bruijn indices
constant symbol db0 : DBId;
constant symbol dbsucc : DBId → DBId;
symbol db1 : DBId ≔ dbsucc db0;
symbol db2 : DBId ≔ dbsucc db1;

symbol dbadd : DBId → DBId → DBId;
rule dbadd db0 $id ↪ $id
with dbadd $id db0 ↪ $id
with dbadd (dbsucc $n) $m ↪ dbsucc (dbadd $n $m)
with dbadd $n (dbsucc $m) ↪ dbsucc (dbadd $n $m);

symbol dbprev : DBId → DBId;
rule dbprev (dbsucc $n) ↪ $n;

// Equality
constant symbol DBEq : DBId → DBId → TYPE;
constant symbol DBRefl (i : DBId) : DBEq i i;
symbol dbcong (f : DBId → DBId) [i j : DBId]
                  : DBEq i j → DBEq (f i) (f j);
rule dbcong $f (DBRefl $i) ↪ DBRefl ($f $i);

// Comparison
constant symbol DBLe : DBId → DBId → TYPE;
constant symbol DBLe_refl (i : DBId) : DBLe i i;
constant symbol DBLe_succ [i j : DBId] : DBLe i j → DBLe i (dbsucc j);

symbol dble_n_S [i j : DBId] : DBLe i j → DBLe (dbsucc i) (dbsucc j);
symbol dble_S_n [i j : DBId] : DBLe (dbsucc i) (dbsucc j) → DBLe i j;
symbol dble_Sn_n [i j : DBId] : DBLe (dbsucc i) j → DBLe i j;
symbol dble_n_Sn (i : DBId) : DBLe i (dbsucc i);
symbol dble_0_n (i : DBId) : DBLe db0 i;
rule dble_n_S (DBLe_refl $i) ↪ DBLe_refl (dbsucc $i)
with dble_n_S (DBLe_succ $h) ↪ DBLe_succ (dble_n_S $h)
with dble_n_Sn $i ↪ DBLe_succ (DBLe_refl $i)
with dble_Sn_n (DBLe_refl (dbsucc $i)) ↪ dble_n_Sn $i
with dble_Sn_n (DBLe_succ $h) ↪ DBLe_succ (dble_Sn_n $h)
with dble_S_n (DBLe_refl (dbsucc $i)) ↪ DBLe_refl $i
with dble_S_n (DBLe_succ $h) ↪ dble_Sn_n $h
with dble_0_n db0 ↪ DBLe_refl db0
with dble_0_n (dbsucc $i) ↪ DBLe_succ (dble_0_n $i);

// Increments the second argument if it is (not strictly) greater than the
// first, otherwise is the identity
symbol dbshift : DBId → DBId → DBId;

rule dbshift (dbsucc $i) (dbsucc $j) ↪ dbsucc (dbshift $i $j)
with dbshift db0 $d ↪ dbsucc $d
with dbshift (dbsucc _) db0 ↪ db0;

// Increases all free variable by one, assuming all the variable strictly lower
// than the first argument to be bound
symbol shift : DBId → Term → Term;
// Computation rules for shifting on terms
rule shift $i (tvar $id) ↪ tvar (dbshift $i $id)
with shift _  (tuniv $s) ↪ tuniv $s
with shift $i (tpi $A $B) ↪ tpi (shift $i $A) (shift (dbsucc $i) $B)
with shift $i (tabs $A $t) ↪ tabs (shift $i $A) (shift (dbsucc $i) $t)
with shift $i (tapp $f $u) ↪ tapp (shift $i $f) (shift $i $u)
with shift _ tnat ↪ tnat
with shift _ tzero ↪ tzero
with shift $i (tsuc $n) ↪ tsuc (shift $i $n)
with shift $i (trec $P $z $H $n) ↪ trec (shift $i $P) (shift $i $z) (shift $i $H) (shift $i $n)
with shift $i (tsig $A $B) ↪ tsig (shift $i $A) (shift (dbsucc $i) $B)
with shift $i (tpair $u $v) ↪ tpair (shift $i $u) (shift $i $v)
with shift $i (tp1 $p) ↪ tp1 (shift $i $p)
with shift $i (tp2 $p) ↪ tp2 (shift $i $p)
with shift $i (tsum $A $B) ↪ tsum (shift $i $A) (shift $i $B)
with shift $i (tinjl $a) ↪ tinjl (shift $i $a)
with shift $i (tinjr $b) ↪ tinjr (shift $i $b)
with shift $i (tcase $A $B $P $a $b $x) ↪ tcase (shift $i $A) (shift $i $B) (shift $i $P) (shift $i $a)
                                                (shift $i $b) (shift $i $x)
with shift $i (tpath $A $x $y) ↪ tpath (shift $i $A) (shift $i $x) (shift $i $y)
with shift $i (tlamP $t) ↪ tlamP (shift $i $t)
with shift $i (tappP $t $j) ↪ tappP (shift $i $t) $j
with shift $i (tsys $f $g $u $v) ↪ tsys $f $g (shift $i $u) (shift $i $v)
with shift _ temptysys ↪ temptysys
with shift $i (ttransp $A $f $a) ↪ ttransp (shift $i $A) $f (shift $i $a)
with shift $i (thcomp $A $f $u $u0) ↪ thcomp (shift $i $A) $f (shift $i $u) (shift $i $u0)
with shift $i (tgluety $f $T $w $A) ↪ tgluety $f (shift $i $T) (shift $i $w) (shift $i $A)
with shift $i (tglue $f $t $a) ↪ tglue $f (shift $i $t) (shift $i $a)
with shift $i (tunglue $f $w $b) ↪ tunglue $f (shift $i $w) (shift $i $b);

// Top-level shift
symbol Shift : Term → Term ≔ shift db0;
symbol Shift1 : Term → Term ≔ shift db1;
// Iterated shifts
symbol Shift* : DBId → Term → Term;
symbol ShiftN : DBId → Term → Term;

rule Shift* db0 $t ↪ $t
with Shift* (dbsucc $n) $t ↪ Shift (Shift* $n $t)
with Shift* _ (tuniv $s) ↪ tuniv $s
with ShiftN $i $t ↪ Shift (Shift* $i $t);

// Interval variables will use disjoint DeBruijn indices, and will thus need their own shift and substitution.
// As the work is obvious on terms once these functions have been defined on interval terms, the
// versions for these kind of terms will be obtained by lifting the definition on the interval.

// Interval variables shift
symbol IshiftI : DBId → ITerm → ITerm;
rule IshiftI _ it0 ↪ it0
with IshiftI _ it1 ↪ it1
with IshiftI $i (itvar $id) ↪ itvar (dbshift $i $id)
with IshiftI $i (itsym $j) ↪ itsym (IshiftI $i $j)
with IshiftI $i (itmin $a $b) ↪ itmin (IshiftI $i $a) (IshiftI $i $b)
with IshiftI $i (itmax $a $b) ↪ itmax (IshiftI $i $a) (IshiftI $i $b);
symbol IshiftF : DBId → FTerm → FTerm;
rule IshiftF _ ft0 ↪ ft0
with IshiftF _ ft1 ↪ ft1
with IshiftF $i (fteq0 $id) ↪ fteq0 (dbshift $i $id)
with IshiftF $i (fteq1 $id) ↪ fteq1 (dbshift $i $id)
with IshiftF $i (ftmin $a $b) ↪ ftmin (IshiftF $i $a) (IshiftF $i $b)
with IshiftF $i (ftmax $a $b) ↪ ftmax (IshiftF $i $a) (IshiftF $i $b);
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

// Wrapper for applying a function on interval variables inside a term
symbol wrap : (DBId → ITerm → ITerm → ITerm) → (DBId → ITerm → FTerm → FTerm) → DBId → ITerm → Term → Term;
rule wrap _ _ _ _ (tvar $id) ↪ (tvar $id)
with wrap _ _ _ _ (tuniv $id) ↪ tuniv $id
with wrap $f $g $i $T (tpi $A $B) ↪ tpi (wrap $f $g $i $T $A) (wrap $f $g $i $T $B)
with wrap $f $g $i $T (tabs $A $t) ↪ tabs (wrap $f $g $i $T $A) (wrap $f $g $i $T $t)
with wrap $f $g $i $T (tapp $u $v) ↪ tapp (wrap $f $g $i $T $u) (wrap $f $g $i $T $v)
with wrap _ _ _ _ tnat ↪ tnat
with wrap _ _ _ _ tzero ↪ tzero
with wrap $f $g $i $T (tsuc $n) ↪ tsuc (wrap $f $g $i $T $n)
with wrap $f $g $i $T (trec $P $z $H $n) ↪ trec (wrap $f $g $i $T $P) (wrap $f $g $i $T $z)
                                                (wrap $f $g $i $T $H) (wrap $f $g $i $T $n)
with wrap $f $g $i $T (tsig $A $B) ↪ tsig (wrap $f $g $i $T $A) (wrap $f $g $i $T $B)
with wrap $f $g $i $T (tpair $a $b) ↪ tpair (wrap $f $g $i $T $a) (wrap $f $g $i $T $b)
with wrap $f $g $i $T (tp1 $p) ↪ tp1 (wrap $f $g $i $T $p)
with wrap $f $g $i $T (tp2 $p) ↪ tp2 (wrap $f $g $i $T $p)
with wrap $f $g $i $T (tsum $A $B) ↪ tsum (wrap $f $g $i $T $A) (wrap $f $g $i $T $B)
with wrap $f $g $i $T (tinjl $a) ↪ tinjl (wrap $f $g $i $T $a)
with wrap $f $g $i $T (tinjr $b) ↪ tinjr (wrap $f $g $i $T $b)
with wrap $f $g $i $T (tcase $A $B $P $a $b $x) ↪ tcase (wrap $f $g $i $T $A) (wrap $f $g $i $T $B)
                                                        (wrap $f $g $i $T $P) (wrap $f $g $i $T $a)
                                                        (wrap $f $g $i $T $b) (wrap $f $g $i $T $x)
with wrap $f $g $i $T (tpath $A $x $y) ↪ tpath (wrap $f $g (dbsucc $i) (IShiftI $T) $A) (wrap $f $g $i $T $x)
                                               (wrap $f $g $i $T $y)
with wrap $f $g $i $T (tlamP $t) ↪ tlamP (wrap $f $g (dbsucc $i) (IShiftI $T) $t)
with wrap $f $g $i $T (tappP $u $v) ↪ tappP (wrap $f $g $i $T $u) ($f $i $T $v)
with wrap $f $g $i $T (tsys $f1 $f2 $u $v) ↪ tsys ($g $i $T $f1) ($g $i $T $f2) (wrap $f $g $i $T $u)
                                                  (wrap $f $g $i $T $v)
with wrap _ _ _ _ temptysys ↪ temptysys
with wrap $f $g $i $T (ttransp $A $p $u) ↪ ttransp (wrap $f $g (dbsucc $i) (IShiftI $T) $A) ($g $i $T $p)
                                                   (wrap $f $g $i $T $u)
with wrap $f $g $i $T (thcomp $A $p $u $u0) ↪ thcomp (wrap $f $g $i $T $A) ($g $i $T $p)
                                                     (wrap $f $g (dbsucc $i) (IShiftI $T) $u) (wrap $f $g $i $T $u0)
with wrap $f $g $i $T (tgluety $p $t $w $A) ↪ tgluety ($g $i $T $p) (wrap $f $g $i $T $t) (wrap $f $g $i $T $w)
                                                      (wrap $f $g $i $T $A)
with wrap $f $g $i $T (tglue $p $t $a) ↪ tglue ($g $i $T $p) (wrap $f $g $i $T $t) (wrap $f $g $i $T $a)
with wrap $f $g $i $T (tunglue $p $w $b) ↪ tunglue ($g $i $T $p) (wrap $f $g $i $T $w) (wrap $f $g $i $T $b);

symbol Ishift : DBId → Term → Term ≔ λ i t, wrap (λ i _, IshiftI i) (λ i _, IshiftF i) i it0 t;
symbol IShift : Term → Term ≔ Ishift db0;
symbol IShift1 : Term → Term ≔ Ishift db1;
symbol IShift* : DBId → Term → Term;
symbol IShiftN : DBId → Term → Term;
rule IShift* db0 $t ↪ $t
with IShift* (dbsucc $n) $t ↪ IShift (IShift* $n $t)
with IShiftN $i $t ↪ IShift (IShift* $i $t);

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
rule subst $i $V (tvar $id) ↪ dbselect $i $id $V (tvar $id) (tvar (dbprev $id))
with subst _  _  (tuniv $s) ↪ tuniv $s
with subst $i $V (tpi $A $B) ↪ tpi (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst $i $V (tabs $A $t) ↪ tabs (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $t)
with subst $i $V (tapp $f $u) ↪ tapp (subst $i $V $f) (subst $i $V $u)
with subst _ _ tnat ↪ tnat
with subst _ _ tzero ↪ tzero
with subst $i $V (tsuc $n) ↪ tsuc (subst $i $V $n)
with subst $i $V (trec $P $z $H $n) ↪ trec (subst $i $V $P) (subst $i $V $z)
                                           (subst $i $V $H) (subst $i $V $n)
with subst $i $V (tsig $A $B) ↪ tsig (subst $i $V $A) (subst (dbsucc $i) (Shift $V) $B)
with subst $i $V (tpair $u $v) ↪ tpair (subst $i $V $u) (subst $i $V $v)
with subst $i $V (tp1 $p) ↪ tp1 (subst $i $V $p)
with subst $i $V (tp2 $p) ↪ tp2 (subst $i $V $p)
with subst $i $V (tsum $A $B) ↪ tsum (subst $i $V $A) (subst $i $V $B)
with subst $i $V (tinjl $a) ↪ tinjl (subst $i $V $a)
with subst $i $V (tinjr $b) ↪ tinjr (subst $i $V $b)
with subst $i $V (tcase $A $B $P $a $b $x) ↪ tcase (subst $i $V $A) (subst $i $V $B) (subst $i $V $P)
                                                   (subst $i $V $a) (subst $i $V $b) (subst $i $V $x)
with subst $i $V (tpath $A $x $y) ↪ tpath (subst $i (IShift $V) $A) (subst $i $V $x) (subst $i $V $y)
with subst $i $V (tlamP $t) ↪ tlamP (subst $i (IShift $V) $t)
with subst $i $V (tappP $t $j) ↪ tappP (subst $i $V $t) $j
with subst $i $V (tsys $f $g $u $v) ↪ tsys $f $g (subst $i $V $u) (subst $i $V $v)
with subst _ _ temptysys ↪ temptysys
with subst $i $V (ttransp $A $f $u) ↪ ttransp (subst $i (IShift $V) $A) $f (subst $i $V $u)
with subst $i $V (thcomp $A $f $u $u0) ↪ thcomp (subst $i $V $A) $f (subst $i (IShift $V) $u) (subst $i $V $u0)
with subst $i $V (tgluety $f $T $w $A) ↪ tgluety $f (subst $i $V $T) (subst $i $V $w) (subst $i $V $A)
with subst $i $V (tglue $f $t $a) ↪ tglue $f (subst $i $V $t) (subst $i $V $a)
with subst $i $V (tunglue $f $w $b) ↪ tunglue $f (subst $i $V $w) (subst $i $V $b);

symbol apply1 (t u : Term) : Term ≔ subst db0 u t;

// Some substitution commutation
// might need the interval/face versions of this
rule shift db0 (shift $i $t) ↪ shift (dbsucc $i) (Shift $t);
// rule shift (dbsucc db0) (shift (dbsucc $i) $t) ↪ shift (dbsucc (dbsucc $i)) (Shift1 $t);
// rule subst $id $u (subst $id $v (shift (dbsucc $id) $t)) ↪ subst db0 (subst db0 $u $v) $t;
rule subst $id _ (shift $id $t) ↪ $t;
rule subst (dbsucc $id) _ (shift $id (shift $id $t)) ↪ shift $id $t;
rule subst $id (tvar $id) (shift (dbsucc $id) $t) ↪ $t;
// rule shift $id (subst $j $u $t) ↪ subst (dbshift (dbsucc $id) $j) (shift $id $u) (shift (dbsucc $id) $t);
rule shift $id (subst db0 $u $t) ↪ subst db0 (shift $id $u) (shift (dbsucc $id) $t);

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
rule IsubstI _ _ it0 ↪ it0
with IsubstI _ _ it1 ↪ it1
with IsubstI $i $V (itvar $id) ↪ dbselectI $i $id $V (itvar $id) (itvar (dbprev $id))
with IsubstI $i $V (itsym $j) ↪ itsym (IsubstI $i $V $j)
with IsubstI $i $V (itmin $a $b) ↪ itmin (IsubstI $i $V $a) (IsubstI $i $V $b)
with IsubstI $i $V (itmax $a $b) ↪ itmax (IsubstI $i $V $a) (IsubstI $i $V $b);

// The computation of the face formula equivalent to having substituted a term for the variable
// in an fteq0 or fteq1
symbol substeq0 : ITerm → FTerm;
symbol substeq1 : ITerm → FTerm;
rule substeq0 it0 ↪ ft1
with substeq0 it1 ↪ ft0
with substeq0 (itvar $id) ↪ fteq0 $id
with substeq0 (itsym $i) ↪ substeq1 $i
with substeq0 (itmin $a $b) ↪ ftmax (substeq0 $a) (substeq0 $b)
with substeq0 (itmax $a $b) ↪ ftmin (substeq0 $a) (substeq0 $b)
with substeq1 it0 ↪ ft0
with substeq1 it1 ↪ ft1
with substeq1 (itvar $id) ↪ fteq1 $id
with substeq1 (itsym $i) ↪ substeq0 $i
with substeq1 (itmin $a $b) ↪ ftmin (substeq1 $a) (substeq1 $b)
with substeq1 (itmax $a $b) ↪ ftmax (substeq1 $a) (substeq1 $b);

symbol IsubstF : DBId → ITerm → FTerm → FTerm;
// as eq0 and eq1 only apply to variables, when substituting the variable we transform the formula to obtain
rule IsubstF _ _ ft0 ↪ ft0
with IsubstF _ _ ft1 ↪ ft1
with IsubstF $i $V (fteq0 $id) ↪ dbselectF $i $id (substeq0 $V) (fteq0 $id) (fteq0 (dbprev $id))
with IsubstF $i $V (fteq1 $id) ↪ dbselectF $i $id (substeq1 $V) (fteq1 $id) (fteq1 (dbprev $id))
with IsubstF $i $V (ftmin $a $b) ↪ ftmin (IsubstF $i $V $a) (IsubstF $i $V $b)
with IsubstF $i $V (ftmax $a $b) ↪ ftmax (IsubstF $i $V $a) (IsubstF $i $V $b);
symbol Isubst : DBId → ITerm → Term → Term ≔ wrap IsubstI IsubstF;

symbol applyI1 (u : Term) (t : ITerm) ≔ Isubst db0 t u;

// Interval substitution commutation
rule IshiftI db0 (IshiftI $i $t) ↪ IshiftI (dbsucc $i) (IShiftI $t);
rule IshiftF db0 (IshiftF $i $t) ↪ IshiftF (dbsucc $i) (IShiftF $t);
rule wrap IsubstI IsubstF $id _ (wrap (λ i _, IshiftI i) (λ i _, IshiftF i) $id _ $t) ↪ $t;
rule IsubstI $id _ (IshiftI $id $t) ↪ $t;
rule IsubstF $id _ (IshiftF $id $t) ↪ $t;
// rule wrap (λ i _ , IshiftI i) (λ i _, IshiftF i) $id _ (wrap IsubstI IsubstF db0 $u $t) ↪
//      wrap IsubstI IsubstF db0 (IshiftI $id $u) (wrap (λ i _, IshiftI i) (λ i _, IshiftF i) (dbsucc $id) it0 $t);
rule wrap IsubstI IsubstF $id (itvar $id) (wrap (λ i _, IshiftI i) (λ i _, IshiftF i) (dbsucc $id) _ $t) ↪ $t;
rule wrap IsubstI IsubstF $id it0 (wrap (λ i _, IshiftI i) (λ i _, IshiftF i) (dbsucc $id) _ $t) ↪
     Ishift $id (Isubst $id it0 $t);
rule wrap IsubstI IsubstF $id it1 (wrap (λ i _, IshiftI i) (λ i _, IshiftF i) (dbsucc $id) _ $t) ↪
     Ishift $id (Isubst $id it1 $t);
rule shift $id (wrap IsubstI IsubstF db0 $u $t) ↪ Isubst db0 $u (shift $id $t);
