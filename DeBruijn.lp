
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
symbol dbeq_inv [i j] : DBEq i j → DBEq j i;
rule dbeq_inv (DBRefl _) ↪ DBRefl _;
symbol dbeq_trans [i j k : DBId] : DBEq i j → DBEq j k → DBEq i k;
rule dbeq_trans (DBRefl _) (DBRefl _) ↪ DBRefl _;

symbol dbeq_S_n [i j : DBId] : DBEq (dbsucc i) (dbsucc j) → DBEq i j;
rule dbeq_S_n (DBRefl _) ↪ DBRefl _;

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

symbol dble_eq_left i j k : DBEq i j → DBLe i k → DBLe j k;
symbol dble_eq_right i j k : DBEq i j → DBLe k i → DBLe k j;
rule dble_eq_left _ _ _ (DBRefl _) $h ↪ $h
with dble_eq_right _ _ _ (DBRefl _) $h ↪ $h;

symbol dble_trans i j k : DBLe i j → DBLe j k → DBLe i k;
rule dble_trans _ _ _ $e (DBLe_refl _) ↪ $e
with dble_trans _ _ _ $e (DBLe_succ $f) ↪ DBLe_succ (dble_trans _ _ _ $e $f);

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

symbol Ishift : DBId → Term → Term;
rule Ishift _ (tvar $id) ↪ (tvar $id)
with Ishift _ (tuniv $id) ↪ tuniv $id
with Ishift $i (tpi $A $B) ↪ tpi (Ishift $i $A) (Ishift $i $B)
with Ishift $i (tabs $A $t) ↪ tabs (Ishift $i $A) (Ishift $i $t)
with Ishift $i (tapp $u $v) ↪ tapp (Ishift $i $u) (Ishift $i $v)
with Ishift _ tnat ↪ tnat
with Ishift _ tzero ↪ tzero
with Ishift $i (tsuc $n) ↪ tsuc (Ishift $i $n)
with Ishift $i (trec $P $z $H $n) ↪ trec (Ishift $i $P) (Ishift $i $z)
                                         (Ishift $i $H) (Ishift $i $n)
with Ishift $i (tsig $A $B) ↪ tsig (Ishift $i $A) (Ishift $i $B)
with Ishift $i (tpair $a $b) ↪ tpair (Ishift $i $a) (Ishift $i $b)
with Ishift $i (tp1 $p) ↪ tp1 (Ishift $i $p)
with Ishift $i (tp2 $p) ↪ tp2 (Ishift $i $p)
with Ishift $i (tsum $A $B) ↪ tsum (Ishift $i $A) (Ishift $i $B)
with Ishift $i (tinjl $a) ↪ tinjl (Ishift $i $a)
with Ishift $i (tinjr $b) ↪ tinjr (Ishift $i $b)
with Ishift $i (tcase $A $B $P $a $b $x) ↪ tcase (Ishift $i $A) (Ishift $i $B)
                                                 (Ishift $i $P) (Ishift $i $a)
                                                 (Ishift $i $b) (Ishift $i $x)
with Ishift $i (tpath $A $x $y) ↪ tpath (Ishift (dbsucc $i) $A) (Ishift $i $x)
                                        (Ishift $i $y)
with Ishift $i (tlamP $t) ↪ tlamP (Ishift (dbsucc $i) $t)
with Ishift $i (tappP $u $v) ↪ tappP (Ishift $i $u) (IshiftI $i $v)
with Ishift $i (tsys $f1 $f2 $u $v) ↪ tsys (IshiftF $i $f1) (IshiftF $i $f2)
                                           (Ishift $i $u) (Ishift $i $v)
with Ishift _ temptysys ↪ temptysys
with Ishift $i (ttransp $A $p $u) ↪ ttransp (Ishift (dbsucc $i) $A) (IshiftF $i $p)
                                            (Ishift $i $u)
with Ishift $i (thcomp $A $p $u $u0) ↪ thcomp (Ishift $i $A) (IshiftF $i $p)
                                              (Ishift (dbsucc $i) $u) (Ishift $i $u0)
with Ishift $i (tgluety $p $t $w $A) ↪ tgluety (IshiftF $i $p) (Ishift $i $t) (Ishift $i $w)
                                               (Ishift $i $A)
with Ishift $i (tglue $p $t $a) ↪ tglue (IshiftF $i $p) (Ishift $i $t) (Ishift $i $a)
with Ishift $i (tunglue $p $w $b) ↪ tunglue (IshiftF $i $p) (Ishift $i $w) (Ishift $i $b);
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
symbol Isubst : DBId → ITerm → Term → Term;
rule Isubst _ _ (tvar $id) ↪ (tvar $id)
with Isubst _ _ (tuniv $id) ↪ tuniv $id
with Isubst $i $T (tpi $A $B) ↪ tpi (Isubst $i $T $A) (Isubst $i $T $B)
with Isubst $i $T (tabs $A $t) ↪ tabs (Isubst $i $T $A) (Isubst $i $T $t)
with Isubst $i $T (tapp $u $v) ↪ tapp (Isubst $i $T $u) (Isubst $i $T $v)
with Isubst _ _ tnat ↪ tnat
with Isubst _ _ tzero ↪ tzero
with Isubst $i $T (tsuc $n) ↪ tsuc (Isubst $i $T $n)
with Isubst $i $T (trec $P $z $H $n) ↪ trec (Isubst $i $T $P) (Isubst $i $T $z)
                                            (Isubst $i $T $H) (Isubst $i $T $n)
with Isubst $i $T (tsig $A $B) ↪ tsig (Isubst $i $T $A) (Isubst $i $T $B)
with Isubst $i $T (tpair $a $b) ↪ tpair (Isubst $i $T $a) (Isubst $i $T $b)
with Isubst $i $T (tp1 $p) ↪ tp1 (Isubst $i $T $p)
with Isubst $i $T (tp2 $p) ↪ tp2 (Isubst $i $T $p)
with Isubst $i $T (tsum $A $B) ↪ tsum (Isubst $i $T $A) (Isubst $i $T $B)
with Isubst $i $T (tinjl $a) ↪ tinjl (Isubst $i $T $a)
with Isubst $i $T (tinjr $b) ↪ tinjr (Isubst $i $T $b)
with Isubst $i $T (tcase $A $B $P $a $b $x) ↪ tcase (Isubst $i $T $A) (Isubst $i $T $B)
                                                    (Isubst $i $T $P) (Isubst $i $T $a)
                                                    (Isubst $i $T $b) (Isubst $i $T $x)
with Isubst $i $T (tpath $A $x $y) ↪ tpath (Isubst (dbsucc $i) (IShiftI $T) $A) (Isubst $i $T $x)
                                           (Isubst $i $T $y)
with Isubst $i $T (tlamP $t) ↪ tlamP (Isubst (dbsucc $i) (IShiftI $T) $t)
with Isubst $i $T (tappP $u $v) ↪ tappP (Isubst $i $T $u) (IsubstI $i $T $v)
with Isubst $i $T (tsys $f1 $f2 $u $v) ↪ tsys (IsubstF $i $T $f1) (IsubstF $i $T $f2) (Isubst $i $T $u)
                                              (Isubst $i $T $v)
with Isubst _ _ temptysys ↪ temptysys
with Isubst $i $T (ttransp $A $p $u) ↪ ttransp (Isubst (dbsucc $i) (IShiftI $T) $A) (IsubstF $i $T $p)
                                               (Isubst $i $T $u)
with Isubst $i $T (thcomp $A $p $u $u0) ↪ thcomp (Isubst $i $T $A) (IsubstF $i $T $p)
                                                 (Isubst (dbsucc $i) (IShiftI $T) $u) (Isubst $i $T $u0)
with Isubst $i $T (tgluety $p $t $w $A) ↪ tgluety (IsubstF $i $T $p) (Isubst $i $T $t) (Isubst $i $T $w)
                                                  (Isubst $i $T $A)
with Isubst $i $T (tglue $p $t $a) ↪ tglue (IsubstF $i $T $p) (Isubst $i $T $t) (Isubst $i $T $a)
with Isubst $i $T (tunglue $p $w $b) ↪ tunglue (IsubstF $i $T $p) (Isubst $i $T $w) (Isubst $i $T $b);

symbol applyI1 (u : Term) (t : ITerm) ≔ Isubst db0 t u;

// Interval bounds simplification
rule IShiftI* _ it0 ↪ it0;
rule IShiftI* _ it1 ↪ it1;

// Interval substitution commutation
rule IshiftI db0 (IshiftI $i $t) ↪ IshiftI (dbsucc $i) (IShiftI $t);
rule IshiftF db0 (IshiftF $i $t) ↪ IshiftF (dbsucc $i) (IShiftF $t);
rule Isubst $id _ (Ishift $id $t) ↪ $t;
rule IsubstI $id _ (IshiftI $id $t) ↪ $t;
rule IsubstF $id _ (IshiftF $id $t) ↪ $t;
// rule Ishift $id (Isubst db0 $u $t) ↪
//      Isubst db0 (IshiftI $id $u) (Ishift (dbsucc $id) $t);
rule Isubst $id (itvar $id) (Ishift (dbsucc $id) $t) ↪ $t;
rule Isubst $id it0 (Ishift (dbsucc $id) $t) ↪
     Ishift $id (Isubst $id it0 $t);
rule Isubst $id it1 (Ishift (dbsucc $id) $t) ↪
     Ishift $id (Isubst $id it1 $t);
rule shift $id (Isubst db0 $u $t) ↪ Isubst db0 $u (shift $id $t);
rule Ishift $id (subst db0 $u $t) ↪ subst db0 (Ishift $id $u) (Ishift $id $t);
