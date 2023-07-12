
require open ctt.ast;
require open ctt.DeBruijn;
require open ctt.Typing;

// Term equality, necessary to express commutation of different operations
constant symbol TEq : Term → Term → TYPE;
constant symbol TRefl (t : Term) : TEq t t;
constant symbol ITEq : ITerm → ITerm → TYPE;
constant symbol ITRefl (t : ITerm) : ITEq t t;
constant symbol FTEq : FTerm → FTerm → TYPE;
constant symbol FTRefl (t : FTerm) : FTEq t t;

// Elimination of term equality
symbol teq_inv [t1 t2 : Term] : TEq t1 t2 → TEq t2 t1;
symbol teq_trans [t1 t2 t3 : Term] : TEq t1 t2 → TEq t2 t3 → TEq t1 t3;
symbol Jt [Γ : Context] [s : Lev] [t1 t2 T : Term]
          : TEq t1 t2 → der Γ t1 T s → der Γ t2 T s;
symbol JT [Γ : Context] [s : Lev] [t T1 T2 : Term]
          : TEq T1 T2 → der Γ t T1 s → der Γ t T2 s;
symbol JtT [Γ : Context] [s : Lev] [t1 t2 T1 T2 : Term]
           : TEq t1 t2 → TEq T1 T2 → der Γ t1 T1 s → der Γ t2 T2 s;
symbol Jcong [t1 t2 : Term] (f : Term → Term)
             : TEq t1 t2 → TEq (f t1) (f t2);
symbol Jeq [Γ : Context] [s : Lev] [T T' t1 t1' t2 t2']
           : TEq T T'
           → TEq t1 t1'
           → TEq t2 t2'
           → der_eq Γ t1  t2  T  s
           → der_eq Γ t1' t2' T' s;
symbol dbcongT [i j : DBId] (f : DBId → Term) : DBEq i j → TEq (f i) (f j);
symbol IcongT [i j : ITerm] (f : ITerm → Term) : ITEq i j → TEq (f i) (f j);
symbol FcongT [i j : FTerm] (f : FTerm → Term) : FTEq i j → TEq (f i) (f j);
rule teq_inv (TRefl $t) ↪ TRefl $t
with teq_trans (TRefl $t) (TRefl _) ↪ TRefl $t
with JtT (TRefl _) (TRefl _) $d ↪ $d
with @Jt _ _ _ _ $T $eqt $d ↪ JtT $eqt (TRefl $T) $d
with @JT _ _ $t _ _ $eqT $d ↪ JtT (TRefl $t) $eqT $d
with @Jcong $t _ $f (TRefl _) ↪ TRefl ($f $t)
with Jeq (TRefl _) (TRefl _) (TRefl _) $d ↪ $d
with dbcongT $f (DBRefl $i) ↪ TRefl ($f $i)
with IcongT $f (ITRefl $i) ↪ TRefl ($f $i)
with FcongT $f (FTRefl $i) ↪ TRefl ($f $i);

// Congruence for term equality
// symbol Jabs [A1 A2 B1 B2 t1 t2 : Term]
//             : TEq A1 A2
//             → TEq B1 B2
//             → TEq t1 t2
//             → TEq (tabs A1 B1 t1) (tabs A2 B2 t2);
// symbol Japp [A1 A2 B1 B2 f1 f2 a1 a2 : Term]
//             : TEq A1 A2
//             → TEq B1 B2
//             → TEq f1 f2
//             → TEq a1 a2
//             → TEq (tapp A1 B1 f1 a1) (tapp A2 B2 f2 a2);
// symbol Jfun [A1 A2 B1 B2 : Term]
//             : TEq A1 A2
//             → TEq B1 B2
//             → TEq (tfun A1 B1) (tfun A2 B2);
// symbol Jpair [A1 A2 B1 B2 a1 a2 b1 b2 : Term]
//              : TEq A1 A2
//              → TEq B1 B2
//              → TEq a1 a2
//              → TEq b1 b2
//              → TEq (tpair A1 B1 a1 b1) (tpair A2 B2 a2 b2);
// symbol Jπ1 [A1 A2 B1 B2 p1 p2 : Term]
//            : TEq A1 A2
//            → TEq B1 B2
//            → TEq p1 p2
//            → TEq (π1 A1 B1 p1) (π1 A2 B2 p2);
// symbol Jπ2 [A1 A2 B1 B2 p1 p2 : Term]
//            : TEq A1 A2
//            → TEq B1 B2
//            → TEq p1 p2
//            → TEq (π2 A1 B1 p1) (π2 A2 B2 p2);
// symbol Jsum [A1 A2 B1 B2 : Term]
//             : TEq A1 A2
//             → TEq B1 B2
//             → TEq (tsum A1 B1) (tsum A2 B2);
// symbol Jrefl [A1 A2 a1 a2 : Term]
//            : TEq A1 A2
//            → TEq a1 a2
//            → TEq (trefl A1 a1) (trefl A2 a2);
// symbol Jteq [A1 A2 a1 a2 b1 b2 : Term]
//             : TEq A1 A2
//             → TEq a1 a2
//             → TEq b1 b2
//             → TEq (teq A1 a1 b1) (teq A2 a2 b2);
// symbol Jselect [eq1 eq2 gt1 gt2 lt1 lt2 : Term] (i j : DBId)
//                : TEq eq1 eq2
//                → TEq gt1 gt2
//                → TEq lt1 lt2
//                → TEq (dbselect i j eq1 gt1 lt1) (dbselect i j eq2 gt2 lt2);

// rule Jabs (TRefl $A) (TRefl $B) (TRefl $t) ↪ TRefl (tabs $A $B $t)
// with Japp (TRefl $A) (TRefl $B) (TRefl $f) (TRefl $a) ↪ TRefl (tapp $A $B $f $a)
// with Jfun (TRefl $A) (TRefl $B) ↪ TRefl (tfun $A $B)
// with Jpair (TRefl $A) (TRefl $B) (TRefl $a) (TRefl $b) ↪ TRefl (tpair $A $B $a $b)
// with Jπ1 (TRefl $A) (TRefl $B) (TRefl $p) ↪ TRefl (π1 $A $B $p)
// with Jπ2 (TRefl $A) (TRefl $B) (TRefl $p) ↪ TRefl (π2 $A $B $p)
// with Jsum (TRefl $A) (TRefl $B) ↪ TRefl (tsum $A $B)
// with Jrefl (TRefl $A) (TRefl $a) ↪ TRefl (trefl $A $a)
// with Jteq (TRefl $A) (TRefl $a) (TRefl $b) ↪ TRefl (teq $A $a $b)
// with Jselect $i $j (TRefl $eq) (TRefl $gt) (TRefl $lt) ↪ TRefl (dbselect $i $j $eq $gt $lt);

// Elimination of interval term equality
symbol iteq_inv [t1 t2 : ITerm] : ITEq t1 t2 → ITEq t2 t1;
symbol iteq_trans [t1 t2 t3 : ITerm] : ITEq t1 t2 → ITEq t2 t3 → ITEq t1 t3;
symbol IJ [Γ : Context] [t1 t2 : ITerm]
          : ITEq t1 t2 → der_I Γ t1 → der_I Γ t2;
symbol IJcong [t1 t2 : ITerm] (f : ITerm → ITerm)
             : ITEq t1 t2 → ITEq (f t1) (f t2);
symbol IJeq [Γ : Context] [t1 t1' t2 t2']
           : ITEq t1 t1'
           → ITEq t2 t2'
           → der_eq_I Γ t1  t2
           → der_eq_I Γ t1' t2';
symbol dbcongI [i j : DBId] (f : DBId → ITerm) : DBEq i j → ITEq (f i) (f j);
rule iteq_inv (ITRefl $t) ↪ ITRefl $t
with iteq_trans (ITRefl $t) (ITRefl _) ↪ ITRefl $t
with IJ (ITRefl _) $d ↪ $d
with @IJcong $t _ $f (ITRefl _) ↪ ITRefl ($f $t)
with IJeq (ITRefl _) (ITRefl _) $d ↪ $d
with dbcongI $f (DBRefl $i) ↪ ITRefl ($f $i);

// Elimination of face term equality
symbol fteq_inv [t1 t2 : FTerm] : FTEq t1 t2 → FTEq t2 t1;
symbol fteq_trans [t1 t2 t3 : FTerm] : FTEq t1 t2 → FTEq t2 t3 → FTEq t1 t3;
symbol FJ [Γ : Context] [t1 t2 : FTerm]
          : FTEq t1 t2 → der_F Γ t1 → der_F Γ t2;
symbol FJcong [t1 t2 : FTerm] (f : FTerm → FTerm)
             : FTEq t1 t2 → FTEq (f t1) (f t2);
symbol FJeq [Γ : Context] [t1 t1' t2 t2']
           : FTEq t1 t1'
           → FTEq t2 t2'
           → der_eq_F Γ t1  t2
           → der_eq_F Γ t1' t2';
symbol FJisOne [Γ : Context] [t1 t2 : FTerm] :
  FTEq t1 t2 → der_isOne Γ t1 → der_isOne Γ t2;
symbol dbcongF [i j : DBId] (f : DBId → FTerm) : DBEq i j → FTEq (f i) (f j);
rule fteq_inv (FTRefl $t) ↪ FTRefl $t
with fteq_trans (FTRefl $t) (FTRefl _) ↪ FTRefl $t
with FJ (FTRefl _) $d ↪ $d
with @FJcong $t _ $f (FTRefl _) ↪ FTRefl ($f $t)
with FJeq (FTRefl _) (FTRefl _) $d ↪ $d
with FJisOne (FTRefl _) $d ↪ $d
with dbcongF $f (DBRefl $i) ↪ FTRefl ($f $i);

// Auxiliary lemmas
// dbselect*_spec_lt
symbol aux_dbselect_spec_lt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc i) j → TEq (dbselect i j eqT gtT ltT) ltT;
rule aux_dbselect_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ TRefl $ltT
with aux_dbselect_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
   ↪ aux_dbselect_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectI_spec_lt (i j : DBId) (eqT gtT ltT : ITerm) :
  DBLe (dbsucc i) j → ITEq (dbselectI i j eqT gtT ltT) ltT;
rule aux_dbselectI_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ ITRefl $ltT
with aux_dbselectI_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
   ↪ aux_dbselectI_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectF_spec_lt (i j : DBId) (eqT gtT ltT : FTerm) :
  DBLe (dbsucc i) j → FTEq (dbselectF i j eqT gtT ltT) ltT;
rule aux_dbselectF_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ FTRefl $ltT
with aux_dbselectF_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
   ↪ aux_dbselectF_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);

// dbselect*_spec_gt
symbol aux_dbselect_spec_gt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc j) i → TEq (dbselect i j eqT gtT ltT) gtT;
rule aux_dbselect_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ TRefl $gtT
with aux_dbselect_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
  ↪ aux_dbselect_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectI_spec_gt (i j : DBId) (eqT gtT ltT : ITerm) :
  DBLe (dbsucc j) i → ITEq (dbselectI i j eqT gtT ltT) gtT;
rule aux_dbselectI_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ ITRefl $gtT
with aux_dbselectI_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
  ↪ aux_dbselectI_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectF_spec_gt (i j : DBId) (eqT gtT ltT : FTerm) :
  DBLe (dbsucc j) i → FTEq (dbselectF i j eqT gtT ltT) gtT;
rule aux_dbselectF_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ FTRefl $gtT
with aux_dbselectF_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h
  ↪ aux_dbselectF_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);

// teq_shift_shift
symbol aux_teq_shift_shift (i j : DBId) (u : Term) :
  DBLe i j → TEq (shift i (shift j u)) (shift (dbsucc j) (shift i u));
symbol aux_teq_shift_shift_var (i j n : DBId) :
  DBLe i j → DBEq (dbshift i (dbshift j n)) (dbshift (dbsucc j) (dbshift i n));

rule aux_teq_shift_shift_var db0 $j $n _ ↪ DBRefl (dbsucc (dbshift $j $n))
with aux_teq_shift_shift_var (dbsucc _) (dbsucc _) db0 _ ↪ DBRefl db0
with aux_teq_shift_shift_var (dbsucc $i) (dbsucc $j) (dbsucc $n) $h
  ↪ dbcongI dbsucc (aux_teq_shift_shift_var $i $j $n (dble_S_n $h))
with aux_teq_shift_shift $i $j (var $n) $h ↪ dbcongT var (aux_teq_shift_shift_var $i $j $n $h)
with aux_teq_shift_shift _ _ (tabs $A $B $t) $h
  ↪ Jabs (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
          (aux_teq_shift_shift _ _ $t (dble_n_S $h))
with aux_teq_shift_shift _ _ (tapp $A $B $f $a) $h
  ↪ Japp (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
          (aux_teq_shift_shift _ _ $f $h)
          (aux_teq_shift_shift _ _ $a $h)
with aux_teq_shift_shift _ _ (tfun $A $B) $h
  ↪ Jfun (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (tsort $s) _ ↪ TRefl (tsort $s)
with aux_teq_shift_shift _ _ (tpair $A $B $a $b) $h
  ↪ Jpair (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $B (dble_n_S $h))
           (aux_teq_shift_shift _ _ $a $h)
           (aux_teq_shift_shift _ _ $b $h)
with aux_teq_shift_shift _ _ (π1 $A $B $p) $h
  ↪ Jπ1 (aux_teq_shift_shift _ _ $A $h)
         (aux_teq_shift_shift _ _ $B (dble_n_S $h))
         (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (π2 $A $B $p) $h
  ↪ Jπ2 (aux_teq_shift_shift _ _ $A $h)
         (aux_teq_shift_shift _ _ $B (dble_n_S $h))
         (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tsum $A $B) $h
  ↪ Jsum (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (trefl $A $a) $h
  ↪ Jrefl (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $a $h)
with aux_teq_shift_shift _ _ (teq $A $a $b) $h
  ↪ Jteq (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $a $h)
          (aux_teq_shift_shift _ _ $b $h);

// teq_shift_shift0
symbol aux_teq_shift_shift0 (i : DBId) (u : Term) :
  TEq (Shift (shift i u)) (shift (dbsucc i) (Shift u)) ≔
  aux_teq_shift_shift db0 i u (dble_0_n i);

// teq_shift_dbselect
symbol aux_teq_shift_dbselect (n i j : DBId) (eqT gtT ltT : Term) :
  TEq (shift n (dbselect i j eqT gtT ltT))
      (dbselect i j (shift n eqT) (shift n gtT) (shift n ltT));
rule aux_teq_shift_dbselect $n db0        db0 $eqT _ _ ↪ TRefl (shift $n $eqT)
with aux_teq_shift_dbselect $n (dbsucc _) db0 _ $gtT _ ↪ TRefl (shift $n $gtT)
with aux_teq_shift_dbselect $n db0 (dbsucc _) _ _ $ltT ↪ TRefl (shift $n $ltT)
with aux_teq_shift_dbselect $n (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT ↪ aux_teq_shift_dbselect $n $i $j $eqT $gtT $ltT;

// teq_shift_dbselect0
symbol aux_teq_shift_dbselect0 (i j : DBId) (eqT gtT ltT : Term) :
  TEq (Shift (dbselect i j eqT gtT ltT))
      (dbselect i j (Shift eqT) (Shift gtT) (Shift ltT)) ≔
  aux_teq_shift_dbselect db0 i j eqT gtT ltT;

// teq_dbselect_fn
symbol aux_teq_dbselect_fn (i n : DBId) (eqT gtT : Term) (f : DBId → Term) :
  TEq (dbselect i n eqT gtT (f n))
      (dbselect i n eqT gtT (f (dbsucc (dbprev n))));
rule aux_teq_dbselect_fn db0 db0 $eqT _ _ ↪ TRefl $eqT
with aux_teq_dbselect_fn (dbsucc _) db0 _ $gtT _ ↪ TRefl $gtT
with aux_teq_dbselect_fn db0 (dbsucc $n) _ _ $f ↪ TRefl ($f (dbsucc $n))
with aux_teq_dbselect_fn (dbsucc $i) (dbsucc $n) $eqT $gtT $f ↪ TRefl (dbselect $i $n $eqT $gtT ($f (dbsucc $n)));

// teq_dbselect_Sn
symbol aux_teq_dbselect_Sn (i n : DBId) (eqT gtT : Term) :
  TEq (dbselect i n eqT gtT (var n))
      (dbselect i n eqT gtT (var (dbsucc (dbprev n)))) ≔
  aux_teq_dbselect_fn i n eqT gtT var;

// teq_subst_shift
symbol aux_teq_subst_shift (i j : DBId) (u t : Term) :
  DBLe j i
  → TEq (subst (dbsucc i) (shift j (Shift* j u)) (shift j t))
        (shift j (subst i (Shift* j u) t));
// teq_subst_shift_var
symbol aux_teq_subst_shift_var (i j : DBId) (u : Term) (n : DBId) :
  DBLe j i
  → TEq (dbselect (dbsucc i) (dbshift j n) (shift j (Shift* j u)) (var (dbshift j n)) (var (dbprev (dbshift j n))))
        (dbselect i n (shift j (Shift* j u)) (var (dbshift j n)) (var (dbshift j (dbprev n))));

rule aux_teq_subst_shift_var $i db0 $u $n _
  ↪ aux_teq_dbselect_Sn $i $n (shift db0 $u) (var (dbsucc $n))
with aux_teq_subst_shift_var (dbsucc _) (dbsucc _) _ db0 _
  ↪ TRefl (var db0)
with aux_teq_subst_shift_var (dbsucc db0) (dbsucc $j) $u (dbsucc db0) $h
  ↪ teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc db0) (dbshift $j db0) (shift (dbsucc $j) (Shift* (dbsucc $j) $u)) (var (dbsucc (dbshift $j db0))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc db0) (dbshift $j db0) (shift $j (Shift* $j $u)) (var (dbshift $j db0)) (var (dbprev (dbshift $j db0))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var db0 $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselect0 db0 db0 (shift $j (Shift* $j $u)) (var (dbshift $j db0)) (var (dbshift $j (dbprev db0)))))
with aux_teq_subst_shift_var (dbsucc (dbsucc $i)) (dbsucc $j) $u (dbsucc db0) $h
  ↪ teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc (dbsucc $i)) (dbshift $j db0) (shift (dbsucc $j) (Shift* (dbsucc $j) $u)) (var (dbsucc (dbshift $j db0))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc (dbsucc $i)) (dbshift $j db0) (shift $j (Shift* $j $u)) (var (dbshift $j db0)) (var (dbprev (dbshift $j db0))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var (dbsucc $i) $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselect0 (dbsucc $i) db0 (shift $j (Shift* $j $u)) (var (dbshift $j db0)) (var (dbshift $j (dbprev db0)))))
with aux_teq_subst_shift_var (dbsucc $i) (dbsucc $j) $u (dbsucc (dbsucc $n)) $h
  ↪ teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc $i) (dbshift $j (dbsucc $n)) (shift (dbsucc $j) (Shift* (dbsucc $j) $u)) (var (dbsucc (dbshift $j (dbsucc $n)))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc $i) (dbshift $j (dbsucc $n)) (shift $j (Shift* $j $u)) (var (dbshift $j (dbsucc $n))) (var (dbprev (dbshift $j (dbsucc $n)))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var $i $j $u (dbsucc $n) (dble_S_n $h)))
         (aux_teq_shift_dbselect0 $i (dbsucc $n) (shift $j (Shift* $j $u)) (var (dbshift $j (dbsucc $n))) (var (dbshift $j ($n)))));

rule aux_teq_subst_shift $i $j $u (var $n) $h
  ↪ teq_trans
       (aux_teq_subst_shift_var $i $j $u $n $h)
       (teq_inv (aux_teq_shift_dbselect $j $i $n (Shift* $j $u) (var $n) (var (dbprev $n))))
with aux_teq_subst_shift $i $j $u (tabs $A $B $t) $h
  ↪ Jabs (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $t (dble_n_S $h))
with aux_teq_subst_shift $i $j $u (tapp $A $B $f $a) $h
  ↪ Japp (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
          (aux_teq_subst_shift $i $j $u $f $h)
          (aux_teq_subst_shift $i $j $u $a $h)
with aux_teq_subst_shift $i $j $u (tfun $A $B) $h
  ↪ Jfun (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
with aux_teq_subst_shift _ _ _ (tsort $s) _
  ↪ TRefl (tsort $s)
with aux_teq_subst_shift $i $j $u (tpair $A $B $a $b) $h
  ↪ Jpair (aux_teq_subst_shift $i $j $u $A $h)
           (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
           (aux_teq_subst_shift $i $j $u $a $h)
           (aux_teq_subst_shift $i $j $u $b $h)
with aux_teq_subst_shift $i $j $u (π1 $A $B $p) $h
  ↪ Jπ1 (aux_teq_subst_shift $i $j $u $A $h)
         (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
         (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (π2 $A $B $p) $h
  ↪ Jπ2 (aux_teq_subst_shift $i $j $u $A $h)
         (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
         (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (tsum $A $B) $h
  ↪ Jsum (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
with aux_teq_subst_shift $i $j $u (trefl $A $a) $h
  ↪ Jrefl (aux_teq_subst_shift $i $j $u $A $h)
           (aux_teq_subst_shift $i $j $u $a $h)
with aux_teq_subst_shift $i $j $u (teq $A $a $b) $h
  ↪ Jteq (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift $i $j $u $a $h)
          (aux_teq_subst_shift $i $j $u $b $h)
;

// teq_subst_shift
symbol teq_subst_shift (i : DBId) (u t : Term) :
  TEq (subst (dbsucc i) (Shift u) (Shift t))
      (Shift (subst i u t)) ≔
  aux_teq_subst_shift i db0 u t (dble_0_n i);

// teq_subst_shift1
symbol teq_subst_shift1 (i : DBId) (u t : Term) :
  TEq (subst (dbsucc (dbsucc i)) (Shift (Shift u)) (Shift1 t))
      (Shift1 (subst (dbsucc i) (Shift u) t)) ≔
  aux_teq_subst_shift (dbsucc i) db1 u t (dble_n_S (dble_0_n i));

// teq_select_shift
symbol teq_select_shift (i id : DBId) (V : Term) :
  TEq (dbselect (dbsucc i) (dbsucc id) (Shift V) (var (dbsucc id)) (var id))
      (Shift (dbselect i id V (var id) (var (dbprev id)))) ≔
  teq_trans
    (aux_teq_dbselect_Sn i id (Shift V) (var (dbsucc id)))
    (teq_inv (aux_teq_shift_dbselect0 i id V (var id) (var (dbprev id))));

// teq_subst_dbselect
symbol aux_teq_subst_dbselect (i j k : DBId) (u eqT gtT ltT : Term) :
  TEq (subst k u (dbselect i j eqT gtT ltT))
      (dbselect i j (subst k u eqT) (subst k u gtT) (subst k u ltT));
rule aux_teq_subst_dbselect db0        db0 $k $u $eqT _ _ ↪ TRefl (subst $k $u $eqT)
with aux_teq_subst_dbselect (dbsucc _) db0 $k $u _ $gtT _ ↪ TRefl (subst $k $u $gtT)
with aux_teq_subst_dbselect db0 (dbsucc _) $k $u _ _ $ltT ↪ TRefl (subst $k $u $ltT)
with aux_teq_subst_dbselect (dbsucc $i) (dbsucc $j) $k $u $eqT $gtT $ltT ↪ aux_teq_subst_dbselect $i $j $k $u $eqT $gtT $ltT;

// teq_shift_cancel_subst
symbol aux_teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift i t)) t;
symbol select_neq : DBId → DBId → Term → Term → Term;
rule select_neq (dbsucc _) db0 $gt _ ↪ $gt
with select_neq db0 (dbsucc _) _ $lt ↪ $lt
with select_neq (dbsucc $i) (dbsucc $n) $gt $lt ↪ select_neq $i $n $gt $lt;
// aux_teq_shift_neq
symbol aux_teq_shift_neq (i n : DBId) (eqT gtT ltT : Term) :
  TEq (dbselect i (dbshift i n) eqT gtT ltT) (select_neq i (dbshift i n) gtT ltT);
// aux_shift_select_neq
symbol aux_shift_select_neq (i j k : DBId) (gtT ltT : Term) :
  TEq (shift k (select_neq i (dbshift i j) gtT ltT)) (select_neq i (dbshift i j) (shift k gtT) (shift k ltT));
// aux_select_neq_Sn
symbol aux_select_neq_Sn (i j : DBId) (gtT : Term) :
  TEq (select_neq i (dbshift i j) gtT (var (dbshift i j)))
      (select_neq i (dbshift i j) gtT (var (dbsucc (dbprev (dbshift i j)))));
// aux_shift_cancel_select_neq
symbol aux_shift_cancel_select_neq (i n : DBId) :
  TEq (select_neq i (dbshift i n) (var (dbshift i n)) (var (dbprev (dbshift i n)))) (var n);

rule aux_teq_shift_neq db0 db0 _ _ $ltT ↪ TRefl $ltT
with aux_teq_shift_neq (dbsucc _) db0 _ $gtT _ ↪ TRefl $gtT
with aux_teq_shift_neq db0 (dbsucc _) _ _ $ltT ↪ TRefl $ltT
with aux_teq_shift_neq (dbsucc $i) (dbsucc $n) $eqT $gtT $ltT ↪ aux_teq_shift_neq $i $n $eqT $gtT $ltT
with aux_shift_select_neq db0 db0 $k _ $ltT ↪ TRefl (shift $k $ltT)
with aux_shift_select_neq (dbsucc _) db0 $k $gtT _ ↪ TRefl (shift $k $gtT)
with aux_shift_select_neq db0 (dbsucc _) $k _ $ltT ↪ TRefl (shift $k $ltT)
with aux_shift_select_neq (dbsucc $i) (dbsucc $j) $k $gtT $ltT ↪ aux_shift_select_neq $i $j $k $gtT $ltT
with aux_select_neq_Sn db0 $n _ ↪ TRefl (var (dbsucc $n))
with aux_select_neq_Sn (dbsucc _) db0 $gtT ↪ TRefl $gtT
with aux_select_neq_Sn (dbsucc $i) (dbsucc $n) $gtT ↪ TRefl (select_neq $i (dbshift $i $n) $gtT (var (dbsucc (dbshift $i $n))))
with aux_shift_cancel_select_neq db0 $n ↪ TRefl (var $n)
with aux_shift_cancel_select_neq (dbsucc _) db0 ↪ TRefl (var db0)
with aux_shift_cancel_select_neq (dbsucc $i) (dbsucc $n)
  ↪ teq_trans
       (teq_trans
         (aux_select_neq_Sn $i $n (var (dbsucc (dbshift $i $n))))
         (teq_inv (aux_shift_select_neq $i $n db0 (var (dbshift $i $n)) (var (dbprev (dbshift $i $n))))))
       (Jcong Shift (aux_shift_cancel_select_neq $i $n))
;

rule aux_teq_shift_cancel_subst $i $u (var $n)
  ↪ teq_trans
       (aux_teq_shift_neq $i $n $u (var (dbshift $i $n)) (var (dbprev (dbshift $i $n))))
       (aux_shift_cancel_select_neq $i $n)
with aux_teq_shift_cancel_subst $i $u (tabs $A $B $t)
  ↪ Jabs (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $t)
with aux_teq_shift_cancel_subst $i $u (tapp $A $B $f $a)
  ↪ Japp (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
          (aux_teq_shift_cancel_subst $i $u $f)
          (aux_teq_shift_cancel_subst $i $u $a)
with aux_teq_shift_cancel_subst $i $u (tfun $A $B)
  ↪ Jfun (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
with aux_teq_shift_cancel_subst _ _ (tsort $s) ↪ TRefl (tsort $s)
with aux_teq_shift_cancel_subst $i $u (tpair $A $B $a $b)
  ↪ Jpair (aux_teq_shift_cancel_subst $i $u $A)
           (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
           (aux_teq_shift_cancel_subst $i $u $a)
           (aux_teq_shift_cancel_subst $i $u $b)
with aux_teq_shift_cancel_subst $i $u (π1 $A $B $p)
  ↪ Jπ1 (aux_teq_shift_cancel_subst $i $u $A)
         (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
         (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (π2 $A $B $p)
  ↪ Jπ2 (aux_teq_shift_cancel_subst $i $u $A)
         (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
         (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (tsum $A $B)
  ↪ Jsum (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
with aux_teq_shift_cancel_subst $i $u (trefl $A $a)
  ↪ Jrefl (aux_teq_shift_cancel_subst $i $u $A)
           (aux_teq_shift_cancel_subst $i $u $a)
with aux_teq_shift_cancel_subst $i $u (teq $A $a $b)
  ↪ Jteq (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst $i $u $a)
          (aux_teq_shift_cancel_subst $i $u $b);

// teq_subst_subst
symbol aux_teq_subst_subst (i j : DBId) (u t1 t2 : Term) :
  DBLe j i
  → TEq (subst i (Shift* i u) (subst j (Shift* j t1) t2))
        (subst j (subst i (Shift* i u) (Shift* j t1)) (subst (dbsucc i) (Shift* (dbsucc i) u) t2));
symbol aux_teq_subst_subst_rec (i j : DBId) (u t1 t2 : Term) (h : DBLe j i) ≔
  teq_trans
   (aux_teq_subst_subst (dbsucc i) (dbsucc j) u t1 t2 (dble_n_S h))
   (Jcong (λ t, subst (dbsucc j) t (subst (dbsucc (dbsucc i)) (Shift* (dbsucc (dbsucc i)) u) t2))
     (teq_subst_shift i (Shift* i u) (Shift* j t1)));

// aux_teq_subst_subst_var
symbol aux_teq_subst_subst_var (i j : DBId) (u t : Term) (n : DBId) :
  DBLe j i
  → TEq (dbselect j n
                  (subst i (Shift* i u) (Shift* j t))
                  (dbselect i n (Shift* i u) (var n) (var (dbprev n)))
                  (dbselect i (dbprev n) (Shift* i u) (var (dbprev n)) (var (dbprev (dbprev n)))))
        (dbselect (dbsucc i) n
                  (subst j (subst i (Shift* i u) (Shift* j t)) (Shift* (dbsucc i) u))
                  (dbselect j n (subst i (Shift* i u) (Shift* j t)) (var n) (var (dbprev n)))
                  (dbselect j (dbprev n) (subst i (Shift* i u) (Shift* j t)) (var (dbprev n)) (var (dbprev (dbprev n)))));

rule aux_teq_subst_subst_var $i db0 $u $t db0 _
  ↪ TRefl (subst $i (Shift* $i $u) $t)
with aux_teq_subst_subst_var (dbsucc _) (dbsucc _) _ _ db0 _
  ↪ TRefl (var db0)
with aux_teq_subst_subst_var db0 db0 $u _ (dbsucc db0) _
  ↪ TRefl $u
with aux_teq_subst_subst_var (dbsucc _) db0 _ _ (dbsucc db0) _
  ↪ TRefl (var db0)
with aux_teq_subst_subst_var db0 db0 _ _ (dbsucc (dbsucc $n)) _
  ↪ TRefl (var $n)
with aux_teq_subst_subst_var (dbsucc $i) db0 $u $t (dbsucc (dbsucc $n)) _
  ↪ Jselect $i $n
       (teq_inv (aux_teq_shift_cancel_subst db0 (subst (dbsucc $i) (Shift* (dbsucc $i) $u) $t) (Shift* (dbsucc $i) $u)))
       (TRefl (var (dbsucc $n)))
       (TRefl (var $n))
with aux_teq_subst_subst_var (dbsucc $i) (dbsucc $j) $u $t (dbsucc $n) $h
  ↪ teq_trans
       (teq_trans
         (aux_teq_dbselect_fn $j $n
           (subst (dbsucc $i) (Shift* (dbsucc $i) $u) (Shift* (dbsucc $j) $t))
           (dbselect (dbsucc $i) (dbsucc $n) (Shift* (dbsucc $i) $u) (var (dbsucc $n)) (var $n))
           (λ n, dbselect (dbsucc $i) n (Shift* (dbsucc $i) $u) (var n) (var (dbprev n))))
         (teq_trans
           (Jselect $j $n
             (teq_subst_shift $i (Shift* $i $u) (Shift* $j $t))
             (teq_select_shift $i $n (Shift* $i $u))
             (teq_select_shift $i (dbprev $n) (Shift* $i $u)))
           (teq_inv (aux_teq_shift_dbselect0 $j $n
             (subst $i (Shift* $i $u) (Shift* $j $t))
             (dbselect $i $n (Shift* $i $u) (var $n) (var (dbprev $n)))
             (dbselect $i (dbprev $n) (Shift* $i $u) (var (dbprev $n)) (var (dbprev (dbprev $n))))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_subst_var $i $j $u $t $n (dble_S_n $h)))
         (teq_trans
           (aux_teq_shift_dbselect0 (dbsucc $i) $n
             (subst $j (subst $i (Shift* $i $u) (Shift* $j $t)) (Shift* (dbsucc $i) $u))
             (dbselect $j $n (subst $i (Shift* $i $u) (Shift* $j $t)) (var $n) (var (dbprev $n)))
             (dbselect $j (dbprev $n) (subst $i (Shift* $i $u) (Shift* $j $t)) (var (dbprev $n)) (var (dbprev (dbprev $n)))))
           (teq_trans
             (teq_trans
               (Jselect (dbsucc $i) $n
                 (teq_inv (teq_subst_shift $j (subst $i (Shift* $i $u) (Shift* $j $t)) (Shift* (dbsucc $i) $u)))
                 (teq_inv (teq_select_shift $j $n (subst $i (Shift* $i $u) (Shift* $j $t))))
                 (teq_inv (teq_select_shift $j (dbprev $n) (subst $i (Shift* $i $u) (Shift* $j $t)))))
               (teq_inv (aux_teq_dbselect_fn (dbsucc $i) $n
                 (subst (dbsucc $j) (Shift (subst $i (Shift* $i $u) (Shift* $j $t))) (Shift* (dbsucc (dbsucc $i)) $u))
                 (dbselect $j $n (Shift (subst $i (Shift* $i $u) (Shift* $j $t))) (var (dbsucc $n)) (var $n))
                 (λ n, dbselect (dbsucc $j) n (Shift (subst $i (Shift* $i $u) (Shift* $j $t))) (var n) (var (dbprev $n))))))
             (Jcong (λ t, dbselect (dbsucc $i) $n (subst (dbsucc $j) t (Shift* (dbsucc (dbsucc $i)) $u))
                                   (dbselect $j $n t (var (dbsucc $n)) (var $n))
                                   (dbselect (dbsucc $j) $n t (var $n) (var (dbprev $n))))
                    (teq_inv (teq_subst_shift $i (Shift* $i $u) (Shift* $j $t)))))));

rule aux_teq_subst_subst $i $j $u $t1 (var $n) $h
  ↪ teq_trans
       (aux_teq_subst_dbselect $j $n $i (Shift* $i $u) (Shift* $j $t1) (var $n) (var (dbprev $n)))
       (teq_trans
         (aux_teq_subst_subst_var $i $j $u $t1 $n $h)
         (teq_inv (aux_teq_subst_dbselect (dbsucc $i) $n $j
                    (subst $i (Shift* $i $u) (Shift* $j $t1))
                    (Shift* (dbsucc $i) $u)
                    (var $n) (var (dbprev $n)))))
with aux_teq_subst_subst $i $j $u $t1 (tabs $A $B $t) $h
  ↪ Jabs (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $t $h)
with aux_teq_subst_subst $i $j $u $t1 (tapp $A $B $f $a) $h
  ↪ Japp (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
          (aux_teq_subst_subst $i $j $u $t1 $f $h)
          (aux_teq_subst_subst $i $j $u $t1 $a $h)
with aux_teq_subst_subst $i $j $u $t1 (tfun $A $B) $h
  ↪ Jfun (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
with aux_teq_subst_subst _ _ _ _ (tsort $s) _ ↪ TRefl (tsort $s)
with aux_teq_subst_subst $i $j $u $t1 (tpair $A $B $a $b) $h
  ↪ Jpair (aux_teq_subst_subst $i $j $u $t1 $A $h)
           (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
           (aux_teq_subst_subst $i $j $u $t1 $a $h)
           (aux_teq_subst_subst $i $j $u $t1 $b $h)
with aux_teq_subst_subst $i $j $u $t1 (π1 $A $B $p) $h
  ↪ Jπ1 (aux_teq_subst_subst $i $j $u $t1 $A $h)
         (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
         (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (π2 $A $B $p) $h
  ↪ Jπ2 (aux_teq_subst_subst $i $j $u $t1 $A $h)
         (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
         (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (tsum $A $B) $h
  ↪ Jsum (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
with aux_teq_subst_subst $i $j $u $t1 (trefl $A $a) $h
  ↪ Jrefl (aux_teq_subst_subst $i $j $u $t1 $A $h)
           (aux_teq_subst_subst $i $j $u $t1 $a $h)
with aux_teq_subst_subst $i $j $u $t1 (teq $A $a $b) $h
  ↪ Jteq (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst $i $j $u $t1 $a $h)
          (aux_teq_subst_subst $i $j $u $t1 $b $h)
;

// teq_subst_apply
symbol teq_subst_apply (i : DBId) (u t1 t2 : Term) :
  TEq (subst i (Shift* i u) (apply1 t2 t1))
      (apply1 (subst (dbsucc i) (Shift* (dbsucc i) u) t2) (subst i (Shift* i u) t1)) ≔
  aux_teq_subst_subst i db0 u t1 t2 (dble_0_n i);

// teq_shift_cancel_subst
symbol teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift (dbsucc i) (shift i t)))
      (shift i t) ≔
  teq_trans
   (Jcong (subst i u)
     (teq_inv (aux_teq_shift_shift i i t (DBLe_refl i))))
   (aux_teq_shift_cancel_subst i u (shift i t));
