
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
symbol Jpi [A1 A2 B1 B2 : Term] :
  TEq A1 A2 → TEq B1 B2 → TEq (tpi A1 B1) (tpi A2 B2);
symbol Jabs [A1 A2 t1 t2 : Term] :
  TEq A1 A2 → TEq t1 t2 → TEq (tabs A1 t1) (tabs A2 t2);
symbol Japp [f1 f2 a1 a2 : Term] :
  TEq f1 f2 → TEq a1 a2 → TEq (tapp f1 a1) (tapp f2 a2);
symbol Jrec [P1 P2 z1 z2 H1 H2 n1 n2] :
  TEq P1 P2 → TEq z1 z2 → TEq H1 H2 → TEq n1 n2 → TEq (trec P1 z1 H1 n1) (trec P2 z2 H2 n2);
symbol Jsig [A1 A2 B1 B2] :
  TEq A1 A2 → TEq B1 B2 → TEq (tsig A1 B1) (tsig A2 B2);
symbol Jpair [a1 a2 b1 b2 : Term] :
  TEq a1 a2 → TEq b1 b2 → TEq (tpair a1 b1) (tpair a2 b2);
symbol Jsum [A1 A2 B1 B2 : Term] :
  TEq A1 A2 → TEq B1 B2 → TEq (tsum A1 B1) (tsum A2 B2);
symbol Jcase [P1 P2 A1 A2 B1 B2 Ha1 Ha2 Hb1 Hb2 t1 t2] :
  TEq P1 P2 → TEq A1 A2 → TEq B1 B2 → TEq Ha1 Ha2 → TEq Hb1 Hb2 → TEq t1 t2 →
  TEq (tcase P1 A1 B1 Ha1 Hb1 t1) (tcase P2 A2 B2 Ha2 Hb2 t2);
symbol Jpath [A1 A2 x1 x2 y1 y2] :
  TEq A1 A2 → TEq x1 x2 → TEq y1 y2 → TEq (tpath A1 x1 y1) (tpath A2 x2 y2);
symbol JappP [u1 u2 v1 v2] :
  TEq u1 u2 → ITEq v1 v2 → TEq (tappP u1 v1) (tappP u2 v2);
symbol Jsys [f1 f2 g1 g2 u1 u2 v1 v2] :
  FTEq f1 f2 → FTEq g1 g2 → TEq u1 u2 → TEq v1 v2 → TEq (tsys f1 g1 u1 v1) (tsys f2 g2 u2 v2);
symbol Jtransp [A1 A2 f1 f2 u1 u2] :
  TEq A1 A2 → FTEq f1 f2 → TEq u1 u2 → TEq (ttransp A1 f1 u1) (ttransp A2 f2 u2);
symbol Jhcomp [A1 A2 f1 f2 u1 u2 v1 v2] :
  TEq A1 A2 → FTEq f1 f2 → TEq u1 u2 → TEq v1 v2 → TEq (thcomp A1 f1 u1 v1) (thcomp A2 f2 u2 v2);
symbol Jselect [eq1 eq2 gt1 gt2 lt1 lt2 : Term] (i j : DBId) :
  TEq eq1 eq2 → TEq gt1 gt2 → TEq lt1 lt2 →
  TEq (dbselect i j eq1 gt1 lt1) (dbselect i j eq2 gt2 lt2);

rule Jpi (TRefl _) (TRefl _) ↪ TRefl _
with Jabs (TRefl _) (TRefl _) ↪ TRefl _
with Japp (TRefl _) (TRefl _) ↪ TRefl _
with Jrec (TRefl _) (TRefl _) (TRefl _) (TRefl _) ↪ TRefl _
with Jsig (TRefl _) (TRefl _) ↪ TRefl _
with Jpair (TRefl _) (TRefl _) ↪ TRefl _
with Jsum (TRefl _) (TRefl _) ↪ TRefl _
with Jcase (TRefl _) (TRefl _) (TRefl _) (TRefl _) (TRefl _) (TRefl _) ↪ TRefl _
with Jpath (TRefl _) (TRefl _) (TRefl _) ↪ TRefl _
with JappP (TRefl _) (ITRefl _) ↪ TRefl _
with Jsys (FTRefl _) (FTRefl _) (TRefl _) (TRefl _) ↪ TRefl _
with Jtransp (TRefl _) (FTRefl _) (TRefl _) ↪ TRefl _
with Jhcomp (TRefl _) (FTRefl _) (TRefl _) (TRefl _) ↪ TRefl _
with Jselect $i $j (TRefl $eq) (TRefl $gt) (TRefl $lt) ↪ TRefl (dbselect $i $j $eq $gt $lt);

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

// Congruence for interval term equality
symbol IJmin [i1 i2 j1 j2] :
  ITEq i1 i2 → ITEq j1 j2 → ITEq (itmin i1 j1) (itmin i2 j2);
symbol IJmax [i1 i2 j1 j2] :
  ITEq i1 i2 → ITEq j1 j2 → ITEq (itmax i1 j1) (itmax i2 j2);
symbol IJselect [eq1 eq2 gt1 gt2 lt1 lt2 : ITerm] (i j : DBId) :
  ITEq eq1 eq2 → ITEq gt1 gt2 → ITEq lt1 lt2 →
  ITEq (dbselectI i j eq1 gt1 lt1) (dbselectI i j eq2 gt2 lt2);

rule IJmin (ITRefl _) (ITRefl _) ↪ ITRefl _
with IJmax (ITRefl _) (ITRefl _) ↪ ITRefl _
with IJselect _ _ (ITRefl _) (ITRefl _) (ITRefl _) ↪ ITRefl _;

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
symbol IcongF [i j : ITerm] (f : ITerm → FTerm) : ITEq i j → FTEq (f i) (f j);
rule fteq_inv (FTRefl $t) ↪ FTRefl $t
with fteq_trans (FTRefl $t) (FTRefl _) ↪ FTRefl $t
with FJ (FTRefl _) $d ↪ $d
with @FJcong $t _ $f (FTRefl _) ↪ FTRefl ($f $t)
with FJeq (FTRefl _) (FTRefl _) $d ↪ $d
with FJisOne (FTRefl _) $d ↪ $d
with dbcongF $f (DBRefl $i) ↪ FTRefl ($f $i)
with IcongF $f (ITRefl $i) ↪ FTRefl ($f $i);

// Congruence for face term equality
symbol FJmin [i1 i2 j1 j2] :
  FTEq i1 i2 → FTEq j1 j2 → FTEq (ftmin i1 j1) (ftmin i2 j2);
symbol FJmax [i1 i2 j1 j2] :
  FTEq i1 i2 → FTEq j1 j2 → FTEq (ftmax i1 j1) (ftmax i2 j2);
symbol FJselect [eq1 eq2 gt1 gt2 lt1 lt2 : FTerm] (i j : DBId) :
  FTEq eq1 eq2 → FTEq gt1 gt2 → FTEq lt1 lt2 →
  FTEq (dbselectF i j eq1 gt1 lt1) (dbselectF i j eq2 gt2 lt2);

rule FJmin (FTRefl _) (FTRefl _) ↪ FTRefl _
with FJmax (FTRefl _) (FTRefl _) ↪ FTRefl _
with FJselect _ _ (FTRefl _) (FTRefl _) (FTRefl _) ↪ FTRefl _;

// Auxiliary lemmas
// dbselect*_spec_lt
symbol aux_dbselect_spec_lt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc i) j → TEq (dbselect i j eqT gtT ltT) ltT;
rule aux_dbselect_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ TRefl $ltT
with aux_dbselect_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselect_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectI_spec_lt (i j : DBId) (eqT gtT ltT : ITerm) :
  DBLe (dbsucc i) j → ITEq (dbselectI i j eqT gtT ltT) ltT;
rule aux_dbselectI_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ ITRefl $ltT
with aux_dbselectI_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselectI_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectF_spec_lt (i j : DBId) (eqT gtT ltT : FTerm) :
  DBLe (dbsucc i) j → FTEq (dbselectF i j eqT gtT ltT) ltT;
rule aux_dbselectF_spec_lt db0 (dbsucc _) _ _ $ltT _ ↪ FTRefl $ltT
with aux_dbselectF_spec_lt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselectF_spec_lt $i $j $eqT $gtT $ltT (dble_S_n $h);

// dbselect*_spec_gt
symbol aux_dbselect_spec_gt (i j : DBId) (eqT gtT ltT : Term) :
  DBLe (dbsucc j) i → TEq (dbselect i j eqT gtT ltT) gtT;
rule aux_dbselect_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ TRefl $gtT
with aux_dbselect_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselect_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectI_spec_gt (i j : DBId) (eqT gtT ltT : ITerm) :
  DBLe (dbsucc j) i → ITEq (dbselectI i j eqT gtT ltT) gtT;
rule aux_dbselectI_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ ITRefl $gtT
with aux_dbselectI_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselectI_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);
symbol aux_dbselectF_spec_gt (i j : DBId) (eqT gtT ltT : FTerm) :
  DBLe (dbsucc j) i → FTEq (dbselectF i j eqT gtT ltT) gtT;
rule aux_dbselectF_spec_gt (dbsucc _) db0 _ $gtT _ _ ↪ FTRefl $gtT
with aux_dbselectF_spec_gt (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT $h ↪
      aux_dbselectF_spec_gt $i $j $eqT $gtT $ltT (dble_S_n $h);

// teq_shift_shift
symbol aux_teq_shift_shift (i j : DBId) (u : Term) :
  DBLe i j → TEq (shift i (shift j u)) (shift (dbsucc j) (shift i u));
symbol aux_teq_shift_shift_var (i j n : DBId) :
  DBLe i j → DBEq (dbshift i (dbshift j n)) (dbshift (dbsucc j) (dbshift i n));

rule aux_teq_shift_shift_var db0 $j $n _ ↪ DBRefl (dbsucc (dbshift $j $n))
with aux_teq_shift_shift_var (dbsucc _) (dbsucc _) db0 _ ↪ DBRefl db0
with aux_teq_shift_shift_var (dbsucc $i) (dbsucc $j) (dbsucc $n) $h ↪
      dbcong dbsucc (aux_teq_shift_shift_var $i $j $n (dble_S_n $h))
with aux_teq_shift_shift $i $j (tvar $n) $h ↪ dbcongT tvar (aux_teq_shift_shift_var $i $j $n $h)
with aux_teq_shift_shift _ _ (tuniv _) _ ↪ TRefl _
with aux_teq_shift_shift _ _ (tpi $A $B) $h ↪
      Jpi (aux_teq_shift_shift _ _ $A $h)
          (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (tabs $A $t) $h ↪
      Jabs (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $t (dble_n_S $h))
with aux_teq_shift_shift _ _ (tapp $f $a) $h ↪
      Japp (aux_teq_shift_shift _ _ $f $h)
           (aux_teq_shift_shift _ _ $a $h)
with aux_teq_shift_shift _ _ tnat _ ↪ TRefl _
with aux_teq_shift_shift _ _ tzero _ ↪ TRefl _
with aux_teq_shift_shift _ _ (tsuc $n) $h ↪ Jcong tsuc (aux_teq_shift_shift _ _ $n $h)
with aux_teq_shift_shift _ _ (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_shift_shift _ _ $P $h)
           (aux_teq_shift_shift _ _ $z $h)
           (aux_teq_shift_shift _ _ $H $h)
           (aux_teq_shift_shift _ _ $n $h)
with aux_teq_shift_shift _ _ (tsig $A $B) $h ↪
      Jsig (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $B (dble_n_S $h))
with aux_teq_shift_shift _ _ (tpair $a $b) $h ↪
      Jpair (aux_teq_shift_shift _ _ $a $h)
            (aux_teq_shift_shift _ _ $b $h)
with aux_teq_shift_shift _ _ (tp1 $p) $h ↪
      Jcong tp1 (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tp2 $p) $h ↪
      Jcong tp2 (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tsum $A $B) $h ↪
      Jsum (aux_teq_shift_shift _ _ $A $h)
           (aux_teq_shift_shift _ _ $B $h)
with aux_teq_shift_shift _ _ (tinjl $p) $h ↪
      Jcong tinjl (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tinjr $p) $h ↪
      Jcong tinjr (aux_teq_shift_shift _ _ $p $h)
with aux_teq_shift_shift _ _ (tcase $P $A $B $Ha $Hb $n) $h ↪
      Jcase (aux_teq_shift_shift _ _ $P $h)
            (aux_teq_shift_shift _ _ $A $h)
            (aux_teq_shift_shift _ _ $B $h)
            (aux_teq_shift_shift _ _ $Ha $h)
            (aux_teq_shift_shift _ _ $Hb $h)
            (aux_teq_shift_shift _ _ $n $h)
with aux_teq_shift_shift _ _ (tpath $A $x $y) $h ↪
      Jpath (aux_teq_shift_shift _ _ $A $h)
            (aux_teq_shift_shift _ _ $x $h)
            (aux_teq_shift_shift _ _ $y $h)
with aux_teq_shift_shift _ _ (tlamP $t) $h ↪
      Jcong tlamP (aux_teq_shift_shift _ _ $t $h)
with aux_teq_shift_shift _ _ (tappP $u _) $h ↪
      JappP (aux_teq_shift_shift _ _ $u $h) (ITRefl _)
with aux_teq_shift_shift _ _ (tsys _ _ $u $v) $h ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_shift_shift _ _ $u $h)
           (aux_teq_shift_shift _ _ $v $h)
with aux_teq_shift_shift _ _ temptysys _ ↪ TRefl _
with aux_teq_shift_shift _ _ (ttransp $A _ $u) $h ↪
      Jtransp (aux_teq_shift_shift _ _ $A $h)
              (FTRefl _)
              (aux_teq_shift_shift _ _ $u $h)
with aux_teq_shift_shift _ _ (thcomp $A _ $u $v) $h ↪
      Jhcomp (aux_teq_shift_shift _ _ $A $h)
             (FTRefl _)
             (aux_teq_shift_shift _ _ $u $h)
             (aux_teq_shift_shift _ _ $v $h);

// teq_Ishift_Ishift
symbol aux_teq_Ishift_Ishift (i j : DBId) (u : Term) :
  DBLe i j → TEq (Ishift i (Ishift j u)) (Ishift (dbsucc j) (Ishift i u));
symbol aux_teq_IshiftI_IshiftI (i j : DBId) (u : ITerm) :
  DBLe i j → ITEq (IshiftI i (IshiftI j u)) (IshiftI (dbsucc j) (IshiftI i u));
symbol aux_teq_IshiftF_IshiftF (i j : DBId) (u : FTerm) :
  DBLe i j → FTEq (IshiftF i (IshiftF j u)) (IshiftF (dbsucc j) (IshiftF i u));

rule aux_teq_Ishift_Ishift _ _ (tvar _) _ ↪ TRefl _
with aux_teq_Ishift_Ishift _ _ (tuniv _) _ ↪ TRefl _
with aux_teq_Ishift_Ishift _ _ (tpi $A $B) $h ↪
      Jpi (aux_teq_Ishift_Ishift _ _ $A $h)
          (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ (tabs $A $B) $h ↪
      Jabs (aux_teq_Ishift_Ishift _ _ $A $h)
           (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ (tapp $A $B) $h ↪
      Japp (aux_teq_Ishift_Ishift _ _ $A $h)
           (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ tnat _ ↪ TRefl _
with aux_teq_Ishift_Ishift _ _ tzero _ ↪ TRefl _
with aux_teq_Ishift_Ishift _ _ (tsuc $s) $h ↪
      Jcong tsuc (aux_teq_Ishift_Ishift _ _ $s $h)
with aux_teq_Ishift_Ishift _ _ (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_Ishift_Ishift _ _ $P $h)
           (aux_teq_Ishift_Ishift _ _ $z $h)
           (aux_teq_Ishift_Ishift _ _ $H $h)
           (aux_teq_Ishift_Ishift _ _ $n $h)
with aux_teq_Ishift_Ishift _ _ (tsig $A $B) $h ↪
      Jsig (aux_teq_Ishift_Ishift _ _ $A $h)
           (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ (tpair $A $B) $h ↪
      Jpair (aux_teq_Ishift_Ishift _ _ $A $h)
            (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ (tp1 $s) $h ↪
      Jcong tp1 (aux_teq_Ishift_Ishift _ _ $s $h)
with aux_teq_Ishift_Ishift _ _ (tp2 $s) $h ↪
      Jcong tp2 (aux_teq_Ishift_Ishift _ _ $s $h)
with aux_teq_Ishift_Ishift _ _ (tsum $A $B) $h ↪
      Jsum (aux_teq_Ishift_Ishift _ _ $A $h)
           (aux_teq_Ishift_Ishift _ _ $B $h)
with aux_teq_Ishift_Ishift _ _ (tinjl $s) $h ↪
      Jcong tinjl (aux_teq_Ishift_Ishift _ _ $s $h)
with aux_teq_Ishift_Ishift _ _ (tinjr $s) $h ↪
      Jcong tinjr (aux_teq_Ishift_Ishift _ _ $s $h)
with aux_teq_Ishift_Ishift _ _ (tcase $P $A $B $Ha $Hb $t) $h ↪
      Jcase (aux_teq_Ishift_Ishift _ _ $P $h)
            (aux_teq_Ishift_Ishift _ _ $A $h)
            (aux_teq_Ishift_Ishift _ _ $B $h)
            (aux_teq_Ishift_Ishift _ _ $Ha $h)
            (aux_teq_Ishift_Ishift _ _ $Hb $h)
            (aux_teq_Ishift_Ishift _ _ $t $h)
with aux_teq_Ishift_Ishift _ _ (tpath $A $x $y) $h ↪
      Jpath (aux_teq_Ishift_Ishift _ _ $A (dble_n_S $h))
            (aux_teq_Ishift_Ishift _ _ $x $h)
            (aux_teq_Ishift_Ishift _ _ $y $h)
with aux_teq_Ishift_Ishift _ _ (tlamP $s) $h ↪
      Jcong tlamP (aux_teq_Ishift_Ishift _ _ $s (dble_n_S $h))
with aux_teq_Ishift_Ishift _ _ (tappP $u $v) $h ↪
      JappP (aux_teq_Ishift_Ishift _ _ $u $h)
            (aux_teq_IshiftI_IshiftI _ _ $v $h)
with aux_teq_Ishift_Ishift _ _ (tsys $f $g $u $v) $h ↪
      Jsys (aux_teq_IshiftF_IshiftF _ _ $f $h)
           (aux_teq_IshiftF_IshiftF _ _ $g $h)
           (aux_teq_Ishift_Ishift _ _ $u $h)
           (aux_teq_Ishift_Ishift _ _ $v $h)
with aux_teq_Ishift_Ishift _ _ temptysys _ ↪ TRefl _
with aux_teq_Ishift_Ishift _ _ (ttransp $A $f $u) $h ↪
      Jtransp (aux_teq_Ishift_Ishift _ _ $A (dble_n_S $h))
              (aux_teq_IshiftF_IshiftF _ _ $f $h)
              (aux_teq_Ishift_Ishift _ _ $u $h)
with aux_teq_Ishift_Ishift _ _ (thcomp $A $f $u $v) $h ↪
      Jhcomp (aux_teq_Ishift_Ishift _ _ $A $h)
             (aux_teq_IshiftF_IshiftF _ _ $f $h)
             (aux_teq_Ishift_Ishift _ _ $u (dble_n_S $h))
             (aux_teq_Ishift_Ishift _ _ $v $h)
with aux_teq_IshiftI_IshiftI _ _ it0 _ ↪ ITRefl _
with aux_teq_IshiftI_IshiftI _ _ it1 _ ↪ ITRefl _
with aux_teq_IshiftI_IshiftI _ _ (itvar $id) $h ↪
      dbcongI itvar (aux_teq_shift_shift_var _ _ $id $h)
with aux_teq_IshiftI_IshiftI _ _ (itsym $i) $h ↪
      IJcong itsym (aux_teq_IshiftI_IshiftI _ _ $i $h)
with aux_teq_IshiftI_IshiftI _ _ (itmin $i $j) $h ↪
      IJmin (aux_teq_IshiftI_IshiftI _ _ $i $h)
            (aux_teq_IshiftI_IshiftI _ _ $j $h)
with aux_teq_IshiftI_IshiftI _ _ (itmax $i $j) $h ↪
      IJmax (aux_teq_IshiftI_IshiftI _ _ $i $h)
            (aux_teq_IshiftI_IshiftI _ _ $j $h)
with aux_teq_IshiftF_IshiftF _ _ ft0 _ ↪ FTRefl _
with aux_teq_IshiftF_IshiftF _ _ ft1 _ ↪ FTRefl _
with aux_teq_IshiftF_IshiftF _ _ (fteq0 $id) $h ↪
      dbcongF fteq0 (aux_teq_shift_shift_var _ _ $id $h)
with aux_teq_IshiftF_IshiftF _ _ (fteq1 $id) $h ↪
      dbcongF fteq1 (aux_teq_shift_shift_var _ _ $id $h)
with aux_teq_IshiftF_IshiftF _ _ (ftmin $i $j) $h ↪
      FJmin (aux_teq_IshiftF_IshiftF _ _ $i $h)
            (aux_teq_IshiftF_IshiftF _ _ $j $h)
with aux_teq_IshiftF_IshiftF _ _ (ftmax $i $j) $h ↪
      FJmax (aux_teq_IshiftF_IshiftF _ _ $i $h)
            (aux_teq_IshiftF_IshiftF _ _ $j $h);

// teq_shift_shift0
symbol aux_teq_shift_shift0 (i : DBId) (u : Term) :
  TEq (Shift (shift i u)) (shift (dbsucc i) (Shift u)) ≔
  aux_teq_shift_shift db0 i u (dble_0_n i);
symbol aux_teq_Ishift_Ishift0 (i : DBId) (u : Term) :
  TEq (IShift (Ishift i u)) (Ishift (dbsucc i) (IShift u)) ≔
  aux_teq_Ishift_Ishift db0 i u (dble_0_n i);

// teq_shift_shiftI
symbol aux_teq_shift_Ishift (i j : DBId) (u : Term) :
  TEq (shift i (Ishift j u)) (Ishift j (shift i u));

rule aux_teq_shift_Ishift _ _ (tvar _) ↪ TRefl _
with aux_teq_shift_Ishift _ _ (tuniv _) ↪ TRefl _
with aux_teq_shift_Ishift $i $j (tpi $A $B) ↪
      Jpi (aux_teq_shift_Ishift $i $j $A)
          (aux_teq_shift_Ishift (dbsucc $i) $j $B)
with aux_teq_shift_Ishift $i $j (tabs $A $t) ↪
      Jabs (aux_teq_shift_Ishift $i $j $A)
           (aux_teq_shift_Ishift (dbsucc $i) $j $t)
with aux_teq_shift_Ishift $i $j (tapp $f $a) ↪
      Japp (aux_teq_shift_Ishift $i $j $f)
           (aux_teq_shift_Ishift $i $j $a)
with aux_teq_shift_Ishift _ _ tnat ↪ TRefl _
with aux_teq_shift_Ishift _ _ tzero ↪ TRefl _
with aux_teq_shift_Ishift $i $j (tsuc $n) ↪
      Jcong tsuc (aux_teq_shift_Ishift $i $j $n)
with aux_teq_shift_Ishift $i $j (trec $P $z $H $n) ↪
      Jrec (aux_teq_shift_Ishift $i $j $P)
           (aux_teq_shift_Ishift $i $j $z)
           (aux_teq_shift_Ishift $i $j $H)
           (aux_teq_shift_Ishift $i $j $n)
with aux_teq_shift_Ishift $i $j (tsig $A $B) ↪
      Jsig (aux_teq_shift_Ishift $i $j $A)
           (aux_teq_shift_Ishift (dbsucc $i) $j $B)
with aux_teq_shift_Ishift $i $j (tpair $a $b) ↪
      Jpair (aux_teq_shift_Ishift $i $j $a)
            (aux_teq_shift_Ishift $i $j $b)
with aux_teq_shift_Ishift $i $j (tp1 $p) ↪
      Jcong tp1 (aux_teq_shift_Ishift $i $j $p)
with aux_teq_shift_Ishift $i $j (tp2 $p) ↪
      Jcong tp2 (aux_teq_shift_Ishift $i $j $p)
with aux_teq_shift_Ishift $i $j (tsum $A $B) ↪
      Jsum (aux_teq_shift_Ishift $i $j $A)
           (aux_teq_shift_Ishift $i $j $B)
with aux_teq_shift_Ishift $i $j (tinjl $p) ↪
      Jcong tinjl (aux_teq_shift_Ishift $i $j $p)
with aux_teq_shift_Ishift $i $j (tinjr $p) ↪
      Jcong tinjr (aux_teq_shift_Ishift $i $j $p)
with aux_teq_shift_Ishift $i $j (tcase $P $A $B $Ha $Hb $n) ↪
      Jcase (aux_teq_shift_Ishift $i $j $P)
            (aux_teq_shift_Ishift $i $j $A)
            (aux_teq_shift_Ishift $i $j $B)
            (aux_teq_shift_Ishift $i $j $Ha)
            (aux_teq_shift_Ishift $i $j $Hb)
            (aux_teq_shift_Ishift $i $j $n)
with aux_teq_shift_Ishift $i $j (tpath $A $x $y) ↪
      Jpath (aux_teq_shift_Ishift $i (dbsucc $j) $A)
            (aux_teq_shift_Ishift $i $j $x)
            (aux_teq_shift_Ishift $i $j $y)
with aux_teq_shift_Ishift $i $j (tlamP $t) ↪
      Jcong tlamP (aux_teq_shift_Ishift $i (dbsucc $j) $t)
with aux_teq_shift_Ishift $i $j (tappP $u _) ↪
      JappP (aux_teq_shift_Ishift $i $j $u) (ITRefl _)
with aux_teq_shift_Ishift $i $j (tsys _ _ $u $v) ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_shift_Ishift $i $j $u)
           (aux_teq_shift_Ishift $i $j $v)
with aux_teq_shift_Ishift _ _ temptysys ↪ TRefl _
with aux_teq_shift_Ishift $i $j (ttransp $A _ $u) ↪
      Jtransp (aux_teq_shift_Ishift $i (dbsucc $j) $A)
              (FTRefl _)
              (aux_teq_shift_Ishift $i $j $u)
with aux_teq_shift_Ishift $i $j (thcomp $A _ $u $v) ↪
      Jhcomp (aux_teq_shift_Ishift $i $j $A)
             (FTRefl _)
             (aux_teq_shift_Ishift $i (dbsucc $j) $u)
             (aux_teq_shift_Ishift $i $j $v);

symbol aux_teq_Shift*_Ishift (i j : DBId) (u : Term) :
  TEq (Shift* i (Ishift j u)) (Ishift j (Shift* i u));

rule aux_teq_Shift*_Ishift db0 _ _ ↪ TRefl _
with aux_teq_Shift*_Ishift (dbsucc $i) $j $u ↪
    teq_trans (Jcong Shift (aux_teq_Shift*_Ishift $i $j $u)) (aux_teq_shift_Ishift db0 $j (Shift* $i $u));

// teq_shift_dbselect
symbol aux_teq_shift_dbselect (n i j : DBId) (eqT gtT ltT : Term) :
  TEq (shift n (dbselect i j eqT gtT ltT))
      (dbselect i j (shift n eqT) (shift n gtT) (shift n ltT));
rule aux_teq_shift_dbselect $n db0        db0 $eqT _ _ ↪ TRefl (shift $n $eqT)
with aux_teq_shift_dbselect $n (dbsucc _) db0 _ $gtT _ ↪ TRefl (shift $n $gtT)
with aux_teq_shift_dbselect $n db0 (dbsucc _) _ _ $ltT ↪ TRefl (shift $n $ltT)
with aux_teq_shift_dbselect $n (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT ↪
      aux_teq_shift_dbselect $n $i $j $eqT $gtT $ltT;

// teq_shift_dbselect0
symbol aux_teq_shift_dbselect0 (i j : DBId) (eqT gtT ltT : Term) :
  TEq (Shift (dbselect i j eqT gtT ltT))
      (dbselect i j (Shift eqT) (Shift gtT) (Shift ltT)) ≔
  aux_teq_shift_dbselect db0 i j eqT gtT ltT;

// teq_Ishift_dbselect
symbol aux_teq_Ishift_dbselect (n i j : DBId) (eqT gtT ltT : Term) :
  TEq (Ishift n (dbselect i j eqT gtT ltT))
      (dbselect i j (Ishift n eqT) (Ishift n gtT) (Ishift n ltT));
rule aux_teq_Ishift_dbselect $n db0        db0 $eqT _ _ ↪ TRefl (Ishift $n $eqT)
with aux_teq_Ishift_dbselect $n (dbsucc _) db0 _ $gtT _ ↪ TRefl (Ishift $n $gtT)
with aux_teq_Ishift_dbselect $n db0 (dbsucc _) _ _ $ltT ↪ TRefl (Ishift $n $ltT)
with aux_teq_Ishift_dbselect $n (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT ↪
      aux_teq_Ishift_dbselect $n $i $j $eqT $gtT $ltT;

// teq_shift_dbselect0
symbol aux_teq_Ishift_dbselect0 (i j : DBId) (eqT gtT ltT : Term) :
  TEq (IShift (dbselect i j eqT gtT ltT))
      (dbselect i j (IShift eqT) (IShift gtT) (IShift ltT)) ≔
  aux_teq_Ishift_dbselect db0 i j eqT gtT ltT;

// teq_shift_dbselectI
symbol aux_teq_shift_dbselectI (n i j : DBId) (eqT gtT ltT : ITerm) :
  ITEq (IshiftI n (dbselectI i j eqT gtT ltT))
      (dbselectI i j (IshiftI n eqT) (IshiftI n gtT) (IshiftI n ltT));
rule aux_teq_shift_dbselectI _ db0        db0 _ _ _ ↪ ITRefl _
with aux_teq_shift_dbselectI _ (dbsucc _) db0 _ _ _ ↪ ITRefl _
with aux_teq_shift_dbselectI _ db0 (dbsucc _) _ _ _ ↪ ITRefl _
with aux_teq_shift_dbselectI $n (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT ↪
      aux_teq_shift_dbselectI $n $i $j $eqT $gtT $ltT;

// teq_shift_dbselectI0
symbol aux_teq_shift_dbselectI0 (i j : DBId) (eqT gtT ltT : ITerm) :
  ITEq (IShiftI (dbselectI i j eqT gtT ltT))
       (dbselectI i j (IShiftI eqT) (IShiftI gtT) (IShiftI ltT)) ≔
  aux_teq_shift_dbselectI db0 i j eqT gtT ltT;

// teq_shift_dbselectF
symbol aux_teq_shift_dbselectF (n i j : DBId) (eqT gtT ltT : FTerm) :
  FTEq (IshiftF n (dbselectF i j eqT gtT ltT))
      (dbselectF i j (IshiftF n eqT) (IshiftF n gtT) (IshiftF n ltT));
rule aux_teq_shift_dbselectF _ db0        db0 _ _ _ ↪ FTRefl _
with aux_teq_shift_dbselectF _ (dbsucc _) db0 _ _ _ ↪ FTRefl _
with aux_teq_shift_dbselectF _ db0 (dbsucc _) _ _ _ ↪ FTRefl _
with aux_teq_shift_dbselectF $n (dbsucc $i) (dbsucc $j) $eqT $gtT $ltT ↪
      aux_teq_shift_dbselectF $n $i $j $eqT $gtT $ltT;

// teq_shift_dbselectF0
symbol aux_teq_shift_dbselectF0 (i j : DBId) (eqT gtT ltT : FTerm) :
  FTEq (IShiftF (dbselectF i j eqT gtT ltT))
       (dbselectF i j (IShiftF eqT) (IShiftF gtT) (IShiftF ltT)) ≔
  aux_teq_shift_dbselectF db0 i j eqT gtT ltT;

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
  TEq (dbselect i n eqT gtT (tvar n))
      (dbselect i n eqT gtT (tvar (dbsucc (dbprev n)))) ≔
  aux_teq_dbselect_fn i n eqT gtT tvar;

// teq_dbselectI_fn
symbol aux_teq_dbselectI_fn (i n : DBId) (eqT gtT : ITerm) (f : DBId → ITerm) :
  ITEq (dbselectI i n eqT gtT (f n))
       (dbselectI i n eqT gtT (f (dbsucc (dbprev n))));
rule aux_teq_dbselectI_fn db0 db0 $eqT _ _ ↪ ITRefl $eqT
with aux_teq_dbselectI_fn (dbsucc _) db0 _ $gtT _ ↪ ITRefl $gtT
with aux_teq_dbselectI_fn db0 (dbsucc $n) _ _ $f ↪ ITRefl ($f (dbsucc $n))
with aux_teq_dbselectI_fn (dbsucc $i) (dbsucc $n) $eqT $gtT $f ↪ ITRefl (dbselectI $i $n $eqT $gtT ($f (dbsucc $n)));

// teq_dbselect_Sn
symbol aux_teq_dbselectI_Sn (i n : DBId) (eqT gtT : ITerm) :
  ITEq (dbselectI i n eqT gtT (itvar n))
       (dbselectI i n eqT gtT (itvar (dbsucc (dbprev n)))) ≔
  aux_teq_dbselectI_fn i n eqT gtT itvar;

// teq_dbselectF_fn
symbol aux_teq_dbselectF_fn (i n : DBId) (eqT gtT : FTerm) (f : DBId → FTerm) :
  FTEq (dbselectF i n eqT gtT (f n))
       (dbselectF i n eqT gtT (f (dbsucc (dbprev n))));
rule aux_teq_dbselectF_fn db0 db0 $eqT _ _ ↪ FTRefl $eqT
with aux_teq_dbselectF_fn (dbsucc _) db0 _ $gtT _ ↪ FTRefl $gtT
with aux_teq_dbselectF_fn db0 (dbsucc $n) _ _ $f ↪ FTRefl ($f (dbsucc $n))
with aux_teq_dbselectF_fn (dbsucc $i) (dbsucc $n) $eqT $gtT $f ↪ FTRefl (dbselectF $i $n $eqT $gtT ($f (dbsucc $n)));

// teq_dbselectF_Sn0
symbol aux_teq_dbselectF_Sn0 (i n : DBId) (eqT gtT : FTerm) :
  FTEq (dbselectF i n eqT gtT (fteq0 n))
       (dbselectF i n eqT gtT (fteq0 (dbsucc (dbprev n)))) ≔
  aux_teq_dbselectF_fn i n eqT gtT fteq0;
// teq_dbselectF_Sn1
symbol aux_teq_dbselectF_Sn1 (i n : DBId) (eqT gtT : FTerm) :
  FTEq (dbselectF i n eqT gtT (fteq1 n))
       (dbselectF i n eqT gtT (fteq1 (dbsucc (dbprev n)))) ≔
  aux_teq_dbselectF_fn i n eqT gtT fteq1;

// teq_shift_substeq*
symbol aux_teq_Ishift_substeq0 (i : DBId) (u : ITerm) :
  FTEq (substeq0 (IshiftI i u)) (IshiftF i (substeq0 u));
symbol aux_teq_Ishift_substeq1 (i : DBId) (u : ITerm) :
  FTEq (substeq1 (IshiftI i u)) (IshiftF i (substeq1 u));
rule aux_teq_Ishift_substeq0 _ it0 ↪ FTRefl _
with aux_teq_Ishift_substeq0 _ it1 ↪ FTRefl _
with aux_teq_Ishift_substeq0 _ (itvar _) ↪ FTRefl _
with aux_teq_Ishift_substeq0 $i (itsym $u) ↪ aux_teq_Ishift_substeq1 $i $u
with aux_teq_Ishift_substeq0 $i (itmin $x $y) ↪
      FJmax (aux_teq_Ishift_substeq0 $i $x)
            (aux_teq_Ishift_substeq0 $i $y)
with aux_teq_Ishift_substeq0 $i (itmax $x $y) ↪
      FJmin (aux_teq_Ishift_substeq0 $i $x)
            (aux_teq_Ishift_substeq0 $i $y)
with aux_teq_Ishift_substeq1 _ it0 ↪ FTRefl _
with aux_teq_Ishift_substeq1 _ it1 ↪ FTRefl _
with aux_teq_Ishift_substeq1 _ (itvar _) ↪ FTRefl _
with aux_teq_Ishift_substeq1 $i (itsym $u) ↪ aux_teq_Ishift_substeq0 $i $u
with aux_teq_Ishift_substeq1 $i (itmin $x $y) ↪
      FJmin (aux_teq_Ishift_substeq1 $i $x)
            (aux_teq_Ishift_substeq1 $i $y)
with aux_teq_Ishift_substeq1 $i (itmax $x $y) ↪
      FJmax (aux_teq_Ishift_substeq1 $i $x)
            (aux_teq_Ishift_substeq1 $i $y);

symbol aux_teq_IShift*_substeq0 (i : DBId) (u : ITerm) :
  FTEq (substeq0 (IShiftI* i u)) (IShiftF* i (substeq0 u));
symbol aux_teq_IShift*_substeq1 (i : DBId) (u : ITerm) :
  FTEq (substeq1 (IShiftI* i u)) (IShiftF* i (substeq1 u));
rule aux_teq_IShift*_substeq0 db0 _ ↪ FTRefl _
with aux_teq_IShift*_substeq0 (dbsucc $i) $u ↪
      fteq_trans (aux_teq_Ishift_substeq0 db0 (IShiftI* $i $u))
                 (FJcong IShiftF (aux_teq_IShift*_substeq0 $i $u))
with aux_teq_IShift*_substeq1 db0 _ ↪ FTRefl _
with aux_teq_IShift*_substeq1 (dbsucc $i) $u ↪
      fteq_trans (aux_teq_Ishift_substeq1 db0 (IShiftI* $i $u))
                 (FJcong IShiftF (aux_teq_IShift*_substeq1 $i $u));

// teq_select_substeq*
symbol aux_teq_select_substeq0 (i j : DBId) (eq gt lt : ITerm) :
  FTEq (substeq0 (dbselectI i j eq gt lt)) (dbselectF i j (substeq0 eq) (substeq0 gt) (substeq0 lt));
rule aux_teq_select_substeq0 db0 db0 $eq _ _ ↪ FTRefl (substeq0 $eq)
with aux_teq_select_substeq0 (dbsucc _) db0 _ $gt _ ↪ FTRefl (substeq0 $gt)
with aux_teq_select_substeq0 db0 (dbsucc _)  _ _ $lt ↪ FTRefl (substeq0 $lt)
with aux_teq_select_substeq0 (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪
      aux_teq_select_substeq0 $i $j $eq $gt $lt;
symbol aux_teq_select_substeq1 (i j : DBId) (eq gt lt : ITerm) :
  FTEq (substeq1 (dbselectI i j eq gt lt)) (dbselectF i j (substeq1 eq) (substeq1 gt) (substeq1 lt));
rule aux_teq_select_substeq1 db0 db0 $eq _ _ ↪ FTRefl (substeq1 $eq)
with aux_teq_select_substeq1 (dbsucc _) db0 _ $gt _ ↪ FTRefl (substeq1 $gt)
with aux_teq_select_substeq1 db0 (dbsucc _)  _ _ $lt ↪ FTRefl (substeq1 $lt)
with aux_teq_select_substeq1 (dbsucc $i) (dbsucc $j) $eq $gt $lt ↪
      aux_teq_select_substeq1 $i $j $eq $gt $lt;

// teq_subst_substeq*
symbol aux_teq_Isubst_substeq0 (i : DBId) (t u : ITerm) :
  FTEq (substeq0 (IsubstI i t u)) (IsubstF i t (substeq0 u));
symbol aux_teq_Isubst_substeq1 (i : DBId) (t u : ITerm) :
  FTEq (substeq1 (IsubstI i t u)) (IsubstF i t (substeq1 u));
rule aux_teq_Isubst_substeq0 _ _ it0 ↪ FTRefl _
with aux_teq_Isubst_substeq0 _ _ it1 ↪ FTRefl _
with aux_teq_Isubst_substeq0 $i $t (itvar $j) ↪
      aux_teq_select_substeq0 $i $j $t (itvar $j) (itvar (dbprev $j))
with aux_teq_Isubst_substeq0 $i $t (itsym $u) ↪ aux_teq_Isubst_substeq1 $i $t $u
with aux_teq_Isubst_substeq0 $i $t (itmin $x $y) ↪
      FJmax (aux_teq_Isubst_substeq0 $i $t $x)
            (aux_teq_Isubst_substeq0 $i $t $y)
with aux_teq_Isubst_substeq0 $i $t (itmax $x $y) ↪
      FJmin (aux_teq_Isubst_substeq0 $i $t $x)
            (aux_teq_Isubst_substeq0 $i $t $y)
with aux_teq_Isubst_substeq1 _ _ it0 ↪ FTRefl _
with aux_teq_Isubst_substeq1 _ _ it1 ↪ FTRefl _
with aux_teq_Isubst_substeq1 $i $t (itvar $j) ↪
      aux_teq_select_substeq1 $i $j $t (itvar $j) (itvar (dbprev $j))
with aux_teq_Isubst_substeq1 $i $t (itsym $u) ↪ aux_teq_Isubst_substeq0 $i $t $u
with aux_teq_Isubst_substeq1 $i $t (itmin $x $y) ↪
      FJmin (aux_teq_Isubst_substeq1 $i $t $x)
            (aux_teq_Isubst_substeq1 $i $t $y)
with aux_teq_Isubst_substeq1 $i $t (itmax $x $y) ↪
      FJmax (aux_teq_Isubst_substeq1 $i $t $x)
            (aux_teq_Isubst_substeq1 $i $t $y);

// teq_subst_shift
symbol aux_teq_subst_shift (i j : DBId) (u t : Term) :
  DBLe j i →
  TEq (subst (dbsucc i) (shift j (Shift* j u)) (shift j t))
      (shift j (subst i (Shift* j u) t));
// teq_subst_shift_var
symbol aux_teq_subst_shift_var (i j : DBId) (u : Term) (n : DBId) :
  DBLe j i →
  TEq (dbselect (dbsucc i) (dbshift j n) (shift j (Shift* j u)) (tvar (dbshift j n)) (tvar (dbprev (dbshift j n))))
      (dbselect i n (shift j (Shift* j u)) (tvar (dbshift j n)) (tvar (dbshift j (dbprev n))));

symbol aux_teq_subst_shift_Ishift (i j : DBId) (u t : Term) (h : DBLe j i) :
  TEq (subst (dbsucc i) (IShift (shift j (Shift* j u))) (shift j t))
      (shift j (subst i (IShift (Shift* j u)) t)) ≔
  teq_trans (Jcong (λ u1, subst (dbsucc i) u1 (shift j t))
                   (teq_inv (aux_teq_shift_Ishift j db0 (Shift* j u))))
            (teq_trans (Jcong (λ u1, subst (dbsucc i) (shift j u1) (shift j t))
                              (teq_inv (aux_teq_Shift*_Ishift j db0 u)))
                       (teq_trans (aux_teq_subst_shift i j (IShift u) t h)
                                  (Jcong (λ u1, shift j (subst i u1 t))
                                         (aux_teq_Shift*_Ishift j db0 u))));

rule aux_teq_subst_shift_var $i db0 $u $n _ ↪
      aux_teq_dbselect_Sn $i $n (shift db0 $u) (tvar (dbsucc $n))
with aux_teq_subst_shift_var (dbsucc _) (dbsucc _) _ db0 _ ↪
      TRefl (tvar db0)
with aux_teq_subst_shift_var (dbsucc db0) (dbsucc $j) $u (dbsucc db0) $h ↪
      teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc db0) (dbshift $j db0) (shift (dbsucc $j) (Shift* (dbsucc $j) $u))
                              (tvar (dbsucc (dbshift $j db0))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc db0) (dbshift $j db0) (shift $j (Shift* $j $u))
                                           (tvar (dbshift $j db0)) (tvar (dbprev (dbshift $j db0))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var db0 $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselect0 db0 db0 (shift $j (Shift* $j $u)) (tvar (dbshift $j db0))
                                  (tvar (dbshift $j (dbprev db0)))))
with aux_teq_subst_shift_var (dbsucc (dbsucc $i)) (dbsucc $j) $u (dbsucc db0) $h ↪
      teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc (dbsucc $i)) (dbshift $j db0) (shift (dbsucc $j) (Shift* (dbsucc $j) $u))
                              (tvar (dbsucc (dbshift $j db0))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc (dbsucc $i)) (dbshift $j db0) (shift $j (Shift* $j $u))
                                           (tvar (dbshift $j db0)) (tvar (dbprev (dbshift $j db0))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var (dbsucc $i) $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselect0 (dbsucc $i) db0 (shift $j (Shift* $j $u))
                                  (tvar (dbshift $j db0)) (tvar (dbshift $j (dbprev db0)))))
with aux_teq_subst_shift_var (dbsucc $i) (dbsucc $j) $u (dbsucc (dbsucc $n)) $h ↪
      teq_trans
       (teq_trans
         (aux_teq_dbselect_Sn (dbsucc $i) (dbshift $j (dbsucc $n)) (shift (dbsucc $j) (Shift* (dbsucc $j) $u))
                              (tvar (dbsucc (dbshift $j (dbsucc $n)))))
         (teq_inv (aux_teq_shift_dbselect0 (dbsucc $i) (dbshift $j (dbsucc $n)) (shift $j (Shift* $j $u))
                                           (tvar (dbshift $j (dbsucc $n)))
                                           (tvar (dbprev (dbshift $j (dbsucc $n)))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_shift_var $i $j $u (dbsucc $n) (dble_S_n $h)))
         (aux_teq_shift_dbselect0 $i (dbsucc $n) (shift $j (Shift* $j $u))
                                     (tvar (dbshift $j (dbsucc $n))) (tvar (dbshift $j ($n)))));

rule aux_teq_subst_shift $i $j $u (tvar $n) $h ↪
      teq_trans
       (aux_teq_subst_shift_var $i $j $u $n $h)
       (teq_inv (aux_teq_shift_dbselect $j $i $n (Shift* $j $u) (tvar $n) (tvar (dbprev $n))))
with aux_teq_subst_shift _ _ _ (tuniv _) _ ↪ TRefl _
with aux_teq_subst_shift $i $j $u (tpi $A $B) $h ↪
      Jpi (aux_teq_subst_shift $i $j $u $A $h)
          (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
with aux_teq_subst_shift $i $j $u (tabs $A $t) $h ↪
      Jabs (aux_teq_subst_shift $i $j $u $A $h)
           (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $t (dble_n_S $h))
with aux_teq_subst_shift $i $j $u (tapp $f $a) $h ↪
      Japp (aux_teq_subst_shift $i $j $u $f $h)
           (aux_teq_subst_shift $i $j $u $a $h)
with aux_teq_subst_shift _ _ _ tnat _ ↪ TRefl _
with aux_teq_subst_shift _ _ _ tzero _ ↪ TRefl _
with aux_teq_subst_shift $i $j $u (tsuc $n) $h ↪
      Jcong tsuc (aux_teq_subst_shift $i $j $u $n $h)
with aux_teq_subst_shift $i $j $u (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_subst_shift $i $j $u $P $h)
           (aux_teq_subst_shift $i $j $u $z $h)
           (aux_teq_subst_shift $i $j $u $H $h)
           (aux_teq_subst_shift $i $j $u $n $h)
with aux_teq_subst_shift $i $j $u (tsig $A $B) $h ↪
      Jsig (aux_teq_subst_shift $i $j $u $A $h)
           (aux_teq_subst_shift (dbsucc $i) (dbsucc $j) $u $B (dble_n_S $h))
with aux_teq_subst_shift $i $j $u (tpair $a $b) $h ↪
      Jpair (aux_teq_subst_shift $i $j $u $a $h)
            (aux_teq_subst_shift $i $j $u $b $h)
with aux_teq_subst_shift $i $j $u (tp1 $p) $h ↪
      Jcong tp1 (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (tp2 $p) $h ↪
      Jcong tp2 (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (tsum $A $B) $h ↪
      Jsum (aux_teq_subst_shift $i $j $u $A $h)
           (aux_teq_subst_shift $i $j $u $B $h)
with aux_teq_subst_shift $i $j $u (tinjl $p) $h ↪
      Jcong tinjl (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (tinjr $p) $h ↪
      Jcong tinjr (aux_teq_subst_shift $i $j $u $p $h)
with aux_teq_subst_shift $i $j $u (tcase $A $B $P $a $b $t) $h ↪
      Jcase (aux_teq_subst_shift $i $j $u $A $h)
            (aux_teq_subst_shift $i $j $u $B $h)
            (aux_teq_subst_shift $i $j $u $P $h)
            (aux_teq_subst_shift $i $j $u $a $h)
            (aux_teq_subst_shift $i $j $u $b $h)
            (aux_teq_subst_shift $i $j $u $t $h)
with aux_teq_subst_shift $i $j $u (tpath $A $x $y) $h ↪
      Jpath (aux_teq_subst_shift_Ishift $i $j $u $A $h)
      (aux_teq_subst_shift $i $j $u $x $h)
      (aux_teq_subst_shift $i $j $u $y $h)
with aux_teq_subst_shift $i $j $u (tlamP $t) $h ↪
      Jcong tlamP (aux_teq_subst_shift_Ishift $i $j $u $t $h)
with aux_teq_subst_shift $i $j $u (tappP $x _) $h ↪
      JappP (aux_teq_subst_shift $i $j $u $x $h) (ITRefl _)
with aux_teq_subst_shift $i $j $u (tsys _ _ $x $y) $h ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_subst_shift $i $j $u $x $h)
           (aux_teq_subst_shift $i $j $u $y $h)
with aux_teq_subst_shift _ _ _ temptysys _ ↪ TRefl _
with aux_teq_subst_shift $i $j $u (ttransp $A _ $x) $h ↪
      Jtransp (aux_teq_subst_shift_Ishift $i $j $u $A $h)
              (FTRefl _)
              (aux_teq_subst_shift $i $j $u $x $h)
with aux_teq_subst_shift $i $j $u (thcomp $A _ $x $y) $h ↪
      Jhcomp (aux_teq_subst_shift $i $j $u $A $h)
             (FTRefl _)
             (aux_teq_subst_shift_Ishift $i $j $u $x $h)
             (aux_teq_subst_shift $i $j $u $y $h);

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

// teq_Isubst_Ishift
symbol aux_teq_Isubst_Ishift (i j : DBId) (u : ITerm) (t : Term) :
  DBLe j i →
  TEq (Isubst (dbsucc i) (IshiftI j (IShiftI* j u)) (Ishift j t))
      (Ishift j (Isubst i (IShiftI* j u) t));
symbol aux_teq_IsubstI_IshiftI (i j : DBId) (u : ITerm) (t : ITerm) :
  DBLe j i →
  ITEq (IsubstI (dbsucc i) (IshiftI j (IShiftI* j u)) (IshiftI j t))
       (IshiftI j (IsubstI i (IShiftI* j u) t));
symbol aux_teq_IsubstF_IshiftF (i j : DBId) (u : ITerm) (t : FTerm) :
  DBLe j i →
  FTEq (IsubstF (dbsucc i) (IshiftI j (IShiftI* j u)) (IshiftF j t))
       (IshiftF j (IsubstF i (IShiftI* j u) t));

// teq_Isubst_Ishift_var
symbol aux_teq_Isubst_Ishift_itvar (i j : DBId) (u : ITerm) (n : DBId) :
  DBLe j i →
  ITEq (dbselectI (dbsucc i) (dbshift j n) (IshiftI j (IShiftI* j u)) (itvar (dbshift j n))
                  (itvar (dbprev (dbshift j n))))
       (dbselectI i n (IshiftI j (IShiftI* j u)) (itvar (dbshift j n)) (itvar (dbshift j (dbprev n))));
rule aux_teq_Isubst_Ishift_itvar $i db0 $u $n _ ↪
      aux_teq_dbselectI_Sn $i $n (IshiftI db0 $u) (itvar (dbsucc $n))
with aux_teq_Isubst_Ishift_itvar (dbsucc _) (dbsucc _) _ db0 _ ↪
      ITRefl (itvar db0)
with aux_teq_Isubst_Ishift_itvar (dbsucc db0) (dbsucc $j) $u (dbsucc db0) $h ↪
      iteq_trans
       (iteq_trans
         (aux_teq_dbselectI_Sn (dbsucc db0) (dbshift $j db0) (IshiftI (dbsucc $j) (IShiftI* (dbsucc $j) $u))
                               (itvar (dbsucc (dbshift $j db0))))
         (iteq_inv (aux_teq_shift_dbselectI0 (dbsucc db0) (dbshift $j db0) (IshiftI $j (IShiftI* $j $u))
                                             (itvar (dbshift $j db0)) (itvar (dbprev (dbshift $j db0))))))
       (iteq_trans
         (IJcong IShiftI (aux_teq_Isubst_Ishift_itvar db0 $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectI0 db0 db0 (IshiftI $j (IShiftI* $j $u)) (itvar (dbshift $j db0))
                                   (itvar (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_itvar (dbsucc (dbsucc $i)) (dbsucc $j) $u (dbsucc db0) $h ↪
      iteq_trans
       (iteq_trans
         (aux_teq_dbselectI_Sn (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftI (dbsucc $j) (IShiftI* (dbsucc $j) $u))
                               (itvar (dbsucc (dbshift $j db0))))
         (iteq_inv (aux_teq_shift_dbselectI0 (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftI $j (IShiftI* $j $u))
                                             (itvar (dbshift $j db0)) (itvar (dbprev (dbshift $j db0))))))
       (iteq_trans
         (IJcong IShiftI (aux_teq_Isubst_Ishift_itvar (dbsucc $i) $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectI0 (dbsucc $i) db0 (IshiftI $j (IShiftI* $j $u))
                                   (itvar (dbshift $j db0)) (itvar (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_itvar (dbsucc $i) (dbsucc $j) $u (dbsucc (dbsucc $n)) $h ↪
      iteq_trans
       (iteq_trans
         (aux_teq_dbselectI_Sn (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftI (dbsucc $j) (IShiftI* (dbsucc $j) $u))
                               (itvar (dbsucc (dbshift $j (dbsucc $n)))))
         (iteq_inv (aux_teq_shift_dbselectI0 (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftI $j (IShiftI* $j $u))
                                             (itvar (dbshift $j (dbsucc $n)))
                                             (itvar (dbprev (dbshift $j (dbsucc $n)))))))
       (iteq_trans
         (IJcong IShiftI (aux_teq_Isubst_Ishift_itvar $i $j $u (dbsucc $n) (dble_S_n $h)))
         (aux_teq_shift_dbselectI0 $i (dbsucc $n) (IshiftI $j (IShiftI* $j $u))
                                      (itvar (dbshift $j (dbsucc $n))) (itvar (dbshift $j ($n)))));

symbol aux_teq_Isubst_Ishift_fteq0 (i j : DBId) (u : FTerm) (n : DBId) :
  DBLe j i →
  FTEq (dbselectF (dbsucc i) (dbshift j n) (IshiftF j (IShiftF* j u)) (fteq0 (dbshift j n))
                  (fteq0 (dbprev (dbshift j n))))
       (dbselectF i n (IshiftF j (IShiftF* j u)) (fteq0 (dbshift j n)) (fteq0 (dbshift j (dbprev n))));
rule aux_teq_Isubst_Ishift_fteq0 $i db0 $u $n _ ↪
      aux_teq_dbselectF_Sn0 $i $n (IshiftF db0 $u) (fteq0 (dbsucc $n))
with aux_teq_Isubst_Ishift_fteq0 (dbsucc _) (dbsucc _) _ db0 _ ↪
      FTRefl (fteq0 db0)
with aux_teq_Isubst_Ishift_fteq0 (dbsucc db0) (dbsucc $j) $u (dbsucc db0) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn0 (dbsucc db0) (dbshift $j db0) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq0 (dbsucc (dbshift $j db0))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc db0) (dbshift $j db0) (IshiftF $j (IShiftF* $j $u))
                                             (fteq0 (dbshift $j db0)) (fteq0 (dbprev (dbshift $j db0))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq0 db0 $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 db0 db0 (IshiftF $j (IShiftF* $j $u)) (fteq0 (dbshift $j db0))
                                   (fteq0 (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_fteq0 (dbsucc (dbsucc $i)) (dbsucc $j) $u (dbsucc db0) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn0 (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq0 (dbsucc (dbshift $j db0))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftF $j (IShiftF* $j $u))
                                             (fteq0 (dbshift $j db0)) (fteq0 (dbprev (dbshift $j db0))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq0 (dbsucc $i) $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 (dbsucc $i) db0 (IshiftF $j (IShiftF* $j $u))
                                   (fteq0 (dbshift $j db0)) (fteq0 (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_fteq0 (dbsucc $i) (dbsucc $j) $u (dbsucc (dbsucc $n)) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn0 (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq0 (dbsucc (dbshift $j (dbsucc $n)))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftF $j (IShiftF* $j $u))
                                             (fteq0 (dbshift $j (dbsucc $n)))
                                             (fteq0 (dbprev (dbshift $j (dbsucc $n)))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq0 $i $j $u (dbsucc $n) (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 $i (dbsucc $n) (IshiftF $j (IShiftF* $j $u))
                                      (fteq0 (dbshift $j (dbsucc $n))) (fteq0 (dbshift $j ($n)))));

symbol aux_teq_Isubst_Ishift_fteq1 (i j : DBId) (u : FTerm) (n : DBId) :
  DBLe j i →
  FTEq (dbselectF (dbsucc i) (dbshift j n) (IshiftF j (IShiftF* j u)) (fteq1 (dbshift j n))
                  (fteq1 (dbprev (dbshift j n))))
       (dbselectF i n (IshiftF j (IShiftF* j u)) (fteq1 (dbshift j n)) (fteq1 (dbshift j (dbprev n))));
rule aux_teq_Isubst_Ishift_fteq1 $i db0 $u $n _ ↪
      aux_teq_dbselectF_Sn1 $i $n (IshiftF db0 $u) (fteq1 (dbsucc $n))
with aux_teq_Isubst_Ishift_fteq1 (dbsucc _) (dbsucc _) _ db0 _ ↪
      FTRefl (fteq1 db0)
with aux_teq_Isubst_Ishift_fteq1 (dbsucc db0) (dbsucc $j) $u (dbsucc db0) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn1 (dbsucc db0) (dbshift $j db0) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq1 (dbsucc (dbshift $j db0))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc db0) (dbshift $j db0) (IshiftF $j (IShiftF* $j $u))
                                             (fteq1 (dbshift $j db0)) (fteq1 (dbprev (dbshift $j db0))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq1 db0 $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 db0 db0 (IshiftF $j (IShiftF* $j $u)) (fteq1 (dbshift $j db0))
                                   (fteq1 (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_fteq1 (dbsucc (dbsucc $i)) (dbsucc $j) $u (dbsucc db0) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn1 (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq1 (dbsucc (dbshift $j db0))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc (dbsucc $i)) (dbshift $j db0) (IshiftF $j (IShiftF* $j $u))
                                             (fteq1 (dbshift $j db0)) (fteq1 (dbprev (dbshift $j db0))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq1 (dbsucc $i) $j $u db0 (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 (dbsucc $i) db0 (IshiftF $j (IShiftF* $j $u))
                                   (fteq1 (dbshift $j db0)) (fteq1 (dbshift $j (dbprev db0)))))
with aux_teq_Isubst_Ishift_fteq1 (dbsucc $i) (dbsucc $j) $u (dbsucc (dbsucc $n)) $h ↪
      fteq_trans
       (fteq_trans
         (aux_teq_dbselectF_Sn1 (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftF (dbsucc $j) (IShiftF* (dbsucc $j) $u))
                                (fteq1 (dbsucc (dbshift $j (dbsucc $n)))))
         (fteq_inv (aux_teq_shift_dbselectF0 (dbsucc $i) (dbshift $j (dbsucc $n)) (IshiftF $j (IShiftF* $j $u))
                                             (fteq1 (dbshift $j (dbsucc $n)))
                                             (fteq1 (dbprev (dbshift $j (dbsucc $n)))))))
       (fteq_trans
         (FJcong IShiftF (aux_teq_Isubst_Ishift_fteq1 $i $j $u (dbsucc $n) (dble_S_n $h)))
         (aux_teq_shift_dbselectF0 $i (dbsucc $n) (IshiftF $j (IShiftF* $j $u))
                                      (fteq1 (dbshift $j (dbsucc $n))) (fteq1 (dbshift $j ($n)))));

rule aux_teq_Isubst_Ishift _ _ _ (tvar _) _ ↪
      TRefl _
with aux_teq_Isubst_Ishift _ _ _ (tuniv _) _ ↪ TRefl _
with aux_teq_Isubst_Ishift $i $j $u (tpi $A $B) $h ↪
      Jpi (aux_teq_Isubst_Ishift $i $j $u $A $h)
          (aux_teq_Isubst_Ishift $i $j $u $B $h)
with aux_teq_Isubst_Ishift $i $j $u (tabs $A $t) $h ↪
      Jabs (aux_teq_Isubst_Ishift $i $j $u $A $h)
           (aux_teq_Isubst_Ishift $i $j $u $t $h)
with aux_teq_Isubst_Ishift $i $j $u (tapp $f $a) $h ↪
      Japp (aux_teq_Isubst_Ishift $i $j $u $f $h)
           (aux_teq_Isubst_Ishift $i $j $u $a $h)
with aux_teq_Isubst_Ishift _ _ _ tnat _ ↪ TRefl _
with aux_teq_Isubst_Ishift _ _ _ tzero _ ↪ TRefl _
with aux_teq_Isubst_Ishift $i $j $u (tsuc $n) $h ↪
      Jcong tsuc (aux_teq_Isubst_Ishift $i $j $u $n $h)
with aux_teq_Isubst_Ishift $i $j $u (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_Isubst_Ishift $i $j $u $P $h)
           (aux_teq_Isubst_Ishift $i $j $u $z $h)
           (aux_teq_Isubst_Ishift $i $j $u $H $h)
           (aux_teq_Isubst_Ishift $i $j $u $n $h)
with aux_teq_Isubst_Ishift $i $j $u (tsig $A $B) $h ↪
      Jsig (aux_teq_Isubst_Ishift $i $j $u $A $h)
           (aux_teq_Isubst_Ishift $i $j $u $B $h)
with aux_teq_Isubst_Ishift $i $j $u (tpair $a $b) $h ↪
      Jpair (aux_teq_Isubst_Ishift $i $j $u $a $h)
            (aux_teq_Isubst_Ishift $i $j $u $b $h)
with aux_teq_Isubst_Ishift $i $j $u (tp1 $p) $h ↪
      Jcong tp1 (aux_teq_Isubst_Ishift $i $j $u $p $h)
with aux_teq_Isubst_Ishift $i $j $u (tp2 $p) $h ↪
      Jcong tp2 (aux_teq_Isubst_Ishift $i $j $u $p $h)
with aux_teq_Isubst_Ishift $i $j $u (tsum $A $B) $h ↪
      Jsum (aux_teq_Isubst_Ishift $i $j $u $A $h)
           (aux_teq_Isubst_Ishift $i $j $u $B $h)
with aux_teq_Isubst_Ishift $i $j $u (tinjl $p) $h ↪
      Jcong tinjl (aux_teq_Isubst_Ishift $i $j $u $p $h)
with aux_teq_Isubst_Ishift $i $j $u (tinjr $p) $h ↪
      Jcong tinjr (aux_teq_Isubst_Ishift $i $j $u $p $h)
with aux_teq_Isubst_Ishift $i $j $u (tcase $A $B $P $a $b $t) $h ↪
      Jcase (aux_teq_Isubst_Ishift $i $j $u $A $h)
            (aux_teq_Isubst_Ishift $i $j $u $B $h)
            (aux_teq_Isubst_Ishift $i $j $u $P $h)
            (aux_teq_Isubst_Ishift $i $j $u $a $h)
            (aux_teq_Isubst_Ishift $i $j $u $b $h)
            (aux_teq_Isubst_Ishift $i $j $u $t $h)
with aux_teq_Isubst_Ishift $i $j $u (tpath $A $x $y) $h ↪
      Jpath (aux_teq_Isubst_Ishift (dbsucc $i) (dbsucc $j) $u $A (dble_n_S $h))
      (aux_teq_Isubst_Ishift $i $j $u $x $h)
      (aux_teq_Isubst_Ishift $i $j $u $y $h)
with aux_teq_Isubst_Ishift $i $j $u (tlamP $t) $h ↪
      Jcong tlamP (aux_teq_Isubst_Ishift (dbsucc $i) (dbsucc $j) $u $t (dble_n_S $h))
with aux_teq_Isubst_Ishift $i $j $u (tappP $x $y) $h ↪
      JappP (aux_teq_Isubst_Ishift $i $j $u $x $h) (aux_teq_IsubstI_IshiftI $i $j $u $y $h)
with aux_teq_Isubst_Ishift $i $j $u (tsys $f $g $x $y) $h ↪
      Jsys (aux_teq_IsubstF_IshiftF $i $j $u $f $h)
           (aux_teq_IsubstF_IshiftF $i $j $u $g $h)
           (aux_teq_Isubst_Ishift $i $j $u $x $h)
           (aux_teq_Isubst_Ishift $i $j $u $y $h)
with aux_teq_Isubst_Ishift _ _ _ temptysys _ ↪ TRefl _
with aux_teq_Isubst_Ishift $i $j $u (ttransp $A $f $x) $h ↪
      Jtransp (aux_teq_Isubst_Ishift (dbsucc $i) (dbsucc $j) $u $A (dble_n_S $h))
              (aux_teq_IsubstF_IshiftF $i $j $u $f $h)
              (aux_teq_Isubst_Ishift $i $j $u $x $h)
with aux_teq_Isubst_Ishift $i $j $u (thcomp $A $f $x $y) $h ↪
      Jhcomp (aux_teq_Isubst_Ishift $i $j $u $A $h)
             (aux_teq_IsubstF_IshiftF $i $j $u $f $h)
             (aux_teq_Isubst_Ishift (dbsucc $i) (dbsucc $j) $u $x (dble_n_S $h))
             (aux_teq_Isubst_Ishift $i $j $u $y $h)
with aux_teq_IsubstI_IshiftI _ _ _ it0 _ ↪ ITRefl _
with aux_teq_IsubstI_IshiftI _ _ _ it1 _ ↪ ITRefl _
with aux_teq_IsubstI_IshiftI $i $j $u (itvar $n) $h ↪
      iteq_trans
       (aux_teq_Isubst_Ishift_itvar $i $j $u $n $h)
       (iteq_inv (aux_teq_shift_dbselectI $j $i $n (IShiftI* $j $u) (itvar $n) (itvar (dbprev $n))))
with aux_teq_IsubstI_IshiftI $i $j $u (itsym $n) $h ↪
      IJcong itsym (aux_teq_IsubstI_IshiftI $i $j $u $n $h)
with aux_teq_IsubstI_IshiftI $i $j $u (itmin $x $y) $h ↪
      IJmin (aux_teq_IsubstI_IshiftI $i $j $u $x $h)
            (aux_teq_IsubstI_IshiftI $i $j $u $y $h)
with aux_teq_IsubstI_IshiftI $i $j $u (itmax $x $y) $h ↪
      IJmax (aux_teq_IsubstI_IshiftI $i $j $u $x $h)
            (aux_teq_IsubstI_IshiftI $i $j $u $y $h)
with aux_teq_IsubstF_IshiftF _ _ _ ft0 _ ↪ FTRefl _
with aux_teq_IsubstF_IshiftF _ _ _ ft1 _ ↪ FTRefl _
with aux_teq_IsubstF_IshiftF $i $j $u (fteq0 $n) $h ↪
      fteq_trans (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbshift $j $n) v
                                                     (fteq0 (dbshift $j $n))
                                                     (fteq0 (dbprev (dbshift $j $n))))
                                     (aux_teq_Ishift_substeq0 $j (IShiftI* $j $u)))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbshift $j $n) (IshiftF $j v)
                                                                 (fteq0 (dbshift $j $n))
                                                                 (fteq0 (dbprev (dbshift $j $n))))
                                                 (aux_teq_IShift*_substeq0 $j $u))
                                         (fteq_trans (aux_teq_Isubst_Ishift_fteq0 $i $j (substeq0 $u) $n $h)
                                                     (FJcong (λ v, dbselectF $i $n (IshiftF $j v)
                                                                             (fteq0 (dbshift $j $n))
                                                                             (fteq0 (dbshift $j (dbprev $n))))
                                                             (fteq_inv (aux_teq_IShift*_substeq0 $j $u))))))
                 (fteq_inv (aux_teq_shift_dbselectF $j $i $n (substeq0 (IShiftI* $j $u)) (fteq0 $n)
                                                             (fteq0 (dbprev $n))))
with aux_teq_IsubstF_IshiftF $i $j $u (fteq1 $n) $h ↪
      fteq_trans (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbshift $j $n) v
                                                     (fteq1 (dbshift $j $n))
                                                     (fteq1 (dbprev (dbshift $j $n))))
                                     (aux_teq_Ishift_substeq1 $j (IShiftI* $j $u)))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbshift $j $n) (IshiftF $j v)
                                                                 (fteq1 (dbshift $j $n))
                                                                 (fteq1 (dbprev (dbshift $j $n))))
                                                 (aux_teq_IShift*_substeq1 $j $u))
                                         (fteq_trans (aux_teq_Isubst_Ishift_fteq1 $i $j (substeq1 $u) $n $h)
                                                     (FJcong (λ v, dbselectF $i $n (IshiftF $j v)
                                                                             (fteq1 (dbshift $j $n))
                                                                             (fteq1 (dbshift $j (dbprev $n))))
                                                             (fteq_inv (aux_teq_IShift*_substeq1 $j $u))))))
                 (fteq_inv (aux_teq_shift_dbselectF $j $i $n (substeq1 (IShiftI* $j $u)) (fteq1 $n)
                                                             (fteq1 (dbprev $n))))
with aux_teq_IsubstF_IshiftF $i $j $u (ftmin $x $y) $h ↪
      FJmin (aux_teq_IsubstF_IshiftF $i $j $u $x $h)
            (aux_teq_IsubstF_IshiftF $i $j $u $y $h)
with aux_teq_IsubstF_IshiftF $i $j $u (ftmax $x $y) $h ↪
      FJmax (aux_teq_IsubstF_IshiftF $i $j $u $x $h)
            (aux_teq_IsubstF_IshiftF $i $j $u $y $h);

// teq_Isubst_Ishift
symbol teq_Isubst_Ishift (i : DBId) (u : ITerm) (t : Term) :
  TEq (Isubst (dbsucc i) (IShiftI u) (IShift t))
      (IShift (Isubst i u t)) ≔
  aux_teq_Isubst_Ishift i db0 u t (dble_0_n i);

// teq_IsubstI_IshiftI
symbol teq_IsubstI_IshiftI (i : DBId) (u t : ITerm) :
  ITEq (IsubstI (dbsucc i) (IShiftI u) (IShiftI t))
       (IShiftI (IsubstI i u t)) ≔
  aux_teq_IsubstI_IshiftI i db0 u t (dble_0_n i);

// teq_IsubstF_IshiftF
symbol teq_IsubstF_IshiftF (i : DBId) (u : ITerm) (t : FTerm) :
  FTEq (IsubstF (dbsucc i) (IShiftI u) (IShiftF t))
       (IShiftF (IsubstF i u t)) ≔
  aux_teq_IsubstF_IshiftF i db0 u t (dble_0_n i);

// teq_subst_Ishift
symbol aux_teq_subst_Ishift (i j : DBId) (u t : Term) :
  TEq (subst i (Ishift j (Shift* i u)) (Ishift j t))
      (Ishift j (subst i (Shift* i u) t));
symbol aux_teq_subst_Ishift_rec (i j : DBId) (u t : Term) ≔
  teq_trans (Jcong (λ v, subst (dbsucc i) v (Ishift j t)) (aux_teq_shift_Ishift db0 j (Shift* i u)))
            (aux_teq_subst_Ishift (dbsucc i) j u t);
symbol aux_teq_subst_Ishift_Irec (i j : DBId) (u t : Term) ≔
  teq_trans (Jcong (λ v, subst i v (Ishift (dbsucc j) t)) (aux_teq_Ishift_Ishift0 j (Shift* i u)))
            (teq_trans (Jcong (λ v, subst i (Ishift (dbsucc j) v) (Ishift (dbsucc j) t))
                              (teq_inv (aux_teq_Shift*_Ishift i db0 u)))
                       (teq_trans (aux_teq_subst_Ishift i (dbsucc j) (IShift u) t)
                                  (Jcong (λ v, Ishift (dbsucc j) (subst i v t)) (aux_teq_Shift*_Ishift i db0 u))));

rule aux_teq_subst_Ishift $i $j $u (tvar $n) ↪
      teq_inv (aux_teq_Ishift_dbselect $j $i $n (Shift* $i $u) (tvar $n) (tvar (dbprev $n)))
with aux_teq_subst_Ishift _ _ _ (tuniv _) ↪ TRefl _
with aux_teq_subst_Ishift $i $j $u (tpi $A $B) ↪
      Jpi (aux_teq_subst_Ishift $i $j $u $A)
          (aux_teq_subst_Ishift_rec $i $j $u $B)
with aux_teq_subst_Ishift $i $j $u (tabs $A $t) ↪
      Jabs (aux_teq_subst_Ishift $i $j $u $A)
           (aux_teq_subst_Ishift_rec $i $j $u $t)
with aux_teq_subst_Ishift $i $j $u (tapp $f $a) ↪
      Japp (aux_teq_subst_Ishift $i $j $u $f)
           (aux_teq_subst_Ishift $i $j $u $a)
with aux_teq_subst_Ishift _ _ _ tnat ↪ TRefl _
with aux_teq_subst_Ishift _ _ _ tzero ↪ TRefl _
with aux_teq_subst_Ishift $i $j $u (tsuc $n) ↪
      Jcong tsuc (aux_teq_subst_Ishift $i $j $u $n)
with aux_teq_subst_Ishift $i $j $u (trec $P $z $H $n) ↪
      Jrec (aux_teq_subst_Ishift $i $j $u $P)
           (aux_teq_subst_Ishift $i $j $u $z)
           (aux_teq_subst_Ishift $i $j $u $H)
           (aux_teq_subst_Ishift $i $j $u $n)
with aux_teq_subst_Ishift $i $j $u (tsig $A $B) ↪
      Jsig (aux_teq_subst_Ishift $i $j $u $A)
           (aux_teq_subst_Ishift_rec $i $j $u $B)
with aux_teq_subst_Ishift $i $j $u (tpair $a $b) ↪
      Jpair (aux_teq_subst_Ishift $i $j $u $a)
            (aux_teq_subst_Ishift $i $j $u $b)
with aux_teq_subst_Ishift $i $j $u (tp1 $p) ↪
      Jcong tp1 (aux_teq_subst_Ishift $i $j $u $p)
with aux_teq_subst_Ishift $i $j $u (tp2 $p) ↪
      Jcong tp2 (aux_teq_subst_Ishift $i $j $u $p)
with aux_teq_subst_Ishift $i $j $u (tsum $A $B) ↪
      Jsum (aux_teq_subst_Ishift $i $j $u $A)
           (aux_teq_subst_Ishift $i $j $u $B)
with aux_teq_subst_Ishift $i $j $u (tinjl $p) ↪
      Jcong tinjl (aux_teq_subst_Ishift $i $j $u $p)
with aux_teq_subst_Ishift $i $j $u (tinjr $p) ↪
      Jcong tinjr (aux_teq_subst_Ishift $i $j $u $p)
with aux_teq_subst_Ishift $i $j $u (tcase $A $B $P $a $b $t) ↪
      Jcase (aux_teq_subst_Ishift $i $j $u $A)
            (aux_teq_subst_Ishift $i $j $u $B)
            (aux_teq_subst_Ishift $i $j $u $P)
            (aux_teq_subst_Ishift $i $j $u $a)
            (aux_teq_subst_Ishift $i $j $u $b)
            (aux_teq_subst_Ishift $i $j $u $t)
with aux_teq_subst_Ishift $i $j $u (tpath $A $x $y) ↪
      Jpath (aux_teq_subst_Ishift_Irec $i $j $u $A)
            (aux_teq_subst_Ishift $i $j $u $x)
            (aux_teq_subst_Ishift $i $j $u $y)
with aux_teq_subst_Ishift $i $j $u (tlamP $t) ↪
      Jcong tlamP (aux_teq_subst_Ishift_Irec $i $j $u $t)
with aux_teq_subst_Ishift $i $j $u (tappP $x _) ↪
      JappP (aux_teq_subst_Ishift $i $j $u $x) (ITRefl _)
with aux_teq_subst_Ishift $i $j $u (tsys _ _ $x $y) ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_subst_Ishift $i $j $u $x)
           (aux_teq_subst_Ishift $i $j $u $y)
with aux_teq_subst_Ishift _ _ _ temptysys ↪ TRefl _
with aux_teq_subst_Ishift $i $j $u (ttransp $A _ $x) ↪
      Jtransp (aux_teq_subst_Ishift_Irec $i $j $u $A)
              (FTRefl _)
              (aux_teq_subst_Ishift $i $j $u $x)
with aux_teq_subst_Ishift $i $j $u (thcomp $A _ $x $y) ↪
      Jhcomp (aux_teq_subst_Ishift $i $j $u $A)
             (FTRefl _)
             (aux_teq_subst_Ishift_Irec $i $j $u $x)
             (aux_teq_subst_Ishift $i $j $u $y);

// teq_Isubst_shift
symbol aux_teq_Isubst_shift (i j : DBId) (u : ITerm) (t : Term) :
  TEq (Isubst i (IShiftI* i u) (shift j t))
      (shift j (Isubst i (IShiftI* i u) t));

rule aux_teq_Isubst_shift _ _ _ (tvar _) ↪ TRefl _
with aux_teq_Isubst_shift _ _ _ (tuniv _) ↪ TRefl _
with aux_teq_Isubst_shift $i $j $u (tpi $A $B) ↪
      Jpi (aux_teq_Isubst_shift $i $j $u $A)
          (aux_teq_Isubst_shift $i (dbsucc $j) $u $B)
with aux_teq_Isubst_shift $i $j $u (tabs $A $t) ↪
      Jabs (aux_teq_Isubst_shift $i $j $u $A)
           (aux_teq_Isubst_shift $i (dbsucc $j) $u $t)
with aux_teq_Isubst_shift $i $j $u (tapp $f $a) ↪
      Japp (aux_teq_Isubst_shift $i $j $u $f)
           (aux_teq_Isubst_shift $i $j $u $a)
with aux_teq_Isubst_shift _ _ _ tnat ↪ TRefl _
with aux_teq_Isubst_shift _ _ _ tzero ↪ TRefl _
with aux_teq_Isubst_shift $i $j $u (tsuc $n) ↪
      Jcong tsuc (aux_teq_Isubst_shift $i $j $u $n)
with aux_teq_Isubst_shift $i $j $u (trec $P $z $H $n) ↪
      Jrec (aux_teq_Isubst_shift $i $j $u $P)
           (aux_teq_Isubst_shift $i $j $u $z)
           (aux_teq_Isubst_shift $i $j $u $H)
           (aux_teq_Isubst_shift $i $j $u $n)
with aux_teq_Isubst_shift $i $j $u (tsig $A $B) ↪
      Jsig (aux_teq_Isubst_shift $i $j $u $A)
           (aux_teq_Isubst_shift $i (dbsucc $j) $u $B)
with aux_teq_Isubst_shift $i $j $u (tpair $a $b) ↪
      Jpair (aux_teq_Isubst_shift $i $j $u $a)
            (aux_teq_Isubst_shift $i $j $u $b)
with aux_teq_Isubst_shift $i $j $u (tp1 $p) ↪
      Jcong tp1 (aux_teq_Isubst_shift $i $j $u $p)
with aux_teq_Isubst_shift $i $j $u (tp2 $p) ↪
      Jcong tp2 (aux_teq_Isubst_shift $i $j $u $p)
with aux_teq_Isubst_shift $i $j $u (tsum $A $B) ↪
      Jsum (aux_teq_Isubst_shift $i $j $u $A)
           (aux_teq_Isubst_shift $i $j $u $B)
with aux_teq_Isubst_shift $i $j $u (tinjl $p) ↪
      Jcong tinjl (aux_teq_Isubst_shift $i $j $u $p)
with aux_teq_Isubst_shift $i $j $u (tinjr $p) ↪
      Jcong tinjr (aux_teq_Isubst_shift $i $j $u $p)
with aux_teq_Isubst_shift $i $j $u (tcase $A $B $P $a $b $t) ↪
      Jcase (aux_teq_Isubst_shift $i $j $u $A)
            (aux_teq_Isubst_shift $i $j $u $B)
            (aux_teq_Isubst_shift $i $j $u $P)
            (aux_teq_Isubst_shift $i $j $u $a)
            (aux_teq_Isubst_shift $i $j $u $b)
            (aux_teq_Isubst_shift $i $j $u $t)
with aux_teq_Isubst_shift $i $j $u (tpath $A $x $y) ↪
      Jpath (aux_teq_Isubst_shift (dbsucc $i) $j $u $A)
            (aux_teq_Isubst_shift $i $j $u $x)
            (aux_teq_Isubst_shift $i $j $u $y)
with aux_teq_Isubst_shift $i $j $u (tlamP $t) ↪
      Jcong tlamP (aux_teq_Isubst_shift (dbsucc $i) $j $u $t)
with aux_teq_Isubst_shift $i $j $u (tappP $x _) ↪
      JappP (aux_teq_Isubst_shift $i $j $u $x) (ITRefl _)
with aux_teq_Isubst_shift $i $j $u (tsys _ _ $x $y) ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_Isubst_shift $i $j $u $x)
           (aux_teq_Isubst_shift $i $j $u $y)
with aux_teq_Isubst_shift _ _ _ temptysys ↪ TRefl _
with aux_teq_Isubst_shift $i $j $u (ttransp $A _ $x) ↪
      Jtransp (aux_teq_Isubst_shift (dbsucc $i) $j $u $A)
              (FTRefl _)
              (aux_teq_Isubst_shift $i $j $u $x)
with aux_teq_Isubst_shift $i $j $u (thcomp $A _ $x $y) ↪
      Jhcomp (aux_teq_Isubst_shift $i $j $u $A)
             (FTRefl _)
             (aux_teq_Isubst_shift (dbsucc $i) $j $u $x)
             (aux_teq_Isubst_shift $i $j $u $y);

// teq_select_shift
symbol teq_select_shift (i id : DBId) (V : Term) :
  TEq (dbselect (dbsucc i) (dbsucc id) (Shift V) (tvar (dbsucc id)) (tvar id))
      (Shift (dbselect i id V (tvar id) (tvar (dbprev id)))) ≔
  teq_trans
    (aux_teq_dbselect_Sn i id (Shift V) (tvar (dbsucc id)))
    (teq_inv (aux_teq_shift_dbselect0 i id V (tvar id) (tvar (dbprev id))));
symbol teq_select_IshiftI (i id : DBId) (V : ITerm) :
  ITEq (dbselectI (dbsucc i) (dbsucc id) (IShiftI V) (itvar (dbsucc id)) (itvar id))
       (IShiftI (dbselectI i id V (itvar id) (itvar (dbprev id)))) ≔
  iteq_trans (aux_teq_dbselectI_Sn i id (IShiftI V) (itvar (dbsucc id)))
             (iteq_inv (aux_teq_shift_dbselectI0 i id V (itvar id) (itvar (dbprev id))));
symbol teq_select_IshiftF0 (i id : DBId) (V : FTerm) :
  FTEq (dbselectF (dbsucc i) (dbsucc id) (IShiftF V) (fteq0 (dbsucc id)) (fteq0 id))
       (IShiftF (dbselectF i id V (fteq0 id) (fteq0 (dbprev id)))) ≔
  fteq_trans (aux_teq_dbselectF_Sn0 i id (IShiftF V) (fteq0 (dbsucc id)))
             (fteq_inv (aux_teq_shift_dbselectF0 i id V (fteq0 id) (fteq0 (dbprev id))));
symbol teq_select_IshiftF1 (i id : DBId) (V : FTerm) :
  FTEq (dbselectF (dbsucc i) (dbsucc id) (IShiftF V) (fteq1 (dbsucc id)) (fteq1 id))
       (IShiftF (dbselectF i id V (fteq1 id) (fteq1 (dbprev id)))) ≔
  fteq_trans (aux_teq_dbselectF_Sn1 i id (IShiftF V) (fteq1 (dbsucc id)))
             (fteq_inv (aux_teq_shift_dbselectF0 i id V (fteq1 id) (fteq1 (dbprev id))));

// teq_subst_dbselect
symbol aux_teq_subst_dbselect (i j k : DBId) (u eqT gtT ltT : Term) :
  TEq (subst k u (dbselect i j eqT gtT ltT))
      (dbselect i j (subst k u eqT) (subst k u gtT) (subst k u ltT));
rule aux_teq_subst_dbselect db0        db0 $k $u $eqT _ _ ↪ TRefl (subst $k $u $eqT)
with aux_teq_subst_dbselect (dbsucc _) db0 $k $u _ $gtT _ ↪ TRefl (subst $k $u $gtT)
with aux_teq_subst_dbselect db0 (dbsucc _) $k $u _ _ $ltT ↪ TRefl (subst $k $u $ltT)
with aux_teq_subst_dbselect (dbsucc $i) (dbsucc $j) $k $u $eqT $gtT $ltT ↪
      aux_teq_subst_dbselect $i $j $k $u $eqT $gtT $ltT;

// teq_Isubst_dbselect
symbol aux_teq_Isubst_dbselect (i j k : DBId) (u : ITerm) (eqT gtT ltT : Term) :
  TEq (Isubst k u (dbselect i j eqT gtT ltT))
      (dbselect i j (Isubst k u eqT) (Isubst k u gtT) (Isubst k u ltT));
rule aux_teq_Isubst_dbselect db0        db0 $k $u $eqT _ _ ↪ TRefl (Isubst $k $u $eqT)
with aux_teq_Isubst_dbselect (dbsucc _) db0 $k $u _ $gtT _ ↪ TRefl (Isubst $k $u $gtT)
with aux_teq_Isubst_dbselect db0 (dbsucc _) $k $u _ _ $ltT ↪ TRefl (Isubst $k $u $ltT)
with aux_teq_Isubst_dbselect (dbsucc $i) (dbsucc $j) $k $u $eqT $gtT $ltT ↪
      aux_teq_Isubst_dbselect $i $j $k $u $eqT $gtT $ltT;

// teq_subst_dbselectI
symbol aux_teq_subst_dbselectI (i j k : DBId) (u eqT gtT ltT : ITerm) :
  ITEq (IsubstI k u (dbselectI i j eqT gtT ltT))
       (dbselectI i j (IsubstI k u eqT) (IsubstI k u gtT) (IsubstI k u ltT));
rule aux_teq_subst_dbselectI db0        db0 $k $u $eqT _ _ ↪ ITRefl (IsubstI $k $u $eqT)
with aux_teq_subst_dbselectI (dbsucc _) db0 $k $u _ $gtT _ ↪ ITRefl (IsubstI $k $u $gtT)
with aux_teq_subst_dbselectI db0 (dbsucc _) $k $u _ _ $ltT ↪ ITRefl (IsubstI $k $u $ltT)
with aux_teq_subst_dbselectI (dbsucc $i) (dbsucc $j) $k $u $eqT $gtT $ltT ↪
      aux_teq_subst_dbselectI $i $j $k $u $eqT $gtT $ltT;

// teq_subst_dbselectF
symbol aux_teq_subst_dbselectF (i j k : DBId) (u : ITerm) (eqT gtT ltT : FTerm) :
  FTEq (IsubstF k u (dbselectF i j eqT gtT ltT))
       (dbselectF i j (IsubstF k u eqT) (IsubstF k u gtT) (IsubstF k u ltT));
rule aux_teq_subst_dbselectF db0        db0 $k $u $eqT _ _ ↪ FTRefl (IsubstF $k $u $eqT)
with aux_teq_subst_dbselectF (dbsucc _) db0 $k $u _ $gtT _ ↪ FTRefl (IsubstF $k $u $gtT)
with aux_teq_subst_dbselectF db0 (dbsucc _) $k $u _ _ $ltT ↪ FTRefl (IsubstF $k $u $ltT)
with aux_teq_subst_dbselectF (dbsucc $i) (dbsucc $j) $k $u $eqT $gtT $ltT ↪
      aux_teq_subst_dbselectF $i $j $k $u $eqT $gtT $ltT;

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
  TEq (select_neq i (dbshift i j) gtT (tvar (dbshift i j)))
      (select_neq i (dbshift i j) gtT (tvar (dbsucc (dbprev (dbshift i j)))));
// aux_shift_cancel_select_neq
symbol aux_shift_cancel_select_neq (i n : DBId) :
  TEq (select_neq i (dbshift i n) (tvar (dbshift i n)) (tvar (dbprev (dbshift i n)))) (tvar n);

rule aux_teq_shift_neq db0 db0 _ _ $ltT ↪ TRefl $ltT
with aux_teq_shift_neq (dbsucc _) db0 _ $gtT _ ↪ TRefl $gtT
with aux_teq_shift_neq db0 (dbsucc _) _ _ $ltT ↪ TRefl $ltT
with aux_teq_shift_neq (dbsucc $i) (dbsucc $n) $eqT $gtT $ltT ↪ aux_teq_shift_neq $i $n $eqT $gtT $ltT
with aux_shift_select_neq db0 db0 $k _ $ltT ↪ TRefl (shift $k $ltT)
with aux_shift_select_neq (dbsucc _) db0 $k $gtT _ ↪ TRefl (shift $k $gtT)
with aux_shift_select_neq db0 (dbsucc _) $k _ $ltT ↪ TRefl (shift $k $ltT)
with aux_shift_select_neq (dbsucc $i) (dbsucc $j) $k $gtT $ltT ↪ aux_shift_select_neq $i $j $k $gtT $ltT
with aux_select_neq_Sn db0 $n _ ↪ TRefl (tvar (dbsucc $n))
with aux_select_neq_Sn (dbsucc _) db0 $gtT ↪ TRefl $gtT
with aux_select_neq_Sn (dbsucc $i) (dbsucc $n) $gtT ↪
      TRefl (select_neq $i (dbshift $i $n) $gtT (tvar (dbsucc (dbshift $i $n))))
with aux_shift_cancel_select_neq db0 $n ↪ TRefl (tvar $n)
with aux_shift_cancel_select_neq (dbsucc _) db0 ↪ TRefl (tvar db0)
with aux_shift_cancel_select_neq (dbsucc $i) (dbsucc $n) ↪
      teq_trans
       (teq_trans
         (aux_select_neq_Sn $i $n (tvar (dbsucc (dbshift $i $n))))
         (teq_inv (aux_shift_select_neq $i $n db0 (tvar (dbshift $i $n)) (tvar (dbprev (dbshift $i $n))))))
       (Jcong Shift (aux_shift_cancel_select_neq $i $n))
;

rule aux_teq_shift_cancel_subst $i $u (tvar $n) ↪
      teq_trans
       (aux_teq_shift_neq $i $n $u (tvar (dbshift $i $n)) (tvar (dbprev (dbshift $i $n))))
       (aux_shift_cancel_select_neq $i $n)
with aux_teq_shift_cancel_subst _ _ (tuniv $s) ↪ TRefl (tuniv $s)
with aux_teq_shift_cancel_subst $i $u (tpi $A $B) ↪
      Jpi (aux_teq_shift_cancel_subst $i $u $A)
          (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
with aux_teq_shift_cancel_subst $i $u (tabs $A $t) ↪
      Jabs (aux_teq_shift_cancel_subst $i $u $A)
           (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $t)
with aux_teq_shift_cancel_subst $i $u (tapp $f $a) ↪
      Japp (aux_teq_shift_cancel_subst $i $u $f)
           (aux_teq_shift_cancel_subst $i $u $a)
with aux_teq_shift_cancel_subst _ _ tnat ↪ TRefl tnat
with aux_teq_shift_cancel_subst _ _ tzero ↪ TRefl tzero
with aux_teq_shift_cancel_subst $i $u (tsuc $n) ↪
      Jcong tsuc (aux_teq_shift_cancel_subst $i $u $n)
with aux_teq_shift_cancel_subst $i $u (trec $P $z $H $n) ↪
      Jrec (aux_teq_shift_cancel_subst $i $u $P)
           (aux_teq_shift_cancel_subst $i $u $z)
           (aux_teq_shift_cancel_subst $i $u $H)
           (aux_teq_shift_cancel_subst $i $u $n)
with aux_teq_shift_cancel_subst $i $u (tsig $A $B) ↪
      Jsig (aux_teq_shift_cancel_subst $i $u $A)
           (aux_teq_shift_cancel_subst (dbsucc $i) (Shift $u) $B)
with aux_teq_shift_cancel_subst $i $u (tpair $a $b) ↪
      Jpair (aux_teq_shift_cancel_subst $i $u $a)
            (aux_teq_shift_cancel_subst $i $u $b)
with aux_teq_shift_cancel_subst $i $u (tp1 $p) ↪
      Jcong tp1 (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (tp2 $p) ↪
      Jcong tp2 (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (tsum $A $B) ↪
      Jsum (aux_teq_shift_cancel_subst $i $u $A)
           (aux_teq_shift_cancel_subst $i $u $B)
with aux_teq_shift_cancel_subst $i $u (tinjl $p) ↪
      Jcong tinjl (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (tinjr $p) ↪
      Jcong tinjr (aux_teq_shift_cancel_subst $i $u $p)
with aux_teq_shift_cancel_subst $i $u (tcase $A $B $P $Ha $Hb $x) ↪
      Jcase (aux_teq_shift_cancel_subst $i $u $A)
            (aux_teq_shift_cancel_subst $i $u $B)
            (aux_teq_shift_cancel_subst $i $u $P)
            (aux_teq_shift_cancel_subst $i $u $Ha)
            (aux_teq_shift_cancel_subst $i $u $Hb)
            (aux_teq_shift_cancel_subst $i $u $x)
with aux_teq_shift_cancel_subst $i $u (tpath $A $x $y) ↪
      Jpath (aux_teq_shift_cancel_subst $i $u $A)
            (aux_teq_shift_cancel_subst $i $u $x)
            (aux_teq_shift_cancel_subst $i $u $y)
with aux_teq_shift_cancel_subst $i $u (tlamP $x) ↪
      Jcong tlamP (aux_teq_shift_cancel_subst $i $u $x)
with aux_teq_shift_cancel_subst $i $u (tappP $x $y) ↪
      JappP (aux_teq_shift_cancel_subst $i $u $x)
            (ITRefl $y)
with aux_teq_shift_cancel_subst $i $u (tsys _ _ $x $y) ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_shift_cancel_subst $i $u $x)
           (aux_teq_shift_cancel_subst $i $u $y)
with aux_teq_shift_cancel_subst _ _ temptysys ↪ TRefl temptysys
with aux_teq_shift_cancel_subst $i $u (ttransp $A _ $x) ↪
      Jtransp (aux_teq_shift_cancel_subst $i $u $A)
              (FTRefl _)
              (aux_teq_shift_cancel_subst $i $u $x)
with aux_teq_shift_cancel_subst $i $u (thcomp $A _ $x $y) ↪
      Jhcomp (aux_teq_shift_cancel_subst $i $u $A)
             (FTRefl _)
             (aux_teq_shift_cancel_subst $i $u $x)
             (aux_teq_shift_cancel_subst $i $u $y);

// teq_shift_cancel_subst
symbol teq_shift_cancel_subst (i : DBId) (u t : Term) :
  TEq (subst i u (shift (dbsucc i) (shift i t)))
      (shift i t) ≔
  teq_trans
   (Jcong (subst i u)
     (teq_inv (aux_teq_shift_shift i i t (DBLe_refl i))))
   (aux_teq_shift_cancel_subst i u (shift i t));

// teq_Ishift_cancel_Isubst
symbol aux_teq_Ishift_cancel_Isubst (i : DBId) (u : ITerm) (t : Term) :
  TEq (Isubst i u (Ishift i t)) t;
symbol aux_teq_IshiftI_cancel_IsubstI (i : DBId) (u t : ITerm) :
  ITEq (IsubstI i u (IshiftI i t)) t;
symbol aux_teq_IshiftF_cancel_IsubstF (i : DBId) (u : ITerm) (t : FTerm) :
  FTEq (IsubstF i u (IshiftF i t)) t;
symbol select_neqI : DBId → DBId → ITerm → ITerm → ITerm;
rule select_neqI (dbsucc _) db0 $gt _ ↪ $gt
with select_neqI db0 (dbsucc _) _ $lt ↪ $lt
with select_neqI (dbsucc $i) (dbsucc $n) $gt $lt ↪ select_neqI $i $n $gt $lt;
symbol select_neqF : DBId → DBId → FTerm → FTerm → FTerm;
rule select_neqF (dbsucc _) db0 $gt _ ↪ $gt
with select_neqF db0 (dbsucc _) _ $lt ↪ $lt
with select_neqF (dbsucc $i) (dbsucc $n) $gt $lt ↪ select_neqF $i $n $gt $lt;
// aux_teq_shift_neqI
symbol aux_teq_shift_neqI (i n : DBId) (eqT gtT ltT : ITerm) :
  ITEq (dbselectI i (dbshift i n) eqT gtT ltT) (select_neqI i (dbshift i n) gtT ltT);
symbol aux_teq_shift_neqF (i n : DBId) (eqT gtT ltT : FTerm) :
  FTEq (dbselectF i (dbshift i n) eqT gtT ltT) (select_neqF i (dbshift i n) gtT ltT);
// aux_Ishift_select_neq
symbol aux_Ishift_select_neq (i j k : DBId) (gtT ltT : Term) :
  TEq (Ishift k (select_neq i (dbshift i j) gtT ltT)) (select_neq i (dbshift i j) (Ishift k gtT) (Ishift k ltT));
symbol aux_Ishift_select_neqI (i j k : DBId) (gtT ltT : ITerm) :
  ITEq (IshiftI k (select_neqI i (dbshift i j) gtT ltT))
       (select_neqI i (dbshift i j) (IshiftI k gtT) (IshiftI k ltT));
symbol aux_Ishift_select_neqF (i j k : DBId) (gtT ltT : FTerm) :
  FTEq (IshiftF k (select_neqF i (dbshift i j) gtT ltT))
       (select_neqF i (dbshift i j) (IshiftF k gtT) (IshiftF k ltT));
// aux_select_neq_Sn
symbol aux_select_neqI_Sn (i j : DBId) (gtT : ITerm) :
  ITEq (select_neqI i (dbshift i j) gtT (itvar (dbshift i j)))
       (select_neqI i (dbshift i j) gtT (itvar (dbsucc (dbprev (dbshift i j)))));
symbol aux_select_neqF_Sn0 (i j : DBId) (gtT : FTerm) :
  FTEq (select_neqF i (dbshift i j) gtT (fteq0 (dbshift i j)))
       (select_neqF i (dbshift i j) gtT (fteq0 (dbsucc (dbprev (dbshift i j)))));
symbol aux_select_neqF_Sn1 (i j : DBId) (gtT : FTerm) :
  FTEq (select_neqF i (dbshift i j) gtT (fteq1 (dbshift i j)))
       (select_neqF i (dbshift i j) gtT (fteq1 (dbsucc (dbprev (dbshift i j)))));
// aux_shift_cancel_select_neq
symbol aux_shift_cancel_select_neqI (i n : DBId) :
  ITEq (select_neqI i (dbshift i n) (itvar (dbshift i n)) (itvar (dbprev (dbshift i n)))) (itvar n);
symbol aux_shift_cancel_select_neqF0 (i n : DBId) :
  FTEq (select_neqF i (dbshift i n) (fteq0 (dbshift i n)) (fteq0 (dbprev (dbshift i n)))) (fteq0 n);
symbol aux_shift_cancel_select_neqF1 (i n : DBId) :
  FTEq (select_neqF i (dbshift i n) (fteq1 (dbshift i n)) (fteq1 (dbprev (dbshift i n)))) (fteq1 n);

rule aux_teq_shift_neqI db0 db0 _ _ $ltT ↪ ITRefl $ltT
with aux_teq_shift_neqI (dbsucc _) db0 _ $gtT _ ↪ ITRefl $gtT
with aux_teq_shift_neqI db0 (dbsucc _) _ _ $ltT ↪ ITRefl $ltT
with aux_teq_shift_neqI (dbsucc $i) (dbsucc $n) $eqT $gtT $ltT ↪ aux_teq_shift_neqI $i $n $eqT $gtT $ltT
with aux_teq_shift_neqF db0 db0 _ _ $ltT ↪ FTRefl $ltT
with aux_teq_shift_neqF (dbsucc _) db0 _ $gtT _ ↪ FTRefl $gtT
with aux_teq_shift_neqF db0 (dbsucc _) _ _ $ltT ↪ FTRefl $ltT
with aux_teq_shift_neqF (dbsucc $i) (dbsucc $n) $eqT $gtT $ltT ↪ aux_teq_shift_neqF $i $n $eqT $gtT $ltT
with aux_Ishift_select_neq db0 db0 $k _ $ltT ↪ TRefl (Ishift $k $ltT)
with aux_Ishift_select_neq (dbsucc _) db0 $k $gtT _ ↪ TRefl (Ishift $k $gtT)
with aux_Ishift_select_neq db0 (dbsucc _) $k _ $ltT ↪ TRefl (Ishift $k $ltT)
with aux_Ishift_select_neq (dbsucc $i) (dbsucc $j) $k $gtT $ltT ↪ aux_Ishift_select_neq $i $j $k $gtT $ltT
with aux_Ishift_select_neqI db0 db0 $k _ $ltT ↪ ITRefl (IshiftI $k $ltT)
with aux_Ishift_select_neqI (dbsucc _) db0 $k $gtT _ ↪ ITRefl (IshiftI $k $gtT)
with aux_Ishift_select_neqI db0 (dbsucc _) $k _ $ltT ↪ ITRefl (IshiftI $k $ltT)
with aux_Ishift_select_neqI (dbsucc $i) (dbsucc $j) $k $gtT $ltT ↪ aux_Ishift_select_neqI $i $j $k $gtT $ltT
with aux_Ishift_select_neqF db0 db0 $k _ $ltT ↪ FTRefl (IshiftF $k $ltT)
with aux_Ishift_select_neqF (dbsucc _) db0 $k $gtT _ ↪ FTRefl (IshiftF $k $gtT)
with aux_Ishift_select_neqF db0 (dbsucc _) $k _ $ltT ↪ FTRefl (IshiftF $k $ltT)
with aux_Ishift_select_neqF (dbsucc $i) (dbsucc $j) $k $gtT $ltT ↪ aux_Ishift_select_neqF $i $j $k $gtT $ltT
with aux_select_neqI_Sn db0 $n _ ↪ ITRefl (itvar (dbsucc $n))
with aux_select_neqI_Sn (dbsucc _) db0 $gtT ↪ ITRefl $gtT
with aux_select_neqI_Sn (dbsucc $i) (dbsucc $n) $gtT ↪
      ITRefl (select_neqI $i (dbshift $i $n) $gtT (itvar (dbsucc (dbshift $i $n))))
with aux_select_neqF_Sn0 db0 $n _ ↪ FTRefl (fteq0 (dbsucc $n))
with aux_select_neqF_Sn0 (dbsucc _) db0 $gtT ↪ FTRefl $gtT
with aux_select_neqF_Sn0 (dbsucc $i) (dbsucc $n) $gtT ↪
      FTRefl (select_neqF $i (dbshift $i $n) $gtT (fteq0 (dbsucc (dbshift $i $n))))
with aux_select_neqF_Sn1 db0 $n _ ↪ FTRefl (fteq1 (dbsucc $n))
with aux_select_neqF_Sn1 (dbsucc _) db0 $gtT ↪ FTRefl $gtT
with aux_select_neqF_Sn1 (dbsucc $i) (dbsucc $n) $gtT ↪
      FTRefl (select_neqF $i (dbshift $i $n) $gtT (fteq1 (dbsucc (dbshift $i $n))))
with aux_shift_cancel_select_neqI db0 $n ↪ ITRefl (itvar $n)
with aux_shift_cancel_select_neqI (dbsucc _) db0 ↪ ITRefl (itvar db0)
with aux_shift_cancel_select_neqI (dbsucc $i) (dbsucc $n) ↪
      iteq_trans
       (iteq_trans
         (aux_select_neqI_Sn $i $n (itvar (dbsucc (dbshift $i $n))))
         (iteq_inv (aux_Ishift_select_neqI $i $n db0 (itvar (dbshift $i $n)) (itvar (dbprev (dbshift $i $n))))))
       (IJcong IShiftI (aux_shift_cancel_select_neqI $i $n))
with aux_shift_cancel_select_neqF0 db0 $n ↪ FTRefl (fteq0 $n)
with aux_shift_cancel_select_neqF0 (dbsucc _) db0 ↪ FTRefl (fteq0 db0)
with aux_shift_cancel_select_neqF0 (dbsucc $i) (dbsucc $n) ↪
      fteq_trans
       (fteq_trans
         (aux_select_neqF_Sn0 $i $n (fteq0 (dbsucc (dbshift $i $n))))
         (fteq_inv (aux_Ishift_select_neqF $i $n db0 (fteq0 (dbshift $i $n)) (fteq0 (dbprev (dbshift $i $n))))))
       (FJcong IShiftF (aux_shift_cancel_select_neqF0 $i $n))
with aux_shift_cancel_select_neqF1 db0 $n ↪ FTRefl (fteq1 $n)
with aux_shift_cancel_select_neqF1 (dbsucc _) db0 ↪ FTRefl (fteq1 db0)
with aux_shift_cancel_select_neqF1 (dbsucc $i) (dbsucc $n) ↪
      fteq_trans
       (fteq_trans
         (aux_select_neqF_Sn1 $i $n (fteq1 (dbsucc (dbshift $i $n))))
         (fteq_inv (aux_Ishift_select_neqF $i $n db0 (fteq1 (dbshift $i $n)) (fteq1 (dbprev (dbshift $i $n))))))
       (FJcong IShiftF (aux_shift_cancel_select_neqF1 $i $n))
;

rule aux_teq_Ishift_cancel_Isubst _ _ (tvar $n) ↪ TRefl (tvar $n)
with aux_teq_Ishift_cancel_Isubst _ _ (tuniv $s) ↪ TRefl (tuniv $s)
with aux_teq_Ishift_cancel_Isubst $i $u (tpi $A $B) ↪
      Jpi (aux_teq_Ishift_cancel_Isubst $i $u $A)
          (aux_teq_Ishift_cancel_Isubst $i $u $B)
with aux_teq_Ishift_cancel_Isubst $i $u (tabs $A $t) ↪
      Jabs (aux_teq_Ishift_cancel_Isubst $i $u $A)
           (aux_teq_Ishift_cancel_Isubst $i $u $t)
with aux_teq_Ishift_cancel_Isubst $i $u (tapp $f $a) ↪
      Japp (aux_teq_Ishift_cancel_Isubst $i $u $f)
           (aux_teq_Ishift_cancel_Isubst $i $u $a)
with aux_teq_Ishift_cancel_Isubst _ _ tnat ↪ TRefl tnat
with aux_teq_Ishift_cancel_Isubst _ _ tzero ↪ TRefl tzero
with aux_teq_Ishift_cancel_Isubst $i $u (tsuc $n) ↪
      Jcong tsuc (aux_teq_Ishift_cancel_Isubst $i $u $n)
with aux_teq_Ishift_cancel_Isubst $i $u (trec $P $z $H $n) ↪
      Jrec (aux_teq_Ishift_cancel_Isubst $i $u $P)
           (aux_teq_Ishift_cancel_Isubst $i $u $z)
           (aux_teq_Ishift_cancel_Isubst $i $u $H)
           (aux_teq_Ishift_cancel_Isubst $i $u $n)
with aux_teq_Ishift_cancel_Isubst $i $u (tsig $A $B) ↪
      Jsig (aux_teq_Ishift_cancel_Isubst $i $u $A)
           (aux_teq_Ishift_cancel_Isubst $i $u $B)
with aux_teq_Ishift_cancel_Isubst $i $u (tpair $a $b) ↪
      Jpair (aux_teq_Ishift_cancel_Isubst $i $u $a)
            (aux_teq_Ishift_cancel_Isubst $i $u $b)
with aux_teq_Ishift_cancel_Isubst $i $u (tp1 $p) ↪
      Jcong tp1 (aux_teq_Ishift_cancel_Isubst $i $u $p)
with aux_teq_Ishift_cancel_Isubst $i $u (tp2 $p) ↪
      Jcong tp2 (aux_teq_Ishift_cancel_Isubst $i $u $p)
with aux_teq_Ishift_cancel_Isubst $i $u (tsum $A $B) ↪
      Jsum (aux_teq_Ishift_cancel_Isubst $i $u $A)
           (aux_teq_Ishift_cancel_Isubst $i $u $B)
with aux_teq_Ishift_cancel_Isubst $i $u (tinjl $p) ↪
      Jcong tinjl (aux_teq_Ishift_cancel_Isubst $i $u $p)
with aux_teq_Ishift_cancel_Isubst $i $u (tinjr $p) ↪
      Jcong tinjr (aux_teq_Ishift_cancel_Isubst $i $u $p)
with aux_teq_Ishift_cancel_Isubst $i $u (tcase $A $B $P $Ha $Hb $x) ↪
      Jcase (aux_teq_Ishift_cancel_Isubst $i $u $A)
            (aux_teq_Ishift_cancel_Isubst $i $u $B)
            (aux_teq_Ishift_cancel_Isubst $i $u $P)
            (aux_teq_Ishift_cancel_Isubst $i $u $Ha)
            (aux_teq_Ishift_cancel_Isubst $i $u $Hb)
            (aux_teq_Ishift_cancel_Isubst $i $u $x)
with aux_teq_Ishift_cancel_Isubst $i $u (tpath $A $x $y) ↪
      Jpath (aux_teq_Ishift_cancel_Isubst (dbsucc $i) (IShiftI $u) $A)
            (aux_teq_Ishift_cancel_Isubst $i $u $x)
            (aux_teq_Ishift_cancel_Isubst $i $u $y)
with aux_teq_Ishift_cancel_Isubst $i $u (tlamP $x) ↪
      Jcong tlamP (aux_teq_Ishift_cancel_Isubst (dbsucc $i) (IShiftI $u) $x)
with aux_teq_Ishift_cancel_Isubst $i $u (tappP $x $y) ↪
      JappP (aux_teq_Ishift_cancel_Isubst $i $u $x)
            (aux_teq_IshiftI_cancel_IsubstI $i $u $y)
with aux_teq_Ishift_cancel_Isubst $i $u (tsys $f $g $x $y) ↪
      Jsys (aux_teq_IshiftF_cancel_IsubstF $i $u $f)
           (aux_teq_IshiftF_cancel_IsubstF $i $u $g)
           (aux_teq_Ishift_cancel_Isubst $i $u $x)
           (aux_teq_Ishift_cancel_Isubst $i $u $y)
with aux_teq_Ishift_cancel_Isubst _ _ temptysys ↪ TRefl temptysys
with aux_teq_Ishift_cancel_Isubst $i $u (ttransp $A $f $x) ↪
      Jtransp (aux_teq_Ishift_cancel_Isubst $i $u $A)
              (aux_teq_IshiftF_cancel_IsubstF $i $u $f)
              (aux_teq_Ishift_cancel_Isubst $i $u $x)
with aux_teq_Ishift_cancel_Isubst $i $u (thcomp $A $f $x $y) ↪
      Jhcomp (aux_teq_Ishift_cancel_Isubst $i $u $A)
             (aux_teq_IshiftF_cancel_IsubstF $i $u $f)
             (aux_teq_Ishift_cancel_Isubst $i $u $x)
             (aux_teq_Ishift_cancel_Isubst $i $u $y)
with aux_teq_IshiftI_cancel_IsubstI _ _ it0 ↪ ITRefl it0
with aux_teq_IshiftI_cancel_IsubstI _ _ it1 ↪ ITRefl it1
with aux_teq_IshiftI_cancel_IsubstI $i $u (itvar $n) ↪
      iteq_trans
       (aux_teq_shift_neqI $i $n $u (itvar (dbshift $i $n)) (itvar (dbprev (dbshift $i $n))))
       (aux_shift_cancel_select_neqI $i $n)
with aux_teq_IshiftI_cancel_IsubstI $i $u (itsym $n) ↪
      IJcong itsym (aux_teq_IshiftI_cancel_IsubstI $i $u $n)
with aux_teq_IshiftI_cancel_IsubstI $i $u (itmin $x $y) ↪
      IJmin (aux_teq_IshiftI_cancel_IsubstI $i $u $x)
            (aux_teq_IshiftI_cancel_IsubstI $i $u $y)
with aux_teq_IshiftI_cancel_IsubstI $i $u (itmax $x $y) ↪
      IJmax (aux_teq_IshiftI_cancel_IsubstI $i $u $x)
            (aux_teq_IshiftI_cancel_IsubstI $i $u $y)
with aux_teq_IshiftF_cancel_IsubstF _ _ ft0 ↪ FTRefl ft0
with aux_teq_IshiftF_cancel_IsubstF _ _ ft1 ↪ FTRefl ft1
with aux_teq_IshiftF_cancel_IsubstF $i $u (fteq0 $n) ↪
      fteq_trans
       (aux_teq_shift_neqF $i $n (substeq0 $u) (fteq0 (dbshift $i $n)) (fteq0 (dbprev (dbshift $i $n))))
       (aux_shift_cancel_select_neqF0 $i $n)
with aux_teq_IshiftF_cancel_IsubstF $i $u (fteq1 $n) ↪
      fteq_trans
       (aux_teq_shift_neqF $i $n (substeq1 $u) (fteq1 (dbshift $i $n)) (fteq1 (dbprev (dbshift $i $n))))
       (aux_shift_cancel_select_neqF1 $i $n)
with aux_teq_IshiftF_cancel_IsubstF $i $u (ftmin $x $y) ↪
      FJmin (aux_teq_IshiftF_cancel_IsubstF $i $u $x)
            (aux_teq_IshiftF_cancel_IsubstF $i $u $y)
with aux_teq_IshiftF_cancel_IsubstF $i $u (ftmax $x $y) ↪
      FJmax (aux_teq_IshiftF_cancel_IsubstF $i $u $x)
            (aux_teq_IshiftF_cancel_IsubstF $i $u $y)
;

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
symbol aux_teq_subst_subst_Irec (i j : DBId) (u t1 t2 : Term) (h : DBLe j i) ≔
  teq_trans (Jcong (λ v, subst i v (subst j (IShift (Shift* j t1)) t2)) (teq_inv (aux_teq_Shift*_Ishift i db0 u)))
            (teq_trans (Jcong (λ v, subst i (Shift* i (IShift u)) (subst j v t2))
                              (teq_inv (aux_teq_Shift*_Ishift j db0 t1)))
                       (teq_trans
                         (teq_trans
                           (teq_trans
                             (teq_trans (aux_teq_subst_subst i j (IShift u) (IShift t1) t2 h)
                                        (Jcong (λ v, subst j (subst i (Shift* i (IShift u)) (Shift* j (IShift t1)))
                                                           (subst (dbsucc i) v t2))
                                               (aux_teq_Shift*_Ishift (dbsucc i) db0 u)))
                             (Jcong (λ v, subst j (subst i (Shift* i (IShift u)) v)
                                                (subst (dbsucc i) (IShift (Shift* (dbsucc i) u)) t2))
                                    (aux_teq_Shift*_Ishift j db0 t1)))
                           (Jcong (λ v, subst j (subst i v (IShift (Shift* j t1)))
                                              (subst (dbsucc i) (IShift (Shift* (dbsucc i) u)) t2))
                                  (aux_teq_Shift*_Ishift i db0 u)))
                         (Jcong (λ v, subst j v (subst (dbsucc i) (IShift (Shift* (dbsucc i) u)) t2))
                                (aux_teq_subst_Ishift i db0 u (Shift* j t1)))));

// aux_teq_subst_subst_var
symbol aux_teq_subst_subst_var (i j : DBId) (u t : Term) (n : DBId) :
  DBLe j i
  → TEq (dbselect j n
                  (subst i (Shift* i u) (Shift* j t))
                  (dbselect i n (Shift* i u) (tvar n) (tvar (dbprev n)))
                  (dbselect i (dbprev n) (Shift* i u) (tvar (dbprev n)) (tvar (dbprev (dbprev n)))))
        (dbselect (dbsucc i) n
                  (subst j (subst i (Shift* i u) (Shift* j t)) (Shift* (dbsucc i) u))
                  (dbselect j n (subst i (Shift* i u) (Shift* j t)) (tvar n) (tvar (dbprev n)))
                  (dbselect j (dbprev n) (subst i (Shift* i u) (Shift* j t)) (tvar (dbprev n))
                            (tvar (dbprev (dbprev n)))));

rule aux_teq_subst_subst_var $i db0 $u $t db0 _ ↪
      TRefl (subst $i (Shift* $i $u) $t)
with aux_teq_subst_subst_var (dbsucc _) (dbsucc _) _ _ db0 _ ↪
      TRefl (tvar db0)
with aux_teq_subst_subst_var db0 db0 $u _ (dbsucc db0) _ ↪
      TRefl $u
with aux_teq_subst_subst_var (dbsucc _) db0 _ _ (dbsucc db0) _ ↪
      TRefl (tvar db0)
with aux_teq_subst_subst_var db0 db0 _ _ (dbsucc (dbsucc $n)) _ ↪
      TRefl (tvar $n)
with aux_teq_subst_subst_var (dbsucc $i) db0 $u $t (dbsucc (dbsucc $n)) _ ↪
      Jselect $i $n
       (teq_inv (aux_teq_shift_cancel_subst db0 (subst (dbsucc $i) (Shift* (dbsucc $i) $u) $t)
                                            (Shift* (dbsucc $i) $u)))
       (TRefl (tvar (dbsucc $n)))
       (TRefl (tvar $n))
with aux_teq_subst_subst_var (dbsucc $i) (dbsucc $j) $u $t (dbsucc $n) $h ↪
      teq_trans
       (teq_trans
         (aux_teq_dbselect_fn $j $n
           (subst (dbsucc $i) (Shift* (dbsucc $i) $u) (Shift* (dbsucc $j) $t))
           (dbselect (dbsucc $i) (dbsucc $n) (Shift* (dbsucc $i) $u) (tvar (dbsucc $n)) (tvar $n))
           (λ n, dbselect (dbsucc $i) n (Shift* (dbsucc $i) $u) (tvar n) (tvar (dbprev n))))
         (teq_trans
           (Jselect $j $n
             (teq_subst_shift $i (Shift* $i $u) (Shift* $j $t))
             (teq_select_shift $i $n (Shift* $i $u))
             (teq_select_shift $i (dbprev $n) (Shift* $i $u)))
           (teq_inv (aux_teq_shift_dbselect0 $j $n
             (subst $i (Shift* $i $u) (Shift* $j $t))
             (dbselect $i $n (Shift* $i $u) (tvar $n) (tvar (dbprev $n)))
             (dbselect $i (dbprev $n) (Shift* $i $u) (tvar (dbprev $n)) (tvar (dbprev (dbprev $n))))))))
       (teq_trans
         (Jcong Shift (aux_teq_subst_subst_var $i $j $u $t $n (dble_S_n $h)))
         (teq_trans
           (aux_teq_shift_dbselect0 (dbsucc $i) $n
             (subst $j (subst $i (Shift* $i $u) (Shift* $j $t)) (Shift* (dbsucc $i) $u))
             (dbselect $j $n (subst $i (Shift* $i $u) (Shift* $j $t)) (tvar $n) (tvar (dbprev $n)))
             (dbselect $j (dbprev $n) (subst $i (Shift* $i $u) (Shift* $j $t))
                          (tvar (dbprev $n)) (tvar (dbprev (dbprev $n)))))
           (teq_trans
             (teq_trans
               (Jselect (dbsucc $i) $n
                 (teq_inv (teq_subst_shift $j (subst $i (Shift* $i $u) (Shift* $j $t)) (Shift* (dbsucc $i) $u)))
                 (teq_inv (teq_select_shift $j $n (subst $i (Shift* $i $u) (Shift* $j $t))))
                 (teq_inv (teq_select_shift $j (dbprev $n) (subst $i (Shift* $i $u) (Shift* $j $t)))))
               (teq_inv (aux_teq_dbselect_fn (dbsucc $i) $n
                 (subst (dbsucc $j) (Shift (subst $i (Shift* $i $u) (Shift* $j $t))) (Shift* (dbsucc (dbsucc $i)) $u))
                 (dbselect $j $n (Shift (subst $i (Shift* $i $u) (Shift* $j $t))) (tvar (dbsucc $n)) (tvar $n))
                 (λ n, dbselect (dbsucc $j) n (Shift (subst $i (Shift* $i $u) (Shift* $j $t)))
                                (tvar n) (tvar (dbprev $n))))))
             (Jcong (λ t, dbselect (dbsucc $i) $n (subst (dbsucc $j) t (Shift* (dbsucc (dbsucc $i)) $u))
                                   (dbselect $j $n t (tvar (dbsucc $n)) (tvar $n))
                                   (dbselect (dbsucc $j) $n t (tvar $n) (tvar (dbprev $n))))
                    (teq_inv (teq_subst_shift $i (Shift* $i $u) (Shift* $j $t)))))));

rule aux_teq_subst_subst $i $j $u $t1 (tvar $n) $h ↪
      teq_trans
       (aux_teq_subst_dbselect $j $n $i (Shift* $i $u) (Shift* $j $t1) (tvar $n) (tvar (dbprev $n)))
       (teq_trans
         (aux_teq_subst_subst_var $i $j $u $t1 $n $h)
         (teq_inv (aux_teq_subst_dbselect (dbsucc $i) $n $j
                    (subst $i (Shift* $i $u) (Shift* $j $t1))
                    (Shift* (dbsucc $i) $u)
                    (tvar $n) (tvar (dbprev $n)))))
with aux_teq_subst_subst _ _ _ _ (tuniv $s) _ ↪ TRefl (tuniv $s)
with aux_teq_subst_subst $i $j $u $t1 (tpi $A $B) $h ↪
      Jpi (aux_teq_subst_subst $i $j $u $t1 $A $h)
          (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
with aux_teq_subst_subst $i $j $u $t1 (tabs $A $t) $h ↪
      Jabs (aux_teq_subst_subst $i $j $u $t1 $A $h)
           (aux_teq_subst_subst_rec $i $j $u $t1 $t $h)
with aux_teq_subst_subst $i $j $u $t1 (tapp $f $a) $h ↪
      Japp (aux_teq_subst_subst $i $j $u $t1 $f $h)
           (aux_teq_subst_subst $i $j $u $t1 $a $h)
with aux_teq_subst_subst _ _ _ _ tnat _ ↪ TRefl tnat
with aux_teq_subst_subst _ _ _ _ tzero _ ↪ TRefl tzero
with aux_teq_subst_subst $i $j $u $t1 (tsuc $n) $h ↪
      Jcong tsuc (aux_teq_subst_subst $i $j $u $t1 $n $h)
with aux_teq_subst_subst $i $j $u $t1 (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_subst_subst $i $j $u $t1 $P $h)
           (aux_teq_subst_subst $i $j $u $t1 $z $h)
           (aux_teq_subst_subst $i $j $u $t1 $H $h)
           (aux_teq_subst_subst $i $j $u $t1 $n $h)
with aux_teq_subst_subst $i $j $u $t1 (tsig $A $B) $h ↪
      Jsig (aux_teq_subst_subst $i $j $u $t1 $A $h)
           (aux_teq_subst_subst_rec $i $j $u $t1 $B $h)
with aux_teq_subst_subst $i $j $u $t1 (tpair $a $b) $h ↪
      Jpair (aux_teq_subst_subst $i $j $u $t1 $a $h)
            (aux_teq_subst_subst $i $j $u $t1 $b $h)
with aux_teq_subst_subst $i $j $u $t1 (tp1 $p) $h ↪
      Jcong tp1 (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (tp2 $p) $h ↪
      Jcong tp2 (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (tsum $A $B) $h ↪
      Jsum (aux_teq_subst_subst $i $j $u $t1 $A $h)
           (aux_teq_subst_subst $i $j $u $t1 $B $h)
with aux_teq_subst_subst $i $j $u $t1 (tinjl $p) $h ↪
      Jcong tinjl (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (tinjr $p) $h ↪
      Jcong tinjr (aux_teq_subst_subst $i $j $u $t1 $p $h)
with aux_teq_subst_subst $i $j $u $t1 (tcase $A $B $P $Ha $Hb $t) $h ↪
      Jcase (aux_teq_subst_subst $i $j $u $t1 $A $h)
            (aux_teq_subst_subst $i $j $u $t1 $B $h)
            (aux_teq_subst_subst $i $j $u $t1 $P $h)
            (aux_teq_subst_subst $i $j $u $t1 $Ha $h)
            (aux_teq_subst_subst $i $j $u $t1 $Hb $h)
            (aux_teq_subst_subst $i $j $u $t1 $t $h)
with aux_teq_subst_subst $i $j $u $t1 (tpath $A $x $y) $h ↪
      Jpath (aux_teq_subst_subst_Irec $i $j $u $t1 $A $h)
            (aux_teq_subst_subst $i $j $u $t1 $x $h)
            (aux_teq_subst_subst $i $j $u $t1 $y $h)
with aux_teq_subst_subst $i $j $u $t1 (tlamP $t) $h ↪
      Jcong tlamP (aux_teq_subst_subst_Irec $i $j $u $t1 $t $h)
with aux_teq_subst_subst $i $j $u $t1 (tappP $x $y) $h ↪
      JappP (aux_teq_subst_subst $i $j $u $t1 $x $h) (ITRefl $y)
with aux_teq_subst_subst $i $j $u $t1 (tsys _ _ $x $y) $h ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_subst_subst $i $j $u $t1 $x $h)
           (aux_teq_subst_subst $i $j $u $t1 $y $h)
with aux_teq_subst_subst _ _ _ _ temptysys _ ↪ TRefl temptysys
with aux_teq_subst_subst $i $j $u $t1 (ttransp $A _ $x) $h ↪
      Jtransp (aux_teq_subst_subst_Irec $i $j $u $t1 $A $h)
              (FTRefl _)
              (aux_teq_subst_subst $i $j $u $t1 $x $h)
with aux_teq_subst_subst $i $j $u $t1 (thcomp $A _ $x $y) $h ↪
      Jhcomp (aux_teq_subst_subst $i $j $u $t1 $A $h)
             (FTRefl _)
             (aux_teq_subst_subst_Irec $i $j $u $t1 $x $h)
             (aux_teq_subst_subst $i $j $u $t1 $y $h);

// teq_subst_apply
symbol teq_subst_apply (i : DBId) (u t1 t2 : Term) :
  TEq (subst i (Shift* i u) (apply1 t2 t1))
      (apply1 (subst (dbsucc i) (Shift* (dbsucc i) u) t2) (subst i (Shift* i u) t1)) ≔
  aux_teq_subst_subst i db0 u t1 t2 (dble_0_n i);

// teq_Isubst_Isubst
symbol aux_teq_Isubst_Isubst (i j : DBId) (u t1 : ITerm) (t2 : Term) :
  DBLe j i
  → TEq (Isubst i (IShiftI* i u) (Isubst j (IShiftI* j t1) t2))
        (Isubst j (IsubstI i (IShiftI* i u) (IShiftI* j t1)) (Isubst (dbsucc i) (IShiftI* (dbsucc i) u) t2));
symbol aux_teq_IsubstI_IsubstI (i j : DBId) (u t1 t2 : ITerm) :
  DBLe j i
  → ITEq (IsubstI i (IShiftI* i u) (IsubstI j (IShiftI* j t1) t2))
         (IsubstI j (IsubstI i (IShiftI* i u) (IShiftI* j t1)) (IsubstI (dbsucc i) (IShiftI* (dbsucc i) u) t2));
symbol aux_teq_IsubstF_IsubstF (i j : DBId) (u t1 : ITerm) (t2 : FTerm) :
  DBLe j i
  → FTEq (IsubstF i (IShiftI* i u) (IsubstF j (IShiftI* j t1) t2))
         (IsubstF j (IsubstI i (IShiftI* i u) (IShiftI* j t1)) (IsubstF (dbsucc i) (IShiftI* (dbsucc i) u) t2));

symbol aux_teq_Isubst_Isubst_Irec (i j : DBId) (u t1 : ITerm) (t2 : Term) (h : DBLe j i) ≔
  teq_trans (aux_teq_Isubst_Isubst (dbsucc i) (dbsucc j) u t1 t2 (dble_n_S h))
            (IcongT (λ t, Isubst (dbsucc j) t (Isubst (dbsucc (dbsucc i)) (IShiftI* (dbsucc (dbsucc i)) u) t2))
                    (teq_IsubstI_IshiftI i (IShiftI* i u) (IShiftI* j t1)));

// aux_teq_Isubst_Isubst_itvar
symbol aux_teq_Isubst_Isubst_itvar (i j : DBId) (u t : ITerm) (n : DBId) :
  DBLe j i →
  ITEq (dbselectI j n
                  (IsubstI i (IShiftI* i u) (IShiftI* j t))
                  (dbselectI i n (IShiftI* i u) (itvar n) (itvar (dbprev n)))
                  (dbselectI i (dbprev n) (IShiftI* i u) (itvar (dbprev n)) (itvar (dbprev (dbprev n)))))
       (dbselectI (dbsucc i) n
                  (IsubstI j (IsubstI i (IShiftI* i u) (IShiftI* j t)) (IShiftI* (dbsucc i) u))
                  (dbselectI j n (IsubstI i (IShiftI* i u) (IShiftI* j t)) (itvar n) (itvar (dbprev n)))
                  (dbselectI j (dbprev n) (IsubstI i (IShiftI* i u) (IShiftI* j t)) (itvar (dbprev n))
                             (itvar (dbprev (dbprev n)))));

rule aux_teq_Isubst_Isubst_itvar $i db0 $u $t db0 _ ↪
      ITRefl (IsubstI $i (IShiftI* $i $u) $t)
with aux_teq_Isubst_Isubst_itvar (dbsucc _) (dbsucc _) _ _ db0 _ ↪
      ITRefl (itvar db0)
with aux_teq_Isubst_Isubst_itvar db0 db0 $u _ (dbsucc db0) _ ↪
      ITRefl $u
with aux_teq_Isubst_Isubst_itvar (dbsucc _) db0 _ _ (dbsucc db0) _ ↪
      ITRefl (itvar db0)
with aux_teq_Isubst_Isubst_itvar db0 db0 _ _ (dbsucc (dbsucc $n)) _ ↪
      ITRefl (itvar $n)
with aux_teq_Isubst_Isubst_itvar (dbsucc $i) db0 $u $t (dbsucc (dbsucc $n)) _ ↪
      IJselect $i $n
               (iteq_inv (aux_teq_IshiftI_cancel_IsubstI db0 (IsubstI (dbsucc $i) (IShiftI* (dbsucc $i) $u) $t)
                                                         (IShiftI* (dbsucc $i) $u)))
               (ITRefl (itvar (dbsucc $n)))
               (ITRefl (itvar $n))
with aux_teq_Isubst_Isubst_itvar (dbsucc $i) (dbsucc $j) $u $t (dbsucc $n) $h ↪
      iteq_trans
       (iteq_trans
         (aux_teq_dbselectI_fn $j $n
                               (IsubstI (dbsucc $i) (IShiftI* (dbsucc $i) $u) (IShiftI* (dbsucc $j) $t))
                               (dbselectI (dbsucc $i) (dbsucc $n) (IShiftI* (dbsucc $i) $u)
                                          (itvar (dbsucc $n)) (itvar $n))
                               (λ n, dbselectI (dbsucc $i) n (IShiftI* (dbsucc $i) $u)
                                               (itvar n) (itvar (dbprev n))))
         (iteq_trans
           (IJselect $j $n
                         (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t))
                         (teq_select_IshiftI $i $n (IShiftI* $i $u))
                         (teq_select_IshiftI $i (dbprev $n) (IShiftI* $i $u)))
           (iteq_inv (aux_teq_shift_dbselectI0 $j $n
                                               (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                               (dbselectI $i $n (IShiftI* $i $u) (itvar $n) (itvar (dbprev $n)))
                                               (dbselectI $i (dbprev $n) (IShiftI* $i $u)
                                                             (itvar (dbprev $n)) (itvar (dbprev (dbprev $n))))))))
       (iteq_trans
         (IJcong IShiftI (aux_teq_Isubst_Isubst_itvar $i $j $u $t $n (dble_S_n $h)))
         (iteq_trans
           (aux_teq_shift_dbselectI0 (dbsucc $i) $n
                                     (IsubstI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                 (IShiftI* (dbsucc $i) $u))
                                     (dbselectI $j $n (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                      (itvar $n) (itvar (dbprev $n)))
                                     (dbselectI $j (dbprev $n) (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                   (itvar (dbprev $n)) (itvar (dbprev (dbprev $n)))))
           (iteq_trans
             (iteq_trans
               (IJselect (dbsucc $i) $n
                         (iteq_inv (teq_IsubstI_IshiftI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                           (IShiftI* (dbsucc $i) $u)))
                         (iteq_inv (teq_select_IshiftI $j $n (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))))
                         (iteq_inv (teq_select_IshiftI $j (dbprev $n) (IsubstI $i (IShiftI* $i $u)
                                                                                  (IShiftI* $j $t)))))
               (iteq_inv (aux_teq_dbselectI_fn (dbsucc $i) $n
                                               (IsubstI (dbsucc $j) (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                          (IShiftI* $j $t)))
                                                        (IShiftI* (dbsucc (dbsucc $i)) $u))
                                               (dbselectI $j $n (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t)))
                                                                (itvar (dbsucc $n)) (itvar $n))
                                               (λ n, dbselectI (dbsucc $j) n (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                                   (IShiftI* $j $t)))
                                                               (itvar n) (itvar (dbprev $n))))))
             (IJcong (λ t, dbselectI (dbsucc $i) $n (IsubstI (dbsucc $j) t (IShiftI* (dbsucc (dbsucc $i)) $u))
                                                  (dbselectI $j $n t (itvar (dbsucc $n)) (itvar $n))
                                                  (dbselectI (dbsucc $j) $n t (itvar $n) (itvar (dbprev $n))))
                    (iteq_inv (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t)))))));

// aux_teq_Isubst_Isubst_fteq0
symbol aux_teq_Isubst_Isubst_fteq0 (i j : DBId) (u t : ITerm) (n : DBId) :
  DBLe j i →
  FTEq (dbselectF j n
                  (substeq0 (IsubstI i (IShiftI* i u) (IShiftI* j t)))
                  (dbselectF i n (substeq0 (IShiftI* i u)) (fteq0 n) (fteq0 (dbprev n)))
                  (dbselectF i (dbprev n) (substeq0 (IShiftI* i u)) (fteq0 (dbprev n)) (fteq0 (dbprev (dbprev n)))))
       (dbselectF (dbsucc i) n
                  (substeq0 (IsubstI j (IsubstI i (IShiftI* i u) (IShiftI* j t)) (IShiftI* (dbsucc i) u)))
                  (dbselectF j n (substeq0 (IsubstI i (IShiftI* i u) (IShiftI* j t))) (fteq0 n) (fteq0 (dbprev n)))
                  (dbselectF j (dbprev n) (substeq0 (IsubstI i (IShiftI* i u) (IShiftI* j t))) (fteq0 (dbprev n))
                             (fteq0 (dbprev (dbprev n)))));

rule aux_teq_Isubst_Isubst_fteq0 $i db0 $u $t db0 _ ↪
      FTRefl (substeq0 (IsubstI $i (IShiftI* $i $u) $t))
with aux_teq_Isubst_Isubst_fteq0 (dbsucc _) (dbsucc _) _ _ db0 _ ↪
      FTRefl (fteq0 db0)
with aux_teq_Isubst_Isubst_fteq0 db0 db0 $u _ (dbsucc db0) _ ↪
      FTRefl (substeq0 $u)
with aux_teq_Isubst_Isubst_fteq0 (dbsucc _) db0 _ _ (dbsucc db0) _ ↪
      FTRefl (fteq0 db0)
with aux_teq_Isubst_Isubst_fteq0 db0 db0 _ _ (dbsucc (dbsucc $n)) _ ↪
      FTRefl (fteq0 $n)
with aux_teq_Isubst_Isubst_fteq0 (dbsucc $i) db0 $u $t (dbsucc (dbsucc $n)) _ ↪
      FJselect $i $n
               (IcongF substeq0 (iteq_inv (aux_teq_IshiftI_cancel_IsubstI db0 (IsubstI (dbsucc $i)
                                                                                       (IShiftI* (dbsucc $i) $u) $t)
                                                                          (IShiftI* (dbsucc $i) $u))))
               (FTRefl (fteq0 (dbsucc $n)))
               (FTRefl (fteq0 $n))
with aux_teq_Isubst_Isubst_fteq0 (dbsucc $i) (dbsucc $j) $u $t (dbsucc $n) $h ↪
      fteq_trans
       (aux_teq_dbselectF_fn $j $n (substeq0 (IsubstI (dbsucc $i) (IShiftI* (dbsucc $i) $u)
                                                      (IShiftI* (dbsucc $j) $t)))
                                   (dbselectF (dbsucc $i) (dbsucc $n) (substeq0 (IShiftI* (dbsucc $i) $u))
                                              (fteq0 (dbsucc $n)) (fteq0 $n))
                                   (λ n1, dbselectF (dbsucc $i) n1 (substeq0 (IShiftI* (dbsucc $i) $u))
                                                    (fteq0 n1) (fteq0 (dbprev n1))))
       (fteq_trans
         (fteq_trans
           (fteq_trans
             (FJselect $j $n (IcongF substeq0 (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t)))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbsucc $n) v
                                                                 (fteq0 (dbsucc $n)) (fteq0 $n))
                                                 (aux_teq_Ishift_substeq0 db0 (IShiftI* $i $u)))
                                         (teq_select_IshiftF0 $i $n (substeq0 (IShiftI* $i $u))))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbsucc (dbprev $n)) v
                                                                 (fteq0 (dbsucc (dbprev $n))) (fteq0 (dbprev $n)))
                                                 (aux_teq_Ishift_substeq0 db0 (IShiftI* $i $u)))
                                         (teq_select_IshiftF0 $i (dbprev $n) (substeq0 (IShiftI* $i $u)))))
             (fteq_trans
               (fteq_trans
                 (FJcong (λ v, dbselectF $j $n v (IShiftF (dbselectF $i $n (substeq0 (IShiftI* $i $u))
                                                                           (fteq0 $n) (fteq0 (dbprev $n))))
                                               (IShiftF (dbselectF $i (dbprev $n) (substeq0 (IShiftI* $i $u))
                                                                      (fteq0 (dbprev $n))
                                                                      (fteq0 (dbprev (dbprev $n))))))
                         (aux_teq_Ishift_substeq0 db0 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))))
                 (fteq_trans
                   (fteq_inv (aux_teq_shift_dbselectF0 $j $n
                                                       (substeq0 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t)))
                                                       (dbselectF $i $n (substeq0 (IShiftI* $i $u))
                                                                        (fteq0 $n) (fteq0 (dbprev $n)))
                                                       (dbselectF $i (dbprev $n) (substeq0 (IShiftI* $i $u))
                                                                  (fteq0 (dbprev $n)) (fteq0 (dbprev (dbprev $n))))))
                   (fteq_trans
                     (fteq_trans
                       (FJcong IShiftF (aux_teq_Isubst_Isubst_fteq0 $i $j $u $t $n (dble_S_n $h)))
                       (aux_teq_shift_dbselectF0 (dbsucc $i) $n
                                                 (substeq0 (IsubstI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                                       (IShiftI* (dbsucc $i) $u)))
                                                 (dbselectF $j $n (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                        (IShiftI* $j $t)))
                                                                  (fteq0 $n) (fteq0 (dbprev $n)))
                                                 (dbselectF $j (dbprev $n) (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                                 (IShiftI* $j $t)))
                                                               (fteq0 (dbprev $n)) (fteq0 (dbprev (dbprev $n))))))
                     (FJcong (λ v, dbselectF (dbsucc $i) $n v
                                             (IShiftF (dbselectF $j $n (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                             (IShiftI* $j $t)))
                                                                       (fteq0 $n) (fteq0 (dbprev $n))))
                                             (IShiftF (dbselectF $j (dbprev $n) (substeq0
                                                                                  (IsubstI $i (IShiftI* $i $u)
                                                                                              (IShiftI* $j $t)))
                                                                 (fteq0 (dbprev $n)) (fteq0 (dbprev (dbprev $n))))))
                             (fteq_inv (aux_teq_Ishift_substeq0 db0 (IsubstI $j (IsubstI $i (IShiftI* $i $u)
                                                                                            (IShiftI* $j $t))
                                                                                (IShiftI* (dbsucc $i) $u))))))))
               (FJselect (dbsucc $i) $n
                         (IcongF substeq0
                                 (iteq_inv
                                   (teq_IsubstI_IshiftI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                           (IShiftI* (dbsucc $i) $u))))
                         (fteq_trans
                           (fteq_inv (teq_select_IshiftF0 $j $n (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t)))))
                           (fteq_inv (FJcong (λ v, dbselectF $j $n v (fteq0 (dbsucc $n)) (fteq0 $n))
                                             (aux_teq_Ishift_substeq0 db0 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t))))))
                         (fteq_trans
                           (fteq_inv (teq_select_IshiftF0 $j (dbprev $n) (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                               (IShiftI* $j $t)))))
                           (fteq_inv (FJcong (λ v, dbselectF (dbsucc $j) (dbsucc (dbprev $n)) v
                                                             (fteq0 (dbsucc (dbprev $n)))
                                                             (fteq0 (dbprev (dbsucc (dbprev $n)))))
                                             (aux_teq_Ishift_substeq0 db0 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t)))))))))
           (fteq_inv (aux_teq_dbselectF_fn (dbsucc $i) $n
                                           (substeq0 (IsubstI (dbsucc $j) (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                               (IShiftI* $j $t)))
                                                              (IShiftI* (dbsucc (dbsucc $i)) $u)))
                                           (dbselectF $j $n (substeq0 (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                           (IShiftI* $j $t))))
                                                            (fteq0 (dbsucc $n)) (fteq0 $n))
                                           (λ n1, dbselectF (dbsucc $j) n1
                                                            (substeq0 (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                           (IShiftI* $j $t))))
                                                            (fteq0 n1) (fteq0 (dbprev n1))))))
         (IcongF (λ t1, dbselectF (dbsucc $i) $n
                                  (substeq0 (IsubstI (dbsucc $j) t1 (IShiftI* (dbsucc (dbsucc $i)) $u)))
                                  (dbselectF $j $n (substeq0 t1) (fteq0 (dbsucc $n)) (fteq0 $n))
                                  (dbselectF (dbsucc $j) $n (substeq0 t1) (fteq0 $n) (fteq0 (dbprev $n))))
                 (iteq_inv (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t)))));

// aux_teq_Isubst_Isubst_fteq1
symbol aux_teq_Isubst_Isubst_fteq1 (i j : DBId) (u t : ITerm) (n : DBId) :
  DBLe j i →
  FTEq (dbselectF j n
                  (substeq1 (IsubstI i (IShiftI* i u) (IShiftI* j t)))
                  (dbselectF i n (substeq1 (IShiftI* i u)) (fteq1 n) (fteq1 (dbprev n)))
                  (dbselectF i (dbprev n) (substeq1 (IShiftI* i u)) (fteq1 (dbprev n)) (fteq1 (dbprev (dbprev n)))))
       (dbselectF (dbsucc i) n
                  (substeq1 (IsubstI j (IsubstI i (IShiftI* i u) (IShiftI* j t)) (IShiftI* (dbsucc i) u)))
                  (dbselectF j n (substeq1 (IsubstI i (IShiftI* i u) (IShiftI* j t))) (fteq1 n) (fteq1 (dbprev n)))
                  (dbselectF j (dbprev n) (substeq1 (IsubstI i (IShiftI* i u) (IShiftI* j t))) (fteq1 (dbprev n))
                             (fteq1 (dbprev (dbprev n)))));

rule aux_teq_Isubst_Isubst_fteq1 $i db0 $u $t db0 _ ↪
      FTRefl (substeq1 (IsubstI $i (IShiftI* $i $u) $t))
with aux_teq_Isubst_Isubst_fteq1 (dbsucc _) (dbsucc _) _ _ db0 _ ↪
      FTRefl (fteq1 db0)
with aux_teq_Isubst_Isubst_fteq1 db0 db0 $u _ (dbsucc db0) _ ↪
      FTRefl (substeq1 $u)
with aux_teq_Isubst_Isubst_fteq1 (dbsucc _) db0 _ _ (dbsucc db0) _ ↪
      FTRefl (fteq1 db0)
with aux_teq_Isubst_Isubst_fteq1 db0 db0 _ _ (dbsucc (dbsucc $n)) _ ↪
      FTRefl (fteq1 $n)
with aux_teq_Isubst_Isubst_fteq1 (dbsucc $i) db0 $u $t (dbsucc (dbsucc $n)) _ ↪
      FJselect $i $n
               (IcongF substeq1 (iteq_inv (aux_teq_IshiftI_cancel_IsubstI db0 (IsubstI (dbsucc $i)
                                                                                       (IShiftI* (dbsucc $i) $u) $t)
                                                                          (IShiftI* (dbsucc $i) $u))))
               (FTRefl (fteq1 (dbsucc $n)))
               (FTRefl (fteq1 $n))
with aux_teq_Isubst_Isubst_fteq1 (dbsucc $i) (dbsucc $j) $u $t (dbsucc $n) $h ↪
      fteq_trans
       (aux_teq_dbselectF_fn $j $n (substeq1 (IsubstI (dbsucc $i) (IShiftI* (dbsucc $i) $u)
                                                      (IShiftI* (dbsucc $j) $t)))
                                   (dbselectF (dbsucc $i) (dbsucc $n) (substeq1 (IShiftI* (dbsucc $i) $u))
                                              (fteq1 (dbsucc $n)) (fteq1 $n))
                                   (λ n1, dbselectF (dbsucc $i) n1 (substeq1 (IShiftI* (dbsucc $i) $u))
                                                    (fteq1 n1) (fteq1 (dbprev n1))))
       (fteq_trans
         (fteq_trans
           (fteq_trans
             (FJselect $j $n (IcongF substeq1 (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t)))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbsucc $n) v
                                                                 (fteq1 (dbsucc $n)) (fteq1 $n))
                                                 (aux_teq_Ishift_substeq1 db0 (IShiftI* $i $u)))
                                         (teq_select_IshiftF1 $i $n (substeq1 (IShiftI* $i $u))))
                             (fteq_trans (FJcong (λ v, dbselectF (dbsucc $i) (dbsucc (dbprev $n)) v
                                                                 (fteq1 (dbsucc (dbprev $n))) (fteq1 (dbprev $n)))
                                                 (aux_teq_Ishift_substeq1 db0 (IShiftI* $i $u)))
                                         (teq_select_IshiftF1 $i (dbprev $n) (substeq1 (IShiftI* $i $u)))))
             (fteq_trans
               (fteq_trans
                 (FJcong (λ v, dbselectF $j $n v (IShiftF (dbselectF $i $n (substeq1 (IShiftI* $i $u))
                                                                           (fteq1 $n) (fteq1 (dbprev $n))))
                                               (IShiftF (dbselectF $i (dbprev $n) (substeq1 (IShiftI* $i $u))
                                                                      (fteq1 (dbprev $n))
                                                                      (fteq1 (dbprev (dbprev $n))))))
                         (aux_teq_Ishift_substeq1 db0 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))))
                 (fteq_trans
                   (fteq_inv (aux_teq_shift_dbselectF0 $j $n
                                                       (substeq1 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t)))
                                                       (dbselectF $i $n (substeq1 (IShiftI* $i $u))
                                                                        (fteq1 $n) (fteq1 (dbprev $n)))
                                                       (dbselectF $i (dbprev $n) (substeq1 (IShiftI* $i $u))
                                                                  (fteq1 (dbprev $n)) (fteq1 (dbprev (dbprev $n))))))
                   (fteq_trans
                     (fteq_trans
                       (FJcong IShiftF (aux_teq_Isubst_Isubst_fteq1 $i $j $u $t $n (dble_S_n $h)))
                       (aux_teq_shift_dbselectF0 (dbsucc $i) $n
                                                 (substeq1 (IsubstI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                                       (IShiftI* (dbsucc $i) $u)))
                                                 (dbselectF $j $n (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                        (IShiftI* $j $t)))
                                                                  (fteq1 $n) (fteq1 (dbprev $n)))
                                                 (dbselectF $j (dbprev $n) (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                                 (IShiftI* $j $t)))
                                                               (fteq1 (dbprev $n)) (fteq1 (dbprev (dbprev $n))))))
                     (FJcong (λ v, dbselectF (dbsucc $i) $n v
                                             (IShiftF (dbselectF $j $n (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                             (IShiftI* $j $t)))
                                                                       (fteq1 $n) (fteq1 (dbprev $n))))
                                             (IShiftF (dbselectF $j (dbprev $n) (substeq1
                                                                                  (IsubstI $i (IShiftI* $i $u)
                                                                                              (IShiftI* $j $t)))
                                                                 (fteq1 (dbprev $n)) (fteq1 (dbprev (dbprev $n))))))
                             (fteq_inv (aux_teq_Ishift_substeq1 db0 (IsubstI $j (IsubstI $i (IShiftI* $i $u)
                                                                                            (IShiftI* $j $t))
                                                                                (IShiftI* (dbsucc $i) $u))))))))
               (FJselect (dbsucc $i) $n
                         (IcongF substeq1
                                 (iteq_inv
                                   (teq_IsubstI_IshiftI $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t))
                                                           (IShiftI* (dbsucc $i) $u))))
                         (fteq_trans
                           (fteq_inv (teq_select_IshiftF1 $j $n (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t)))))
                           (fteq_inv (FJcong (λ v, dbselectF $j $n v (fteq1 (dbsucc $n)) (fteq1 $n))
                                             (aux_teq_Ishift_substeq1 db0 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t))))))
                         (fteq_trans
                           (fteq_inv (teq_select_IshiftF1 $j (dbprev $n) (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                               (IShiftI* $j $t)))))
                           (fteq_inv (FJcong (λ v, dbselectF (dbsucc $j) (dbsucc (dbprev $n)) v
                                                             (fteq1 (dbsucc (dbprev $n)))
                                                             (fteq1 (dbprev (dbsucc (dbprev $n)))))
                                             (aux_teq_Ishift_substeq1 db0 (IsubstI $i (IShiftI* $i $u)
                                                                                      (IShiftI* $j $t)))))))))
           (fteq_inv (aux_teq_dbselectF_fn (dbsucc $i) $n
                                           (substeq1 (IsubstI (dbsucc $j) (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                               (IShiftI* $j $t)))
                                                              (IShiftI* (dbsucc (dbsucc $i)) $u)))
                                           (dbselectF $j $n (substeq1 (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                           (IShiftI* $j $t))))
                                                            (fteq1 (dbsucc $n)) (fteq1 $n))
                                           (λ n1, dbselectF (dbsucc $j) n1
                                                            (substeq1 (IShiftI (IsubstI $i (IShiftI* $i $u)
                                                                                           (IShiftI* $j $t))))
                                                            (fteq1 n1) (fteq1 (dbprev n1))))))
         (IcongF (λ t1, dbselectF (dbsucc $i) $n
                                  (substeq1 (IsubstI (dbsucc $j) t1 (IShiftI* (dbsucc (dbsucc $i)) $u)))
                                  (dbselectF $j $n (substeq1 t1) (fteq1 (dbsucc $n)) (fteq1 $n))
                                  (dbselectF (dbsucc $j) $n (substeq1 t1) (fteq1 $n) (fteq1 (dbprev $n))))
                 (iteq_inv (teq_IsubstI_IshiftI $i (IShiftI* $i $u) (IShiftI* $j $t)))));

rule aux_teq_Isubst_Isubst _ _ _ _ (tvar $n) _ ↪
      TRefl (tvar $n)
with aux_teq_Isubst_Isubst _ _ _ _ (tuniv $s) _ ↪ TRefl (tuniv $s)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tpi $A $B) $h ↪
      Jpi (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
          (aux_teq_Isubst_Isubst $i $j $u $t1 $B $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tabs $A $t) $h ↪
      Jabs (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $t $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tapp $f $a) $h ↪
      Japp (aux_teq_Isubst_Isubst $i $j $u $t1 $f $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $a $h)
with aux_teq_Isubst_Isubst _ _ _ _ tnat _ ↪ TRefl tnat
with aux_teq_Isubst_Isubst _ _ _ _ tzero _ ↪ TRefl tzero
with aux_teq_Isubst_Isubst $i $j $u $t1 (tsuc $n) $h ↪
      Jcong tsuc (aux_teq_Isubst_Isubst $i $j $u $t1 $n $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (trec $P $z $H $n) $h ↪
      Jrec (aux_teq_Isubst_Isubst $i $j $u $t1 $P $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $z $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $H $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $n $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tsig $A $B) $h ↪
      Jsig (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $B $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tpair $a $b) $h ↪
      Jpair (aux_teq_Isubst_Isubst $i $j $u $t1 $a $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $b $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tp1 $p) $h ↪
      Jcong tp1 (aux_teq_Isubst_Isubst $i $j $u $t1 $p $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tp2 $p) $h ↪
      Jcong tp2 (aux_teq_Isubst_Isubst $i $j $u $t1 $p $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tsum $A $B) $h ↪
      Jsum (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $B $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tinjl $p) $h ↪
      Jcong tinjl (aux_teq_Isubst_Isubst $i $j $u $t1 $p $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tinjr $p) $h ↪
      Jcong tinjr (aux_teq_Isubst_Isubst $i $j $u $t1 $p $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tcase $A $B $P $Ha $Hb $t) $h ↪
      Jcase (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $B $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $P $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $Ha $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $Hb $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $t $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tpath $A $x $y) $h ↪
      Jpath (aux_teq_Isubst_Isubst_Irec $i $j $u $t1 $A $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $x $h)
            (aux_teq_Isubst_Isubst $i $j $u $t1 $y $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tlamP $t) $h ↪
      Jcong tlamP (aux_teq_Isubst_Isubst_Irec $i $j $u $t1 $t $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tappP $x $y) $h ↪
      JappP (aux_teq_Isubst_Isubst $i $j $u $t1 $x $h)
            (aux_teq_IsubstI_IsubstI $i $j $u $t1 $y $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (tsys $f $g $x $y) $h ↪
      Jsys (aux_teq_IsubstF_IsubstF $i $j $u $t1 $f $h)
           (aux_teq_IsubstF_IsubstF $i $j $u $t1 $g $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $x $h)
           (aux_teq_Isubst_Isubst $i $j $u $t1 $y $h)
with aux_teq_Isubst_Isubst _ _ _ _ temptysys _ ↪ TRefl temptysys
with aux_teq_Isubst_Isubst $i $j $u $t1 (ttransp $A $f $x) $h ↪
      Jtransp (aux_teq_Isubst_Isubst_Irec $i $j $u $t1 $A $h)
              (aux_teq_IsubstF_IsubstF $i $j $u $t1 $f $h)
              (aux_teq_Isubst_Isubst $i $j $u $t1 $x $h)
with aux_teq_Isubst_Isubst $i $j $u $t1 (thcomp $A $f $x $y) $h ↪
      Jhcomp (aux_teq_Isubst_Isubst $i $j $u $t1 $A $h)
             (aux_teq_IsubstF_IsubstF $i $j $u $t1 $f $h)
             (aux_teq_Isubst_Isubst_Irec $i $j $u $t1 $x $h)
             (aux_teq_Isubst_Isubst $i $j $u $t1 $y $h)
with aux_teq_IsubstI_IsubstI _ _ _ _ it0 _ ↪ ITRefl it0
with aux_teq_IsubstI_IsubstI _ _ _ _ it1 _ ↪ ITRefl it1
with aux_teq_IsubstI_IsubstI $i $j $u $t1 (itvar $n) $h ↪
      iteq_trans
       (aux_teq_subst_dbselectI $j $n $i (IShiftI* $i $u) (IShiftI* $j $t1) (itvar $n) (itvar (dbprev $n)))
       (iteq_trans
         (aux_teq_Isubst_Isubst_itvar $i $j $u $t1 $n $h)
         (iteq_inv (aux_teq_subst_dbselectI (dbsucc $i) $n $j
                    (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1))
                    (IShiftI* (dbsucc $i) $u)
                    (itvar $n) (itvar (dbprev $n)))))
with aux_teq_IsubstI_IsubstI $i $j $u $t1 (itsym $n) $h ↪
      IJcong itsym (aux_teq_IsubstI_IsubstI $i $j $u $t1 $n $h)
with aux_teq_IsubstI_IsubstI $i $j $u $t1 (itmin $x $y) $h ↪
      IJmin (aux_teq_IsubstI_IsubstI $i $j $u $t1 $x $h)
            (aux_teq_IsubstI_IsubstI $i $j $u $t1 $y $h)
with aux_teq_IsubstI_IsubstI $i $j $u $t1 (itmax $x $y) $h ↪
      IJmax (aux_teq_IsubstI_IsubstI $i $j $u $t1 $x $h)
            (aux_teq_IsubstI_IsubstI $i $j $u $t1 $y $h)
with aux_teq_IsubstF_IsubstF _ _ _ _ ft0 _ ↪ FTRefl ft0
with aux_teq_IsubstF_IsubstF _ _ _ _ ft1 _ ↪ FTRefl ft1
with aux_teq_IsubstF_IsubstF $i $j $u $t1 (fteq0 $n) $h ↪
      fteq_trans
       (aux_teq_subst_dbselectF $j $n $i (IShiftI* $i $u) (substeq0 (IShiftI* $j $t1))
                                         (fteq0 $n) (fteq0 (dbprev $n)))
       (fteq_trans
         (FJcong (λ v, dbselectF $j $n v (IsubstF $i (IShiftI* $i $u) (fteq0 $n))
                                       (IsubstF $i (IShiftI* $i $u) (fteq0 (dbprev $n))))
                 (fteq_inv (aux_teq_Isubst_substeq0 $i (IShiftI* $i $u) (IShiftI* $j $t1))))
         (fteq_trans
           (aux_teq_Isubst_Isubst_fteq0 $i $j $u $t1 $n $h)
           (fteq_trans
             (FJcong (λ v, dbselectF (dbsucc $i) $n v
                                     (dbselectF $j $n (substeq0 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1)))
                                                      (fteq0 $n) (fteq0 (dbprev $n)))
                                     (dbselectF $j (dbprev $n) (substeq0 (IsubstI $i (IShiftI* $i $u)
                                                                                     (IShiftI* $j $t1)))
                                                   (fteq0 (dbprev $n)) (fteq0 (dbprev (dbprev $n)))))
                     (aux_teq_Isubst_substeq0 $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1))
                                                 (IShiftI* (dbsucc $i) $u)))
             (fteq_inv (aux_teq_subst_dbselectF (dbsucc $i) $n $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1))
                                                                  (substeq0 (IShiftI* (dbsucc $i) $u))
                                                                  (fteq0 $n) (fteq0 (dbprev $n)))))))
with aux_teq_IsubstF_IsubstF $i $j $u $t1 (fteq1 $n) $h ↪
      fteq_trans
       (aux_teq_subst_dbselectF $j $n $i (IShiftI* $i $u) (substeq1 (IShiftI* $j $t1))
                                         (fteq1 $n) (fteq1 (dbprev $n)))
       (fteq_trans
         (FJcong (λ v, dbselectF $j $n v (IsubstF $i (IShiftI* $i $u) (fteq1 $n))
                                       (IsubstF $i (IShiftI* $i $u) (fteq1 (dbprev $n))))
                 (fteq_inv (aux_teq_Isubst_substeq1 $i (IShiftI* $i $u) (IShiftI* $j $t1))))
         (fteq_trans
           (aux_teq_Isubst_Isubst_fteq1 $i $j $u $t1 $n $h)
           (fteq_trans
             (FJcong (λ v, dbselectF (dbsucc $i) $n v
                                     (dbselectF $j $n (substeq1 (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1)))
                                                      (fteq1 $n) (fteq1 (dbprev $n)))
                                     (dbselectF $j (dbprev $n) (substeq1 (IsubstI $i (IShiftI* $i $u)
                                                                                     (IShiftI* $j $t1)))
                                                   (fteq1 (dbprev $n)) (fteq1 (dbprev (dbprev $n)))))
                     (aux_teq_Isubst_substeq1 $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1))
                                                 (IShiftI* (dbsucc $i) $u)))
             (fteq_inv (aux_teq_subst_dbselectF (dbsucc $i) $n $j (IsubstI $i (IShiftI* $i $u) (IShiftI* $j $t1))
                                                                  (substeq1 (IShiftI* (dbsucc $i) $u))
                                                                  (fteq1 $n) (fteq1 (dbprev $n)))))))
with aux_teq_IsubstF_IsubstF $i $j $u $t1 (ftmin $x $y) $h ↪
      FJmin (aux_teq_IsubstF_IsubstF $i $j $u $t1 $x $h)
            (aux_teq_IsubstF_IsubstF $i $j $u $t1 $y $h)
with aux_teq_IsubstF_IsubstF $i $j $u $t1 (ftmax $x $y) $h ↪
      FJmax (aux_teq_IsubstF_IsubstF $i $j $u $t1 $x $h)
            (aux_teq_IsubstF_IsubstF $i $j $u $t1 $y $h);

// teq_Isubst_Iapply
symbol teq_Isubst_Iapply (i : DBId) (u t1 : ITerm) (t2 : Term) :
  TEq (Isubst i (IShiftI* i u) (applyI1 t2 t1))
      (applyI1 (Isubst (dbsucc i) (IShiftI* (dbsucc i) u) t2) (IsubstI i (IShiftI* i u) t1)) ≔
  aux_teq_Isubst_Isubst i db0 u t1 t2 (dble_0_n i);

// TODO subst/Isubst commutations
// aux_teq_Isubst_subst
symbol aux_teq_Isubst_subst (i j : DBId) (u : ITerm) (t1 t2 : Term) :
  TEq (Isubst i (IShiftI* i u) (subst j (Shift* j t1) t2))
      (subst j (Isubst i (IShiftI* i u) (Shift* j t1)) (Isubst i (IShiftI* i u) t2));
symbol aux_teq_Isubst_subst_rec (i j : DBId) (u : ITerm) (t1 t2 : Term) ≔
  teq_trans (aux_teq_Isubst_subst i (dbsucc j) u t1 t2)
            (Jcong (λ v, subst (dbsucc j) v (Isubst i (IShiftI* i u) t2))
                   (aux_teq_Isubst_shift i db0 u (Shift* j t1)));
symbol aux_teq_Isubst_subst_Irec (i j : DBId) (u : ITerm) (t1 t2 : Term) ≔
  teq_trans (Jcong (λ v, Isubst (dbsucc i) (IShiftI* (dbsucc i) u) (subst j v t2))
                   (teq_inv (aux_teq_Shift*_Ishift j db0 t1)))
            (teq_trans (aux_teq_Isubst_subst (dbsucc i) j u (IShift t1) t2)
                       (teq_trans (Jcong (λ v, subst j (Isubst (dbsucc i) (IShiftI* (dbsucc i) u) v)
                                                     (Isubst (dbsucc i) (IShiftI* (dbsucc i) u) t2))
                                         (aux_teq_Shift*_Ishift j db0 t1))
                                  (Jcong (λ v, subst j v (Isubst (dbsucc i) (IShiftI* (dbsucc i) u) t2))
                                         (aux_teq_Isubst_Ishift i db0 (IShiftI* i u) (Shift* j t1) (dble_0_n i)))));

rule aux_teq_Isubst_subst $i $j $u $t1 (tvar $n) ↪
      aux_teq_Isubst_dbselect $j $n $i (IShiftI* $i $u) (Shift* $j $t1) (tvar $n) (tvar (dbprev $n))
with aux_teq_Isubst_subst _ _ _ _ (tuniv $l) ↪ TRefl (tuniv $l)
with aux_teq_Isubst_subst $i $j $u $t1 (tpi $A $B) ↪
      Jpi (aux_teq_Isubst_subst $i $j $u $t1 $A)
          (aux_teq_Isubst_subst_rec $i $j $u $t1 $B)
with aux_teq_Isubst_subst $i $j $u $t1 (tabs $A $B) ↪
      Jabs (aux_teq_Isubst_subst $i $j $u $t1 $A)
           (aux_teq_Isubst_subst_rec $i $j $u $t1 $B)
with aux_teq_Isubst_subst $i $j $u $t1 (tapp $A $B) ↪
      Japp (aux_teq_Isubst_subst $i $j $u $t1 $A)
           (aux_teq_Isubst_subst $i $j $u $t1 $B)
with aux_teq_Isubst_subst _ _ _ _ tnat ↪ TRefl tnat
with aux_teq_Isubst_subst _ _ _ _ tzero ↪ TRefl tzero
with aux_teq_Isubst_subst $i $j $u $t1 (tsuc $n) ↪
      Jcong tsuc (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (trec $P $z $H $n) ↪
      Jrec (aux_teq_Isubst_subst $i $j $u $t1 $P)
           (aux_teq_Isubst_subst $i $j $u $t1 $z)
           (aux_teq_Isubst_subst $i $j $u $t1 $H)
           (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (tsig $A $B) ↪
      Jsig (aux_teq_Isubst_subst $i $j $u $t1 $A)
           (aux_teq_Isubst_subst_rec $i $j $u $t1 $B)
with aux_teq_Isubst_subst $i $j $u $t1 (tpair $A $B) ↪
      Jpair (aux_teq_Isubst_subst $i $j $u $t1 $A)
            (aux_teq_Isubst_subst $i $j $u $t1 $B)
with aux_teq_Isubst_subst $i $j $u $t1 (tp1 $n) ↪
      Jcong tp1 (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (tp2 $n) ↪
      Jcong tp2 (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (tsum $A $B) ↪
      Jsum (aux_teq_Isubst_subst $i $j $u $t1 $A)
           (aux_teq_Isubst_subst $i $j $u $t1 $B)
with aux_teq_Isubst_subst $i $j $u $t1 (tinjl $n) ↪
      Jcong tinjl (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (tinjr $n) ↪
      Jcong tinjr (aux_teq_Isubst_subst $i $j $u $t1 $n)
with aux_teq_Isubst_subst $i $j $u $t1 (tcase $A $B $P $Ha $Hb $t) ↪
      Jcase (aux_teq_Isubst_subst $i $j $u $t1 $A)
            (aux_teq_Isubst_subst $i $j $u $t1 $B)
            (aux_teq_Isubst_subst $i $j $u $t1 $P)
            (aux_teq_Isubst_subst $i $j $u $t1 $Ha)
            (aux_teq_Isubst_subst $i $j $u $t1 $Hb)
            (aux_teq_Isubst_subst $i $j $u $t1 $t)
with aux_teq_Isubst_subst $i $j $u $t1 (tpath $A $x $y) ↪
      Jpath (aux_teq_Isubst_subst_Irec $i $j $u $t1 $A)
            (aux_teq_Isubst_subst $i $j $u $t1 $x)
            (aux_teq_Isubst_subst $i $j $u $t1 $y)
with aux_teq_Isubst_subst $i $j $u $t1 (tlamP $x) ↪
      Jcong tlamP (aux_teq_Isubst_subst_Irec $i $j $u $t1 $x)
with aux_teq_Isubst_subst $i $j $u $t1 (tappP $x _) ↪
      JappP (aux_teq_Isubst_subst $i $j $u $t1 $x) (ITRefl _)
with aux_teq_Isubst_subst $i $j $u $t1 (tsys _ _ $x $y) ↪
      Jsys (FTRefl _) (FTRefl _)
           (aux_teq_Isubst_subst $i $j $u $t1 $x)
           (aux_teq_Isubst_subst $i $j $u $t1 $y)
with aux_teq_Isubst_subst _ _ _ _ temptysys ↪ TRefl temptysys
with aux_teq_Isubst_subst $i $j $u $t1 (ttransp $A _ $x) ↪
      Jtransp (aux_teq_Isubst_subst_Irec $i $j $u $t1 $A)
              (FTRefl _)
              (aux_teq_Isubst_subst $i $j $u $t1 $x)
with aux_teq_Isubst_subst $i $j $u $t1 (thcomp $A _ $x $y) ↪
      Jhcomp (aux_teq_Isubst_subst $i $j $u $t1 $A)
             (FTRefl _)
             (aux_teq_Isubst_subst_Irec $i $j $u $t1 $x)
             (aux_teq_Isubst_subst $i $j $u $t1 $y);
