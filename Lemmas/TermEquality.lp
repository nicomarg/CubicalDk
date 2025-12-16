require open ctt.Contexts.Subst;

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
symbol Jt [Γ : Context] [s : Sort] [t1 t2 T : Term]
          : TEq t1 t2 → der Γ t1 T s → der Γ t2 T s;
symbol JT [Γ : Context] [s : Sort] [t T1 T2 : Term]
          : TEq T1 T2 → der Γ t T1 s → der Γ t T2 s;
symbol JtT [Γ : Context] [s : Sort] [t1 t2 T1 T2 : Term]
           : TEq t1 t2 → TEq T1 T2 → der Γ t1 T1 s → der Γ t2 T2 s;
symbol Jcong [t1 t2 : Term] (f : Term → Term)
             : TEq t1 t2 → TEq (f t1) (f t2);
symbol Jeq [Γ : Context] [s : Sort] [T T' t1 t1' t2 t2']
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
symbol Jselect [eq1 eq2 gt1 gt2 lt1 lt2 : Term] (i j : DBId) :
  TEq eq1 eq2 → TEq gt1 gt2 → TEq lt1 lt2 →
  TEq (dbselect i j eq1 gt1 lt1) (dbselect i j eq2 gt2 lt2);

rule Jselect $i $j (TRefl $eq) (TRefl $gt) (TRefl $lt) ↪ TRefl (dbselect $i $j $eq $gt $lt);

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
symbol IJselect [eq1 eq2 gt1 gt2 lt1 lt2 : ITerm] (i j : DBId) :
  ITEq eq1 eq2 → ITEq gt1 gt2 → ITEq lt1 lt2 →
  ITEq (dbselectI i j eq1 gt1 lt1) (dbselectI i j eq2 gt2 lt2);

rule IJselect _ _ (ITRefl _) (ITRefl _) (ITRefl _) ↪ ITRefl _;

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
symbol FJselect [eq1 eq2 gt1 gt2 lt1 lt2 : FTerm] (i j : DBId) :
  FTEq eq1 eq2 → FTEq gt1 gt2 → FTEq lt1 lt2 →
  FTEq (dbselectF i j eq1 gt1 lt1) (dbselectF i j eq2 gt2 lt2);

rule FJselect _ _ (FTRefl _) (FTRefl _) (FTRefl _) ↪ FTRefl _;

// Universe level equality
constant symbol LEq : Sort → Sort → TYPE;
constant symbol LRefl (t : Sort) : LEq t t;

// Elimination of term equality
symbol leq_inv [t1 t2 : Sort] : LEq t1 t2 → LEq t2 t1;
symbol leq_trans [t1 t2 t3 : Sort] : LEq t1 t2 → LEq t2 t3 → LEq t1 t3;
symbol Jl [Γ : Context] [s s' : Sort] [t T : Term]
          : LEq s s' → der Γ t T s → der Γ t T s';
symbol Jlcong [t1 t2 : Sort] (f : Sort → Sort)
             : LEq t1 t2 → LEq (f t1) (f t2);
symbol Jleq [Γ : Context] [s s' : Sort] [T t1 t2]
           : LEq s s'
           → der_eq Γ t1 t2 T s
           → der_eq Γ t1 t2 T s';
rule leq_inv (LRefl $t) ↪ LRefl $t
with leq_trans (LRefl $t) (LRefl _) ↪ LRefl $t
with Jl (LRefl _) $d ↪ $d
with Jleq (LRefl _) $d ↪ $d;
