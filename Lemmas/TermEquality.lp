require open ctt.Var.Subst;

// Term equality, necessary to express commutation of different operations
constant symbol TEq : Term → Term → TYPE;
constant symbol TRefl (t : Term) : TEq t t;
constant symbol TyEq : Typ → Typ → TYPE;
constant symbol TyRefl (t : Typ) : TyEq t t;

// Elimination of term equality
symbol teq_inv [t1 t2 : Term] : TEq t1 t2 → TEq t2 t1;
symbol teq_trans [t1 t2 t3 : Term] : TEq t1 t2 → TEq t2 t3 → TEq t1 t3;
symbol tyeq_inv [t1 t2 : Typ] : TyEq t1 t2 → TyEq t2 t1;
symbol tyeq_trans [t1 t2 t3 : Typ] : TyEq t1 t2 → TyEq t2 t3 → TyEq t1 t3;
symbol Jt [Γ : Context] [s : Sort] [t1 t2 : Term] [T : Typ]
          : TEq t1 t2 → der Γ t1 T s → der Γ t2 T s;
symbol JT [Γ : Context] [s : Sort] [t : Term] [T1 T2 : Typ]
          : TyEq T1 T2 → der Γ t T1 s → der Γ t T2 s;
symbol JtT [Γ : Context] [s : Sort] [t1 t2 : Term] [T1 T2 : Typ]
           : TEq t1 t2 → TyEq T1 T2 → der Γ t1 T1 s → der Γ t2 T2 s;
symbol Jty [Γ : Context] [s : Sort] [T1 T2 : Typ]
           : TyEq T1 T2 → der_type Γ T1 s → der_type Γ T2 s;
symbol Jcong [t1 t2 : Term] (f : Term → Term)
             : TEq t1 t2 → TEq (f t1) (f t2);
symbol JTcong [t1 t2 : Typ] (f : Typ → Typ)
              : TyEq t1 t2 → TyEq (f t1) (f t2);
symbol JtTcong [t1 t2 : Term] (f : Term → Typ) : TEq t1 t2 → TyEq (f t1) (f t2);
symbol JTtcong [t1 t2 : Typ] (f : Typ → Term) : TyEq t1 t2 → TEq (f t1) (f t2);
symbol Jeq [Γ : Context] [s : Sort] [T T' t1 t1' t2 t2']
           : TyEq T T'
           → TEq t1 t1'
           → TEq t2 t2'
           → der_eq Γ t1  t2  T  s
           → der_eq Γ t1' t2' T' s;
symbol JTeq [Γ : Context] [s : Sort] [T1 T1' T2 T2' : Typ] :
  TyEq T1 T1' → TyEq T2 T2' → der_eqT Γ T1 T2 s → der_eqT Γ T1' T2' s;
symbol dbcongT [i j : DBId] (f : DBId → Term) : DBEq i j → TEq (f i) (f j);
symbol dbcongTy [i j : DBId] (f : DBId → Typ) : DBEq i j → TyEq (f i) (f j);
rule teq_inv (TRefl $t) ↪ TRefl $t
with tyeq_inv (TyRefl $t) ↪ TyRefl $t
with tyeq_trans (TyRefl $t) (TyRefl _) ↪ TyRefl $t
with JtT (TRefl _) (TyRefl _) $d ↪ $d
with @Jt _ _ _ _ $T $eqt $d ↪ JtT $eqt (TyRefl $T) $d
with @JT _ _ $t _ _ $eqT $d ↪ JtT (TRefl $t) $eqT $d
with Jty (TyRefl _) $d ↪ $d 
with Jcong _ (TRefl _) ↪ TRefl _
with JTcong _ (TyRefl _) ↪ TyRefl _
with JtTcong _ (TRefl _) ↪ TyRefl _
with JTtcong _ (TyRefl _) ↪ TRefl _
with Jeq (TyRefl _) (TRefl _) (TRefl _) $d ↪ $d
with JTeq (TyRefl _) (TyRefl _) $d ↪ $d
with dbcongT $f (DBRefl $i) ↪ TRefl ($f $i)
with dbcongTy $f (DBRefl $i) ↪ TyRefl ($f $i);

// Congruence for term equality
symbol Jselect [eq1 eq2 gt1 gt2 lt1 lt2 : Term] (i j : DBId) :
  TEq eq1 eq2 → TEq gt1 gt2 → TEq lt1 lt2 →
  TEq (dbselect i j eq1 gt1 lt1) (dbselect i j eq2 gt2 lt2);

rule Jselect $i $j (TRefl $eq) (TRefl $gt) (TRefl $lt) ↪ TRefl (dbselect $i $j $eq $gt $lt);

// Universe level equality
constant symbol LEq : Sort → Sort → TYPE;
constant symbol LRefl (t : Sort) : LEq t t;

// Elimination of term equality
symbol leq_inv [t1 t2 : Sort] : LEq t1 t2 → LEq t2 t1;
symbol leq_trans [t1 t2 t3 : Sort] : LEq t1 t2 → LEq t2 t3 → LEq t1 t3;
symbol Jl [Γ : Context] [s s' : Sort] [t : Term] [T : Typ]
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
