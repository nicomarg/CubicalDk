require open ctt.Contexts.DeBruijn;

constant symbol Empty : Context;
constant symbol Push : Term → Sort → Context → Context;
constant symbol PushI : Context → Context;
constant symbol PushF : FTerm → Context → Context;

symbol get : Context → DBId → Term;
symbol getS : Context → DBId → Sort;
symbol getΓ : Context → DBId → Context;
symbol IgetΓ : Context → DBId → Context;
rule get (Push $t _ _) db0 ↪ $t
with get (Push _ _ $t) (dbsucc $i) ↪ get $t $i
with get (PushF _ $t) $i ↪ get $t $i
with get (PushI $t) $i ↪ get $t $i
with getS (Push _ $s _) db0 ↪ $s
with getS (Push _ _ $t) (dbsucc $i) ↪ getS $t $i
with getS (PushI $t) $i ↪ getS $t $i
with getS (PushF _ $t) $i ↪ getS $t $i
with getΓ (Push _ _ $t) db0 ↪ $t
with getΓ (Push _ _ $t) (dbsucc $i) ↪ getΓ $t $i
with getΓ (PushI $t) $i ↪ getΓ $t $i
with getΓ (PushF _ $t) $i ↪ getΓ $t $i
with getΓ (getΓ $Γ $n) $m ↪ getΓ $Γ (dbsucc (dbadd $n $m))
with IgetΓ (Push _ _ $t) $i ↪ IgetΓ $t $i
with IgetΓ (PushI $t) db0 ↪ $t
with IgetΓ (PushI $t) (dbsucc $i) ↪ IgetΓ $t $i
with IgetΓ (PushF _ $t) $i ↪ IgetΓ $t $i
with IgetΓ (IgetΓ $Γ $n) $m ↪ IgetΓ $Γ (dbsucc (dbadd $n $m));

// Computes the 'length' (or maximum defined index + 1) of a context
symbol len : Context → DBId;
symbol lenI : Context → DBId;
rule len Empty ↪ db0
with len (Push _ _ $t) ↪ dbsucc (len $t)
with len (PushI $t) ↪ len $t
with len (PushF _ $t) ↪ len $t
with lenI Empty ↪ db0
with lenI (Push _ _ $t) ↪ lenI $t
with lenI (PushI $t) ↪ dbsucc (lenI $t)
with lenI (PushF _ $t) ↪ lenI $t;
