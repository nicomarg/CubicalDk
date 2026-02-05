require open ctt.Context;
require open ctt.DeBruijn;

constant symbol Push : Typ → Sort → Context → Context;

symbol get : Context → DBId → Typ;
symbol getS : Context → DBId → Sort;
symbol getΓ : Context → DBId → Context;

rule get (Push $t _ _) db0 ↪ $t
with get (Push _ _ $t) (dbsucc $i) ↪ get $t $i
with getS (Push _ $s _) db0 ↪ $s
with getS (Push _ _ $t) (dbsucc $i) ↪ getS $t $i
with getΓ (Push _ _ $t) db0 ↪ $t
with getΓ (Push _ _ $t) (dbsucc $i) ↪ getΓ $t $i
with getΓ (getΓ $Γ $n) $m ↪ getΓ $Γ (dbsucc (dbadd $n $m));

symbol len : Context → DBId;
rule len Empty ↪ db0
with len (Push _ _ $t) ↪ dbsucc (len $t);

constant symbol der_context_Push : Π (Γ : Context) (l : Sort) (A : Typ),
  der_type Γ A l → der_context Γ → der_context (Push A l Γ);

symbol der_getΓ [Γ : Context] (id : DBId) (_ : der_context Γ) :
  der_type (getΓ Γ id) (get Γ id) (getS Γ id);
symbol der_subΓ [Γ : Context] (id : DBId) (_ : der_context Γ) : der_context (getΓ Γ id);
rule der_getΓ db0 (der_context_Push _ _ _ $dA _) ↪ $dA
with der_getΓ (dbsucc $id) (der_context_Push _ _ _ _ $dt) ↪ der_getΓ $id $dt
with der_subΓ db0 (der_context_Push _ _ _ _ $dΓ) ↪ $dΓ
with der_subΓ (dbsucc $id) (der_context_Push _ _ _ _ $dΓ) ↪ der_subΓ $id $dΓ
;

// Better der_context_push
symbol pushΓ [Γ : Context] [l : Sort] [T : Typ] (d : der_type Γ T l) (dΓ : der_context Γ) :
  der_context (Push T l Γ) ≔ der_context_Push Γ l T d dΓ;
