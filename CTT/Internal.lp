// Internal (cubical) theory
symbol Lev : TYPE;
constant symbol lzero : Lev;
constant symbol lsuc : Lev → Lev;
symbol lmax : Lev → Lev → Lev;
rule lmax lzero $n ↪ $n
with lmax $n lzero ↪ $n
with lmax (lsuc $n) (lsuc $m) ↪ lsuc (lmax $n $m)
with lmax $s $s ↪ $s;

// Universes
constant symbol T : Lev → TYPE;
injective symbol eps [i] : T i → TYPE;

constant symbol t (i:Lev) : T (lsuc i);
rule eps (t $i) ↪ T $i;
// unif_rule T $l ≡ eps $t ↪ [ $t ≡ t $l];

constant symbol lUp [i] : T i → T (lsuc i);
rule eps (lUp $a) ↪ eps $a;

// Nat
constant symbol Nat i : T i;
symbol tNat ≔ λ i, eps (Nat i);
constant symbol zero [i] : tNat i;
constant symbol S [i] : @tNat i → @tNat i;
symbol recursor [i j] (tau : (tNat i → T j)) : eps (tau zero) → (Π (n : tNat i), eps (tau n) → eps (tau (S n))) →
                                               Π (m : tNat i), eps (tau m);
rule recursor _ $H _ zero ↪ $H;
rule recursor $tau $Hz $Hs (S $n) ↪ $Hs $n (recursor $tau $Hz $Hs $n);

// Pi-types
constant symbol Pi [i j] (A : T i) : (eps A → T j) → T (lmax i j);
symbol tPi [i j] ≔ λ (A : T i) (B : eps A → T j), eps (Pi A B);
rule eps (Pi $A $B) ↪ Π (x : eps $A), eps ($B x);

symbol ndPi [i j] ≔ λ (A : T i) (B : T j), Pi A (λ _, B);
symbol tndPi [i j] ≔ λ (A : T i) (B : T j), eps (ndPi A B);

// Sigma Types
constant symbol Sig [i j] (A : T i) : (eps A → T j) → T (lmax i j);
symbol tSig [i j] (A : T i) (B : eps A → T j) ≔ eps (Sig A B);
constant symbol pair [i j] [A : T i] [B : eps A → T j] (x : eps A) : eps (B x) → tSig A B;
symbol p1 [i j] [A : T i] [B : eps A → T j] : tSig A B → eps A;
symbol p2 [i j] [A : T i] [B : eps A → T j] (a : tSig A B) : eps (B (p1 a));
rule p1 (pair $a _) ↪ $a;
rule p2 (pair _ $b) ↪ $b;

symbol ndSig [i j] (A : T i) (B : T j) ≔ Sig A (λ _, B);
symbol tndSig [i j] (A : T i) (B : T j) ≔ tSig A (λ _, B);

// Disjoint sum
constant symbol Sum [i j] : T i → T j → T (lmax i j);
symbol tSum [i j] (A : T i) (B : T j) ≔ eps (Sum A B);
constant symbol injl [i j] [A : T i] [B : T j] : eps A → tSum A B;
constant symbol injr [i j] [A : T i] [B : T j] : eps B → tSum A B;
symbol case [i j k] [A : T i] [B : T j] (tau : (tSum A B → T k)) :
  (Π a : eps A, eps (tau (injl a))) → (Π b : eps B, eps (tau (injr b))) →
  Π (e : tSum A B), eps (tau e);
rule case _ $caseA _ (injl $a) ↪ $caseA $a;
rule case _ _ $caseB (injr $b) ↪ $caseB $b;
