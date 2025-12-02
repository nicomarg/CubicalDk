require open ctt.CTT.Interval;

// Face lattice
constant symbol F : xT;
symbol tF ≔ xeps F;
constant symbol 0f : tF;
constant symbol 1f : tF;

injective symbol eq0 : tI → tF;
injective symbol eq1 : tI → tF;
rule eq0 i0 ↪ 1f;
rule eq0 i1 ↪ 0f;
rule eq1 i0 ↪ 0f;
rule eq1 i1 ↪ 1f;

symbol Fmin : tF → tF → tF;
rule Fmin _ 0f ↪ 0f;
rule Fmin 0f _ ↪ 0f;
rule Fmin $a 1f ↪ $a;
rule Fmin 1f $a ↪ $a;

symbol Fmax : tF → tF → tF;
rule Fmax $a 0f ↪ $a;
rule Fmax 0f $a ↪ $a;
rule Fmax _ 1f ↪ 1f;
rule Fmax 1f _ ↪ 1f;

rule eq1 (Imax $a $b) ↪ Fmax (eq1 $a) (eq1 $b);
rule eq1 (Imin $a $b) ↪ Fmin (eq1 $a) (eq1 $b);
rule eq0 (Imax $a $b) ↪ Fmin (eq0 $a) (eq0 $b);
rule eq0 (Imin $a $b) ↪ Fmax (eq0 $a) (eq0 $b);

rule eq0 (sym $i) ↪ eq1 $i
with eq1 (sym $i) ↪ eq0 $i;

/* These would break conluence if added as rewrite rules. We will be happy with
the type of their witnesses being isomorphic to the empty type
rule Fmin (eq1 $a) (eq0 $a) ↪ 0f;
rule Fmin (eq0 $a) (eq1 $a) ↪ 0f;
*/
