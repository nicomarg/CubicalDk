require open ctt.CTT.External;

// Interval type
constant symbol I : xT;
symbol tI ≔ xeps I;
constant symbol i0 : tI;
constant symbol i1 : tI;

symbol Imin : tI → tI → tI;
rule Imin _ i0 ↪ i0;
rule Imin i0 _ ↪ i0;
rule Imin $a i1 ↪ $a;
rule Imin i1 $a ↪ $a;

symbol Imax : tI → tI → tI;
rule Imax $a i0 ↪ $a;
rule Imax i0 $a ↪ $a;
rule Imax _ i1 ↪ i1;
rule Imax i1 _ ↪ i1;

symbol sym : tI → tI;
rule sym i0 ↪ i1;
rule sym i1 ↪ i0;
rule sym (Imax $a $b) ↪ Imin (sym $a) (sym $b)
with sym (Imin $a $b) ↪ Imax (sym $a) (sym $b);
rule sym (sym $a) ↪ $a;

symbol OneNeqZero : xtEq i1 i0 → xtFalse;
