require open ctt.CTT.Faces;

/* One creates a type isOne φ recording the fact that the face formula φ holds.
As directly describing isOne on face constructors with rewrite rules would lead
to confluence problems (for instance because True × A is isomorphic but not
convertible to A), we only provide isomorphisms between those types. */

constant symbol isOne : tF → xT;
symbol tisOne (f : tF) ≔ xeps (isOne f);
symbol isOneConv (f : tF) : tisOne f → xtEq 1f f;

injective symbol isOneZeroUp : tisOne 0f → xtFalse;
injective symbol isOneZeroDown : xtFalse → tisOne 0f;
rule isOneZeroDown (isOneZeroUp $a) ↪ $a;
rule isOneZeroUp (isOneZeroDown $a) ↪ $a;
symbol elimIsOneZero [A : xT] (p : tisOne 0f) : xeps A ≔ xelimFalse A (isOneZeroUp p);

injective symbol isOneOneUp : tisOne 1f → xtTrue;
injective symbol isOneOneDown : xtTrue → tisOne 1f;
rule isOneOneDown (isOneOneUp $a) ↪ $a;
rule isOneOneUp (isOneOneDown $a) ↪ $a;
symbol itIsOne : tisOne 1f ≔ isOneOneDown xtt;
symbol elimIsOneOne (A : tisOne 1f → xT) (H : xeps (A itIsOne)) (p : tisOne 1f) : xeps (A p) ≔
  xelimTrue (λ p, A (isOneOneDown p)) H (isOneOneUp p);
rule isOneConv 1f _ ↪ xrefl;

injective symbol isOneEq1Up [i] : tisOne (eq1 i) → xtEq i i1;
injective symbol isOneEq1Down [i] : xtEq i i1 → tisOne (eq1 i);
rule isOneEq1Down (isOneEq1Up $a) ↪ $a;
rule isOneEq1Up (isOneEq1Down $a) ↪ $a;
symbol OneEqualsOne : tisOne (eq1 i1) ≔ isOneEq1Down xrefl;
symbol elimIsOneEq1 (tau : (tI → xT)) (H : xeps (tau i1)) (i : tI) (p : tisOne (eq1 i)) : xeps (tau i) ≔
  xJ (λ x _, tau x) H i (xsymmetry (isOneEq1Up p));

injective symbol isOneEq0Up [i] : tisOne (eq0 i) → xtEq i i0;
injective symbol isOneEq0Down [i] : xtEq i i0 → tisOne (eq0 i);
rule isOneEq0Down (isOneEq0Up $a) ↪ $a;
rule isOneEq0Up (isOneEq0Down $a) ↪ $a;
symbol ZeroEqualsZero : tisOne (eq0 i0) ≔ isOneEq1Down xrefl;
symbol elimIsOneEq0 (tau : (tI → xT)) (H : xeps (tau i0)) (i : tI) (p : tisOne (eq0 i)) : xeps (tau i) ≔
  xJ (λ x _, tau x) H i (xsymmetry (isOneEq0Up p));

symbol isOneEq1Eq0 (i : tI) (p1 : tisOne (eq0 i)) (p2 : tisOne (eq1 i)) : xtFalse ≔
  OneNeqZero (xtransitivity (xsymmetry (isOneEq1Up p2)) (isOneEq0Up p1));

injective symbol isOneMinUp [a b : tF] : tisOne (Fmin a b) → xtProd (isOne a) (isOne b);
injective symbol isOneMinDown [a b : tF] : xtProd (isOne a) (isOne b) → tisOne (Fmin a b);
rule @isOneMinUp $a $b (@isOneMinDown $a $b $x) ↪ $x;
rule isOneMinDown (isOneMinUp $a) ↪ $a;
symbol isOnePair [a b : tF] (p1 : tisOne a) (p2 : tisOne b) : tisOne (Fmin a b) ≔
  isOneMinDown (xpair p1 p2);
symbol isOneFst [a b : tF] (p : tisOne (Fmin a b)) : tisOne a ≔
  xfst (@isOneMinUp a b p);
symbol isOneSnd [a b : tF]  (p : tisOne (Fmin a b)) : tisOne b ≔
  xsnd (@isOneMinUp a b p);

injective symbol isOneMaxUp [a b : tF] : tisOne (Fmax a b) → xtSum (isOne a) (isOne b);
injective symbol isOneMaxDown [a b : tF] : xtSum (isOne a) (isOne b) → tisOne (Fmax a b);
rule @isOneMaxUp $a $b (@isOneMaxDown $a $b $x) ↪ $x;
rule isOneMaxDown (isOneMaxUp $a) ↪ $a;
symbol isOneinjl [a b : tF] (p : tisOne a) : tisOne (Fmax a b) ≔
  @isOneMaxDown a b (xinjl p);
symbol isOneinjr [a b : tF] (p : tisOne b) : tisOne (Fmax a b) ≔
  @isOneMaxDown a b (xinjr p);
symbol isOneCases (a b : tF) (tau : xT) (f : tisOne a → xeps tau) (g : tisOne b → xeps tau)
                  (p : tisOne (Fmax a b)) : xeps tau ≔
  xcase (λ _, tau) f g (isOneMaxUp p);
