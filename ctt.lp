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

// Extra universe for objets inaccessible in the theory, but used for typechecking
constant symbol xT : TYPE;
injective symbol xeps : xT → TYPE;

// Pi-types for the extra universe
constant symbol xPi (A : xT) : (xeps A → xT) → xT;
symbol xtPi ≔ λ (A : xT) (B : xeps A → xT), xeps (xPi A B);
rule xeps (xPi $A $B) ↪ Π (x : xeps $A), xeps ($B x);

symbol xndPi ≔ λ (A : xT) (B : xT), xPi A (λ _, B);
symbol xtndPi ≔ λ (A : xT) (B : xT), xeps (xndPi A B);

// Sigma Types for the extra universe
constant symbol xSig (A : xT) : (xeps A → xT) → xT;
symbol xtSig (A : xT) (B : xeps A → xT) ≔ xeps (xSig A B);
constant symbol xpair [A : xT] [B : xeps A → xT] (x : xeps A) : xeps (B x) → xtSig A B;
symbol xp1 [A : xT] [B : xeps A → xT] : xtSig A B → xeps A;
symbol xp2 [A : xT] [B : xeps A → xT] (a : xtSig A B) : xeps (B (xp1 a));
rule xp1 (xpair $a _) ↪ $a;
rule xp2 (xpair _ $b) ↪ $b;

// Some datatypes in the external layer needed later
constant symbol xFalse : xT;
symbol xtFalse ≔ xeps xFalse;
symbol xelimFalse : Π (A : xT), xtFalse → xeps A;

constant symbol xTrue : xT;
symbol xtTrue ≔ xeps xTrue;
constant symbol xtt : xtTrue;
symbol xelimTrue : Π (tau : (xtTrue → xT)), xeps (tau xtt) → Π (p : xtTrue), xeps (tau p);
rule xelimTrue _ $e xtt ↪ $e;

symbol xProd (A : xT) (B : xT) : xT ≔ xSig A (λ _, B);
symbol xtProd ≔ λ (A : xT) (B : xT), xeps (xProd A B);
symbol xfst [A B] ≔ @xp1 A (λ _, B);
symbol xsnd [A B] ≔ @xp2 A (λ _, B);

constant symbol xSum : xT → xT → xT;
symbol xtSum ≔ λ (A B : xT), xeps (xSum A B);
constant symbol xinjl [A B] : xeps A → xtSum A B;
constant symbol xinjr [A B] : xeps B → xtSum A B;
symbol xcase [A B] (tau : xtSum A B → xT) :
             (Π (a : xeps A), xeps (tau (xinjl a))) →
             (Π (b : xeps B), xeps (tau (xinjr b))) →
             Π (x : xtSum A B), xeps (tau x);

/* External equality, used to describe conversion which cannot be defined as
rewrite rules, mainly extended conversion on interval and face types, and
conversions which only hold on certain faces */

constant symbol xEq [A : xT] : xeps A → xeps A → xT;
symbol xtEq [A] ≔ λ (x y : xeps A), xeps (xEq x y);
constant symbol xrefl [A : xT] [x : xeps A] : xtEq x x;
symbol xJ [A : xT] [x : xeps A] (tau : Π (y : xeps A) (p : xtEq x y), xT) :
  xeps (tau x xrefl) → Π (y : xeps A) (p : xtEq x y), xeps (tau y p);
rule xJ _ $H _ xrefl ↪ $H;

// UIP for external equality
symbol xK [A] [x : xeps A] (tau : Π (p : xtEq x x), xT) :
  xeps (tau xrefl) → Π (p : xtEq x x), xeps (tau p);
rule xK _ $H xrefl ↪ $H;

symbol UIP [A] (x y : xeps A) (p p' : xtEq x y) : xtEq p p' ≔
begin
assume A x;
refine xJ (λ y p, xPi (xEq x y) (λ p', xEq p p')) _;
refine xK _ xrefl;
end;

// FunExt for external equality
symbol FunExt [A B] (f g : xtPi A B) (p : Π (a : xeps A), xtEq (f a) (g a)) :
  xtEq f g;

symbol xsymmetry [A] [x y : xeps A] : xtEq x y → xtEq y x ≔
  λ p, xJ (λ y _, xEq y x) xrefl y p;

symbol xcomposition [A] [x y z : xeps A] : xtEq x y → xtEq y z → xtEq x z ≔
  λ p1 p2, xJ (λ z _, xEq x z) p1 z p2;

symbol xcong [A B] (f : xtndPi A B) [x y : xeps A] : (xtEq x y) → xtEq (f x) (f y) ≔
  λ eq, xJ (λ y _, xEq (f x) (f y)) xrefl y eq;

// Coercion from internal to external layer

constant symbol c [i] : T i → xT;
symbol tc [i] ≔ λ (A : T i), xeps (c A);

injective symbol isoUp [i] [A : T i] : eps A → tc A;
injective symbol isoDown [i] [A : T i] : tc A → eps A;
rule isoDown (isoUp $x) ↪ $x;
rule isoUp (isoDown $x) ↪ $x;

symbol clift [i] ≔ λ (A : T i) (B : eps A → T i) (xa : tc A), c (B (isoDown xa));

// c (Pi A B) isomorphic / equal to Pi (c A) (c B) ?

// macros for using external equality as cubical conversion
symbol conv [i] [A : T i] (x y : eps A) ≔ xEq (isoUp x) (isoUp y);
symbol tconv [i] [A : T i] (x y : eps A) ≔ xeps (conv x y);
symbol convrefl [i] [A : T i] [x : eps A] : tconv x x ≔ xrefl;
symbol convtype [i] (A B : T i) ≔ @conv (lsuc i) (t i) A B;
symbol tconvtype [i] (A B : T i) ≔ @tconv (lsuc i) (t i) A B;

symbol convelim [i j] [A : T i] [x : eps A]
                (tau : Π (y : eps A), tconv x y → T j) :
  eps (tau x convrefl) → Π (y : eps A) (p : tconv x y), eps (tau y p) ≔
begin
assume i j A x tau H y p;
refine isoDown _;
refine xJ (λ z q, c (tau (isoDown z) q)) _ _ _;
refine isoUp _;
refine H
end;
print convelim;

symbol convtransp [i] [A : eps (t i)] [B : eps (t i)] : tconv A B → eps A → eps B ≔
  λ p a, @convelim (lsuc i) i (t i) A (λ B _, B) a _ p;

symbol convcong [l m] [A : T l] [B : T m] (f : tndPi A B) [x y : eps A] (eq : tconv x y) : tconv (f x) (f y) ≔
  xJ (λ y _, conv (f x) (f (isoDown y))) convrefl (isoUp y) eq;

symbol convcongtype [l m] [A : T l] (f : tndPi A (t m)) [x y : eps A] (eq : tconv x y) : tconv (f x) (f y) ≔
  convcong f eq;

// Cubical primitives
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
  OneNeqZero (xcomposition (xsymmetry (isOneEq1Up p2)) (isOneEq0Up p1));

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

// Path types
constant symbol PathP [i] (A : tI → T i) : eps (A i0) → eps (A i1) → T i;
symbol tPathP [i] (A : tI → T i) (x : eps (A i0)) (y : eps (A i1)) ≔ eps (PathP A x y);

symbol Path [i] [A : T i] (x y : eps A) ≔ PathP (λ _, A) x y;
symbol tPath [i] [A : T i] (x y : eps A) ≔ eps (Path x y);

injective symbol lamP [l] (A : tI → T l) (p : Π (i : tI), eps (A i)) : tPathP A (p i0) (p i1);

symbol lamPfull [l] (A : tI → T l) (x : eps (A i0)) (y : eps (A i1))
                         (p : Π (i : tI), eps (A i)) : tconv (p i0) x → tconv (p i1) y → tPathP A x y ≔
begin
  assume l A x y p eqx eqy;
  refine convtransp (convcongtype (λ z, PathP A z y) eqx) _;
  refine convtransp (convcongtype (λ z, PathP A (p i0) z) eqy) _;
  refine lamP A p;
end;

symbol app [l] [A : tI → T l] [u : eps (A i0)] [v : eps (A i1)] : (tPathP A u v) → Π i : tI, eps (A i);

rule app (lamP _ $p) $i ↪ $p $i;
rule @app _ _ $u _ _ i0 ↪ $u;
rule @app _ _ _ $v _ i1 ↪ $v;
rule lamP $A (λ i, @app $_.[] $A.[] $_.[] $_.[] $p.[] i) ↪ $p;

symbol lam [l] [A : T l] (p : tI → eps A) ≔ lamP (λ _, A) p;

symbol pathrefl [l] [A : T l] [x :eps A] : tPath x x ≔ lam (λ _, x);

symbol pathsym [l] [A : T l] [x y : eps A] (p : tPath x y) : tPath y x ≔
  lam (λ i, app p (sym i));
symbol pathcong [l] [A : T l] [x y : eps A] [B : eps A → T l] (f : tPi A B)
                (p : tPath x y) : tPathP (λ i, B (app p i)) (f x) (f y) ≔
  lamP (λ i, B (app p i)) (λ i, f (app p i));

symbol symId [l] [A : T l] [x y : eps A] (p : tPath x y) : tPath (pathsym (pathsym p)) p ≔
  pathrefl;
symbol congId [l] [A : T l] [x y : eps A] (p : tPath x y) : tPath (pathcong (λ x, x) p) p ≔
  pathrefl;
symbol congComp [l] [A B C : T l] (f : tndPi A B) (g : tndPi B C) [x y : eps A]
                (p : tPath x y) : tPath (pathcong (λ a, g (f a)) p) (pathcong g (pathcong f p)) ≔
  pathrefl;

symbol pathFunExt [l] [A : T l] [B : eps A → T l] [f g : tPi A B]
                  (p : Π x : eps A, tPath (f x) (g x)) : @tPath l (Pi A B) (λ x, f x) (λ x, g x) ≔
  lam (λ i : tI, λ x : eps A, app (p x) i);

// Transport
// Primitive transport, with the explicit side condition that A must be constant on the extent f
symbol transp [l] (A : tI → T l) (f : tF) (a : eps (A i0)) :
  (tisOne f → Π (i : tI), tconvtype (A i0) (A i)) → eps (A i1);
protected symbol primTransp [l] (A : tI → T l) (f : tF) (a : eps (A i0)) : eps (A i1);
rule transp $A $f $a _ ↪ primTransp $A $f $a;
rule primTransp (λ _, _) 1f $a ↪ $a;

/* the resulting conversion transp A f a = a on the extent f. As the fact that A is a constant
type family on f doesn't always hold up to Dedukti conversion, we have to transport along our
external equality representing conversion for the resulting conversion to typecheck */
symbol transpConv [l] (A : tI → T l) (f : tF) (a : eps (A i0)) (eq : tisOne f → Π i : tI, tconvtype (A i0) (A i)) :
  Π (p : tisOne f), tconv (transp A f a eq) (convtransp (eq p i1) a);

/* Transp filling operation, which comes with the proof that f ⇒ A = A (i0) implies
f ∨ (i = 0) ⇒ A (i ∨ j) = A (i ∨ j) (i0) */
symbol transpFill [l] (A : tI → T l) (f : tF) (a : eps (A i0)) (eq : tisOne f → Π i : tI, tconvtype (A i0) (A i)) :
  Π i : tI, eps (A i) ≔
begin
assume l A f a eq i;
refine transp (λ j, A (Imin i j)) (Fmax f (eq0 i)) a _;
assume p k;
apply isOneCases f (eq0 i) _ (λ p1, _) (λ p1, _) p
{ apply eq p1}
{ apply elimIsOneEq0 (λ i, convtype (A (Imin i i0)) (A (Imin i k)))  _ i p1;
  refine convrefl }
end;

protected symbol primTranspFill [l] (A : tI → T l) (f : tF) (a : eps (A i0)) (i : tI) : eps (A i) ≔
  primTransp (λ j, A (Imin i j)) (Fmax f (eq0 i)) a;

symbol forward [l] (A : tI → T l) (r : tI) (a : eps (A r)) : eps (A i1) ≔
begin
  assume l A r a;
  refine transp (λ i, A (Imax i r)) (eq1 r) a _;
  assume p i;
  apply elimIsOneEq1 (λ r, convtype (A (Imax i0 r)) (A (Imax i r))) _ r p;
  refine convrefl
end;

// Usual transport is then defined like this
symbol transport [l] [A B : T l] (p : @tPath (lsuc l) (t l) A B) (x : eps A) : eps B ≔
  transp (λ i, app p i) 0f x (λ p i, elimIsOneZero p);

// J eliminator for path types, whose usual computation rule only holds up to path equality
symbol J [i j : Lev] [A : T i] [x : eps A] (tau : Π y : eps A, tPath x y → T j) (H : eps (tau x pathrefl))
     (y : eps A) (p : tPath x y) : eps (tau y p) ≔
  transport (lam (λ r, tau (app p r) (lam (λ s, app p (Imin r s))))) H;

symbol transportRefl [l] (A : T l) (x : eps A) : tPath (transport (pathrefl) x) x ≔
  lam (λ i, transp (λ _, A) (eq1 i) x (λ _ _, convrefl));

symbol Jrefl [l l'] [A : T l] [x : eps A] (tau : Π (y : eps A), tPath x y → T l')
             (H : eps (tau x pathrefl)) : tPath (J tau H x pathrefl) H ≔
  transportRefl (tau x pathrefl) H;

// Partial elements

// The type Partial φ A represents terms only defined when φ holds.
constant symbol Partial [l] : tF → T l → xT;
symbol tPartial [l] (f : tF) (A : T l) ≔ xeps (Partial f A);
rule xeps (Partial $f $A) ↪ tisOne $f → eps $A;

symbol PartialP [l] (f : tF) : tPartial f (t l) → xT;
symbol tPartialP [l] (f : tF) (A : tPartial f (t l)) ≔ xeps (PartialP f A);
rule xeps (PartialP $f $A) ↪ Π (p : tisOne $f), eps ($A p);

/* The (nontrivial) inhabitants of Partial φ A are defined depending on the
shape of the face φ:
* When it is 1f or 0f, they come from a total element in A, or the elimination
  of the empty type respectively.
* When it is (i = 0) or (i = 1), one can inhabit Partial (i = 0) A i by
  inhabiting A 0 or A 1
* When it is a conjunction, the inhabitants have no particular form, they can
  use both subformulae by accessing isOneFst φ and isOneSnd φ
* When it is a disjunction, one provides a term system, meaning partial terms
  for both cases, along with the proof that they are equal when both formulae
  hold. */

symbol PartialEmpty [l] [A : T l] : tPartial 0f A ≔ λ p, isoDown (elimIsOneZero p);

symbol PartialEq0 [l] (A : tI → T l) (x : eps (A i0)) (i : tI) : tPartial (eq0 i) (A i);
rule PartialEq0 _ $x i0 _ ↪ $x;
symbol PartialEq1 [l] (A : tI → T l) (x : eps (A i1)) (i : tI) : tPartial (eq1 i) (A i);
rule PartialEq1 _ $x i1 _ ↪ $x;

symbol PartialSys [l] [A : T l] (f g : tF) (u : tPartial f A) (v : tPartial g A) :
  (Π (p1 : tisOne f) (p2 : tisOne g), tconv (u p1) (v p2)) → tPartial (Fmax f g) A;
protected symbol primSys [l] [A : T l] (f g : tF) (u : tPartial f A) (v : tPartial g A) : tPartial (Fmax f g) A;
rule PartialSys $f $g $u $v _ ↪ primSys $f $g $u $v;
rule primSys 1f _ $u _ ↪ $u;
rule primSys _ 1f _ $v ↪ $v;
rule primSys 0f _ _ $v ↪ $v;
rule primSys _ 0f $u _ ↪ $u;

/* With this definition of Partial, the conversion we expect on partial (i.e.
terms agree only when φ holds) is just function extentionality (whenever given a
proof of isOne φ, if the terms are convertible, then the functions are too)
however, as (for convenience) this product isn't between two external types, we
have to assume function extentionality for this special product */

symbol PartialConv [l] [f : tF] [A : T l] (x y : tPartial f A) :
  (Π (p : tisOne f), tconv (x p) (y p)) → @xtEq (Partial f A) x y;

/* A type expressing the CCHM/CHM macro A[φ ↦ u] (and the corresponding Sub cubical Agda type)
whose inhabitants are terms of type A, which are convertible to u on the extent φ */
constant symbol Sub [l] (A : T l) (f : tF) : tPartial f A → xT;
symbol tSub [l] (A : T l) (f : tF) (u : tPartial f A) ≔ xeps (Sub A f u);

symbol inS [l] [A : T l] [f : tF] [u : tPartial f A] (x : eps A)
           (eq : Π p : tisOne f, tconv x (u p)) : tSub A f u;
symbol outS [l] [A : T l] [f : tF] [u : tPartial f A] (x : tSub A f u) : eps A;
symbol proofS [l] [A : T l] [f : tF] [u : tPartial f A] (x : tSub A f u) (p : tisOne f) :
  tconv (outS x) (u p);
rule outS (inS $x _) ↪ $x;
rule proofS (inS _ $p) ↪ $p;

// Homogeneous composition
symbol hcomp [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A) :
  (Π p : tisOne f, tconv u0 (u i0 p)) → eps A;
protected symbol primHcomp [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A) : eps A;
rule hcomp $A $f $u $u0 _ ↪ primHcomp $A $f $u $u0;
rule primHcomp _ 1f $u _ ↪ $u i1 itIsOne;

symbol hcompConv [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A)
                 (eq : Π p : tisOne f, tconv u0 (u i0 p)) (p : tisOne f) : tconv (hcomp A f u u0 eq) (u i1 p);

symbol hfillSys [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A)
                (eq : Π p : tisOne f, tconv u0 (u i0 p)) (i : tI) (j : tI) : tPartial (Fmax (eq0 i) f) A ≔
begin
  assume l A f u u0 eq i j;
  refine PartialSys (eq0 i) f (λ _, u0) (u (Imin i j)) _;
  assume p1 p2;
  refine elimIsOneEq0 (λ k, conv u0 (u (Imin k j) p2)) _ i p1;
  refine eq p2
end;

symbol hfill [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A)
             (eq : Π p : tisOne f, tconv u0 (u i0 p)) (i : tI) : eps A ≔
  hcomp A (Fmax (eq0 i) f) (hfillSys A f u u0 eq i) u0
        (λ p, isOneCases (eq0 i) f (conv u0 (hfillSys A f u u0 eq i i0 p))
            (λ p1, elimIsOneEq0 (λ i, xPi (isOne (Fmax (eq0 i) f)) (λ p, conv u0 (hfillSys A f u u0 eq i i0 p)))
                                (λ _, convrefl) i p1 p)
            (λ p2, xJ (λ g _, xPi (xPi I (λ i, Partial g A))
                                  (λ u, xPi (xPi (isOne g) (λ p, conv u0 (u i0 p)))
                                      (λ eq, xPi (isOne (Fmax (eq0 i) g))
                                          (λ p, conv u0 (hfillSys A g u u0 eq i i0 p)))))
                      (λ u eq p, eq p) f (isOneConv f p2) u eq p) p);
// begin
//   assume l A f u u0 eq i;
//   refine hcomp A (Fmax (eq0 i) f) (hfillSys A f u u0 eq i) u0 _;
//   assume p;
//   refine isOneCases (eq0 i) f _ (λ p1, _) (λ p2, _) p
//   { refine elimIsOneEq0 (λ i, xPi (isOne (Fmax (eq0 i) f)) (λ p, conv u0 (hfillSys A f u u0 eq i 0 p)))
//                         (λ _, convrefl) i p1 p }
//   { refine xJ (λ g _, xPi (xPi I (λ i, Partial l g A))
//                           (λ u, xPi (xPi (isOne g) (λ p, conv u0 (u 0 p)))
//                                     (λ eq, xPi (isOne (Fmax (eq0 i) g))
//                                                (λ p, conv u0 (hfillSys A g u u0 eq i 0 p)))))
//         (λ u eq p, eq p) f (isOneConv f p2) u eq p;
//      };
// end;

symbol primHfill [l] (A : T l) (f : tF) (u : tI → tPartial f A) (u0 : eps A) (i : tI) : eps A ≔
  primHcomp A (Fmax (eq0 i) f) (λ j, primSys (eq0 i) f (λ _, u0) (u (Imin i j))) u0;

symbol pathcompsys [l] [A : T l] [x y z : eps A] (p : tPath x y) (q : tPath y z) (i j : tI) ≔
  PartialSys (eq0 i) (eq1 i) (λ _, x) (λ _, app q j) (λ p1 p2, xelimFalse (conv x (app q j)) (isOneEq1Eq0 i p1 p2));

symbol pathcomp [l] [A : T l] [x y z : eps A] (p : tPath x y) (q : tPath y z) : tPath x z ≔
begin
  assume l A x y z p q;
  refine lam (λ i, hcomp A (Fmax (eq0 i) (eq1 i)) (pathcompsys p q i) (app p i) _);
  assume  p12;
  refine isOneCases (eq0 i) (eq1 i) (conv (app p i) _) (λ p1, _) (λ p2, _) p12
  { refine elimIsOneEq0 (λ i, xPi (isOne (Fmax (eq0 i) (eq1 i)))
                                  (λ p12, conv (app p i) (pathcompsys p q i i0 p12)))
                        (λ _, convrefl) i p1 p12 }
  { refine elimIsOneEq1 (λ i, xPi (isOne (Fmax (eq0 i) (eq1 i)))
                                  (λ p12, conv (app p i) (pathcompsys p q i i0 p12)))
                        (λ _, convrefl) i p2 p12 }
end;

symbol comp [l] (A : tI → T l) (f : tF) (u : Π i, tPartial f (A i)) (u0 : eps (A i0))
            (eq : Π p : tisOne f, tconv u0 (u i0 p)) : eps (A i1) ≔
  hcomp (A i1) f (λ i p, forward A i (u i p)) (transport (lam A) u0)
        (λ p, convcong (λ x, transp (λ i, A i) 0f x (λ p i, elimIsOneZero p)) (eq p));

symbol compConv [l] (A : tI → T l) (f : tF) (u : Π i, tPartial f (A i)) (u0 : eps (A i0))
            (eq : Π p : tisOne f, tconv u0 (u i0 p)) : Π p : tisOne f, tconv (comp A f u u0 eq) (u i1 p) ≔
begin
  assume l A f u u0 eq p;
  simplify;
  refine hcompConv (A i1) f (λ i p, forward A i (u i p)) (transport (lam A) u0) _ p;
  assume p1;
  simplify;
  refine convcong (λ x, primTransp (λ i, A i) 0f x) (eq p1)
end;

symbol primComp [l] (A : tI → T l) (f : tF) (u : Π i, tPartial f (A i)) (u0 : eps (A i0)) : eps (A i1) ≔
  primHcomp (A i1) f (λ i p, forward A i (u i p)) (transport (lam A) u0);

// TODO Glue types

// Conversion rules for transp on normal forms, by case analysis on the type
rule primTransp (λ _, Nat _) _ zero ↪ zero;
rule primTransp (λ _, Nat _) $f (S $n) ↪ S (primTransp (λ _, Nat _) $f $n);

rule primTransp (λ i, PathP $A.[i] $u.[i] $v.[i]) $f $u0 ↪
     lamP $A.[i1] (λ j, primComp (λ i, $A.[i] j) (Fmax $f (Fmax (eq0 j) (eq1 j)))
                 (λ i, primSys $f (Fmax (eq0 j) (eq1 j))
                               (λ _, primTranspFill (λ k, $A.[k] j) $f (app $u0 j) i)
                               (primSys (eq0 j) (eq1 j)
                                        (PartialEq0 $A.[i] $u.[i] j)
                                        (PartialEq1 $A.[i] $v.[i] j)))
                 (app $u0 j));

rule primTransp (λ i, @Sig $_.[] $_.[] $A.[i] $B.[i]) $f $u0 ↪
     pair (primTransp (λ i, $A.[i]) $f (p1 $u0))
          (primTransp (λ i, $B.[i] (primTranspFill (λ j, $A.[j]) $f (p1 $u0) i)) $f (p2 $u0));

rule primTransp (λ i, @Pi $_.[] $_.[] $A.[i] $B.[i]) $f $u0 $v ↪
     primTransp (λ i, $B.[i] (primTransp (λ j, $A.[Imax i (sym j)]) (Fmax $f (eq1 i)) $v))
                $f ($u0 (primTransp (λ i, $A.[sym i]) $f $v));

rule primTransp (λ i, @Sum $_.[] _ $A.[i] _) $f (injl $a) ↪
     injl (primTransp (λ i, $A.[i]) $f $a);
rule primTransp (λ i, @Sum _ $_.[] _ $B.[i]) $f (injr $b) ↪
     injr (primTransp (λ i, $B.[i]) $f $b);

rule primTransp (λ _, t _) _ $A ↪ $A;

// Glue Types ?

// Conversion rules for hcomp on normal forms by case analysis on the type
rule primHcomp (Nat _) _ _ zero ↪ zero;
rule primHcomp (Nat _) $f (λ i p, S $n.[i;p]) (S $n0) ↪ S (primHcomp (Nat _) $f (λ i p, $n.[i;p]) $n0);

rule primHcomp (PathP $A $v $w) $f $u $u0 ↪
     lamP $A (λ j, primHcomp ($A j) (Fmax $f (Fmax (eq0 j) (eq1 j)))
             (λ i, primSys $f (Fmax (eq0 j) (eq1 j)) (λ p, app ($u i p) j)
             (primSys (eq0 j) (eq1 j) (PartialEq0 $A $v j) (PartialEq1 $A $w j))) (app $u0 j));

symbol hcompSigRHS [l m] (A : T l) (B : eps A → T m) (f : tF)
                   (u : tI → tPartial f (Sig A B)) (u0 : tSig A B) : tSig A B ≔
begin
  assume l m A B f u u0;
  refine pair _ _
  { refine primHcomp A f (λ i p, p1 (u i p)) (p1 u0) }
  { refine primComp (λ i, B (primHfill A f (λ i p, p1 (u i p)) (p1 u0) i)) f _ _
    { assume i p;
      have H: tconvtype (B (p1 (u i p))) (B (primHfill A f (λ i1 p', p1 (u i1 p')) (p1 u0) i))
      { refine convcongtype (λ t, B t) _;
        refine xJ (λ g _, xPi (isOne g)
                              (λ p, xPi (xPi I (λ i, Partial g (Sig A B)))
                                        (λ u, conv (p1 (u i p)) (primHfill A g (λ i1 p', p1 (u i1 p')) (p1 u0) i))))
               (λ q v, _) f (isOneConv f p) p u;
        refine xcong (λ q, isoUp (p1 (v i q))) (elimIsOneOne (λ q, xEq q itIsOne) xrefl q) };
      refine convtransp H (p2 (u i p)) }
    { refine p2 u0 } }
end;

rule primHcomp (Sig $A $B) $f $u $u0 ↪ hcompSigRHS $A $B $f $u $u0;
     // pair (primHcomp $A $f (λ i p, p1 ($u i p)) (p1 $u0))
     //      (primComp (λ i, $B (primHfill $A $f (λ i p, p1 ($u i p)) (p1 $u0) i))
     //                $f (λ i p, p2 ($u i p)) (p2 $u0));

rule primHcomp (Pi _ $B) $f $u $u0 $v ↪ primHcomp ($B $v) $f (λ i p, ($u i p) $v) ($u0 $v);

rule primHcomp (Sum $A _) $f (λ i p, injl ($u.[i;p])) (injl $a) ↪
     injl (primHcomp $A $f (λ i p, $u.[i;p]) $a);

rule primHcomp (Sum _ $B) $f (λ i p, injr ($u.[i;p])) (injr $b) ↪
     injr (primHcomp $B $f (λ i p, $u.[i;p]) $b);

// Rule for primHcomp (t l) uses Glue
