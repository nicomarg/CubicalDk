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

symbol xtransitivity [A] [x y z : xeps A] : xtEq x y → xtEq y z → xtEq x z ≔
  λ p1 p2, xJ (λ z _, xEq x z) p1 z p2;

symbol xcong [A B] (f : xtndPi A B) [x y : xeps A] : (xtEq x y) → xtEq (f x) (f y) ≔
  λ eq, xJ (λ y _, xEq (f x) (f y)) xrefl y eq;
