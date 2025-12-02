// Coercion from internal to external layer
require open ctt.CTT.Internal;
require open ctt.CTT.External;

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

symbol convtransp [i] [A : eps (t i)] [B : eps (t i)] : tconv A B → eps A → eps B ≔
  λ p a, @convelim (lsuc i) i (t i) A (λ B _, B) a _ p;

symbol convtransptrans [l : Lev] [A B C : T l] (p1 : tconv A B) (p2 : tconv B C) (a : eps A) :
  tconv (convtransp (xtransitivity p1 p2) a) (convtransp p2 (convtransp p1 a)) ≔
  xJ (λ (C : tc (t l)) (p : tconv B (isoDown C)), conv (convtransp (xtransitivity p1 p) a) (convtransp p (convtransp p1 a)))
    xrefl (isoUp C) p2;

symbol convtranspUIP [l : Lev] [A B : T l] (p1 p2 : tconv A B) (a : eps A) : tconv (convtransp p1 a) (convtransp p2 a) ≔
  xJ (λ p _, conv (convtransp p1 a) (convtransp p a)) xrefl p2 (UIP _ _ p1 p2);

symbol convcong [l m] [A : T l] [B : T m] (f : tndPi A B) [x y : eps A] (eq : tconv x y) : tconv (f x) (f y) ≔
  xJ (λ y _, conv (f x) (f (isoDown y))) convrefl (isoUp y) eq;

symbol convcongtype [l m] [A : T l] (f : tndPi A (t m)) [x y : eps A] (eq : tconv x y) : tconv (f x) (f y) ≔
  convcong f eq;
