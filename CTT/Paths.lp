require open ctt.CTT.Interval;
require open ctt.CTT.Internal;

// Path types
constant symbol PathP [i] (A : tI → T i) : eps (A i0) → eps (A i1) → T i;
symbol tPathP [i] (A : tI → T i) (x : eps (A i0)) (y : eps (A i1)) ≔ eps (PathP A x y);

symbol Path [i] [A : T i] (x y : eps A) ≔ PathP (λ _, A) x y;
symbol tPath [i] [A : T i] (x y : eps A) ≔ eps (Path x y);

injective symbol lamP [l] (A : tI → T l) (p : Π (i : tI), eps (A i)) : tPathP A (p i0) (p i1);

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
