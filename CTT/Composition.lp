require open ctt.CTT.IsOne;
require open ctt.CTT.2LTT;
require open ctt.CTT.Paths;
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

// TODO Glue Types

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

// TODO Glue types (and universes whic hdepend on those)
