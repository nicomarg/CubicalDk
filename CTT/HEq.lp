require open ctt.CTT.2LTT;

// heterogeneous equality for cubical conversion
symbol Hconv (l : Lev) (A B : T l) (a : eps A) (b : eps B) : xT ≔
  xSig (conv A B) (λ p, conv (convtransp p a) b);
symbol tHconv (l : Lev) (A B : T l) (a : eps A) (b : eps B) : TYPE ≔
  xeps (Hconv l A B a b);
symbol H [l : Lev] [A B : T l] (a : eps A) (b : eps B) ≔ Hconv l A B a b;
// This is weird, the correct way to do this is having transport injective in its final argument only
// as we can't do that, we make the end of the chain injective as it is a composition of injective maps
// the total type is xeps (xSig (xEq (isoUp A) (isoUp B)) (xEq (isoUp (convtransp p a)) (isoUp b)))
// where xeps, xSig, xEq, isoUp and convtransp p _ are injective
injective symbol tH [l : Lev] [A B : T l] (a : eps A) (b : eps B)  ≔ tHconv  l A B a b;

// symbol Hpair' [l : Lev] [A B : T l] (a : eps A) (b : eps B) (p : tconv A B) (h : tconv (convtransp p a) b) : tH a b ≔
//   xpair p h;
// symbol Hpair [l : Lev] [A B : T l] [a : eps A] [b : eps B] ≔ Hpair' a b;

symbol eq_to_heq [l : Lev] [A : T l] [a b : eps A] (p : tconv a b) : tH a b ≔
  xpair xrefl p;
symbol heq_to_eq [l : Lev] [A : T l] [a b : eps A] (h : tH a b) : tconv a b ≔
  xJ (λ p _, conv (convtransp p a) b) (xp2 h)
     xrefl (xK (λ p, xEq p xrefl) (xrefl) (xp1 h));

symbol heq_refl [l : Lev] [A : T l] (a : eps A) : tH a a ≔ xpair xrefl xrefl;
symbol heq_trans [l : Lev] [A B C : T l] [a : eps A] [b : eps B] [c : eps C]
                 (hab : tH a b) (hbc : tH b c) : tH a c ≔
  xpair (xtransitivity (xp1 hab) (xp1 hbc))
        (xtransitivity
          (convtransptrans (xp1 hab) (xp1 hbc) a)
          (xtransitivity (convcong (convtransp (xp1 hbc)) (xp2 hab)) (xp2 hbc)));
symbol heq_sym [l : Lev] [A B : T l] [a : eps A] [b : eps B]
                (h : tH a b) : tH b a ≔
  xpair (xsymmetry (xp1 h))
        (xtransitivity
          (xsymmetry (xtransitivity
                       (convtransptrans (xp1 h) (xsymmetry (xp1 h)) a)
                       (convcong (convtransp (xsymmetry (xp1 h))) (xp2 h))))
          (convtranspUIP (xtransitivity (xp1 h) (xsymmetry (xp1 h))) xrefl a));

symbol lift_to_heq [l l' : Lev] [A : T l] [B : eps A → T l']
                   (f : tPi A B) (u v : eps A) (p : tconv u v)
                   : tHconv l' (B u) (B v) (f u) (f v) ≔
  xJ (λ (v : tc A) _, Hconv l' (B u) (B (isoDown v)) (f u) (f (isoDown v))) (heq_refl (f u)) (isoUp v) p;

symbol heq_of_transport [l : Lev] [A B : T l] (a : eps A) (p : tconv A B) : tH a (convtransp p a) ≔
  xpair p xrefl;
symbol eq_of_transport [l : Lev] [A : T l] (a : eps A) (p : tconv A A) : tconv a (convtransp p a) ≔
  heq_to_eq (heq_of_transport a p);

symbol heq_conj [l : Lev] [A B C D : T l] [b : eps B] [c : eps C] (h : tH b c)
                (pBA : tconv B A) (pCD : tconv C D) : tH (convtransp pBA b) (convtransp pCD c) ≔
  heq_trans (heq_sym (heq_of_transport b pBA))
            (heq_trans h (heq_of_transport c pCD));
symbol heq_conj' [l : Lev] [A B C D : T l] [b : eps B] [c : eps C] (h : tH b c)
                (pAB : tconv A B) (pDC : tconv D C) : tH (convtransp (xsymmetry pAB) b) (convtransp (xsymmetry pDC) c) ≔
  heq_conj h (xsymmetry pAB) (xsymmetry pDC);
symbol heq_contract_R [l : Lev] [A B C : T l] (a : eps A) (c : eps C)
                    (p : tconv C B)
                    (h : tH a (convtransp p c)) :
                    tH a c ≔
  heq_trans h (heq_sym (heq_of_transport c p));
symbol heq_extend_R [l : Lev] [A B C : T l] (a : eps A) (b : eps B)
                    (p : tconv B C)
                    (h : tH a b) :
                    tH a (convtransp p b) ≔
  heq_trans h (heq_of_transport b p);
symbol heq_contract_L [l : Lev] [A B C : T l] (a : eps A) (c : eps C)
                    (p : tconv A B)
                    (h : tH (convtransp p a) c) :
                    tH a c ≔
  heq_trans (heq_of_transport a p) h;
symbol heq_extend_L [l : Lev] [A B C : T l] (b : eps B) (c : eps C)
                    (p : tconv B A)
                    (h : tH b c) :
                    tH (convtransp p b) c ≔
  heq_trans (heq_sym (heq_of_transport b p)) h;
