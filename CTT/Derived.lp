require open ctt.CTT.Paths;
require open ctt.CTT.2LTT;

symbol lamPfull [l] (A : tI → T l) (x : eps (A i0)) (y : eps (A i1))
                         (p : Π (i : tI), eps (A i)) : tconv (p i0) x → tconv (p i1) y → tPathP A x y ≔
begin
  assume l A x y p eqx eqy;
  refine convtransp (convcongtype (λ z, PathP A z y) eqx) _;
  refine convtransp (convcongtype (λ z, PathP A (p i0) z) eqy) _;
  refine lamP A p;
end;
