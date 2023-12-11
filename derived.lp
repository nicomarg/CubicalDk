
require open ctt.ast;
require open ctt.DeBruijn;

symbol ttranspFill (A : Term) (f : FTerm) (u : Term) : Term ≔
  ttransp (applyI1 (IShift1 (IShift1 A)) (itmin (itvar db0) (itvar db1))) (ftmax (IShiftF f) (fteq0 db0)) (IShift u);

symbol forward (A : Term) (r : ITerm) (a : Term) : Term ≔
  ttransp (applyI1 (IShift1 A) (itmax (itvar db0) r)) (IsubstF db0 r (fteq1 db0)) a;

symbol thfill (A : Term) (f: FTerm) (u u0 : Term) : Term ≔
  thcomp (IShift A) (ftmax (fteq0 db0) (IShiftF f)) (tsys (fteq0 db1) (IShiftF (IShiftF f)) (IShift1 (IShift u0))
                                       (applyI1 (IShift1 (IShift1 u)) (itmax (itvar db0) (itvar db1)))) (IShift u0);

symbol tcomp (A : Term) (f : FTerm) (u u0 : Term) : Term ≔
  thcomp (applyI1 A it1) f (forward (IShift1 A) (itvar db0) u) (forward A it0 u0);
