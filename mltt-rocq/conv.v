Require ctt.

Definition tr_fold {U T:Type}(ety:U=T) (x:T) : U :=
  eq_rect_r (fun a => a) x ety.
Definition tr_unf {U T:Type}(ety:U=T) (x:U) : T :=
  eq_rect _ (fun a => a) x _ ety.
Definition sort_fold {l1 l2} (ety:l1=l2) (x:ctt.T l2) :=
  eq_rect_r (fun a => ctt.T a) x ety.
Definition sort_unf {l1 l2} (ety:l1=l2) (x:ctt.T l1) :=
  eq_rect _ (fun a => ctt.T a) x _ ety.
Definition elt_fold {l U} {T:ctt.T l} (ety:U=T) (x:ctt.eps T) :=
  eq_rect_r (fun a => ctt.eps a) x ety.
Definition elt_unf {l U} {T:ctt.T l} (ety:U=T) (x:ctt.eps U) :=
  eq_rect _ (fun a => ctt.eps a) x _ ety.


Definition conv {l:ctt.Lev} (T:ctt.T l) (t1 t2 : ctt.eps T) : Type :=
  ctt.xeps (@ctt.conv l T t1 t2).

(*
Parameter convT : forall {l1 l2}, ctt.T l1 -> ctt.T l2 -> Type.
Parameter Trefl : forall {l} {a:ctt.T l}, convT a a.
Parameter Tsym : forall {l1 l2} {a:ctt.T l1} {b:ctt.T l2}, convT a b -> convT b a.
Parameter Ttrans : forall {l1 l2 l3} {a:ctt.T l1} {b:ctt.T l2} {c:ctt.T l3},
    convT a b -> convT b c -> convT a c.
Parameter transport : forall {l} {T U:ctt.T l},
    convT T U ->  ctt.eps T -> ctt.eps U.*)

Definition convT {l} (A B: ctt.T l) :=
  @ctt.tconv _ (ctt.t l) (ctt.cd A) (ctt.cd B).

Definition transport {l} {T U:ctt.T l}
  (e:convT T U) (x:ctt.eps T) : ctt.eps U :=
  ctt.convtransp e x.

Definition ctransport {l} {T U:ctt.T l}(x y : ctt.eps T)
  (e:convT T U) :
    conv T x y -> conv U (transport e x) (transport e y).
unfold conv, ctt.conv.
intros.
rewrite <-(ctt.isoUpDown y).
apply @ctt.xJ with (p:=X) (tau:=fun y _ =>
 ctt.xEq _ (ctt.isoUp (transport e x))
         (ctt.isoUp (transport e (ctt.isoDown y)))).
rewrite (ctt.isoUpDown x).
apply ctt.xrefl.
Qed.

Definition ctransportK {l} {T U:ctt.T l}(x y : ctt.eps T)
  (e e':convT T U) :
    conv T x y -> conv U (transport e x) (transport e' y).
Admitted.

