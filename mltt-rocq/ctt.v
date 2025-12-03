  Parameter Lev : Type.
  Parameter lsuc : Lev -> Lev.

  Parameter T : Lev -> Type.
  Parameter eps : forall {l}, T l -> Type.
  Parameter t : forall l, T (lsuc l).
  Parameter cd : forall {l}, T l -> eps (t l).
  Parameter dc : forall {l}, eps (t l) -> T l.
  Parameter cdc : forall {l} {a:T l}, eps (dc (cd a)) -> eps a.
  Parameter cdc_exp : forall {l} {a:T l}, eps a -> eps (dc (cd a)).

  Parameter lUp : forall {l}, T l -> T(lsuc l).
  Parameter lUp_eps : forall {l} {a:T l}, eps (lUp a) = eps a.

  Parameter Nat : forall l:Lev, T l.
  Definition tNat := fun l => eps (Nat l).
  Parameter zero : forall {l}, tNat l.
  Parameter S : forall {l}, @tNat l -> @tNat l.

  Parameter Pi : forall {l} (A :T l), (eps A->T l) -> T l.
  Parameter app : forall {l} {A :T l }{B:eps A->T l},
     eps (Pi A B) -> forall x:eps A, eps (B x).

  Parameter xT : Type.
  Parameter xeps : xT -> Type.

  Parameter xEq : forall A : xT, xeps A -> xeps A -> xT.
  Parameter xrefl : forall {A : xT}{x : xeps A}, xeps (xEq A x x).
  Parameter xJ :
    forall {A : xT}{x : xeps A}
           (tau : forall (y : xeps A) (p:xeps(xEq A x y)), xT),
      xeps (tau x xrefl) ->
      forall (y : xeps A) (p : xeps (xEq A x y)), xeps (tau y p).
  Parameter xJ_def :
    forall {A : xT}{x : xeps A}
           (tau : forall (y : xeps A) (p:xeps(xEq A x y)), xT)
           (h : xeps (tau x xrefl)),
      xJ tau h _ xrefl = h.
  Parameter xK : forall (A:xT) (x y:xeps A) (p q:xeps (xEq A x y)), p=q.
  Lemma xsym : forall {a x y}, xeps(xEq a x y) -> xeps(xEq a y x).
intros.
elim X using xJ with (tau := fun y p => xEq a y x).
apply xrefl.
Defined.
  Lemma xtrans :
    forall {a x y z}, xeps(xEq a x y) -> xeps(xEq a y z) -> xeps(xEq a x z).
intros.
elim X0 using xJ with (tau := fun y p => xEq a x y); exact X.
Defined.
  Lemma eq_xEq {A:xT} {x y:xeps A}:
    x = y -> xeps (xEq A x y).
destruct 1; apply xrefl.
Defined.

  Parameter c : forall {l}, T l -> xT.
  Definition tc {l} (A : T l) := xeps (c A).
  Parameter isoUp : forall {l} {A:T l}, eps A -> tc A.
  Parameter isoDown : forall {l} {A:T l}, tc A -> eps A.
  Parameter isoUpDown : forall {l} {A:T l}(x:eps A), isoDown (isoUp x) = x.
  Parameter isoDownUp : forall {l} {A:T l}(x:tc A), isoUp (isoDown x) = x.
  Parameter iso_wequiv: forall {l} {A:T l}(x:eps A),
      isoDownUp (isoUp x) = f_equal isoUp (isoUpDown x).

  Definition conv {l} {A : T l} (x y : eps A) :=
    xEq (c A) (isoUp x) (isoUp y).
  Definition tconv {l} {a:T l} (x y:eps a) := xeps (conv x y).

  Lemma convrefl {l a x} : @tconv l a x x.
apply xrefl.
Defined.
  Lemma convsym {l a x y} : tconv x y -> @tconv l a y x.
apply xsym.
Defined.
  Lemma convtrans {l a x y z} : tconv x y -> tconv y z -> @tconv l a x z.
apply xtrans.
Defined.

  Lemma tconv_eq1 {l} {A:T l} {x y:eps A}:
    isoUp x = isoUp y -> tconv x y.
intros; apply eq_xEq; trivial.
Defined.
(*  Lemma tconv_eq {l} {A:T l} (x y:eps A):
    tconv x y -> isoUp x = isoUp y.
unfold tconv, conv.
intros.
elim X using xJ
*)
  Lemma convxelim : forall {i}{A : T i}{x : eps A}
                (tau : forall (y : eps A), tconv x y -> xT),
      xeps (tau x convrefl) -> forall (y : eps A) (p : tconv x y), xeps (tau y p).
intros.
pose (q := fun y:eps A => isoDownUp (isoUp y)).
pose (q' := fun y:eps A => f_equal isoUp (isoUpDown y)).
assert (forall y, q y=q' y) by ( intros; apply iso_wequiv).
replace (tau y p) with (tau (isoDown (isoUp y)) (xtrans p (eq_xEq (eq_sym (q y))))).
2:{
 rewrite H.
 unfold q'.
 replace (eq_sym (f_equal isoUp (isoUpDown y)))
   with (f_equal isoUp (eq_sym (isoUpDown y))).
 destruct (eq_sym(isoUpDown y)).
 unfold eq_xEq, f_equal; simpl.
 unfold xtrans.
 rewrite xJ_def; trivial.
 destruct (isoUpDown y); reflexivity. }
 unfold q.
 elim p using xJ with (tau:=fun y p => tau (isoDown y) (xtrans p (eq_xEq (eq_sym (isoDownUp y))))).
 fold (q x).
 rewrite H.
 unfold q'.
 replace (eq_sym (f_equal isoUp (isoUpDown x)))
   with (f_equal isoUp (eq_sym (isoUpDown x))).
 destruct (eq_sym(isoUpDown x)).
 unfold eq_xEq, f_equal; simpl.
 unfold xtrans.
 rewrite xJ_def; trivial.
 destruct (isoUpDown x); reflexivity.
Qed.

  Lemma convelim : forall {i j}{A : T i}{x : eps A}
                (tau : forall (y : eps A), tconv x y -> T j),
      eps (tau x convrefl) -> forall (y : eps A) (p : tconv x y), eps (tau y p).
intros.
apply isoDown.
unfold tc.
apply convxelim with (tau := fun y p => c (tau y p)).
apply isoUp; trivial.
Defined.

  Definition convtransp {l}{A B : T l} : tconv (cd A) (cd B) -> eps A -> eps B :=
    fun p a => cdc (@convelim (lsuc l) l (t l) (cd A) (fun B _ => dc B) (cdc_exp a) _ p).  
