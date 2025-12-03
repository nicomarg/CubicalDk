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

(*// Ast*)
Parameter Sort : Type.

Parameter Context : Type.
Parameter Typ : Type.


Parameter Term : Type.


(*// Judgments*)
Parameter der_context : Context -> Type.
Parameter der_type : Context -> Typ -> Sort -> Type. (* does not subsumes der_context*)
Parameter der_eqT : Context -> Typ -> Typ -> Sort -> Type.
Parameter der : Context -> Term -> Typ -> Sort -> Type.
Parameter der_eq : Context -> Term -> Term -> Typ -> Sort -> Type.

Parameter der_eqT_refl :
  forall {Γ T s}, der_type Γ T s -> der_eqT Γ T T s.
Parameter der_eqT_sym :
  forall {Γ T U s}, der_eqT Γ T U s -> der_eqT Γ U T s.
Parameter der_eqT_trans :
  forall {Γ T U V s}, der_eqT Γ T U s -> der_eqT Γ U V s -> der_eqT Γ T V s.
Parameter der_eq_refl :
  forall {Γ M T s}, der Γ M T s -> der_eq Γ M M T s.
Parameter der_eq_sym :
  forall {Γ M N T s}, der_eq Γ M N T s -> der_eq Γ N M T s.
Parameter der_eq_trans :
  forall {Γ M N P T s}, der_eq Γ M N T s -> der_eq Γ N P T s -> der_eq Γ M P T s.

Parameter Ssuc : Sort -> Sort.

Parameter der_type_lift : forall {Γ T s},
  der_type Γ T s -> der_type Γ T (Ssuc s).
Parameter der_lift : forall {Γ M T s},
  der Γ M T s -> der Γ M T (Ssuc s).

Parameter der_conv :
 forall {Γ M T U s},
  der_eqT Γ T U s ->
  der Γ M T s ->
  der Γ M U s.
Parameter der_eq_conv :
  forall {Γ M N T U s},
  der_eqT Γ T U s ->
  der_eq Γ M N T s ->
  der_eq Γ M N U s.



(*// Lemmas*)
Parameter der_eqT_left : forall Γ {T U s}, der_eqT Γ T U s -> der_type Γ T s.
Parameter der_eqT_right : forall Γ {T U s}, der_eqT Γ T U s -> der_type Γ U s.
Parameter der_eq_left : forall Γ {x y T s}, der_eq Γ x y T s -> der Γ x T s.
Parameter der_eq_right : forall Γ {x y T s}, der_eq Γ x y T s -> der Γ y T s.

Parameter der_eqT_left_refl : forall Γ {T s} (d:der_type Γ T s),
  der_eqT_left Γ (der_eqT_refl d) = d.
Parameter der_eqT_right_refl : forall Γ {T s} (d:der_type Γ T s),
  der_eqT_right Γ (der_eqT_refl d) = d.
Parameter der_eqT_left_sym : forall Γ {T U s} (d:der_eqT Γ T U s),
  der_eqT_left Γ (der_eqT_sym d) = der_eqT_right Γ d.
Parameter der_eqT_right_sym : forall Γ {T U s} (d:der_eqT Γ T U s),
  der_eqT_right Γ (der_eqT_sym d) = der_eqT_left Γ d.
Parameter der_eqT_left_trans : forall Γ {T U V s}
  (d1:der_eqT Γ T U s) (d2:der_eqT Γ U V s),
  der_eqT_left Γ (der_eqT_trans d1 d2) = der_eqT_left Γ d1.
Parameter der_eqT_right_trans : forall Γ {T U V s}
  (d1:der_eqT Γ T U s) (d2:der_eqT Γ U V s),
  der_eqT_right Γ (der_eqT_trans d1 d2) = der_eqT_right Γ d2.

Parameter der_eq_left_refl : forall Γ {M T s} (d:der Γ M T s),
  der_eq_left Γ (der_eq_refl d) = d.
Parameter der_eq_right_refl : forall Γ {M T s} (d:der Γ M T s),
  der_eq_right Γ (der_eq_refl d) = d.
Parameter der_eq_left_sym : forall Γ {M N T s} (d:der_eq Γ M N T s),
  der_eq_left Γ (der_eq_sym d) = der_eq_right Γ d.
Parameter der_eq_right_sym : forall Γ {M N T s} (d:der_eq Γ M N T s),
  der_eq_right Γ (der_eq_sym d) = der_eq_left Γ d.
Parameter der_eq_left_trans : forall Γ {M N P T s}
  (d1:der_eq Γ M N T s) (d2:der_eq Γ N P T s),
  der_eq_left Γ (der_eq_trans d1 d2) = der_eq_left Γ d1.
Parameter der_eq_right_trans : forall Γ {M N P T s}
  (d1:der_eq Γ M N T s) (d2:der_eq Γ N P T s),
  der_eq_right Γ (der_eq_trans d1 d2) = der_eq_right Γ d2.

Parameter der_sort : forall {Γ M T s}, der Γ M T s -> der_type Γ T s.

(*// Translation*)
Parameter τ_s : Sort -> ctt.Lev.
Parameter τ_s_S : forall {s}, τ_s (Ssuc s) = ctt.lsuc (τ_s s).

Parameter TContext : Type.
Parameter τ_Γ : TContext -> Context.
Parameter τ_dΓ : forall (Γ : TContext), der_context (τ_Γ Γ).

Parameter τ_T : forall (Γ : TContext) (T : Typ){s:Sort},
  der_type (τ_Γ Γ) T s -> ctt.T (τ_s s).

Parameter τ_eqT :
  forall (Γ : TContext) {T1 T2 : Typ}{s:Sort}
         (d1 : der_type (τ_Γ Γ) T1 s) (d2 : der_type (τ_Γ Γ) T2 s),
    der_eqT (τ_Γ Γ) T1 T2 s ->
    convT (τ_T Γ T1 d1) (τ_T Γ T2 d2).

Parameter τ :
  forall (Γ : TContext) (M : Term){T : Typ}{s:Sort}
         (dT : der_type (τ_Γ Γ) T s),
    der (τ_Γ Γ) M T s -> ctt.eps (τ_T Γ T dT).

Parameter τ_eq :
  forall (Γ : TContext) {t1 t2 : Term}{T:Typ}{s:Sort}
         (dT : der_type (τ_Γ Γ) T s)
         (d1 : der (τ_Γ Γ) t1 T s) (d2 : der (τ_Γ Γ) t2 T s),
    der_eq (τ_Γ Γ) t1 t2 T s -> conv (τ_T Γ T dT) (τ Γ t1 dT d1) (τ Γ t2 dT d2).

(* Equivalence of der_eq and der_eqT *)


(* Lemma *)
(*Parameter τ_T_irrel_gen :
  forall Γ {T s1 s2} (d1:der_type _ T s1)(d2:der_type _ T s2),
    eps
    convT (τ_T Γ T d1) (τ_T Γ T d2).
*)
Parameter τ_T_irrel :
  forall Γ {T s} (d1 d2:der_type _ T s),
    convT (τ_T Γ T d1) (τ_T Γ T d2).
Parameter τ_T_irrel_refl :
  forall Γ {T s} (d :der_type _ T s),
    τ_T_irrel Γ d d = ctt.convrefl.

Parameter τ_irrel :
  forall Γ {M T s} (dT:der_type _ T s) (d1 d2 : der _ M T s),
    conv (τ_T Γ T dT) (τ Γ M dT d1) (τ Γ M dT d2).
Parameter τ_irrel_refl :
  forall Γ {M T s} (dT : der_type _ T s)(d:der _ M T s),
    τ_irrel Γ dT d d = ctt.convrefl.

Parameter τ_eqT_refl :
  forall Γ T s (d1 d2 dT : der_type _ T s),
    τ_eqT Γ d1 d2 (der_eqT_refl dT) = τ_T_irrel Γ d1 d2.

Parameter τ_eqT_sym :
  forall Γ T U s (dT : der_type _ T s) (dU : der_type _ U s)
         (dTU : der_eqT _ T U s),
    τ_eqT Γ dU dT (der_eqT_sym dTU) = ctt.convsym (τ_eqT Γ dT dU dTU).

Parameter τ_eqT_trans :
  forall Γ T U V s
         (dT : der_type _ T s) (dU : der_type _ U s) (dV : der_type _ V s)
         (dTU : der_eqT _ T U s)
         (dUV : der_eqT _ U V s),
    τ_eqT Γ dT dV (der_eqT_trans dTU dUV) =
      ctt.convtrans (τ_eqT Γ dT dU dTU) (τ_eqT Γ dU dV dUV).

Parameter τ_eq_refl :
  forall Γ M T s (dT : der_type _ T s) (d1 d2 dM : der _ M T s),
    τ_eq Γ dT d1 d2 (der_eq_refl dM) = τ_irrel Γ dT d1 d2.

Parameter τ_eq_sym :
  forall Γ M N T s
         (dT : der_type _ T s) (dM:der _ M T s) (dN : der _ N T s)
         (dMN : der_eq _ M N T s),
    τ_eq Γ dT dN dM (der_eq_sym dMN) = ctt.convsym (τ_eq Γ dT dM dN dMN).

Parameter τ_eq_trans :
  forall Γ M N P T s
         (dT : der_type _ T s)
         (dM : der _ M T s)(dN : der _ N T s)(dP : der _ P T s)
         (dMN : der_eq _ M N T s)
         (dNP : der_eq _ N P T s),
    τ_eq Γ dT dM dP (der_eq_trans dMN dNP) =
      ctt.convtrans (τ_eq Γ dT dM dN dMN) (τ_eq Γ dT dN dP dNP).

(*// transport*)

Parameter τ_T_lift : forall Γ {T s} (d:der_type _ T s),
    τ_T Γ T (der_type_lift d) =
      sort_fold τ_s_S (ctt.lUp (τ_T Γ T d)).

Lemma τ_lift0_def : forall Γ {M T s} (dT:der_type (τ_Γ Γ) T s) (d:der (τ_Γ Γ) M T s),
(*    let lhs := τ Γ M (der_type_lift dT) (der_lift d) in*)
    ctt.eps (τ_T Γ T (der_type_lift dT)).
intros.
pose (x := τ Γ M dT d).
rewrite τ_T_lift.
pose (e:=eq_sym (@τ_s_S s)).
unfold sort_fold, eq_rect_r.
fold e.
destruct e; simpl.
exact (tr_fold ctt.lUp_eps x).
Defined.

Parameter τ_lift0 : forall Γ {M T s} (dT:der_type _ T s) (d:der _ M T s),
    τ Γ M (der_type_lift dT) (der_lift d) =
      τ_lift0_def Γ dT d.


Lemma τ_lift_def : forall Γ {M T s} (dT:der_type (τ_Γ Γ) T (Ssuc s)) (d:der (τ_Γ Γ) M T s),
(*    let lhs := τ Γ M (der_type_lift dT) (der_lift d) in*)
    ctt.eps (τ_T Γ T dT).
intros.
pose (dT' := der_sort d).
apply transport with (1:=τ_T_irrel Γ (der_type_lift dT') dT).
apply τ_lift0_def with (1:=d).
Defined.


(*// first attempt: sorts must be the same*)
Definition τ_conv_rhs Γ {M T U s} (dU:der_type (τ_Γ Γ) U s)
  (dTU:der_eqT (τ_Γ Γ) T U s) (dM:der (τ_Γ Γ) M T s)
  : ctt.eps (τ_T Γ _ dU) :=
  let dT : der_type (τ_Γ Γ) T s := der_eqT_left _ dTU in
  let tM : ctt.eps (τ_T Γ _ dT) := τ Γ _ dT dM in
  let tEq : convT (τ_T Γ _ dT) (τ_T Γ _ dU) := τ_eqT Γ dT dU dTU in
  transport (*(τ_s s) (τ_T Γ dT) (τ_T Γ dU)*) tEq tM.

Parameter τ_conv_def :
  forall Γ M T U s (dU:der_type _ U s) (dTU:der_eqT _ T U s) (dM:der _ M T s), 
    τ Γ M dU (der_conv dTU dM) = τ_conv_rhs Γ dU dTU dM.

(* Lemma (refl case : τ_irrel) *)
Parameter τ_type_change :
  forall Γ M T U s
         (dT:der_type _ T s) (dU:der_type _ U s)
         (eTU : convT (τ_T Γ T dT) (τ_T Γ U dU))
         (dM1 : der _ M T s) (dM2 : der _ M U s),
    conv (τ_T Γ U dU) (τ Γ M dU dM2) (transport eTU (τ Γ M dT dM1)).

Lemma τ_eq_conv_rhs :
  forall Γ {M N T U s} (dU:der_type _ U s) (dTU:der_eqT (τ_Γ Γ) T U s)
         (d1 : der _ M U s) (d2:der _ N U s) (dMN:der_eq (τ_Γ Γ) M N T s), 
(*    let lhs := τ_eq Γ dU d1 d2 (der_eq_conv dTU dMN) in*)
    conv (τ_T Γ U dU) (τ Γ M dU d1) (τ Γ N dU d2).
intros.
assert (dT := der_eqT_left _ dTU).
specialize τ_eqT with (1:=dTU)(d1:=dT)(d2:=dU); intros eTU.
assert (dM := der_eq_left _ dMN).
assert (dN := der_eq_right _ dMN).
specialize τ_eq with (1:=dMN)(dT:=dT)(d1:=dM)(d2:=dN); intros eMN.
(*
specialize τ_conv_def with (dU:=dU)(dTU:=dTU)(dM:=dM); intro.
specialize τ_conv_def with (dU:=dU)(dTU:=dTU)(dM:=dN); intro.
*)
eapply ctransport with (e:=eTU) in eMN.
apply @ctt.convtrans with (transport eTU (τ Γ M dT dM)).
 apply τ_type_change; trivial.
apply @ctt.convtrans with (1:=eMN).
apply ctt.convsym.
 apply τ_type_change; trivial.
Defined.

Parameter τ_eq_conv_def :
  forall Γ M N T U s (dU:der_type _ U s) (dTU:der_eqT _ T U s)
         (d1 : der _ M U s) (d2:der _ N U s) (dMN:der_eq _ M N T s), 
    τ_eq Γ dU d1 d2 (der_eq_conv dTU dMN) =
      τ_eq_conv_rhs Γ dU dTU d1 d2 dMN.



(* Nat *)

Parameter Nat : Sort -> Typ.
Parameter der_Nat : forall {Γ s}, der_type Γ (Nat s) s.
Parameter τ_Nat : forall {Γ s},
  τ_T Γ (Nat s) der_Nat = ctt.Nat (τ_s s).

Parameter Zer : Term.
Parameter Suc : Term -> Term.
Parameter der_Zer : forall {Γ s}, der Γ Zer (Nat s) s.
Parameter der_Suc : forall {Γ s n}, der Γ n (Nat s) s -> der Γ (Suc n) (Nat s) s.
Parameter der_sort_Nat : forall {Γ s},
  der_sort (@der_Zer Γ s) = der_Nat.
Parameter der_sort_Succ : forall {Γ s n} {d:der Γ n (Nat s) s},
  der_sort (der_Suc d) = der_Nat.

Parameter τ_Zer : forall {Γ s},
  τ Γ Zer der_Nat der_Zer = elt_fold (@τ_Nat _ s) ctt.zero.
Parameter τ_Suc : forall {Γ s n} (d:der _ n (Nat s) s),
  τ Γ (Suc n) der_Nat (der_Suc d) =
     elt_fold (@τ_Nat _ s) (ctt.S (elt_unf τ_Nat (τ Γ n der_Nat d))).

(* Arrow type *)
Parameter Arr : Typ -> Typ -> Typ.
Parameter der_Arr : forall {Γ T U s}, der_type Γ T s -> der_type Γ U s -> der_type Γ (Arr T U) s.
Parameter der_eq_Arr : forall {Γ T T' U U' s}, der_eqT Γ T T' s -> der_eqT Γ U U' s -> der_eqT Γ (Arr T U) (Arr T' U') s.

(* inv lemma *)
Parameter der_Arr_inv_right : forall {Γ T U s},
  der_type Γ (Arr T U) s -> der_type Γ U s.

Parameter τ_Arr : forall {Γ T U s} dT dU,
  τ_T Γ (Arr T U) (der_Arr (s:=s) dT dU) = ctt.Pi (τ_T Γ T dT) (fun _ => τ_T Γ U dU).

Parameter App : Term -> Term -> Term.
Parameter der_App : forall {Γ M N T U s},
  der Γ M (Arr T U) s ->
  der Γ N T s ->
  der Γ (App M N) U s.

Parameter der_sort_App : forall {Γ M N T U s} {dM:der Γ M (Arr T U) s} {dN:der Γ N T s},
    der_sort (der_App dM dN) =
      der_Arr_inv_right (der_sort dM).

Parameter τ_App : forall {Γ M N T U s}{dM dN} {dU:der_type _ U s},
  τ Γ (App M N) dU (der_App dM dN) =
    let dT : der_type _ T s := der_sort dN in
    ctt.app (elt_unf (τ_Arr _ _) (τ Γ M (der_Arr dT dU) dM))
            (τ Γ N dT dN).

(*
Parameter Lam : Typ->(Term->Term)->Term.
Parameter der_Lam : forall {Γ M N T U s},
  der_type Γ T s ->
  (forall x, der Γ x A s -> der Γ (F x) T s ->
  der Γ (Lam T F) (Arr T U) s.
*)

