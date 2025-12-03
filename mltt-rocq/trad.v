Require ctt.
Require Import conv syntax.

(*// Translation*)
Parameter τ_s : Sort -> ctt.Lev.

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

(** Translation definition *)

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

Lemma τ_eq_conv_rhs Γ {M N T U s} (dU:der_type _ U s) (dTU:der_eqT (τ_Γ Γ) T U s)
         (dMU : der _ M U s) (dNU:der _ N U s) (dMN:der_eq (τ_Γ Γ) M N T s):
    conv (τ_T Γ U dU) (τ Γ M dU dMU) (τ Γ N dU dNU).
Proof.
pose (dMU' := der_conv dTU (der_eq_left _ dMN)).
pose (dNU' := der_conv dTU (der_eq_right _ dMN)).
apply @ctt.convtrans with (τ Γ M dU dMU'); [apply τ_irrel|].
apply @ctt.convtrans with (τ Γ N dU dNU'); [|apply ctt.convsym;apply τ_irrel].
subst dMU' dNU'.
do 2 rewrite τ_conv_def.
unfold τ_conv_rhs.
set (dT := der_eqT_left _ dTU).
apply ctransport.
apply τ_eq with (1:=dMN).
Defined.

Parameter τ_eq_conv_def :
  forall Γ M N T U s (dU:der_type _ U s) (dTU:der_eqT _ T U s)
         (d1 : der _ M U s) (d2:der _ N U s) (dMN:der_eq _ M N T s), 
    τ_eq Γ dU d1 d2 (der_eq_conv dTU dMN) =
      τ_eq_conv_rhs Γ dU dTU d1 d2 dMN.







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

