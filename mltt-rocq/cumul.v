Require Import conv syntax.

(** Syntax *)
Parameter Ssuc : Sort -> Sort.

(** Typing rules *)
Parameter der_type_lift : forall {Γ T s},
  der_type Γ T s -> der_type Γ T (Ssuc s).
Parameter der_lift : forall {Γ M T s},
  der Γ M T s -> der Γ M T (Ssuc s).

(** Lemmas *)
Parameter der_sort_lift : forall {Γ M T s} (dM : der Γ M T s),
  der_sort (der_lift dM) = der_type_lift (der_sort dM).


(** Translation *)
Require Import trad.

Parameter τ_s_S : forall {s}, τ_s (Ssuc s) = ctt.lsuc (τ_s s).

(** Types *)
Parameter τ_T_lift : forall Γ {T s} (d:der_type _ T s),
    τ_T Γ T (der_type_lift d) =
      sort_fold τ_s_S (ctt.lUp (τ_T Γ T d)).

(** Terms *)

Lemma τ_lift0_def : forall Γ {M T s} (dT:der_type (τ_Γ Γ) T s) (d:der (τ_Γ Γ) M T s),
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

