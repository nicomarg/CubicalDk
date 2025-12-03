Require Import conv syntax.

(** Nat *)

(** Nat syntax *)
Parameter Nat : Sort -> Typ.
Parameter der_Nat : forall {Γ s}, der_type Γ (Nat s) s.

Parameter Zer : Term.
Parameter Suc : Term -> Term.
Parameter der_Zer : forall {Γ s}, der Γ Zer (Nat s) s.
Parameter der_Suc : forall {Γ s n}, der Γ n (Nat s) s -> der Γ (Suc n) (Nat s) s.

(** Lemmas *)
Parameter der_sort_Nat : forall {Γ s},
  der_sort (@der_Zer Γ s) = der_Nat.
Parameter der_sort_Succ : forall {Γ s n} {d:der Γ n (Nat s) s},
  der_sort (der_Suc d) = der_Nat.

(** Translation *)
Require Import trad.

Parameter τ_Nat : forall {Γ s},
  τ_T Γ (Nat s) der_Nat = ctt.Nat (τ_s s).

Parameter τ_Zer : forall {Γ s},
  τ Γ Zer der_Nat der_Zer = elt_fold (@τ_Nat _ s) ctt.zero.
Parameter τ_Suc : forall {Γ s n} (d:der _ n (Nat s) s),
  τ Γ (Suc n) der_Nat (der_Suc d) =
     elt_fold (@τ_Nat _ s) (ctt.S (elt_unf τ_Nat (τ Γ n der_Nat d))).
