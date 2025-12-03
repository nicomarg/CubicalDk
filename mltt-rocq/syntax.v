(** Syntactic classes *)
Parameter Sort : Type.

Parameter Context : Type.
Parameter Typ : Type.

Parameter Term : Type.


(** Judgments*)
Parameter der_context : Context -> Type.
Parameter der_type : Context -> Typ -> Sort -> Type. (* does not subsumes der_context*)
Parameter der_eqT : Context -> Typ -> Typ -> Sort -> Type.
Parameter der : Context -> Term -> Typ -> Sort -> Type.
Parameter der_eq : Context -> Term -> Term -> Typ -> Sort -> Type.

(* Structural rules *)
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



(** Lemmas *)
Parameter der_eqT_left : forall Γ {T U s}, der_eqT Γ T U s -> der_type Γ T s.
Parameter der_eqT_right : forall Γ {T U s}, der_eqT Γ T U s -> der_type Γ U s.
Parameter der_eq_left : forall Γ {x y T s}, der_eq Γ x y T s -> der Γ x T s.
Parameter der_eq_right : forall Γ {x y T s}, der_eq Γ x y T s -> der Γ y T s.
Parameter der_sort : forall {Γ M T s}, der Γ M T s -> der_type Γ T s.

(** Proof of lemmas for structiral rules *)
Parameter der_eqT_left_refl : forall {Γ T s} (d:der_type Γ T s),
  der_eqT_left Γ (der_eqT_refl d) = d.
Parameter der_eqT_right_refl : forall {Γ T s} (d:der_type Γ T s),
  der_eqT_right Γ (der_eqT_refl d) = d.
Parameter der_eqT_left_sym : forall {Γ T U s} (d:der_eqT Γ T U s),
  der_eqT_left Γ (der_eqT_sym d) = der_eqT_right Γ d.
Parameter der_eqT_right_sym : forall {Γ T U s} (d:der_eqT Γ T U s),
  der_eqT_right Γ (der_eqT_sym d) = der_eqT_left Γ d.
Parameter der_eqT_left_trans : forall {Γ T U V s}
  (d1:der_eqT Γ T U s) (d2:der_eqT Γ U V s),
  der_eqT_left Γ (der_eqT_trans d1 d2) = der_eqT_left Γ d1.
Parameter der_eqT_right_trans : forall {Γ T U V s}
  (d1:der_eqT Γ T U s) (d2:der_eqT Γ U V s),
  der_eqT_right Γ (der_eqT_trans d1 d2) = der_eqT_right Γ d2.

Parameter der_eq_left_refl : forall {Γ M T s} (d:der Γ M T s),
  der_eq_left Γ (der_eq_refl d) = d.
Parameter der_eq_right_refl : forall {Γ M T s} (d:der Γ M T s),
  der_eq_right Γ (der_eq_refl d) = d.
Parameter der_eq_left_sym : forall {Γ M N T s} (d:der_eq Γ M N T s),
  der_eq_left Γ (der_eq_sym d) = der_eq_right Γ d.
Parameter der_eq_right_sym : forall {Γ M N T s} (d:der_eq Γ M N T s),
  der_eq_right Γ (der_eq_sym d) = der_eq_left Γ d.
Parameter der_eq_left_trans : forall {Γ M N P T s}
  (d1:der_eq Γ M N T s) (d2:der_eq Γ N P T s),
  der_eq_left Γ (der_eq_trans d1 d2) = der_eq_left Γ d1.
Parameter der_eq_right_trans : forall {Γ M N P T s}
  (d1:der_eq Γ M N T s) (d2:der_eq Γ N P T s),
  der_eq_right Γ (der_eq_trans d1 d2) = der_eq_right Γ d2.
Parameter der_eq_left_conv : forall {Γ M N T U s}
  (dTU : der_eqT _ T U s) (dMN : der_eq _ M N T s),
  der_eq_left Γ (der_eq_conv dTU dMN) =
    der_conv dTU (der_eq_left _ dMN).
Parameter der_eq_right_conv : forall {Γ M N T U s}
  (dTU : der_eqT _ T U s) (dMN : der_eq _ M N T s),
  der_eq_right Γ (der_eq_conv dTU dMN) =
    der_conv dTU (der_eq_right _ dMN).

Parameter der_sort_conv : forall {Γ M T U s}
  (dTU : der_eqT Γ T U s) (dM : der Γ M T s),
  der_sort (der_conv dTU dM) = der_eqT_right _ dTU.
