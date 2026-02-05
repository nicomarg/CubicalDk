require open ctt.Translation.Context;
require open ctt.Translation;
require open ctt.Var.Context;

constant symbol TPush
  (Γ : TContext) (l : Sort) (A : Typ) (dA : der_type (τ_Γ Γ) A l)
  : eps (τ_T Γ dA) → TContext;

// Translation of context
rule τ_Γ (TPush $t $s $A _ _) ↪ Push $A $s (τ_Γ $t);

rule τ_dΓ (TPush $Γ _ _ $dA _) ↪ pushΓ $dA (τ_dΓ $Γ);

symbol tgetS (id : DBId) (Γ : TContext) : Sort ≔ getS (τ_Γ Γ) id;
symbol tgetA (id : DBId) (Γ : TContext) : Typ ≔ get (τ_Γ Γ) id;
symbol tgetΓ : DBId → TContext → TContext;

rule tgetΓ db0 (TPush $t _ _ _ _) ↪ $t
with tgetΓ (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetΓ $id $t
// Simple commutation
with τ_Γ (tgetΓ $id $Γ) ↪ getΓ (τ_Γ $Γ) $id;

symbol tgetD (id : DBId) (Γ : TContext) : der_type (τ_Γ (tgetΓ id Γ)) (tgetA id Γ) (tgetS id Γ);
rule tgetD db0 (TPush _ _ _ $d _) ↪ $d
with tgetD (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetD $id $t;

// Another commutation
rule tgetD $id $Γ ↪ der_getΓ $id (τ_dΓ $Γ);

require open ctt.Var.Shift;
require open ctt.Lemmas.Derivations;
symbol tgetT (id : DBId) (Γ : TContext) : T (τ_lev (tgetS id Γ)) ≔
  @τ_T (tgetΓ id Γ) (tgetA id Γ) (tgetS id Γ) (tgetD id Γ);
symbol tgetTShift (id : DBId) (Γ : TContext) : T (τ_lev (tgetS id Γ)) ≔
  @τ_T Γ (shiftgetΓ (τ_Γ Γ) id) (tgetS id Γ) (der_type_shift id (τ_dΓ Γ) (tgetD id Γ));

symbol tget (id : DBId) (Γ : TContext) : eps (tgetT id Γ);
rule tget db0 (TPush _ _ _ _ $a) ↪ $a
with tget (dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t;

symbol τ_shift0T_eq (Γ : TContext) [s s' : Sort] [T A : Typ]
                    (dT : der_type (τ_Γ Γ) T s)
                    (dA : der_type (τ_Γ Γ) A s')
                    (a : eps (τ_T Γ dA)) :
  tconvtype
      (τ_T Γ dT)
      (τ_T (TPush Γ s' A dA a) (der_type_shift0 dA (τ_dΓ Γ) dT));
symbol τ_shift0_eq (Γ : TContext) [s s' : Sort] [t : Term] [T A : Typ]
                   (dΓ : der_context (τ_Γ Γ))
                   (dt : der (τ_Γ Γ) t T s)
                   (dA : der_type (τ_Γ Γ) A s')
                   (a : eps (τ_T Γ dA)) :
  tH (τ Γ dt)
     (τ (TPush Γ s' A dA a) (der_shift0 dA dΓ dt));
symbol τ_shift0T (Γ : TContext) [s s' : Sort] [T A : Typ]
                    (dT : der_type (τ_Γ Γ) T s)
                    (dA : der_type (τ_Γ Γ) A s')
                 (a : eps (τ_T Γ dA)) ≔
  convtransp (τ_shift0T_eq Γ dT dA a);
symbol τ_shift0T' (Γ : TContext) [s s' : Sort] [T A : Typ]
                (dT : der_type (τ_Γ Γ) T s)
                (dA : der_type (τ_Γ Γ) A s')
                (a : eps (τ_T Γ dA)) ≔
  convtransp (xsymmetry (τ_shift0T_eq Γ dT dA a));

symbol tgetShift (id : DBId) (Γ : TContext) : eps (tgetTShift id Γ);
rule tgetShift db0 (TPush $Γ $s $A $dA $a)
     ↪ @τ_shift0T $Γ $s $s $A $A
          $dA $dA $a $a
with tgetShift (dbsucc $id) (TPush $Γ $s $A $dA $a)
  ↪ @τ_shift0T $Γ (tgetS $id $Γ) $s (shiftgetΓ (τ_Γ $Γ) $id) $A
        (der_type_shift $id (τ_dΓ $Γ) (tgetD $id $Γ))
        $dA $a (tgetShift $id $Γ);

symbol tgetShift_eq (id : DBId) (Γ : TContext) [s : Sort] [A : Typ] (dA : der_type (τ_Γ Γ) A s) (a : eps (τ_T Γ dA)) :
  tH (tgetShift id Γ) (tgetShift (dbsucc id) (TPush Γ s A dA a)) ≔
  heq_of_transport (tgetShift id Γ) (τ_shift0T_eq Γ (der_type_shift id (τ_dΓ Γ) (tgetD id Γ)) dA a);

// rule tgetShift_eq db0 (TPush $Γ _ _ $dA $a) ↪ heq_of_transport ($a) (τ_shift0T_eq $Γ $dA $dA $a)
// with tgetShift_eq (dbsucc $id) (TPush $Γ _ _ $dA $a) ↪
//      heq_trans (tgetShift_eq $id $Γ) (heq_of_transport (tgetShift $id $Γ) (τ_shift0T_eq $Γ (der_type_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) $dA $a));

// Packed Context
require open ctt.Lemmas.Irrel;
constant symbol PCPush
  [s : Sort] [A1 A2 : Typ] (P : PContext)
  (dA1 : der_type (τ_Γ (projΓ1 P)) A1 s)
  (dA2 : der_type (τ_Γ (projΓ2 P)) A2 s)
  [a1 : eps (τ_T (projΓ1 P) dA1)] [a2 : eps (τ_T (projΓ2 P) dA2)]
  : tH a1 a2 → PContext;

// Necessary to keep confluence of pgetS
rule getS (τ_Γ (projΓ2 $P)) ↪ getS (τ_Γ (projΓ1 $P));

// Implementation of projΓ*
rule projΓ1 (@PCPush $s $A1 _ $P $dA1 _ $a1 _ _) ↪ TPush (projΓ1 $P) $s $A1 $dA1 $a1
with projΓ2 (@PCPush $s _ $A2 $P _ $dA2 _ $a2 _) ↪ TPush (projΓ2 $P) $s $A2 $dA2 $a2;

symbol pgetS : DBId → PContext → Sort;
rule pgetS $id $P ↪ tgetS $id (projΓ1 $P)
with pgetS $id $P ↪ tgetS $id (projΓ2 $P);
symbol pgetA1 : DBId → PContext → Typ;
symbol pgetA2 : DBId → PContext → Typ;
rule pgetA1 $id $P ↪ tgetA $id (projΓ1 $P)
with pgetA2 $id $P ↪ tgetA $id (projΓ2 $P);
symbol pgetΓ1 : DBId → PContext → TContext;
symbol pgetΓ2  : DBId → PContext → TContext;
rule pgetΓ1 $id $P ↪ tgetΓ $id (projΓ1 $P)
with pgetΓ2 $id $P ↪ tgetΓ $id (projΓ2 $P);

symbol pgetD1 (id : DBId) (HC : PContext)
     : der_type (τ_Γ (pgetΓ1 id HC)) (pgetA1 id HC) (pgetS id HC);
symbol pgetD2 (id : DBId) (HC : PContext)
              : der_type (τ_Γ (pgetΓ2 id HC)) (pgetA2 id HC) (pgetS id HC);
rule pgetD1 $id $P ↪ tgetD $id (projΓ1 $P)
with pgetD2 $id $P ↪ tgetD $id (projΓ2 $P);

symbol pget1 (id : DBId) (HC : PContext) : eps (τ_T (pgetΓ1 id HC) (pgetD1 id HC));
symbol pget2  (id : DBId) (HC : PContext) : eps (τ_T (pgetΓ2 id HC) (pgetD2 id HC));
rule pget1 $id $P ↪ tget $id (projΓ1 $P)
with pget2 $id $P ↪ tget $id (projΓ2 $P);

symbol pgetTShift1 (id : DBId) (HC : PContext) : T (τ_lev (pgetS id HC));
symbol pgetTShift2 (id : DBId) (HC : PContext) : T (τ_lev (pgetS id HC));
rule pgetTShift1 $id $P ↪ tgetTShift $id (projΓ1 $P)
with pgetTShift2 $id $P ↪ tgetTShift $id (projΓ2 $P);

symbol pgetShift1 (id : DBId) (HC : PContext) : eps (pgetTShift1 id HC);
symbol pgetShift2 (id : DBId) (HC : PContext) : eps (pgetTShift2 id HC);
rule pgetShift1 $id $P ↪ tgetShift $id (projΓ1 $P)
with pgetShift2 $id $P ↪ tgetShift $id (projΓ2 $P);

symbol pgetH  (id : DBId) (HC : PContext) : tH (pget1 id HC) (pget2 id HC);
rule pgetH db0 (PCPush _ _ _ $h) ↪ $h
with pgetH (dbsucc $id) (PCPush $P _ _ _) ↪ pgetH $id $P
with pgetH $id (PBase $Γ) ↪ heq_refl (tget $id $Γ);

symbol pgetHShift (id : DBId) (HC : PContext) : tH (pgetShift1 id HC) (pgetShift2 id HC);
rule pgetHShift db0 (@PCPush $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 $h)
   ↪ heq_conj $h
        (@τ_shift0T_eq (projΓ1 $P) $s $s $A1 $A1 $dA1 $dA1 $a1)
        (@τ_shift0T_eq (projΓ2 $P) $s $s $A2 $A2 $dA2 $dA2 $a2)
with pgetHShift (dbsucc $id) (@PCPush $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 _)
   ↪ heq_conj (pgetHShift $id $P)
        (@τ_shift0T_eq (projΓ1 $P) (pgetS $id $P) $s (tshiftΓ (τ_Γ (projΓ1 $P)) $id (pgetA1 $id $P)) $A1
            (der_type_shift $id (τ_dΓ (projΓ1 $P)) (pgetD1 $id $P))
            $dA1 $a1)
        (@τ_shift0T_eq (projΓ2 $P) (pgetS $id $P) $s (tshiftΓ (τ_Γ (projΓ2 $P)) $id (pgetA2 $id $P)) $A2
            (der_type_shift $id (τ_dΓ (projΓ2 $P)) (pgetD2 $id $P))
            $dA2 $a2)
with pgetHShift $id (PBase $Γ) ↪ heq_refl (tgetShift $id $Γ);
