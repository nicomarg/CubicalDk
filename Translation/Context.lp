require open ctt.Translation;
require open ctt.Context;
// require open ctt.Contexts.Typing;
// require open ctt.Contexts.Shift;
// require open ctt.Lemmas.Derivations;
// require open ctt.Univ.Subst;

// Translation context constructors
constant symbol TEmpty : TContext;
// constant symbol TPush
//   (Γ : TContext) (l : Sort) (A : Typ) (dA : der_type (τ_Γ Γ) A l)
//   : eps (τ_T Γ dA) → TContext;
// constant symbol TPushI (Γ : TContext) : tI → TContext;
// constant symbol TPushF (Γ : TContext) (f : FTerm) (df : der_F (τ_Γ Γ) f) : tisOne (τ_F Γ df) → TContext;

// Translation of context
rule τ_Γ TEmpty ↪ Empty;
// with τ_Γ (TPush $t $s $A _ _) ↪ Push $A $s (τ_Γ $t)
// with τ_Γ (TPushI $t _) ↪ PushI (τ_Γ $t)
// with τ_Γ (TPushF $t $f _ _) ↪ PushF $f (τ_Γ $t);

rule τ_dΓ TEmpty ↪ der_context_empty;
// rule τ_dΓ (TPush $Γ _ _ $dA _) ↪ pushΓ $dA (τ_dΓ $Γ)
// with τ_dΓ (TPushI $Γ _) ↪ pushΓI (τ_dΓ $Γ)
// with τ_dΓ (TPushF $Γ _ $df _) ↪ pushΓF $df (τ_dΓ $Γ);

// symbol tgetS (id : DBId) (Γ : TContext) : Sort ≔ getS (τ_Γ Γ) id;
// symbol tgetA (id : DBId) (Γ : TContext) : Term ≔ get (τ_Γ Γ) id;
// symbol tgetΓ : DBId → TContext → TContext;
// symbol tIgetΓ : DBId → TContext → TContext;

// rule tgetΓ db0 (TPush $t _ _ _ _) ↪ $t
// with tgetΓ (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetΓ $id $t
// with tgetΓ $id (TPushI $t _) ↪ tgetΓ $id $t
// with tgetΓ $id (TPushF $t _ _ _) ↪ tgetΓ $id $t
// Simple commutation
// with τ_Γ (tgetΓ $id $Γ) ↪ getΓ (τ_Γ $Γ) $id;
// rule tIgetΓ $id (TPush $t _ _ _ _) ↪ tIgetΓ $id $t
// with tIgetΓ db0 (TPushI $t _) ↪ $t
// with tIgetΓ (dbsucc $id) (TPushI $t _) ↪ tgetΓ $id $t
// with tIgetΓ $id (TPushF $t _ _ _) ↪ tIgetΓ $id $t
// with τ_Γ (tIgetΓ $id $Γ) ↪ IgetΓ (τ_Γ $Γ) $id;

// symbol tgetD (id : DBId) (Γ : TContext) : der (τ_Γ (tgetΓ id Γ)) (tgetA id Γ) (tuniv (tgetS id Γ)) (tlsuc (tgetS id Γ));
// rule tgetD db0 (TPush _ _ _ $d _) ↪ $d
// with tgetD (dbsucc $id) (TPush $t _ _ _ _) ↪ tgetD $id $t
// with tgetD $id (TPushI $t _) ↪ tgetD $id $t
// with tgetD $id (TPushF $t _ _ _) ↪ tgetD $id $t;

// symbol tgetT (id : DBId) (Γ : TContext) : T (τ_lev (tgetS id Γ)) ≔
//   @τ_T (tgetΓ id Γ) (tgetA id Γ) (tgetS id Γ) (tgetD id Γ);
// symbol tgetTShift (id : DBId) (Γ : TContext) : T (τ_lev (tgetS id Γ)) ≔
//   @τ_T Γ (shiftgetΓ (τ_Γ Γ) id) (tgetS id Γ) (der_shift id (τ_dΓ Γ) (tgetD id Γ));

// symbol tget (id : DBId) (Γ : TContext) : eps (tgetT id Γ);
// rule tget db0 (TPush _ _ _ _ $a) ↪ $a
// with tget (dbsucc $id) (TPush $t _ _ _ _) ↪ tget $id $t
// with tget $id (TPushI $t _) ↪ tget $id $t
// with tget $id (TPushF $t _ _ _) ↪ tget $id $t;
// symbol tIget (id : DBId) (Γ : TContext) : tI;
// rule tIget $id (TPush $t _ _ _ _) ↪ tIget $id $t
// with tIget db0 (TPushI _ $t) ↪ $t
// with tIget (dbsucc $id) (TPushI $t _) ↪ tIget $id $t
// with tIget $id (TPushF $t _ _ _) ↪ tIget $id $t;

// require open ctt.Lemmas.Translation;
// symbol tgetShift (id : DBId) (Γ : TContext) : eps (tgetTShift id Γ);
// rule tgetShift db0 (TPush $Γ $s $A $dA $a)
//      ↪ @τ_shift0T $Γ $s $s $A $A
//           $dA $dA $a $a
// with tgetShift (dbsucc $id) (TPush $Γ $s $A $dA $a)
//   ↪ @τ_shift0T $Γ (tgetS $id $Γ) $s (shiftgetΓ (τ_Γ $Γ) $id) $A
//         (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ))
//         $dA $a (tgetShift $id $Γ)
// with tgetShift $id (TPushI $Γ $i) ↪
//   τ_Ishift0T $Γ (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) $i (tgetShift $id $Γ)
// with tgetShift $id (TPushF $Γ _ $df $one) ↪
//   τ_Fshift0T $Γ (der_shift $id (τ_dΓ $Γ) (tgetD $id $Γ)) $df $one (tgetShift $id $Γ);

// Packed Context
// constant symbol PContext : TContext → TYPE;
// symbol projΓ1 [Γ : TContext] : PContext Γ → TContext;
// symbol projΓ2 [Γ : TContext] : PContext Γ → TContext;
// constant symbol PCEmpty (Γ : TContext) : PContext Γ;
// constant symbol PCPush
//   [Γ : TContext] [s : Sort] [A1 A2 : Term] (P : PContext Γ)
//   (dA1 : der (τ_Γ (projΓ1 P)) A1 (tuniv s) (tlsuc s))
//   (dA2 : der (τ_Γ (projΓ2 P)) A2 (tuniv s) (tlsuc s))
//   [a1 : eps (τ_T (projΓ1 P) dA1)] [a2 : eps (τ_T (projΓ2 P) dA2)]
//   : tH a1 a2 → PContext Γ;
// constant symbol PCPushI [Γ : TContext] (P : PContext Γ)
//                         [i1 i2 : tI] : xtEq i1 i2 → PContext Γ;
// constant symbol PCPushF
//   [Γ : TContext] [f1 f2 : FTerm] (P : PContext Γ)
//   (df1 : der_F (τ_Γ (projΓ1 P)) f1)
//   (df2 : der_F (τ_Γ (projΓ2 P)) f2)
//   (one1 : tisOne (τ_F (projΓ1 P) df1)) (one2 : tisOne (τ_F (projΓ2 P) df2))
//   : PContext Γ;

// Necessary to keep confluence of pgetS
// rule getS (τ_Γ (projΓ2 $P)) ↪ getS (τ_Γ (projΓ1 $P));

// Implementation of projΓ*
// rule projΓ1 (PCEmpty $Γ) ↪ $Γ
// with projΓ2 (PCEmpty $Γ) ↪ $Γ;
// with projΓ1 (@PCPush _ $s $A1 _ $P $dA1 _ $a1 _ _) ↪ TPush (projΓ1 $P) $s $A1 $dA1 $a1
// with projΓ1 (@PCPushI _ $P $i1 _ _) ↪ TPushI (projΓ1 $P) $i1
// with projΓ1 (@PCPushF _ $f1 _ $P $df1 _ $one1 _) ↪ TPushF (projΓ1 $P) $f1 $df1 $one1
// with projΓ2 (@PCPush _ $s _ $A2 $P _ $dA2 _ $a2 _) ↪ TPush (projΓ2 $P) $s $A2 $dA2 $a2
// with projΓ2 (@PCPushI _ $P _ $i2 _) ↪ TPushI (projΓ2 $P) $i2
// with projΓ2 (@PCPushF _ _ $f2 $P _ $df2 _ $one2) ↪ TPushF (projΓ2 $P) $f2 $df2 $one2;

// symbol pgetS [Γ : TContext] : DBId → PContext Γ → Sort;
// rule pgetS $id $P ↪ tgetS $id (projΓ1 $P)
// with pgetS $id $P ↪ tgetS $id (projΓ2 $P);
// symbol pgetA1 [Γ : TContext] : DBId → PContext Γ → Term;
// symbol pgetA2 [Γ : TContext] : DBId → PContext Γ → Term;
// rule pgetA1 $id $P ↪ tgetA $id (projΓ1 $P)
// with pgetA2 $id $P ↪ tgetA $id (projΓ2 $P);
// symbol pgetΓ1 [Γ : TContext] : DBId → PContext Γ → TContext;
// symbol pgetΓ2 [Γ : TContext] : DBId → PContext Γ → TContext;
// rule pgetΓ1 $id $P ↪ tgetΓ $id (projΓ1 $P)
// with pgetΓ2 $id $P ↪ tgetΓ $id (projΓ2 $P);

// symbol pgetD1 [Γ : TContext] (id : DBId) (HC : PContext Γ)
//               : der (τ_Γ (pgetΓ1 id HC)) (pgetA1 id HC) (tuniv (pgetS id HC)) (tlsuc (pgetS id HC));
// symbol pgetD2 [Γ : TContext] (id : DBId) (HC : PContext Γ)
//               : der (τ_Γ (pgetΓ2 id HC)) (pgetA2 id HC) (tuniv (pgetS id HC)) (tlsuc (pgetS id HC));
// rule pgetD1 $id $P ↪ tgetD $id (projΓ1 $P)
// with pgetD2 $id $P ↪ tgetD $id (projΓ2 $P);

// symbol pget1 [Γ : TContext] (id : DBId) (HC : PContext Γ) : eps (τ (pgetΓ1 id HC) (pgetD1 id HC));
// symbol pget2 [Γ : TContext] (id : DBId) (HC : PContext Γ) : eps (τ (pgetΓ2 id HC) (pgetD2 id HC));
// rule pget1 $id $P ↪ tget $id (projΓ1 $P)
// with pget2 $id $P ↪ tget $id (projΓ2 $P);

// symbol pgetTShift1 [Γ : TContext] (id : DBId) (HC : PContext Γ) : T (τ_lev (pgetS id HC));
// symbol pgetTShift2 [Γ : TContext] (id : DBId) (HC : PContext Γ) : T (τ_lev (pgetS id HC));
// rule pgetTShift1 $id $P ↪ tgetTShift $id (projΓ1 $P)
// with pgetTShift2 $id $P ↪ tgetTShift $id (projΓ2 $P);

// symbol pgetShift1 [Γ : TContext] (id : DBId) (HC : PContext Γ) : eps (pgetTShift1 id HC);
// symbol pgetShift2 [Γ : TContext] (id : DBId) (HC : PContext Γ) : eps (pgetTShift2 id HC);
// rule pgetShift1 $id $P ↪ tgetShift $id (projΓ1 $P)
// with pgetShift2 $id $P ↪ tgetShift $id (projΓ2 $P);

// symbol pgetH [Γ : TContext] (id : DBId) (HC : PContext Γ) : tH (pget1 id HC) (pget2 id HC);
// rule pgetH db0 (PCPush _ _ _ $h) ↪ $h
// with pgetH (dbsucc $id) (PCPush $P _ _ _) ↪ pgetH $id $P
// with pgetH $id (PCEmpty $Γ) ↪ heq_refl (tget $id $Γ)
// with pgetH $id (PCPushI $P _) ↪ pgetH $id $P
// with pgetH $id (PCPushF $P _ _ _ _) ↪ pgetH $id $P;

// symbol pgetHShift [Γ : TContext] (id : DBId) (HC : PContext Γ) : tH (pgetShift1 id HC) (pgetShift2 id HC);
// rule pgetHShift db0 (@PCPush _ $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 $h)
//    ↪ heq_conj $h
//         (@τ_shift0T_eq (projΓ1 $P) $s $s $A1 $A1 $dA1 $dA1 $a1)
//         (@τ_shift0T_eq (projΓ2 $P) $s $s $A2 $A2 $dA2 $dA2 $a2)
// with pgetHShift (dbsucc $id) (@PCPush _ $s $A1 $A2 $P $dA1 $dA2 $a1 $a2 _)
//    ↪ heq_conj (pgetHShift $id $P)
//         (@τ_shift0T_eq (projΓ1 $P) (pgetS $id $P) $s (shiftΓ (τ_Γ (projΓ1 $P)) $id (pgetA1 $id $P)) $A1
//             (der_shift $id (τ_dΓ (projΓ1 $P)) (pgetD1 $id $P))
//             $dA1 $a1)
//         (@τ_shift0T_eq (projΓ2 $P) (pgetS $id $P) $s (shiftΓ (τ_Γ (projΓ2 $P)) $id (pgetA2 $id $P)) $A2
//             (der_shift $id (τ_dΓ (projΓ2 $P)) (pgetD2 $id $P))
//             $dA2 $a2)
// with pgetHShift $id (PCEmpty $Γ) ↪ heq_refl (tgetShift $id $Γ)
// with pgetHShift $id (@PCPushI _ $P $i1 $i2 _) ↪
//   heq_conj (pgetHShift $id $P)
//            (τ_Ishift0T_eq (projΓ1 $P) (der_shift $id (τ_dΓ (projΓ1 $P)) (pgetD1 $id $P)) $i1)
//            (τ_Ishift0T_eq (projΓ2 $P) (der_shift $id (τ_dΓ (projΓ2 $P)) (pgetD2 $id $P)) $i2)
// with pgetHShift $id (PCPushF $P $df1 $df2 $done1 $done2) ↪
//   heq_conj (pgetHShift $id $P)
//            (τ_Fshift0T_eq (projΓ1 $P) (der_shift $id (τ_dΓ (projΓ1 $P)) (pgetD1 $id $P)) $df1 $done1)
//            (τ_Fshift0T_eq (projΓ2 $P) (der_shift $id (τ_dΓ (projΓ2 $P)) (pgetD2 $id $P)) $df2 $done2);
