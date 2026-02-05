require open ctt.Var.TContext;
require open ctt.Lemmas.Derivations.Shifting;

constant symbol ShiftTContext : TContext → DBId → TYPE;
symbol tsc_to_sc [Γ : TContext] [id : DBId] : ShiftTContext Γ id → ShiftContext (τ_Γ Γ) id;
symbol tsc_to_tc [Γ : TContext] [id : DBId] : ShiftTContext Γ id → TContext;
symbol tsc_to_ctx [Γ : TContext] [id : DBId] : ShiftTContext Γ id → Context;
rule tsc_to_ctx $sc ↪ sc_to_ctx (tsc_to_sc $sc)
with τ_Γ (tsc_to_tc $sc) ↪ sc_to_ctx (tsc_to_sc $sc);
symbol tsc_to_stc [Γ : TContext] [id : DBId] [s : Sort] [A : Typ]
                  (dA : der_type (τ_Γ Γ) A s)
                  : eps (τ_T Γ dA) → ShiftTContext Γ id → TContext;
symbol tsc_to_sctx [Γ : TContext] [id : DBId] [s : Sort] [A : Typ]
                   : der_type (τ_Γ Γ) A s → ShiftTContext Γ id → Context;
rule tsc_to_sctx $dA $sc ↪ sc_to_sctx $dA (tsc_to_sc $sc)
with τ_Γ (tsc_to_stc $dA _ $sc) ↪ sc_to_sctx $dA (tsc_to_sc $sc);

constant symbol TSC0 (Γ : TContext) : der_context (τ_Γ Γ) → ShiftTContext Γ db0;
constant symbol TSCSucc [Γ : TContext] [s : Sort] [A : Typ] [id : DBId]
                        (sc : ShiftTContext Γ id) (dA : der_type (tsc_to_ctx sc) A s)
                        : eps (τ_T (tsc_to_tc sc) dA) → ShiftTContext Γ (dbsucc id);
rule tsc_to_sc (TSC0 _ $dΓ) ↪ SC0 $dΓ
with tsc_to_sc (TSCSucc $sc $dA _) ↪ SCSucc (tsc_to_sc $sc) $dA
with tsc_to_tc (TSC0 $Γ _) ↪ $Γ
with tsc_to_tc (TSCSucc $sc $dA $a) ↪ TPush (tsc_to_tc $sc) _ _ $dA $a;

symbol τ_shift_n [Γ : TContext] [s s' : Sort] [t : Term] [T A : Typ] (id : DBId)
                 (sc : ShiftTContext Γ id) (dt : der (tsc_to_ctx sc) t T s)
                 (dA : der_type (τ_Γ Γ) A s')
                 (a : eps (τ_T Γ dA)) :
  tH (τ (tsc_to_tc sc) dt)
     (τ (tsc_to_stc dA a sc) (der_shift_n id (tsc_to_sc sc) dA dt));
symbol τ_shiftT_n [Γ : TContext] [s s' : Sort] [T A : Typ] (id : DBId)
                  (sc : ShiftTContext Γ id) (dT : der_type (tsc_to_ctx sc) T s)
                  (dA : der_type (τ_Γ Γ) A s')
                  (a : eps (τ_T Γ dA)) :
  tconvtype (τ_T (tsc_to_tc sc) dT)
            (τ_T (tsc_to_stc dA a sc) (der_type_shift_n id (tsc_to_sc sc) dA dT));

rule tsc_to_stc $d $x (TSC0 $Γ _) ↪ TPush $Γ _ _ $d $x
with tsc_to_stc $d $x (TSCSucc $sc $dA $a) ↪
 TPush (tsc_to_stc $d $x $sc) _ _
       (der_type_shift_n _ (tsc_to_sc $sc) $d $dA)
       (convtransp (τ_shiftT_n _ $sc $dA $d $x) $a);

rule τ_shift0T_eq $Γ $dT $dA $a ↪ τ_shiftT_n db0 (TSC0 $Γ (τ_dΓ $Γ)) $dT $dA $a
with τ_shift0_eq $Γ $dΓ $dt $dA $a ↪ τ_shift_n db0 (TSC0 $Γ $dΓ) $dt $dA $a;

symbol Jτ (Γ : TContext) [s : Sort] [t u : Term] [T U : Typ] (e : TEq t u) (E : TyEq T U) (d : der (τ_Γ Γ) t T s) :
  tH (τ Γ (JtT e E d)) (τ Γ d);
rule Jτ _ (TRefl _) (TyRefl _) _ ↪ heq_refl _;
// symbol τ_leq [s s' : Sort] : LEq s s' → xtEq (τ_lev s) (τ_lev s');
// rule τ_leq (LRefl _) ↪ xrefl;
// symbol τ_lev_eq (Γ : TContext) [s s' : Sort] : LEq s s' → xtEq (τ_lev s) (τ_lev s');
// symbol Jlτ (Γ : TContext) [s s' : Sort] [t : Term] [T : Typ] (e : LEq s s') (d : der (τ_Γ Γ) t T s) :
//   tH (τ Γ (Jl e d)) (τ Γ d);
// rule Jτ _ (TRefl _) (TyRefl _) _ ↪ heq_refl _;

// rule τ_shift1T_eq $Γ $dT $dA $dB $a $b ↪ τ_shiftT_n db1 (TSCSucc (TSC0 $Γ (τ_dΓ $Γ)) $dA $a) $dT $dB $b;
// symbol τ_shift0T_eq (Γ : TContext) [s s' : Sort] [T A : Typ]
//                     (dT : der_type (τ_Γ Γ) T s)
//                     (dA : der_type (τ_Γ Γ) A s')
//                     (a : eps (τ_T Γ dA)) :
//   tconvtype
//       (τ_T Γ dT)
//       (τ_T (TPush Γ s' A dA a) (der_type_shift0 dA (τ_dΓ Γ) dT));
// symbol τ_shift0T (Γ : TContext) [s s' : Sort] [T A : Typ]
//                     (dT : der_type (τ_Γ Γ) T s)
//                     (dA : der_type (τ_Γ Γ) A s')
//                  (a : eps (τ_T Γ dA)) ≔
//   convtransp (τ_shift0T_eq Γ dT dA a);
// symbol τ_shift0T' (Γ : TContext) [s s' : Sort] [T A : Typ]
//                 (dT : der_type (τ_Γ Γ) T s)
//                 (dA : der_type (τ_Γ Γ) A s')
//                 (a : eps (τ_T Γ dA)) ≔
//   convtransp (xsymmetry (τ_shift0T_eq Γ dT dA a));

// symbol τ_Ishift0T_eq (Γ : TContext) [s : Sort] [T : Typ]
//                      (dT : der_type (τ_Γ Γ) T s)
//                      (i : tI):
//   tconvtype
//       (τ_T Γ dT)
//       (τ_T (TPushI Γ i) (der_Ishift0 (τ_dΓ Γ) dT));
// symbol τ_Ishift0T (Γ : TContext) [s : Sort] [T : Term]
//                   (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
//                   (i : tI) ≔
//   convtransp (τ_Ishift0T_eq Γ dT i);
// symbol τ_Ishift0T' (Γ : TContext) [s : Sort] [T : Term]
//                    (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
//                    (i : tI) ≔
//   convtransp (xsymmetry (τ_Ishift0T_eq Γ dT i));

// symbol τ_Fshift0T_eq (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
//                      (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
//                      (df : der_F (τ_Γ Γ) f)
//                      (fone : tisOne (τ_F Γ df)):
//   tconvtype
//       (τ_T Γ dT)
//       (τ_T (TPushF Γ f df fone) (der_weakF (τ_dΓ Γ) dT df));
// symbol τ_Fshift0T (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
//                   (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
//                   (df : der_F (τ_Γ Γ) f)
//                   (fone : tisOne (τ_F Γ df)) ≔
//   convtransp (τ_Fshift0T_eq Γ dT df fone);
// symbol τ_Fshift0T' (Γ : TContext) [s : Sort] [T : Term] [f : FTerm]
//                    (dT : der (τ_Γ Γ) T (tuniv s) (tlsuc s))
//                    (df : der_F (τ_Γ Γ) f)
//                    (fone : tisOne (τ_F Γ df)) ≔
//   convtransp (xsymmetry (τ_Fshift0T_eq Γ dT df fone));
