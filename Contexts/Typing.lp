require open ctt.Contexts.Definition;
require open ctt.Univ.Syntax;

constant symbol der_context_empty : der_context Empty;
constant symbol der_context_Push : Π (Γ : Context) (l : Sort) (A : Term),
  der Γ A (tuniv l) (tlsuc l) → der_context Γ → der_context (Push A l Γ);
constant symbol der_context_PushI : Π (Γ : Context), der_context Γ → der_context (PushI Γ);
constant symbol der_context_PushF : Π (Γ : Context) (f : FTerm), der_F Γ f → der_context Γ → der_context (PushF f Γ);

// der_context accessors
// Might get expanded for other constructor when needed
symbol der_getΓ [Γ : Context] (id : DBId) (_ : der_context Γ) :
  der (getΓ Γ id) (get Γ id) (tuniv (getS Γ id)) (tlsuc (getS Γ id));
symbol der_subΓ [Γ : Context] (id : DBId) (_ : der_context Γ) : der_context (getΓ Γ id);
rule der_getΓ db0 (der_context_Push _ _ _ $dA _) ↪ $dA
with der_getΓ (dbsucc $id) (der_context_Push _ _ _ _ $dt) ↪ der_getΓ $id $dt
with der_getΓ $id (der_context_PushI _ $dt) ↪ der_getΓ $id $dt
with der_getΓ $id (der_context_PushF _ _ _ $dt) ↪ der_getΓ $id $dt
with der_subΓ db0 (der_context_Push _ _ _ _ $dΓ) ↪ $dΓ
with der_subΓ (dbsucc $id) (der_context_Push _ _ _ _ $dΓ) ↪ der_subΓ $id $dΓ
with der_subΓ $id (der_context_PushI _ $dt) ↪ der_subΓ $id $dt
with der_subΓ $id (der_context_PushF _ _ _ $dt) ↪ der_subΓ $id $dt
;

// Better der_context_push
symbol pushΓ [Γ : Context] [l : Sort] [T : Term] (d : der Γ T (tuniv l) (tlsuc l)) (dΓ : der_context Γ) :
  der_context (Push T l Γ) ≔ der_context_Push Γ l T d dΓ;
symbol pushΓF [Γ : Context] [f : FTerm] (df : der_F Γ f) (dΓ : der_context Γ) :
  der_context (PushF f Γ) ≔ der_context_PushF Γ f df dΓ;
symbol pushΓI [Γ : Context] (dΓ : der_context Γ) :
  der_context (PushI Γ) ≔ der_context_PushI Γ dΓ;
