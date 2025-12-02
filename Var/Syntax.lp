require open ctt.Symbols;
require open ctt.Contexts.DeBruijn;
require open ctt.Contexts.Shift;
require open ctt.Contexts.Definition;

constant symbol tvar : DBId → Term;

constant symbol der_var : Π[Γ : Context] [id : DBId], DBLe (dbsucc id) (len Γ) →
  der Γ (tvar id) (shiftgetΓ Γ id) (getS Γ id);
