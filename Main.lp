require open ctt.Symbols;
require open ctt.Univ.Syntax;
require open ctt.Translation;
require ctt.Var.Proofs;
require ctt.Univ.Proofs;
require open ctt.Var.Syntax;
require open ctt.Contexts.DeBruijn;

symbol l : tLev;
symbol A : T (τ_lev l);
symbol a : eps A;

symbol Γ1 : TContext ≔ TPush TEmpty (tlsuc l) (tuniv l) der_univ A;
symbol Γ2 : TContext ≔
begin
  apply TPush {refine Γ1} {refine l} {refine (tvar db0)} {refine der_var dble_db0} {simplify;}
end;

compute τ (TPush (TPush TEmpty (tlsuc l) (tuniv l) (der_univ) A) l (tvar db0) (der_var dble_db0) a);
