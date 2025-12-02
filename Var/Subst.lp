require open ctt.Var.Syntax;
require open ctt.Contexts.DeBruijn;

require open ctt.Contexts.Shift;
rule shift $i (tvar $id) ↪ tvar (dbshift $i $id)
with Ishift _ (tvar $id) ↪ (tvar $id);

require open ctt.Contexts.Subst;
rule subst $i $V (tvar $id) ↪ dbselect $i $id $V (tvar $id) (tvar (dbprev $id))
with Isubst _ _ (tvar $id) ↪ (tvar $id);
