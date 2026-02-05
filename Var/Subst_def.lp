require open ctt.Var.Syntax;
require open ctt.DeBruijn;

require open ctt.Var.Shift;
rule shift $i (tvar $id) ↪ tvar (dbshift $i $id);

require open ctt.Var.Subst;
rule subst $i $V (tvar $id) ↪ dbselect $i $id $V (tvar $id) (tvar (dbprev $id));
