require open ctt.Univ.Syntax;

require open ctt.Var.Shift;
rule tshift _ (tuniv $id) ↪ tuniv $id
with TShift* _ (tuniv $s) ↪ tuniv $s
// with Ishift _ (tuniv $id) ↪ (tuniv $id)
with tshiftΓ _ _ (tuniv $s) ↪ tuniv $s
with tshift $id (tel $t) ↪ tel (shift $id $t)
with shift $id (as_term $t) ↪ as_term (tshift $id $t);

require open ctt.Var.Subst;
rule tsubst _ _ (tuniv $id) ↪ tuniv $id
with tsubst $id $u (tel $t) ↪ tel (subst $id $u $t)
with subst $id $u (as_term $t) ↪ as_term (tsubst $id $u $t);
// with Isubst _ _ (tuniv $id) ↪ (tuniv $id);
