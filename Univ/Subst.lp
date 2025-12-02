require open ctt.Univ.Syntax;

require open ctt.Contexts.Shift;
rule shift _ (tuniv $id) ↪ tuniv $id
with Shift* _ (tuniv $s) ↪ tuniv $s
with Ishift _ (tuniv $id) ↪ (tuniv $id)
with shiftΓ _ _ (tuniv $s) ↪ tuniv $s;

require open ctt.Contexts.Subst;
rule subst _ _ (tuniv $id) ↪ tuniv $id
with Isubst _ _ (tuniv $id) ↪ (tuniv $id);
