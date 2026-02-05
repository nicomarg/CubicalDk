require open ctt.Lemmas.TermEquality;
require open ctt.Var.Shift;

symbol swap_shift_shift (i j : DBId) (u : Term) :
  DBLe i j → TEq (shift i (shift j u)) (shift (dbsucc j) (shift i u));

symbol swap_tshift_tshift (i j : DBId) (u : Typ) :
  DBLe i j → TyEq (tshift i (tshift j u)) (tshift (dbsucc j) (tshift i u));

symbol swap_Shift_shift (j : DBId) (u : Term) :
  TEq (shift db0 (shift j u)) (shift (dbsucc j) (shift db0 u)) ≔
    swap_shift_shift db0 j u (dble_0_n _);

symbol swap_TShift_tshift (j : DBId) (u : Typ) :
  TyEq (tshift db0 (tshift j u)) (tshift (dbsucc j) (tshift db0 u)) ≔
    swap_tshift_tshift db0 j u (dble_0_n _);
// symbol swap_shift_Ishift (i j : DBId) (u : Term) :
//   TEq (shift i (Ishift j u)) (Ishift j (shift i u));
