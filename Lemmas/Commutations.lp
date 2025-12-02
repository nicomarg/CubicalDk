require open ctt.Contexts.Shift;
require open ctt.Lemmas.TermEquality;

symbol swap_shift_shift (i j : DBId) (u : Term) :
  DBLe i j → TEq (shift i (shift j u)) (shift (dbsucc j) (shift i u));

symbol swap_Shift_shift (j : DBId) (u : Term) :
  TEq (shift db0 (shift j u)) (shift (dbsucc j) (shift db0 u)) ≔
    swap_shift_shift db0 j u (dble_0_n _);

symbol swap_shift_Ishift (i j : DBId) (u : Term) :
  TEq (shift i (Ishift j u)) (Ishift j (shift i u));
