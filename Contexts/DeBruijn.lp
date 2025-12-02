require open ctt.Symbols;

constant symbol db0 : DBId;
constant symbol dbsucc : DBId → DBId;
symbol db1 : DBId ≔ dbsucc db0;
symbol db2 : DBId ≔ dbsucc db1;

symbol dbadd : DBId → DBId → DBId;
rule dbadd db0 $id ↪ $id
with dbadd $id db0 ↪ $id
with dbadd (dbsucc $n) $m ↪ dbsucc (dbadd $n $m)
with dbadd $n (dbsucc $m) ↪ dbsucc (dbadd $n $m);

symbol dbprev : DBId → DBId;
rule dbprev (dbsucc $n) ↪ $n;

// Equality
constant symbol DBEq : DBId → DBId → TYPE;
constant symbol DBRefl (i : DBId) : DBEq i i;
symbol dbcong (f : DBId → DBId) [i j : DBId]
                  : DBEq i j → DBEq (f i) (f j);
rule dbcong $f (DBRefl $i) ↪ DBRefl ($f $i);
symbol dbeq_inv [i j] : DBEq i j → DBEq j i;
rule dbeq_inv (DBRefl _) ↪ DBRefl _;
symbol dbeq_trans [i j k : DBId] : DBEq i j → DBEq j k → DBEq i k;
rule dbeq_trans (DBRefl _) (DBRefl _) ↪ DBRefl _;

symbol dbeq_S_n [i j : DBId] : DBEq (dbsucc i) (dbsucc j) → DBEq i j;
rule dbeq_S_n (DBRefl _) ↪ DBRefl _;

// Comparison
constant symbol DBLe : DBId → DBId → TYPE;
constant symbol DBLe_refl (i : DBId) : DBLe i i;
constant symbol DBLe_succ [i j : DBId] : DBLe i j → DBLe i (dbsucc j);

symbol dble_n_S [i j : DBId] : DBLe i j → DBLe (dbsucc i) (dbsucc j);
symbol dble_S_n [i j : DBId] : DBLe (dbsucc i) (dbsucc j) → DBLe i j;
symbol dble_Sn_n [i j : DBId] : DBLe (dbsucc i) j → DBLe i j;
symbol dble_n_Sn (i : DBId) : DBLe i (dbsucc i);
symbol dble_0_n (i : DBId) : DBLe db0 i;
rule dble_n_S (DBLe_refl $i) ↪ DBLe_refl (dbsucc $i)
with dble_n_S (DBLe_succ $h) ↪ DBLe_succ (dble_n_S $h)
with dble_n_Sn $i ↪ DBLe_succ (DBLe_refl $i)
with dble_Sn_n (DBLe_refl (dbsucc $i)) ↪ dble_n_Sn $i
with dble_Sn_n (DBLe_succ $h) ↪ DBLe_succ (dble_Sn_n $h)
with dble_S_n (DBLe_refl (dbsucc $i)) ↪ DBLe_refl $i
with dble_S_n (DBLe_succ $h) ↪ dble_Sn_n $h
with dble_0_n db0 ↪ DBLe_refl db0
with dble_0_n (dbsucc $i) ↪ DBLe_succ (dble_0_n $i);

symbol dble_eq_left i j k : DBEq i j → DBLe i k → DBLe j k;
symbol dble_eq_right i j k : DBEq i j → DBLe k i → DBLe k j;
rule dble_eq_left _ _ _ (DBRefl _) $h ↪ $h
with dble_eq_right _ _ _ (DBRefl _) $h ↪ $h;

symbol dble_trans i j k : DBLe i j → DBLe j k → DBLe i k;
rule dble_trans _ _ _ $e (DBLe_refl _) ↪ $e
with dble_trans _ _ _ $e (DBLe_succ $f) ↪ DBLe_succ (dble_trans _ _ _ $e $f);

symbol dble_db0 [n : DBId] : DBLe (dbsucc db0) (dbsucc n) ≔
  dble_n_S (dble_0_n n);
symbol dble_db1 [n : DBId] : DBLe (dbsucc (dbsucc db0)) (dbsucc (dbsucc n)) ≔
  dble_n_S (dble_n_S (dble_0_n n));
