require open ctt.Var.Shift;

// Shifting derivation
symbol der_shift0 [Γ : Context] [t : Term] [A T : Typ] [l l' : Sort]
                  (_ : der_type Γ A l') (_ : der_context Γ) (_ : der Γ t T l) :
  der (Push A l' Γ) (Shift t) (TShift T) l;
symbol der_type_shift0 [Γ : Context] [A T : Typ] [l l' : Sort]
                  (_ : der_type Γ A l') (_ : der_context Γ) (_ : der_type Γ T l) :
  der_type (Push A l' Γ) (TShift T) l;
// symbol der_Ishift0 [Γ : Context] [t T : Term] [l : Sort]
//                   (_ : der_context Γ) (_ : der Γ t T l) :
//   der (PushI Γ) (IShift t) (IShift T) l;
// symbol der_Ishift0F [Γ : Context] [f : FTerm]
//                   (_ : der_context Γ) (_ : der_F Γ f) :
//   der_F (PushI Γ) (IShiftF f);
symbol der_eq_shift0 [Γ : Context] [t1 t2 : Term] [A T : Typ] [l l' : Sort]
                     (_ : der_type Γ A l') (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) :
  der_eq (Push A l' Γ) (Shift t1) (Shift t2) (TShift T) l;
symbol der_eqT_shift0 [Γ : Context] [t1 t2 : Typ] [A : Typ] [l l' : Sort]
                     (_ : der_type Γ A l') (_ : der_context Γ) (_ : der_eqT Γ t1 t2 l) :
  der_eqT (Push A l' Γ) (TShift t1) (TShift t2) l;
// symbol der_eq_Ishift0 [Γ : Context] [t1 t2 T : Term] [l : Sort]
//                       (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) :
//   der_eq (PushI Γ) (IShift t1) (IShift t2) (IShift T) l;
symbol der_shift1 [Γ : Context] [t : Term] [A T B : Typ] [l la lb : Sort]
                  (_ : der_type Γ A la)
                  (_ : der_type Γ B lb)
                  (_ : der_context Γ)
                  (_ : der (Push A la Γ) t T l) : der (Push (TShift A) la (Push B lb Γ)) (Shift1 t) (TShift1 T) l;
symbol der_type_shift1 [Γ : Context] [t : Typ] [A B : Typ] [l la lb : Sort]
                  (_ : der_type Γ A la)
                  (_ : der_type Γ B lb)
                  (_ : der_context Γ)
                  (_ : der_type (Push A la Γ) t l) : der_type (Push (TShift A) la (Push B lb Γ)) (TShift1 t) l;
// symbol der_Ishift1 [Γ : Context] [t T : Term] [l: Sort]
//                   (_ : der_context Γ)
//                   (_ : der (PushI Γ) t T l) : der (PushI (PushI Γ)) (IShift1 t) (IShift1 T) l;

// symbol der_Ishift_context [Γ : Context] [t T A : Term] [l l' : Sort]
//                           (_ : der_context Γ) (_ : der Γ A (tuniv l) (tlsuc l))
//                           (_ : der (PushI (Push A l Γ)) t T l') : der (Push (IShift A) l (PushI Γ)) t T l';
// symbol der_weakF [Γ : Context] [t T : Term] [f : FTerm] [l : Sort]
//                  (_ : der_context Γ) (_ : der Γ t T l) (_ : der_F Γ f) :
//   der (PushF f Γ) t T l;
// symbol der_weakFF [Γ : Context] [f g : FTerm]
//                  (_ : der_context Γ) (_ : der_F Γ g) (_ : der_F Γ f) :
//   der_F (PushF f Γ) g;
// symbol der_eq_weakF [Γ : Context] [t1 t2 T : Term] [l : Sort] [f : FTerm]
//                     (_ : der_context Γ) (_ : der_eq Γ t1 t2 T l) (_ : der_F Γ f) :
//   der_eq (PushF f Γ) t1 t2 T l;
// symbol der_weakF1 [Γ : Context] [t A T : Term] [f : FTerm] [l l' : Sort]
//                  (_ : der_context Γ) (_ : der Γ A (tuniv l') (tlsuc l')) (_ : der (Push A l' Γ) t T l) (_ : der_F Γ f) :
//   der (Push A l' (PushF f Γ)) t T l;

// Iterated shifting
symbol der_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [t : Term] [T : Typ] [l : Sort] (_ : der (getΓ Γ id) t T l) :
  der Γ (shiftΓ Γ id t) (tshiftΓ Γ id T) l;
symbol der_type_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [T : Typ] [l : Sort] (_ : der_type (getΓ Γ id) T l) :
  der_type Γ (tshiftΓ Γ id T) l;
// Implementation of der_shift
rule der_shift db0 (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ $d
with der_shift (dbsucc $id) (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_shift0 $dA $dΓ (der_shift $id $dΓ $d);
rule der_type_shift db0 (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_type_shift0 $dA $dΓ $d
with der_type_shift (dbsucc $id) (der_context_Push _ _ _ $dA $dΓ) $d ↪ der_type_shift0 $dA $dΓ (der_type_shift $id $dΓ $d);
// with der_shift $id (der_context_PushI _ $dΓ) $d ↪ der_Ishift0 $dΓ (der_shift $id $dΓ $d)
// with der_shift $id (der_context_PushF _ _ $df $dΓ) $d ↪ der_weakF $dΓ (der_shift $id $dΓ $d) $df;
symbol der_eq_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [t1 t2 : Term] [T : Typ] [l : Sort]
                    (_ : der_eq (getΓ Γ id) t1 t2 T l) :
  der_eq Γ (shiftΓ Γ id t1) (shiftΓ Γ id t2) (tshiftΓ Γ id T) l;
symbol der_eqT_shift (id : DBId) [Γ : Context] (_ : der_context Γ) [t1 t2 : Typ] [l : Sort]
                    (_ : der_eqT (getΓ Γ id) t1 t2 l) :
  der_eqT Γ (tshiftΓ Γ id t1) (tshiftΓ Γ id t2) l;
