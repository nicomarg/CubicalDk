// Syntax types
constant symbol Sort : TYPE;
constant symbol tlsuc : Sort → Sort;

constant symbol DBId : TYPE;

constant symbol Typ : TYPE;
constant symbol Term : TYPE;
constant symbol ITerm : TYPE;
constant symbol FTerm : TYPE;

constant symbol Context : TYPE;

// Typing
constant symbol der_type : Context → Typ → Sort → TYPE;
constant symbol der_eqT : Context → Typ → Typ → Sort → TYPE;
constant symbol der : Context → Term → Typ → Sort → TYPE;
constant symbol der_eq : Context → Term → Term → Typ → Sort → TYPE;
constant symbol der_I : Context → ITerm → TYPE;
constant symbol der_eq_I : Context → ITerm → ITerm → TYPE;
constant symbol der_F : Context → FTerm → TYPE;
constant symbol der_eq_F : Context → FTerm → FTerm → TYPE;
constant symbol der_isOne : Context → FTerm → TYPE;

constant symbol der_context : Context → TYPE;
