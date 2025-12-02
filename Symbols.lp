// Syntax types
constant symbol tLev : TYPE;
constant symbol tlsuc : tLev → tLev;

constant symbol DBId : TYPE;

constant symbol Term : TYPE;
constant symbol ITerm : TYPE;
constant symbol FTerm : TYPE;

constant symbol Context : TYPE;

// Typing
constant symbol der : Context → Term → Term → tLev → TYPE;
constant symbol der_eq : Context → Term → Term → Term → tLev → TYPE;
constant symbol der_I : Context → ITerm → TYPE;
constant symbol der_eq_I : Context → ITerm → ITerm → TYPE;
constant symbol der_F : Context → FTerm → TYPE;
constant symbol der_eq_F : Context → FTerm → FTerm → TYPE;
constant symbol der_isOne : Context → FTerm → TYPE;

constant symbol der_context : Context → TYPE;
