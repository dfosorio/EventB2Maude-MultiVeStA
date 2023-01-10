/*
 * Probabilistic Event-B Grammar
 * Main production: model
 * Contexts are defined without the EXTEND clause nor axioms. Deferred sets may
 * explicitly list the constants that inhabitant it or specify the cardinality of
 * the set. 
 * In machines, the invariant is just the type of each variable
 */

grammar EventB;

// -----------------------------------
// Keywords and tokens
// -----------------------------------

// Model/machine related symbols
CONTEXT           : 'CONTEXT' ;
SETS              : 'SETS' ;
CONSTANTS         : 'CONSTANTS' ; 
END               : 'END' ;
MACHINE           : 'MACHINE' ;
SEES              : 'SEES' ;
VARIABLES         : 'VARIABLES' ;
INVARIANTS        : 'INVARIANTS' ;
INITIALISATION    : 'INITIALISATION' ;
EVENT             : 'EVENT' ;
WEIGHT            : 'WEIGHT' ;
WHERE             : 'WHERE' ;
THEN              : 'THEN' ;
ANY               : 'ANY' ;
PROPERTIES        : 'PROPERTIES' ;

// Types
TyNAT             : 'Nat' ; 
TyINT             : 'Int' ; 
TyBOOL            : 'Bool' ; 
CARTPROD          : '**' ; // Cartesian product
POWERSET          : 'POW' ; 

// Expressions on sets and relations
EMPTY             : 'empty' ;
EMPTYREL          : 'emptyrel' ;
DOM               : 'dom' ;
RAN               : 'ran' ;
CARD              : 'card' ;
DOMRES            : '<|' ;
OVERR             : '<+' ;
RANRES            : '|>' ;
INTRANGE          : '..' ;
INCHOICE          : '<:' ;
IN                : ':' ; 
NOTIN             : '/:' ;
UNION             : '\\s/' ; 
INTERSECTION      : '/s\\' ;
SUBSTRACTION      : '\\' ;

// Boolean expressions
TRUE              : 'True' ;
FALSE             : 'False' ;
CONJ              : '/\\' ;
DISJ              : '\\/' ;

// Arithmetic expressions
PLUS              : '+';
MINUS             : '-';
TIMES             : '*' ;
DIV               : '/' ;
INT               : '-'?[0-9]+ ;
FLOAT             : INT '.' INT ;
MOD               : 'mod' ; 

// Relational expressions
EQ                : '=' ;
NEQ               : '<>' ;
RELSYM            : '<' | '>' | '>=' | '<=' ;

// Miscellaneous 
SEP               : ',' ;
WHITESPACE        : (' ' | '\t')+ -> skip  ;
NEWLINE           : ('\r'? '\n' | '\r')+ -> skip ;
ID                : '_'* [A-Za-z][A-Za-z0-9_\-]* ;

// Initial production
model : context  
        machine 
        props?
        ;

COMMENT    : ('#' .*? ('#' | '\n' )) -> skip ;

// CONTEXT 
context: CONTEXT    ID
           SETS       setdef*
           CONSTANTS  ctedef*
         END 
         ;

// Defining deferred sets
setdef :  ID ':' setdecl ;

setdecl : INT               // Cardinality 
          | '{' listID '}'  // explicit enumeration
          ;

listID :  // List of IDs
      ID
    | ID SEP listID
    ;

// Constant definitions
ctedef : 
          ID ':' typeT ':=' val ;


// Types for constants and variables
typeT :   btype  // basic types (nat, int, bool, deferred sets)
        | ptype  // product type
        | stype  // sets / relations
        ; 

// Basic types
btype :   TyNAT 
        | TyINT 
        | TyBOOL 
        | ID // (deferred set)
        ; 

// Cartesian product
ptype : btype CARTPROD btype ;  

// Powerset 
stype : POWERSET '(' (btype | ptype) ')' ; 

// Values and expressions

val        :   bvalue  // basic values
             | pvalue  // pairs (power set)
             | lvalue  // list of values
             ; 

bvalue    :    INT 
             | boolV 
             | ID // constants from deferred sets
             ; 

boolV      : TRUE | FALSE  ; 
pvalue     : bvalue '|->' bvalue ; // Pairs 
svalue     : bvalue | pvalue ;     // Single values

// Simple lists of values
blvalue    :   EMPTY  
             | EMPTYREL 
             | '{' svaluelist '}' 
             | '{' expr INTRANGE expr '}'
             ; 

// Explicit enumerations
svaluelist :   svalue 
             | svalue SEP svaluelist ; 
            
// General list of values (including cartesian products)
lvalue     :  blvalue 
            | blvalue CARTPROD blvalue  ; 


// MACHINES

machine: MACHINE ID
             SEES ID
             VARIABLES vardecl
             INVARIANTS invdef*
             INITIALISATION initst
             eventdecl*
         END
         ;
// Variable declaration 
vardecl : ID* ; 

// Invariants (type of variables)
invdef : ID ':' typeT ;

// Simple assignments 
simplassg : ID ':=' expr ; 

// Machine initialization 
initst : simplassg* ; 

// Expressions
expr : val                                                              # ExprVal
       | '(' inner=expr ')'                                             # Parentheses
       | left=expr operator=(TIMES | DIV | MOD)        right=expr       # ArithExprTD
       | left=expr operator=(PLUS|MINUS)               right=expr       # ArithExprPM
       | left=expr operator=(EQ | NEQ)                 right=expr       # CompExpr
       | left=expr operator=RELSYM                     right=expr       # RelExpr
       | left=expr operator=(CONJ | DISJ)              right=expr       # BoolExpr
       | left=expr operator=(DOMRES | RANRES | OVERR)  
       						       right=expr       # RelationExpr
       | (DOM | RAN | CARD ) '(' expr ')'                               # DomRanCardExpr
       | left=expr operator=(IN | NOTIN | UNION | INTERSECTION | SUBSTRACTION) 
                                                      right=expr        # SetExpr
       | '{' intrange '}'                                               # IntRangeExpr
       | '{' ID '.' expr '|' expr '}'                                   # MapExpr 
       | '{' ID '.' expr '||' expr '}'                                  # FilterExpr 
       ;

// Events
eventdecl : EVENT ID
                WEIGHT expr 
                anydecl?
                wheredecl
                THEN evassg+
            END
            ;

// ANY (parameters) declaration
anydecl   : ANY anyvardef+ ; 
anyvardef : ID INCHOICE anyrange ; 
// Choice of values
anyrange  :   intrange   // ranges as 1..42
            | strrange   // explicit enumerations
            | setrange ; // arbitrary set/relation expressions 

intrange  : expr INTRANGE  expr  ; 
strrange  : '{' listID '}' ;
setrange  : expr  ;  

// Guard declaration 
wheredecl : WHERE expr ;  

// Action of the event
evassg    :   simplassg    // Simple assigment
            | probassg     // probabilistic assigment 
            ; 

probassg : ID ':=' '{' problist '}' ;
probexpr : expr '@' FLOAT ;
problist : probexpr| probexpr ',' problist ;

// Properties to be translated to PveSTa expressions
props : PROPERTIES proplist ;
proplist   : prop | prop ';' proplist ;
prop       : expr ;

