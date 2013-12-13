# The Lem Language


## Metavariables and Identifiers

    indexvar n , i , j , k   {{ Index variables for meta-lists }}
    metavar num              {{ Numeric literal }}
    metavar string           {{ String literal }}
    metavar backtick_string  {{ String literal preceded by ' }}
    metavar regexp           {{ Regular expresion, as a string literal }}
    metavar l                {{ Source location }}
    metavar x                {{ Name }}
    metavar ix               {{ Infix name }}

    id  ::= {{ Long identifers }}
      | x1 . .. xn . x l        

    a  ::=  {{ Type variables }}
      | ' x                     

## Literals

    lit  ::=  {{ Literal constants }}
      | true 
      | false
      | num     
      | hex     
      | bin     
      | string
      | ( )                     


## Types

    typ  ::=  {{ Types }}
      | _                                   {{ Unspecified type }}
      | a                                   {{ Type variables }}
      | typ1 -> typ2                        {{ Function types }}
      | typ1 * .... * typn                  {{ Tuple types }}
      | id typ1 .. typn                     {{ Type applications }}
      | backtick_string typ1 .. typn        {{ Backend-Type applications }}
      | ( typ )                         

## Patterns

    pat ::=   {{ Patterns }}
      | _                                   {{ Wildcards }}
      | ( pat as x )                        {{ Named patterns }}
      | ( pat : typ )                       {{ Typed patterns }}
      | id pat1 .. patn                     {{ Single variable and constructor patterns }}
      | <| fpat1 ; ... ; fpatn semi_opt |>  {{ Record patterns }}
      | ( pat1 , .... , patn )              {{ Tuple patterns }}
      | [ pat1 ; .. ; patn semi_opt ]       {{ List patterns }}
      | ( pat )                         
      | pat1 :: pat2                      {{ Cons patterns }}
      | x + num                           {{ constant addition patterns }}
      | lit                                 {{ Literal constant patterns }}


    fpat ::=  {{ Field patterns }}
      | id = pat l      

    bar_opt  ::=          {{ Optional bars }}
      |                         
      | '|'                     

    semi_opt  ::=        {{ Optional semi-colons }}
      |                 
      | ;             


## Expressions

    exp ::=  {{ Expressions }}
      | id                                                 {{ Identifiers }}
      | backtick_string                                    {{ identifier that should be literally used in output }}
      | fun psexp                                          {{ Curried functions }}
      | function bar_opt pexp1 '|' ... '|' pexpn end       {{ Functions with pattern matching }}
      | exp1 exp2                                          {{ Function applications }}
      | exp1 ix exp2                                       {{ Infix applications }}
      | <| fexps |>                                        {{ Records }}
      | <| exp with fexps |>                               {{ Functional update for records }}
      | exp . id                                           {{ Field projection for records }}
      | match exp with bar_opt pexp1 '|' ... '|' pexpn l end     {{ Pattern matching expressions }}
      | ( exp : typ )                                      {{ Type-annotated expressions }}
      | let letbind in exp                                 {{ Let expressions }}
      | ( exp1 , .... , expn )                             {{ Tuples }}
      | [ exp1 ; .. ; expn semi_opt ]                      {{ Lists }}
      | ( exp )                                         
      | begin exp end                                      {{ Alternate syntax for (exp) }}
      | if exp1 then exp2 else exp3                        {{ Conditionals }}
      | exp1 :: exp2                                     {{ Cons expressions }}
      | lit                                                {{ Literal constants }}
      | { exp1 | exp2 }                                    {{ Set comprehensions }}
      | { exp1 | forall qbind1 .. qbindn | exp2 }          {{ Set comprehensions with explicit binding }}
      | { exp1 ; .. ; expn semi_opt }                      {{ Sets }}
      | q qbind1 ... qbindn . exp                          {{ Logical quantifications }}
      | [ exp1 | forall qbind1 .. qbindn | exp2 ]          {{ List comprehensions (all binders must be quantified) }}
      | do id pat1 <- exp1 ; .. patn <- expn ; in exp end  {{ Do notation for monads }}

    q ::=  {{ Quantifiers }}
      | forall  
      | exists  

    qbind  ::= {{ Bindings for quantifiers}}
      | x                                                       
      | ( pat IN exp )                                    {{ Restricted quantifications over sets}}
      | ( pat MEM exp )                                     {{ Restricted quantifications over lists }}

    fexp  ::=  {{ Field-expressions }}
      | id = exp l                      

    fexps ::=  {{ Field-expression lists }}
      | fexp1 ; ... ; fexpn semi_opt l  

    pexp ::=  {{ Pattern matches }}
      | pat -> exp l                    

    psexp ::=  {{ Multi-pattern matches }}
      | pat1 ... patn -> exp l          

    tannot_opt ::=  {{ Optional type annotations }}
      |                 
      | : typ   

    funcl  ::=  {{ Function clauses }}
      | x pat1 ... patn tannot_opt = exp        

    letbind  ::= {{ Let bindings }}
      | pat tannot_opt = exp        {{ Value bindings }}
      | funcl                       {{ Function bindings }}


## Inductive Relation Definitions

    name_t ::=  {{ Name or name with type for inductively defined relation clauses }}
      | x                
      | ( x : typ )

    name_ts ::=  {{ Names with optional types for inductively defined relation clauses }}
      | name_t0 .. name_tn 

    rule ::=  {{ Inductively defined relation clauses }}
      | x : forall name_t1 .. name_ti . exp ==> x1 exp1 .. expn 

    witness_opt  ::= {{ Optional witness type name declaration. Must be present for a witness type to be generated. }}  
      |                  
      | witness type x ; 

    check_opt  ::=  {{ Option check name declaration }}
      |                 
      | check x ;       

    functions_opt  ::=  {{ Optional names and types for functions to be generated. Types should use only in, out, unit, or the witness type }}
      |                   
      | x : typ 
      | x : typ ; functions_opt

    indreln_name ::=  {{ Name for inductively defined relation }}
      | [ x : typschm witness_opt check_opt functions_opt ] 



## Type Definitions

    typs ::=      {{ Type lists }}
      | typ1 * ... * typn       

    ctor_def ::= {{ Datatype definition clauses }}
      | x of typs
      | x                {{ Constant constructors }}

    texp ::=  {{ Type definition bodies }}
      | typ                                                 {{ Type abbreviations }}
      | <| x1 : typ1 ; ... ; xn : typn semi_opt |>          {{ Record types }}
      | bar_opt ctor_def1 '|' ... '|' ctor_defn             {{ Variant types }}

    name_opt ::=  {{ Optional name specification for variables of defined type }} 
      |                       
      | [ name = regexp ] 

    td ::= {{ Type definitions }}
      | x tnvars name_opt = texp                                
      | x       tnvars name_opt                             {{ Definitions of opaque types }}


## Type Schemes

    c ::=  {{ Typeclass constraints }}
      | id tnvar

    cs ::=  {{ Typeclass constraint lists }}
      |                                                         
      | c1 , .. , ci =>                                             {{ Must have >0 constraints }}

    c_pre ::=  {{ Type and instance scheme prefixes }}
      |                                                         
      | forall tnvar1 .. tnvarn . cs                                {{ Must have >0 type variables }}

    typschm ::=    {{ Type schemes }}
      | c_pre typ                       

    instschm ::=  {{ Instance schemes }}
      | c_pre ( id typ )                                                



## Target Descriptions

    target ::=  {{ Backend target names }}
      | hol             
      | isabelle        
      | ocaml   
      | coq             
      | tex             
      | html    
      | lem     

    targets  ::=  {{ Backend target name lists }}
      | { target1 ; .. ; targetn }              
      | ~{ target1 ; .. ; targetn }               {{ all targets except the listed ones }}

    targets_opt ::=    {{ Optional targets }}
      |                                                         
      | targets                                                 

## Import, Open, and Include

    open_import  ::=  {{ Open or import statements }}
      | open                                                    
      | import                                                  
      | open import                                                     
      | include                                                 
      | include import                                          

## Lemmas, Assertions, and Theorems

    lemma_typ ::= {{ Types of Lemmata }}
      | assert                                                  
      | lemma                                                           
      | theorem                                                         

    lemma_decl ::=   {{ Lemmata and Tests }}
      | lemma_typ targets_opt x : exp                           


## Unused?

    dexp ::=  {{ declaration field-expressions }}
      | name_s = string l                                               
      | format = string l                                               
      | arguments = exp1 ... expn l                                     
      | targuments = texp1 ... texpn l                          

    declare_arg ::=   {{ arguments to a declaration }}
      | string                                                  
      | <| dexp1 ; ... ; dexpn semi_opt l |>                    


## Target Representation Declarations

    component  ::= {{ components }}
      | module   
      | function 
      | type     
      | field    

    termination_setting ::= {{ termination settings }}
      | automatic 
      | manual    

    exhaustivity_setting  ::= {{ exhaustivity settings }}
      | exhaustive   
      | inexhaustive 

    elim_opt ::=  {{ optional terms used as eliminators for pattern matching }}
      |     
      | id  

    fixity_decl ::= {{ fixity declarations for infix identifiers }}
      | right_assoc nat 
      | left_assoc  nat 
      | non_assoc   nat 
      |                 

    target_rep_rhs ::=  {{ right hand side of a target representation declaration }}
      | infix fixity_decl backtick_string 
      | exp                          
      | typ                          
      | special string exp1 ... expn 
      |                              

    target_rep_lhs  ::= {{ left hand side of a target representation declaration }}
      | target_rep component id x1 .. xn 
      | target_rep component id tnvars       

    declare_def  ::=   {{ declarations }}
      | declare targets_opt compile_message id = string                    {{ compile_message_decl       }}
      | declare targets_opt rename module = x                              {{ rename_current_module_decl }}
      | declare targets_opt rename component id = x                        {{ rename_decl                }}
      | declare targets_opt ascii_rep component id = backtick_string       {{ ascii_rep_decl             }}
      | declare target target_rep target_rep_lhs = target_rep_rhs          {{ target_rep_decl            }}
      | declare set_flag x1 = x2                                           {{ set_flag_decl              }}
      | declare targets_opt termination_argument id = termination_setting  {{ termination_argument_decl  }}
      | declare targets_opt pattern_match exhaustivity_setting id tnvars = [ id1 ; ... ; idn semi_opt ] elim_opt {{ pattern_match_decl }}

## Value Definitions

    val_def ::=  {{ Value definitions }}
      | let targets_opt letbind                             {{ Non-recursive value definitions }}
      | let rec targets_opt funcl1 and ... and funcln       {{ Recursive function definitions }}
      | let inline targets_opt letbind                      {{ Function definitions to be inlined }}
      | let lem_transform targets_opt letbind               {{ Function definitions to be transformed }}

    ascii_opt ::=   {{ an optional ascii representation }}
      |                     
      | [ backtick_string ]

## Class and Instance Declarations

    instance_decl ::=   {{ is it an instance or the default instance? }}
      | instance         
      | default_instance 

    class_decl ::=   {{ is a class an inlined one? }}
      | class        
      | class inline 

## Value Type Specifications

    val_spec ::=  {{ Value type specifications }} 
      | val x ascii_opt : typschm       


## Top-level Definitions

    semisemi_opt ::=  {{ Optional double-semi-colon }}
      |                                                         
      | ;;                                                      

    def  ::=  {{ Top-level definitions }}
      | type td1 and ... and tdn                                    {{ Type definitions }}
      | val_spec                                                    {{ Top-level type constraints }}
      | val_def                                                     {{ Value definitions }}
      | lemma_decl                                                  {{ Lemmata }}
      | module x = struct defs end                                  {{ Module definitions }}
      | module x = id                                               {{ Module renamings }}
      | open_import id1 ... idn                                     {{ importing and/or opening modules }}
      | open_import targets_opt backtick_string1 ... backtick_stringn   
           {{ importing and/or opening only for a target / it does not influence the Lem state }}
      | indreln targets_opt indreln_name1 and ... and indreln_namei rule1 and ... and rulen                 
           {{ Inductively defined relations }}
      | class_decl ( x tnvar ) val targets_opt1 x1 ascii_opt1 : typ1 l1 ... val targets_optn xn ascii_optn : typn ln end    
           {{ Typeclass definitions }}
      | instance_decl instschm val_def1 l1 ... val_defn ln end              
           {{ Typeclass instantiations }}
      | declare_def                                                 {{ modify Lem behaviour }}


    defs ::=  {{ Definition sequences }}
      | def1 semisemi_opt1 .. defn semisemi_optn

