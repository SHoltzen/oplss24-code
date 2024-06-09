(** defines the core parser
  * see https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
%{
  open Syntax
%}

/* Tokens */
%token EOF
%token PLUS MINUS MULTIPLY DIVIDE MODULUS
%token LT LTE GT GTE EQUAL_TO NEQ EQUAL LEFTSHIFT RIGHTSHIFT
%token AND OR NOT DISCRETE IFF XOR SAMPLE
%token LPAREN RPAREN
%token IF THEN ELSE TRUE FALSE IN INT
%token SEMICOLON COMMA COLON
%token LET OBSERVE FLIP LBRACE RBRACE FST SND FUN BOOL ITERATE UNIFORM BINOMIAL
%token LIST LBRACKET RBRACKET CONS HEAD TAIL LENGTH BIND RETURN FROM GAUSSIAN

%token <int>    INT_LIT
%token <string> FLOAT_LIT
%token <string> ID

/* associativity rules */
%left OR
%left AND
%left NOT
%left IFF
%left XOR
%left LTE GTE LT GT NEQ
%right CONS
%left PLUS MINUS EQUAL_TO LEFTSHIFT RIGHTSHIFT
%left MULTIPLY DIVIDE MODULUS
/* entry point */

%start program
%type <Syntax.program> program

%%
num:
    | FLOAT_LIT { (Bignum.of_string $1) }
    | INT_LIT { (Bignum.of_int $1) }
    | INT_LIT DIVIDE INT_LIT { Bignum.($1 // $3) }

expr:
    | (* (e) *) delimited(LPAREN, expr, RPAREN) { $1 }
    | (* observe e; e *) OBSERVE expr SEMICOLON expr { Observe({startpos=$startpos; endpos=$endpos}, $2, $4) }
    | (* x *)ID { Ident({startpos=$startpos; endpos=$endpos}, $1) }
    | num { Real({startpos=$startpos; endpos=$endpos}, $1) }
    | TRUE { Bool({startpos=$startpos; endpos=$endpos}, true) }
    | FALSE { Bool({startpos=$startpos; endpos=$endpos}, false) }
    | (* if e then e else e *) IF expr THEN expr ELSE expr { Ite({startpos=$startpos; endpos=$endpos}, $2, $4, $6) }
    | (* x <- e; e *)
      ID BIND expr SEMICOLON expr { Bind({startpos=$startpos; endpos=$endpos}, $1, $3, $5) }
    | UNIFORM { Unif({startpos=$startpos; endpos=$endpos}) }
    | FLIP num { Flip({startpos=$startpos; endpos=$endpos}, $2) }
    | (* e + e *)
      expr PLUS expr { Plus({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | (* e * e *)
      expr MULTIPLY expr { Mul({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | (* e < e *)
      expr LT expr { Lt({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | (* e && e *)
      expr AND expr { And({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | (* e || e *)
      expr OR expr { Or({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | (* !e *)
      NOT expr { Not({startpos=$startpos; endpos=$endpos}, $2) }
    | RETURN expr { Return({startpos=$startpos; endpos=$endpos}, $2) }





program:
  body=expr; EOF { { body=body } }
