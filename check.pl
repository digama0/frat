#!/usr/bin/env swipl

:- initialization(main, main).

:- ["/home/sk/prelude"].

remove(ELEM, [ELEM | LIST], LIST) :- !.
remove(ELEM, [HEAD | LIST], [HEAD | REST]) :- remove(ELEM, LIST, REST).

is_perm(LIST, LIST) :- !.
is_perm([ELEM | LIST_A], LIST_B) :- 
  remove(ELEM, LIST_B, TEMP_B), !, 
  is_perm(LIST_A, TEMP_B).

string_number(STR, NUM) :- number_string(NUM, STR).

string_cla(STR,CLA) :- 
  split_string(STR, " ", " ", TEMP), 
  append(NUMSTRS, ["0"], TEMP),
  cmap(string_number, NUMSTRS, CLA).

is_comment(STR) :- string_concat("c", _, STR). 
is_header(STR) :- string_concat("p cnf", _, STR). 

stream_prob(STM, NUM, IN, OUT) :-
  read_line_to_string(STM, LINE), 
  (
    LINE = end_of_file -> OUT = IN 
  ;
    (is_comment(LINE) ; is_header(LINE)) -> 
    stream_prob(STM, NUM, IN, OUT)
  ;
    string_cla(LINE, CLA), 
    put_assoc(NUM, IN, CLA, TEMP), 
    num_suc(NUM, SUC), !,
    stream_prob(STM, SUC, TEMP, OUT)
  ).

dimacs_prob(DIMACS, PROB) :- 
  open(DIMACS, read, STM),
  empty_assoc(EMP),
  stream_prob(STM, 1, EMP, PROB).

get_nat(STM, NUM) :- 
  get_byte(STM, BYTE), 
  (
    BYTE < 128 -> 
    NUM = BYTE 
  ;
    DIFF is (BYTE - 128), 
    get_nat(STM, TEMP),  
    NUM is (TEMP * 128) + DIFF
  ).

get_int(STM, NUM) :-  
  get_nat(STM, UNS), 
  REM is mod(UNS, 2),
  QUO is div(UNS, 2), !, 
  (
    REM = 0 -> 
    NUM is QUO ;
    NUM is -QUO
  ).  

get_ints(STM, INTS) :-  
  get_int(STM, INT), 
  get_ints(STM, INT, INTS).

get_ints(_, 0, []) :-  !.
get_ints(STM, INT, [INT | INTS]) :- get_ints(STM, INTS). 

get_pairs(STM, PAIRS) :- 
  get_nat(STM, NAT), 
  get_pairs(STM, NAT, PAIRS).
get_pairs(_, 0, []) :- !.
get_pairs(STM, ID_A, [(ID_A, ID_B) | PAIRS]) :- 
  get_nat(STM, ID_B), !,
  get_pairs(STM, PAIRS).

stm_hints(STM, l, HINTS) :- !, 
  get_char(STM, l), 
  get_ints(STM, HINTS).
stm_hints(_, _, none). 

stm_step(STM, a, a(ID, LITS, HINTS)) :- 
  get_nat(STM, ID), 
  get_ints(STM, LITS), 
  peek_char(STM, CHAR),
  stm_hints(STM, CHAR, HINTS).
stm_step(STM, o, o(ID, LITS)) :- get_nat(STM, ID), get_ints(STM, LITS).
stm_step(STM, d, d(ID, LITS)) :- get_nat(STM, ID), get_ints(STM, LITS).
stm_step(STM, f, f(ID, LITS)) :- get_nat(STM, ID), get_ints(STM, LITS).
stm_step(STM, r, r(PAIRS)) :- get_pairs(STM, PAIRS).
stm_step(STM, l, l(INTS)) :- get_ints(STM, INTS).
stm_step(STM, t, t(NAT)) :- get_nat(STM, NAT), get_nat(STM, 0).

stm_step(STM, STEP) :- 
  get_char(STM, CHAR), 
  stm_step(STM, CHAR, STEP). 

lit_abs_sign(LIT, LIT, true) :- 0 < LIT, !.
lit_abs_sign(LIT, NEG, false) :- NEG is -LIT.

add_unit(UNIT, VAL, NEW_VAL) :- 
  lit_abs_sign(UNIT, ABS, SIGN), 
  put_assoc(ABS, VAL, SIGN, NEW_VAL).

falsified(VAL, LIT) :- 
  lit_abs_sign(LIT, ABS, SIGN_A),
  get_assoc(ABS, VAL, SIGN_B), 
  SIGN_A \= SIGN_B.

cla_val_unit([LIT], _, LIT) :- !.
cla_val_unit([LIT | CLA], VAL, UNIT) :- 
  falsified(VAL, LIT) -> 
  cla_val_unit(CLA, VAL, UNIT)  
;
  LIT = UNIT, 
  cmap(falsified(VAL), CLA). 
  
rup_no_hint(VAL, CLAS) :- 
  pluck(CLAS, CLA, REST), 
  cla_val_unit(CLA, VAL, UNIT), !, 
  (
    falsified(VAL, UNIT) -> true ;
    add_unit(UNIT, VAL, NEW_VAL), 
    rup_no_hint(NEW_VAL, REST)
  ).

rup_hinted(CTX, VAL, HINTS) :- 
  pluck(HINTS, HINT, REST), 
  get_assoc(HINT, CTX, CLA), 
  cla_val_unit(CLA, VAL, UNIT), !, 
  (
    falsified(VAL, UNIT) -> true ;
    add_unit(UNIT, VAL, NEW_VAL), 
    rup_hinted(CTX, NEW_VAL, REST)
  ).

rup(CTX, LITS, none) :- !, 
  build_val(LITS, VAL), !,
  assoc_to_values(CTX, CLAS), !, 
  rup_no_hint(VAL, CLAS), !.
rup(CTX, LITS, HINTS) :- 
  build_val(LITS, VAL), !,
  rup_hinted(CTX, VAL, HINTS).

neg(NUM, NEG) :- NEG is -NUM.

target(_).
% target(ID) :- 
%   REM is mod(ID, 10000), 
%   REM = 0.

report_add(ID) :-
  target(ID) -> 
  format("Adding ID = ~w\n", ID) ; true.

report_del(ID) :-
  target(ID) -> 
  format("Deleting ID = ~w\n", ID) ; true.

build_val(LITS, VAL) :- 
  cmap(neg, LITS, NEGS), 
  empty_assoc(EMP), 
  foldl(add_unit, NEGS, EMP, VAL).

loop(CTX, _, a(ID, [], HINTS)) :- !, 
  target(ID) -> rup(CTX, [], HINTS) ; true.
  % rup(CTX, [], HINTS). 

loop(CTX, STM, d(ID, LITS)) :- 
  del_assoc(ID, CTX, CLA, TEMP), 
  is_perm(LITS, CLA), !, 
  loop(TEMP, STM).

loop(CTX, STM, a(ID, LITS, HINTS)) :- 
  (target(ID) -> rup(CTX, LITS, HINTS) ; true), !,
  put_assoc(ID, CTX, LITS, NEW_CTX), !,
  loop(NEW_CTX, STM).
loop(PROB, STM, o(ID, LITS)) :- 
  get_assoc(ID, PROB, CLA), 
  is_perm(CLA, LITS), !, 
  loop(PROB, STM).
loop(PROB, STM, t(_)) :- !,
  loop(PROB, STM).

loop(_, _, STEP) :- 
  format("Cannot verify step = ~w\n", STEP), !, false.

loop(PROB, STM) :- 
  stm_step(STM, STEP), !, 
  format("Checking step = ~w\n", STEP), !,
  loop(PROB, STM, STEP).

main([DIMACS, FRAT]) :- !,
  writeln("Collecting original clauses..."),
  dimacs_prob(DIMACS, PROB), !,
  writeln("Checking FRAT steps..."),
  open(FRAT, read, STM, [encoding(octet)]), !,
  loop(PROB, STM),
  write("Proof verified").

  
  
  

