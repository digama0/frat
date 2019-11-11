#!/usr/bin/env swipl

% Prolog script for reading in a FRAT0 proof and compiling it to LRAT

:- initialization(main, main).

write_list([]).

write_list([Elem | List]) :-
  write(Elem),
  write("\n"),
  write_list(List).

write_list(_, []).

write_list(Stream, [Elem | List]) :-
  write(Stream, Elem),
  write(Stream, "\n"),
  write_list(Stream, List).

file_write_list(Target, List) :-
  open(Target, write, Stream),
  write_list(Stream, List), 
  close(Stream).

sep_zero([0 | Bytes], [], Bytes).

sep_zero([Byte | Bytes], [Byte | BytesA], BytesB) :- 
  Byte \= 0,
  sep_zero(Bytes, BytesA, BytesB).

num_lit(Num, Lit) :- 
  Quo is div(Num, 2),
  Mod is Num mod 2,
  ( Mod = 0 -> 
    Lit = Quo ;
    Lit is -Quo ).

bytes_num([Byte | Bytes], Byte, Bytes) :-
  Byte < 128.

bytes_num([Byte | Bytes], Num, Rem) :-
  128 =< Byte,
  Low is Byte /\ 127,
  bytes_num(Bytes, High, Rem), 
  Num is (High * 128) + Low.

bytes_nums([], []).

bytes_nums(Bytes, [Num | Nums]) :- 
  bytes_num(Bytes, Num, Rem),
  bytes_nums(Rem, Nums).

parse_nums(Bytes, Nums, Rem) :- 
  sep_zero(Bytes, NumBytes, Rem),
  bytes_nums(NumBytes, Nums).

parse([], []).

parse([97 | Bytes], [add(ID, Lits, IDs) | Lines]) :- 
  parse_nums(Bytes, [ID | Nums], [108 | Temp]),
  maplist(num_lit, Nums, Lits),
  parse_nums(Temp, IDs, Rem),
  parse(Rem, Lines).

parse([97 | Bytes], [add(ID, Lits) | Lines]) :- 
  parse_nums(Bytes, [ID | Nums], Rem),
  maplist(num_lit, Nums, Lits),
  \+ Rem = [108 | _], 
  parse(Rem, Lines).

parse([100 | Bytes], [del(ID, Lits) | Lines]) :- 
  parse_nums(Bytes, [ID | Nums], Rem),
  maplist(num_lit, Nums, Lits),
  parse(Rem, Lines).

parse([102 | Bytes], [final(ID, Lits) | Lines]) :- 
  parse_nums(Bytes, [ID | Nums], Rem),
  maplist(num_lit, Nums, Lits),
  parse(Rem, Lines).

parse([111 | Bytes], [orig(ID, Lits) | Lines]) :- 
  parse_nums(Bytes, [ID | Nums], Rem),
  maplist(num_lit, Nums, Lits),
  parse(Rem, Lines).

parse(_, _) :- 
  write("Invalid code\n"),
  false.

id_sta_lits(ID, [(ID, Sta, Lits) | Clas], Sta, Lits, Clas).

id_sta_lits(ID, [Cla | Clas], Sta, Lits, [Cla | Rem]) :-
  \+ Cla = (ID, _, _),
  id_sta_lits(ID, Clas, Sta, Lits, Rem).

negate(Num, Neg) :-
  Neg is -Num.
 
collect(_, [], []).

collect(Goal, [Elem | List], [Rst | Rsts])  :- 
  call(Goal, Elem, Rst),
  collect(Goal, List, Rsts).

collect(Goal, [Elem | List], Rsts)  :- 
  \+ call(Goal, Elem, _),
  collect(Goal, List, Rsts).

get_unit_lit((_, [X]), X).

build_val(Clas, Lits, Val) :- 
  collect(get_unit_lit, Clas, LitsA), 
  maplist(negate, Lits, LitsB), 
  append(LitsA, LitsB, Temp),
  list_to_ord_set(Temp, Val).

false_under(Val, Lit) :-
  negate(Lit, Neg), 
  member(Neg, Val).  

propagate_all(Clas, Val, []) :- 
  member((_, m, Lits), Clas), 
  exclude(false_under(Val), Lits, []). 

propagate_all(Clas, Val, [ID]) :- 
  member((ID, u, Lits), Clas), 
  exclude(false_under(Val), Lits, []). 

propagate_all(Clas, Val, IDs) :- 
  id_sta_lits(_, Clas, m, Lits, Rem), 
  exclude(false_under(Val), Lits, [Lit]), !,
  propagate_all(Rem, [Lit | Val], IDs). 

propagate_all(Clas, Val, [ID | IDs]) :- 
  id_sta_lits(ID, Clas, u, Lits, Rem), 
  exclude(false_under(Val), Lits, [Lit]), !,
  propagate_all(Rem, [Lit | Val], IDs). 

propagate(Clas, [ID | IDs], Val) :- 
  id_sta_lits(ID, Clas, _, Lits, _), 
  exclude(false_under(Val), Lits, Rem), 
  ( 
    Rem = [] ;
    (
      Rem = [Lit], 
      propagate(Clas, IDs, [Lit | Val])
    )
  ).

pluck([Elem | List], Elem, List).

pluck([ElemA | List], ElemB, [ElemA | Rem]) :-
  pluck(List, ElemB, Rem).

undelete(Clas, Prf, [ID | IDs], NewClas, SubPrf) :- 
  member((ID, m, _), Clas), 
  undelete(Clas, Prf, IDs, NewClas, SubPrf).

undelete(Clas, [del(ID, Lits) | Prf], [ID | IDs], NewClas, SubPrf) :- 
  id_sta_lits(ID, Clas, u, Lits, Rem), 
  undelete([(ID, m, Lits) | Rem], Prf, IDs, NewClas, SubPrf).

undelete(Clas, Prf, [], Clas, Prf).

get_lits(Clas, ID, Lits) :-
  member((ID, Lits), Clas).

frat01_core(Clas, [add(ID, _) | Steps], Prf) :- 
  id_sta_lits(ID, Clas, u, _, Rem), 
  frat01_core(Rem, Steps, Prf).

frat01_core(Clas, [add(ID, _, _) | Steps], Prf) :- 
  id_sta_lits(ID, Clas, u, _, Rem), 
  frat01_core(Rem, Steps, Prf).

frat01_core(Clas, [add(ID, Lits) | Steps], Prf) :- 
  id_sta_lits(ID, Clas, m, _, Rem), 
  maplist(negate, Lits, Val),
  propagate_all(Rem, Val, IDs), 
  undelete(Rem, Prf, IDs, New, [add(ID, Lits, IDs) | SubPrf]), 
  frat01_core(New, Steps, SubPrf).

frat01_core(Clas, [add(ID, Lits, IDs) | Steps], Prf) :- 
  id_sta_lits(ID, Clas, m, _, Rem), 
  maplist(negate, Lits, Val),
  propagate(Rem, IDs, Val), 
  undelete(Rem, Prf, IDs, New, [add(ID, Lits, IDs) | SubPrf]), 
  frat01_core(New, Steps, SubPrf).

frat01_core(Clas, [orig(ID, Lits) | Steps], [orig(ID, Lits) | Prf]) :- 
  id_sta_lits(ID, Clas, m, _, Rem), 
  frat01_core(Rem, Steps, Prf).

frat01_core(Clas, [orig(ID, _) | Steps], Prf) :- 
  id_sta_lits(ID, Clas, u, _, Rem), 
  frat01_core(Rem, Steps, Prf).

frat01_core(Clas, [del(ID, Lits) | Steps], Prf) :- 
  frat01_core([(ID, Lits) | Clas], Steps, Prf).

frat01_core(Clas, [final(ID, []) | Steps], Prf) :- 
  frat01_core([(ID, m, []) | Clas], Steps, Prf).

frat01_core(Clas, [final(ID, Lits) | Steps], Prf) :- 
  \+ Lits = [],
  frat01_core([(ID, u, Lits) | Clas], Steps, Prf).

frat01_core([], [], []).

read_bytes_core(Stream, Bytes) :-
  get_code(Stream, Code),
  ( 
    Code = -1 -> 
    Bytes = [] ;
    ( Bytes = [Code | Rem],
      read_bytes_core(Stream, Rem) ) 
  ).

read_bytes(Source, Bytes) :-
  open(Source, read, Stream, [encoding(octet)]),
  read_bytes_core(Stream, Bytes),
  close(Stream).
  
read_frat0(Source, Frat0) :- 
  read_bytes(Source, Bytes),
  parse(Bytes, Frat0).

frat01(Frat0, Frat1) :- 
  reverse(Frat0, Lines),
  frat01_core([], Lines, Frat1).

read_lines_core(Stream, Lines) :-
  read_line_to_codes(Stream, Line), 
  (
    Line = end_of_file -> 
    Lines = [] ;
    ( 
      Lines = [Line | Rest],
      read_lines_core(Stream, Rest)
    )
  ).

codes_string(Codes, String) :-
  string_codes(String, Codes).

read_lines(Source, Lines) :-
  open(Source, read, Stream), 
  read_lines_core(Stream, Lines), 
  close(Stream).

string_number(Str, Num) :- 
  number_string(Num, Str).
  
line_cla(Line, Cla) :- 
  string_codes(Str, Line), 
  split_string(Str, " ", " 0", Strs), 
  maplist(string_number, Strs, Cla).

read_cnf(Source, CNF) :-
  read_lines(Source, [_ | Lines]), 
  maplist(line_cla, Lines, CNF).

is_permutation(ListA, ListB) :-
  msort(ListA, Sorted),
  msort(ListB, Sorted).

calc_id_map(_, _, Map, [], Map).
  
calc_id_map(CNF, Num, Map, [orig(ID, LitsA) | Lines], NewMap) :- 
  member((ID, _), Map) -> 
  calc_id_map(CNF, Num, Map, Lines, NewMap) ; 
  (
    nth1(Idx, CNF, LitsB), 
    is_permutation(LitsA, LitsB), 
    calc_id_map(CNF, Num, [(ID, Idx) | Map], Lines, NewMap) 
  ).

calc_id_map(CNF, Num, Map, [del(_, _) | Lines], NewMap) :- 
  calc_id_map(CNF, Num, Map, Lines, NewMap).

calc_id_map(CNF, Num, Map, [add(ID, _, _) | Lines], NewMap) :- 
  Succ is Num + 1, 
  calc_id_map(CNF, Succ, [(ID, Succ) | Map], Lines, NewMap).

update_id(Map, ID, NewID) :- 
  member((ID, NewID), Map).

flrat_core(Map, [orig(_, _) | Lines], LRAT) :- 
  flrat_core(Map, Lines, LRAT).

flrat_core(Map, [del(ID, _) | Lines], [del(NewID) | LRAT]) :-
  update_id(Map, ID, NewID),
  flrat_core(Map, Lines, LRAT).

flrat_core(Map, [add(ID, [], IDs) | _], [add(NewID, [], NewIDs)]) :-
  update_id(Map, ID, NewID),
  maplist(update_id(Map), IDs, NewIDs).

flrat_core(Map, [add(ID, Lits, IDs) | Lines], [add(NewID, Lits, NewIDs) | LRAT]) :-
  \+ Lits = [],
  update_id(Map, ID, NewID),
  maplist(update_id(Map), IDs, NewIDs),
  flrat_core(Map, Lines, LRAT).

flrat(CNF, FRAT1, LRAT) :- 
  reverse(FRAT1, Lines),
  length(CNF, Num),
  calc_id_map(CNF, Num, [], Lines, Map), 
  flrat_core(Map, Lines, LRAT).

numbers_string(Nums, Str) :-
  maplist(number_string, Nums, Strs),
  strings_concat_with(" ", Strs, Str).

lrat_strs(_, [], []).

lrat_strs(_, [add(ID, Lits, IDs) | LRAT], [Str | Strs]) :- 
  append([[ID], Lits,  [0 | IDs], [0]], Nums), 
  numbers_string(Nums, Str), 
  lrat_strs(ID, LRAT, Strs).

lrat_strs(Num, [del(ID) | LRAT], [Str | Strs]) :- 
  number_string(Num, NumStr),
  number_string(ID, IDStr),
  strings_concat_with(" ", [NumStr, "d", IDStr, "0"], Str), 
  lrat_strs(Num, LRAT, Strs).

main([CNF_Src, FRAT0_Src, Target]) :-
  read_cnf(CNF_Src, CNF),
  read_frat0(FRAT0_Src, FRAT0), !,
  frat01(FRAT0, FRAT1), !,
  flrat(CNF, FRAT1, LRAT),
  lrat_strs(0, LRAT, Strs),
  file_write_list(Target, Strs),
  true.

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).