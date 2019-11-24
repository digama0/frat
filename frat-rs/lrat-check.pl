#!/usr/bin/env swipl

% Prolog script for checking an LRAT proof

:- initialization(main, main).
:- use_module(library(nb_hashtbl)).


%%% Auxiliary predicates %%%

maplist_idx(_, _, []).

maplist_idx(Goal, Idx, [Elem | List]) :- 
  call(Goal, Idx, Elem), 
  Succ is Idx + 1, 
  maplist_idx(Goal, Succ, List).

is_permutation(ListA, ListB) :-
  msort(ListA, Sorted),
  msort(ListB, Sorted).

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).

map_cut(_, []).

map_cut(Goal, [Elem | List]) :- 
  call(Goal, Elem), !,
  map_cut(Goal, List).
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

negate(Num, Neg) :-
  Neg is -Num.

pluck([Elem | List], Elem, List).

pluck([ElemA | List], ElemB, [ElemA | Rem]) :-
  pluck(List, ElemB, Rem).


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

read_lines(File, Lines) :-
  open(File, read, Stream), 
  read_lines_core(Stream, Lines), 
  close(Stream).

string_number(Str, Num) :- 
  number_string(Num, Str).
  
% Add elememnt X to hash table T. Ensures that T is empty at key K.
ht_add(T, K, X) :- 
  \+ nb_hashtbl_get(T, K, _),
  nb_hashtbl_set(T, K, X).

% Delete elememnt X from hash table T. Ensures that T is not empty at key K.
ht_del(T, K) :- 
  nb_hashtbl_get(T, K, _),
  nb_hashtbl_delete(T, K).

% File(+) = DIMACS file containing a SAT problem 
% Prob(-) = Hash table containing all clauses of the SAT problem, keyed by line numbers
file_prob(File, Prob, Log) :-
  read_lines(File, Lines), 
  empty_nb_hashtbl(Prob),
  lines_prob(1, Lines, Prob, Log).

lines_prob(_, [], _, _).

lines_prob(Idx, [Line | Lines], Prob, Log) :- 
  (Line = [99 | _] ; Line = [112 | _]), 
  lines_prob(Idx, Lines, Prob, Log).

lines_prob(Idx, [Line | Lines], Prob, Log) :- 
  line_strs(Line, Strs),
  maplist(string_number, Strs, Cla), 
  ht_add(Prob, Idx, Cla),
  Succ is Idx + 1, !,
  format(Log, '~w : ~w\n', [Idx, Cla]),
  lines_prob(Succ, Lines, Prob, Log).

line_strs(Line, Strs) :- 
  string_codes(Str, Line), 
  string_concat(Body, " 0", Str),
  split_string(Body, " ", "", Strs).

line_step_aux(_, ["d" | Strs], del(Nums)) :- 
  maplist(string_number, Strs, Nums).

line_step_aux(ID, Strs, add(ID, Cla, IDs)) :- 
  Strs \= ["d" | _],
  maplist(string_number, Strs, Nums), 
  append(Cla, [0 | IDs], Nums).

line_step(Line, Step) :- 
  string_codes(LineStr, Line), 
  string_concat(Str, " 0", LineStr),
  split_string(Str, " ", "", [IDStr | Strs]), 
  number_string(ID, IDStr),
  line_step_aux(ID, Strs, Step).

file_lrat(File, LRAT) :-
  read_lines(File, Lines), 
  maplist(line_step, Lines, LRAT).

has_id(IDs, (ID, _)) :-
  member(ID, IDs).

init_vas(Cla, Vas) :- 
  empty_nb_hashtbl(Vas), 
  init_vas_core(Cla, Vas).

is_neg(Num, true) :- Num < 0.
is_neg(Num, false) :- 0 =< Num.

is_pos(Num, true) :- 0 < Num.
is_pos(Num, false) :- Num =< 0.

init_vas_core([], _).

init_vas_core([Lit | Cla], Vas) :- 
  abs(Lit, Prop),
  is_neg(Lit, Val),
  ht_add(Vas, Prop, Val),
  init_vas_core(Cla, Vas).

assign_lit(Vas, Lit) :- 
  abs(Lit, Prop),
  is_pos(Lit, Val),
  ht_add(Vas, Prop, Val).

false_under(Vas, Lit) :- 
  abs(Lit, Prop),
  nb_hashtbl_get(Vas, Prop, ValA), 
  is_pos(Lit, ValB),
  ValA \= ValB.

get_unit_lit(Vas, [Lit | Prem], Unit) :- 
  false_under(Vas, Lit), 
  get_unit_lit(Vas, Prem, Unit).

get_unit_lit(Vas, [Lit | Prem], Lit) :- 
  \+ false_under(Vas, Lit), 
  map_cut(false_under(Vas), Prem).

rup_check(Clas, Vas, [ID]) :-
  nb_hashtbl_get(Clas, ID, Prem), 
  map_cut(false_under(Vas), Prem).

rup_check(Clas, Vas, [ID | IDs]) :-
  IDs \= [],
  nb_hashtbl_get(Clas, ID, Prem), 
  get_unit_lit(Vas, Prem, Lit), 
  assign_lit(Vas, Lit), 
  rup_check(Clas, Vas, IDs).

lrat_check(_, [], _).

lrat_check(Clas, [del(IDs) | LRAT], Log) :- 
  maplist(ht_del(Clas), IDs), !,
  format(Log, 'Delete clauses ~w\n', [IDs]),
  lrat_check(Clas, LRAT, Log).

lrat_check(Clas, [add(ID, Cla, IDs) | LRAT], Log) :-
  init_vas(Cla, Vas),
  rup_check(Clas, Vas, IDs), 
  ht_add(Clas, ID, Cla), !,
  format(Log, 'Add clause ~w : ~w\n', [ID, Cla]),
  lrat_check(Clas, LRAT, Log).

main([CNF_FILE, LRAT_FILE]) :-
  open("lrat-log", write, Log), 
  write(Log, "Input CNF: \n\n"),
  file_prob(CNF_FILE, PROB, Log), !,
  file_lrat(LRAT_FILE, LRAT), !,
  write(Log, "\nLRAT proof: \n\n"),
  lrat_check(PROB, LRAT, Log),
  writeln(Log, "\nProof verified\n").

% main(["/home/sk/projects/cnfs/3cnf_10_120.cnf", "test.lrat"]).