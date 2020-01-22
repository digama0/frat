#!/usr/bin/env swipl

% Prolog script for parsing a FRAT proof 

:- initialization(main, main).

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

put_bytes(_, []).

put_bytes(Stream, [Byte | Bytes]) :- 
  put_byte(Stream, Byte),
  put_bytes(Stream, Bytes).

read_until_zero(Stream, Bytes) :- 
  get_code(Stream, Byte),
  ( 
    Byte = 0 -> 
    (Bytes = []) ;
    ( 
      Bytes = [Byte | Rest], 
      read_until_zero(Stream, Rest)
    )
  ).

read_step_core(a, Proof, Step) :-
  read_until_zero(Proof, BytesA), 
  bytes_nums(BytesA, [ID | Nums]),
  maplist(num_lit, Nums, Lits),
  ( 
    peek_char(Proof, l) -> 
    (
      get_byte(Proof, _), 
      read_until_zero(Proof, BytesB), 
      bytes_nums(BytesB, IDS),
      Step = add(ID, Lits, IDS)
    ) ; 
    Step = add(ID, Lits)
  ).

read_step_core(d, Proof, del(ID, Lits)) :-
  read_until_zero(Proof, Bytes), 
  bytes_nums(Bytes, [ID | Nums]),
  maplist(num_lit, Nums, Lits).

read_step_core(f, Proof, fin(ID, Lits)) :-
  read_until_zero(Proof, Bytes), 
  bytes_nums(Bytes, [ID | Nums]),
  maplist(num_lit, Nums, Lits).

read_step_core(o, Proof, ori(ID, Lits)) :-
  read_until_zero(Proof, Bytes), 
  bytes_nums(Bytes, [ID | Nums]),
  maplist(num_lit, Nums, Lits).

read_step_core(r, Proof, rel(IDs)) :-
  read_until_zero(Proof, Bytes), 
  bytes_nums(Bytes, IDs).

read_step(Proof, Step) :-
  get_char(Proof, Rule),
  ( 
    Rule = end_of_file -> 
    Step = end_of_proof ;
    read_step_core(Rule, Proof, Step)
  ).

strip(add(ID, Lits, _), add(ID, Lits)).

strip(Step, Step) :-
  Step \= add(_, _, _).

aux(FRAT) :- 
  read_step(FRAT, Step),
  (
    Step = end_of_proof -> 
    true ;
    (
      % strip(Step, NewStep),
      % step_bytes(NewStep, Bytes),
      % put_bytes(FRAT0, Bytes),
      format('~w\n', Step),
      aux(FRAT)
    )
  ).

main([FRAT_file]) :-
  open(FRAT_file, read, FRAT, [encoding(octet)]),
  % open(FRAT0_file, write, FRAT0, [encoding(octet)]),
  aux(FRAT),
  close(FRAT).
  %close(FRAT0).

% strings_concat([], "").
% 
% strings_concat([Str | Strs], NewStr) :- 
%   strings_concat(Strs, TempStr), 
%   string_concat(Str, TempStr, NewStr). 
% 
% strings_concat_with(_, [], "").
% 
% strings_concat_with(_, [Str], Str).
% 
% strings_concat_with(Div, [Str | Strs], Result) :-
%   strings_concat_with(Div, Strs, TempStr),
%   strings_concat([Str, Div, TempStr], Result).