#!/usr/bin/env swipl

% Prolog script for reading in and verifying a reversed FRAT proof.

:- initialization(main, main).

read_bytes(Stream, Bytes) :-
  get_code(Stream, Code),
  ( 
    Code = -1 -> 
    ( close(Stream), Bytes = [] ) ;
    ( Bytes = [Code | Rem],
      read_bytes(Stream, Rem) ) 
  ).

write_list([]).

write_list([Elem | List]) :-
  write(Elem),
  write("\n"),
  write_list(List).

sep_zero([0 | Bytes], [], Bytes).

sep_zero([Byte | Bytes], [Byte | BytesA], BytesB) :- 
  Byte \= 0,
  sep_zero(Bytes, BytesA, BytesB).

parse([], []).

parse([111, ID | Bytes], [orig(ID, Lits) | Lines]) :- 
  sep_zero(Bytes, LitBytes, RemBytes),
  maplist(decode, LitBytes, Lits),
  parse(RemBytes, Lines).

parse([97, ID | Bytes], [add(ID, Lits) | Lines]) :- 
  sep_zero(Bytes, LitBytes, RemBytes),
  maplist(decode, LitBytes, Lits),
  parse(RemBytes, Lines).

parse([102, ID | Bytes], [final(ID, Lits) | Lines]) :- 
  sep_zero(Bytes, LitBytes, RemBytes),
  maplist(decode, LitBytes, Lits),
  parse(RemBytes, Lines).

parse([108 | Bytes], [add(ID, Lits, IDs) | Lines]) :- 
  sep_zero(Bytes, IDs, RemBytes),
  parse(RemBytes, [add(ID, Lits) | Lines]).

decode(Byte, Num) :-
  Num is div(Byte, 2),
  0 is Byte mod 2.

decode(Byte, Num) :-
  Quo is div(Byte, 2),
  Num is -Quo,
  1 is Byte mod 2.

sep_finals([final(ID, Lits) | Lines], [(ID, Lits) | Fins], Rem) :- 
  sep_finals(Lines, Fins, Rem).

sep_finals(Lines, [], Lines).

remove_cla(ID, [(ID, _) | IDClas], IDClas).

remove_cla(ID, [IDCla | IDClas], [IDCla | Rem]) :-
  remove_cla(ID, IDClas, Rem).

negate(Num, Neg) :-
  Neg is -Num.

satisfied(Val, Cla) :- 
  member(Lit, Val),
  member(Lit, Cla).

union([], []).

union([List | Lists], Union) :- 
  union(Lists, TempUnion),
  union(List, TempUnion, Union).

snd((_, X), X).

unit([_]).

remove(Elem, List, NewList) :-
  delete(List, Elem, NewList).

update(Val, Cla, NewCla) :-
  exclude(negated(Val), Cla, NewCla).

negated(Val, Lit) :- 
  negate(Lit, Neg), 
  member(Neg, Val).

propagate(Val, _) :- 
  member(Num, Val), 
  0 < Num,
  negate(Num, Neg), 
  member(Neg, Val).

propagate(Val, Clas) :- 
  exclude(satisfied(Val), Clas, ClasA),
  maplist(update(Val), ClasA, ClasB),
  (
    member([], ClasB) ; 
    ( 
      partition(unit, ClasB, Units, ClasC), 
      Units \= [], 
      union([Val | Units], NewVal), 
      propagate(NewVal, ClasC)
    )
  ).

check(IDClas, [add(ID, Lits) | Steps]) :- 
  remove_cla(ID, IDClas, NewIDClas), 
  maplist(snd, NewIDClas, Clas),
  maplist(negate, Lits, Val),
  propagate(Val, Clas),
  check(NewIDClas, Steps).

check(IDClas, [add(ID, Lits, IDs) | Steps]) :- 
  remove_cla(ID, IDClas, NewIDClas), 
  maplist(find_cla(NewIDClas), IDs, Clas),
  maplist(negate, Lits, Val),
  propagate(Val, Clas),
  check(NewIDClas, Steps).

check(IDClas, [orig(ID, _) | Steps]) :- 
  remove_cla(ID, IDClas, NewIDClas), 
  check(NewIDClas, Steps).

check([], []).

find_cla(IDClas, ID, Cla) :-
  member((ID, Cla), IDClas).

main([Source]) :-
  open(Source, read, Stream, [encoding(octet)]),
  read_bytes(Stream, Bytes),
  parse(Bytes, Lines),
  write_list(Lines),
  sep_finals(Lines, Fins, Steps),
  write("\nSteps : \n"),
  write_list(Steps),
  write("\nFinal clauses : \n"),
  write_list(Fins),
  check(Fins, Steps),
  write("\nProof verified.").
