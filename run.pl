#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic, results].



nmap(_, NUM, UB) :- UB =< NUM, !.
nmap(GOAL, NUM, UB) :- 
  call(GOAL, NUM), !, 
  num_suc(NUM, SUC),
  nmap(GOAL, SUC, UB).

print_missing(NUM) :-
  (num_df_time(NUM, _) ; format("FRAT ~w missing.\n", NUM)), !,
  (num_dd_time(NUM, _) ; format("DRAT ~w missing.\n", NUM)).

main :- nmap(print_missing, 1, 98).
