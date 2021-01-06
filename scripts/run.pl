#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic, results, problems].

nmap(_, NUM, UB) :- UB =< NUM, !.
nmap(GOAL, NUM, UB) :- 
  call(GOAL, NUM), !, 
  num_suc(NUM, SUC),
  nmap(GOAL, SUC, UB).

is_failed(NUM) :- is_failed_core(NUM), !.

is_failed_core(NUM) :- 
  num_df_time(NUM, fail(_)) ;
  num_frat_size(NUM, fail(_)) ;
  num_missing(NUM, fail(_)) ;
  num_fl_time(NUM, fail(_)) ;
  num_fl_mem(NUM, fail(_)) ;
  num_temp_size(NUM, fail(_)) ;
  num_lf_size(NUM, fail(_)) ;
  num_lf_check_time(NUM, fail(_)).

print_time(NUM) :-
  num_df_time(NUM, TIME),
  format("ID = ~w, TIME = ~w\n", [NUM, TIME]).

print_fail(NUM) :-
  is_failed(NUM) -> 
  num_name(NUM, NAME),
  format("NAME : ~w\n", [NAME]), 
  format("ID : ~w\n", [NUM]), 
  num_df_time(NUM, TIME),
  format("TIME : ~w\n", [TIME]), 
  num_frat_size(NUM, SIZE), 
  format("SIZE : ~w\n\n", [SIZE])
;
  true.

main :- nmap(print_fail, 1, 98).
