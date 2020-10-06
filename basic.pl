num_suc(NUM, SUC) :- SUC is NUM + 1.

num_pre(NUM, PRE) :- PRE is NUM - 1.

nth(0, [ELEM | _], ELEM).
nth(NUM, [_ | LIST], ELEM) :-
  0 < NUM, 
  num_pre(NUM, PRE),
  nth(PRE, LIST, ELEM).

nth1(1, [ELEM | _], ELEM).
nth1(NUM, [_ | LIST], ELEM) :-
  1 < NUM, 
  num_pre(NUM, PRE),
  nth1(PRE, LIST, ELEM).

drop(0, LIST, LIST). 
drop(NUM, [_ | LIST], REST) :- 
  num_pre(NUM, PRE),
  drop(PRE, LIST, REST).

take(0, _, []). 
take(NUM, [ELEM | LIST], [ELEM | REST]) :- 
  num_pre(NUM, PRE),
  take(PRE, LIST, REST).

slice(DROP, TAKE, LIST, SLICE) :- 
  drop(DROP, LIST, TEMP), 
  take(TAKE, TEMP, SLICE). 

write_list([]).
write_list([ELEM | LIST]) :- writeln(ELEM), !, write_list(LIST).

write_list(_, []).
write_list(STRM, [ELEM | LIST]) :- writeln(STRM, ELEM), !, write_list(STRM, LIST).

cmap(_, []).
cmap(GOAL, [ELEM | LIST]) :- 
  call(GOAL, ELEM), !, 
  cmap(GOAL, LIST).

cmap(_, [], []).
cmap(GOAL, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, ElemA, ElemB), !, 
  cmap(GOAL, ListA, ListB). 

delete_file_if_exists(FILE) :-
  exists_file(FILE) ->
  delete_file(FILE) ; 
  true.
  
  

trace_if_debug(OPTS) :-
  member('--debug', OPTS) ->
  write("Begin tracing.\n\n"),
  guitracer,
  trace 
;
  true.

cleanup :- 
  delete_file_if_exists("temp"),
  delete_file_if_exists("frat_stats"),
  delete_file_if_exists("test.frat"),
  delete_file_if_exists("test.frat.temp"),
  delete_file_if_exists("test.lrat"),
  delete_file_if_exists("test.drat").
  
