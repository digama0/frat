


num_suc(NUM, SUC) :- SUC is NUM + 1.

num_pre(NUM, PRE) :-
  0 < NUM,
  PRE is NUM - 1.

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

