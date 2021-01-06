:- [basic, problems, results].

is_fail(fail(_)). 
not_fail(X) :- \+ is_fail(X).

item_not_fail(ITEM) :- 
  call(ITEM, VAL),
  not_fail(VAL).

exactly_one(ITEM) :- findall(X, call(ITEM, X), [_]), !.

well_formed(NUM) :-
  exactly_one(num_df_time(NUM)),
  exactly_one(num_frat_size(NUM)),
  exactly_one(num_missing(NUM)),
  exactly_one(num_fl_time(NUM)),
  exactly_one(num_fl_mem(NUM)),
  exactly_one(num_temp_size(NUM)),
  exactly_one(num_lf_size(NUM)),
  exactly_one(num_lf_check_time(NUM)),
  exactly_one(num_dd_time(NUM)),
  exactly_one(num_drat_size(NUM)),
  exactly_one(num_dl_time(NUM)),
  exactly_one(num_dl_mem(NUM)),
  exactly_one(num_ld_size(NUM)),
  exactly_one(num_ld_check_time(NUM)).

num_frat_vals(NUM, [DFT, FSZ, MS, FLT, FLM, TSZ, LSZ, LCT]) :-
  num_df_time(NUM, DFT),
  num_frat_size(NUM, FSZ),
  num_missing(NUM, MS),
  num_fl_time(NUM, FLT),
  num_fl_mem(NUM, FLM),
  num_temp_size(NUM, TSZ),
  num_lf_size(NUM, LSZ),
  num_lf_check_time(NUM, LCT).

num_drat_vals(NUM, [DDT, DSZ, DLT, DLM, LSZ, LCT]) :-
  num_dd_time(NUM, DDT),
  num_drat_size(NUM, DSZ),
  num_dl_time(NUM, DLT),
  num_dl_mem(NUM, DLM),
  num_ld_size(NUM, LSZ),
  num_ld_check_time(NUM, LCT).

frat_passed(NUM) :-
  item_not_fail(num_df_time(NUM)),
  item_not_fail(num_frat_size(NUM)),
  item_not_fail(num_missing(NUM)),
  item_not_fail(num_fl_time(NUM)),
  item_not_fail(num_fl_mem(NUM)),
  item_not_fail(num_temp_size(NUM)),
  item_not_fail(num_lf_size(NUM)),
  item_not_fail(num_lf_check_time(NUM)).

drat_passed(NUM) :-
  item_not_fail(num_dd_time(NUM)),
  item_not_fail(num_drat_size(NUM)),
  item_not_fail(num_dl_time(NUM)),
  item_not_fail(num_dl_mem(NUM)),
  item_not_fail(num_ld_size(NUM)),
  item_not_fail(num_ld_check_time(NUM)).

num_dfl_time(NUM, TIME) :-
 num_df_time(NUM, DF),
 num_fl_time(NUM, FL),
 TIME is DF + FL.

num_ddl_time(NUM, TIME) :-
 num_dd_time(NUM, DD),
 num_dl_time(NUM, DL),
 TIME is DD + DL.

passed(NUM) :- frat_passed(NUM), !, drat_passed(NUM).

all(NUMS) :- findall(NUM, within(1,97,NUM), NUMS).
set(NUMS) :- findall(NUM, (within(1,97,NUM), passed(NUM)), NUMS).


abrv_one(NAME, USED, ABV) :- 
  atom_codes(NAME, [FST | CODES]), 
  member(SND, CODES),
  \+ member(SND, [45, 95]),
  atom_codes(ABV, [FST, SND]), 
  \+ member(ABV, USED), !.

abrv_many([], [], _, []).
abrv_many([NUM | NUMS], [NAME | NAMES], USED, [(NUM, ABV) | PAIRS]) :-
  abrv_one(NAME, USED, ABV), 
  abrv_many(NUMS, NAMES, [ABV | USED], PAIRS). 

compare_by_ddl(ORD, NUM_A, NUM_B) :- 
  num_ddl_time(NUM_A, TIME_A),
  num_ddl_time(NUM_B, TIME_B),
  compare(ORD, TIME_A, TIME_B).

esc_us_core([], []). 
esc_us_core([95 | CODES_IN], [92, 95 | CODES_OUT]) :- !, esc_us_core(CODES_IN, CODES_OUT).
esc_us_core([CODE | CODES_IN], [CODE | CODES_OUT]) :- !, esc_us_core(CODES_IN, CODES_OUT).

esc_us(IN, OUT) :-
  atom_codes(IN, CODES_IN), 
  esc_us_core(CODES_IN, CODES_OUT), 
  atom_codes(OUT, CODES_OUT). 

print_row(NUM) :-
  num_name(NUM, NAME),
  atom_concat(NAME, '.cnf', FILE),
  num_frat_vals(NUM, FRAT_VALS),
  num_drat_vals(NUM, DRAT_VALS),
  append(FRAT_VALS, DRAT_VALS, VALS),
  atomic_list_concat([FILE | VALS], ',', ROW),
  write(ROW), nl.
  
cp_to_arch(NUM) :-
  num_name(NUM, NAME),
  atomic_list_concat(["cp probs/", NAME, ".cnf arch/", NAME, ".cnf"], CMD),
  shell(CMD).
  
