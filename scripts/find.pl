#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].

line_ent(LINE, (BENCHMARK, SOLVER, CONFIG, SOLV_TIME, STAT, RESULT, VERIF_TIME, VERIF_RST)) :-
  split_string(LINE, ",", " ", [BENCHMARK,SOLVER,CONFIG,SOLV_TIME,STAT,RESULT,VERIF_TIME,VERIF_RST]).

/*
bench_unseen(BENCH, SEEN) :- \+ get_assoc(BENCH, SEEN, _).

ent_bench(STR, BENCH) :- ent_items(STR, BENCH, _, _, _, _, _, _, _, _, _, _, _, _).
ent_result(STR, RST) :- ent_items(STR, _, _, _, _, _, RST, _, _, _, _, _, _, _).

bench_seen(BENCH, ASC) :- get_assoc(BENCH, ASC, c).
bench_new(BENCH, ASC) :- \+ bench_seen(BENCH, ASC).

ent_name(ENTRY, NAME) :-
  ent_bench(ENTRY, BENCH), 
  (atom_concat('new/', TEMP, BENCH) ; atom_concat('old/', TEMP, BENCH)), !, 
  atom_concat(NAME, '.cnf.bz2', TEMP).
  
loop(STRM, ASC, CNT) :-
  read_line_to_string(STRM, ENTRY), 
  (
    ENTRY = end_of_file -> 
    writeln("EOF reached."),
    true
  ;
    ent_bench(ENTRY, BENCH),
    ( 
      bench_seen(BENCH, ASC) ->
      ASC_N = ASC,
      CNT_N = CNT 
    ;
      ent_result(ENTRY, "UNSAT") ->
      CNT_N is CNT + 1,
      format("New unsat bench found = ~w\n", BENCH),
      format("Unsat bench count = ~w\n", CNT_N),
      put_assoc(BENCH, ASC, c, ASC_N)
    ;
      ent_result(ENTRY, RST),
      format("Bench ~w is new, but not unsat. Result = ~w\n", [BENCH, RST]),
      ASC_N = ASC,
      CNT_N = CNT 
    ),
    loop(STRM, ASC_N, CNT_N)
  ).

get_new(STRM, SEEN, NEW) :- 
  read_line_to_string(STRM, ENTRY), 
  (
    ENTRY = end_of_file -> 
    writeln("EOF reached.")
  ;
    ent_bench(ENTRY, BENCH), 
    (
      bench_unseen(BENCH, SEEN) ->  
      (
        atom_concat('new/', NAME, BENCH) -> 
        put_assoc(BENCH, SEEN, c, SEEN_NEW),
        get_new(STRM, SEEN_NEW, TAIL),  
        NEW = [NAME | TAIL]
      ;
        % format("Bench is unseen, but not new = ~w\n", BENCH),
        get_new(STRM, SEEN, NEW) 
      )
    ;
      get_new(STRM, SEEN, NEW) 
    )
  ).



get_bench_result_pairs(STRM, SEEN, PAIRS) :- 
  read_line_to_string(STRM, ENTRY), 
  (
    ENTRY = end_of_file -> 
    writeln("EOF reached.")
  ;
    ent_name(ENTRY, NAME), 
    (
      get_assoc(NAME, SEEN, _) ->  
      get_bench_result_pairs(STRM, SEEN, PAIRS) 
    ;
      put_assoc(NAME, SEEN, c, SEEN_NEW),
      ent_result(ENTRY, RST),
      get_bench_result_pairs(STRM, SEEN_NEW, TAIL), 
      PAIRS = [(NAME, RST) | TAIL]
    )
  ).



  

*/

print_lth(LIST) :-
  length(LIST, LTH),
  format("Length of list = ~w\n", LTH).

trace_if_debug(OPTS) :-
  member('--debug', OPTS) ->
  write("Begin tracing.\n\n"),
  guitracer,
  trace 
;
  true.


fst((X, _), X).
snd((_, X), X).


% pair_unsat_name((NAME, "UNSAT"), NAME).
% pair_sat_name((NAME, "SAT"), NAME).
% pair_unknown_name((NAME, "UNKNOWN"), NAME).
% pair_error_name((NAME, "ERROR"), NAME).

strm_ents(STRM, ENTS) :- 
  read_line_to_string(STRM, LINE), 
  (
    LINE = end_of_file -> 
    writeln("EOF reached.")
  ;
    line_ent(LINE, ENT),
    ENTS = [ENT | REST],
    strm_ents(STRM, REST) 
  ).
  
ents(ENTS) :- 
  open('results2019.csv', read, STRM), 
  read_line_to_string(STRM, FST),
  format("First line = ~w\n", FST),
  strm_ents(STRM, ENTS),
  close(STRM).

ent_bench((BENCH, _), BENCH).
ent_rst((_,_,_,_,_,RST,_), RST).
ent_vrst((_,_,_,_,_,_,_,VRST), VRST).

by_cadical_default((_,"CaDiCaL","default",_)).

is_unsat(ENT) :- ent_rst(ENT, "UNSAT").

ent_rst_pair(ENT, (RST, VRST)) :-
  ent_rst(ENT, RST), 
  ent_vrst(ENT, VRST).


path_files(PATH, [PATH]) :- 
  exists_file(PATH). 

path_files(PATH, FILES) :- 
  exists_directory(PATH), 
  folder_paths(PATH, TEMP), 
  maplist(directory_file_path(PATH), TEMP, PATHS),
  maplist(path_files, PATHS, FILESS),
  append(FILESS, FILES).

folder_paths(FOLDER, PATHS) :- 
  directory_files(FOLDER, X), 
  delete(X, '.', Y),
  delete(Y, '..', PATHS).
 
showlist(LIST) :-
  write_list(LIST),
  print_lth(LIST).

path_filename(PATH, FILENAME) :- 
  atom_codes(PATH, X), 
  append(_, [47 | Y], X), 
  \+ member(47, Y), !, 
  atom_codes(FILENAME, Y), !.

path_stem(EXT, PATH, STEM) :- 
  path_filename(PATH, FILENAME), 
  atom_concat(TEMP, EXT, FILENAME), 
  atom_concat(STEM, '.', TEMP). 
  
% 
% 
% stem_dup_check(_, []).
% stem_dup_check(STEMS, [PATH | LIST]) :-
%   path_stem(PATH, STEM), !, 
%   (
%     member(STEM, STEMS) -> 
%     format("DUP = ~w\n", PATH),
%     stem_dup_check(STEMS, LIST)
%   ;
%     stem_dup_check([STEM | STEMS], LIST)
%   ).

  
eligible(NAMES, FILE) :- 
  path_stem('cnf.xz', FILE, NAME), 
  member(NAME, NAMES).

mv_sat(FILE) :-
  path_filename(FILE, FILENAME), 
  atom_concat('./set/', FILENAME, DST),
  mv(FILE, DST).

main(OPTS) :- 
  path_files("test", FILES), !,
  cmap(path_stem('cnf'), FILES, NAMES),
  sort(NAMES, SORTED), 
  write_list(SORTED),
  open('probs.txt', write, STRM), 
  write_term(STRM, SORTED, [fullstop(true), nl(true), quoted(true)]),
  close(STRM).
  
%   trace_if_debug(OPTS),
%   ents(ENTS), !,
%   include(by_cadical_default, ENTS, TEMP),
%   include(is_unsat, TEMP, SET),
%   maplist_cut(ent_bench, SET, BENCHES),
%   maplist_cut(path_stem('cnf.bz2'), BENCHES, UNSAT_NAMES), !,
%   path_files("sr2019", FILES), !,
%   include(eligible(UNSAT_NAMES), FILES, TARGET),
%   maplist_cut(mv_sat, TARGET),
%   true.

