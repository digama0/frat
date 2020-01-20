#!/usr/bin/env swipl

:- initialization(main, main).

read_time(Codes, Time) :- 
  append(TimeCodes, [117, 115, 101, 114 | _], Codes),
  number_codes(Time, TimeCodes).

read_missing(Codes, Missing) :- 
  append(_, [40 | Rest], Codes),
  append(MissingCodes, [37| _], Rest),
  number_codes(Missing, MissingCodes).

read_item_core(Goal, Stream, Item) :- 
  read_line_to_codes(Stream, Codes), 
  (
    Codes = end_of_file -> 
    (
      write("Read item fail, EOF\n"),
      false
    ) ; 
    (
      call(Goal, Codes, Item) ; 
      read_item_core(Goal, Stream, Item)
    )
  ).

read_item(Goal, File, Time) :- 
  open(File, read, Stream), 
  read_item_core(Goal, Stream, Time).

run_and_time(Strings, TIME) :- 
  atomic_list_concat(Strings, CMD),
  atomic_list_concat(["time ", CMD, " 2> temp"], TIME_CMD),
  shell(TIME_CMD, _),
  read_item(read_time, "temp", TIME).

main([CNF_FILE]) :- 
  % FRAT tests
  run_and_time(["hackdical -q ", CNF_FILE, " test.frat --lrat=true"], DIMACS_FRAT_TIME),
  size_file("test.frat", FRAT_SIZE), % test.frat
  shell("cargo run --release fratchk test.frat > temp"),
  read_item(read_missing, "temp", MISSING),

  %%% Script for FRAT0 tests %%%
  % shell("cargo run --release strip-frat test.frat test.frat0", _), % test.frat, test.frat0
  % run_and_time(["cargo run --release elab ", CNF_FILE, " test.frat0 test.lrat"], FRAT0_LRAT_TIME), % test.frat, test.frat0, test.frat0.temp, test.lrat
  % delete_file("test.frat0"),
  % delete_file("test.frat0.temp"),
  % delete_file("test.lrat"), % test.frat

  run_and_time(["cargo run --release elab ", CNF_FILE, " test.frat test.lrat"], FRAT_LRAT_TIME), % test.frat, test.frat.temp, test.lrat
  delete_file("test.frat"), % test.frat.temp, test.lrat
  size_file("test.frat.temp", TEMP_SIZE), 
  delete_file("test.frat.temp"), % test.lrat
  size_file("test.lrat", FRAT_LRAT_SIZE), 
  run_and_time(["lrat-check ", CNF_FILE, " test.lrat"], FRAT_LRAT_CHK_TIME),
  delete_file("test.lrat"), % test.frat

  %%% Script for FRAT1 tests %%%
  % shell("cargo run --release elab --full null test.frat", _), % test.frat, test.frat.temp 
  % shell("cargo run --release refrat test.frat.temp test.frat1", _), % test.frat1, test.frat.temp 
  % delete_file("test.frat.temp"), % test.frat1
  % run_and_time(["cargo run --release elab ", CNF_FILE, " test.frat1 test.lrat"], FRAT1_LRAT_TIME), % test.frat1, test.frat1.temp, test.lrat
  % delete_file("test.frat1"),
  % delete_file("test.frat1.temp"),
  % delete_file("test.lrat"), % 

  % DRAT tests
  run_and_time(["cadical -q ", CNF_FILE, " test.drat"], DIMACS_DRAT_TIME),
  size_file("test.drat", DRAT_SIZE), 
  run_and_time(["drat-trim ", CNF_FILE, " test.drat -L test.lrat"], DRAT_LRAT_TIME),
  delete_file("test.drat"), % test.lrat
  size_file("test.lrat", DRAT_LRAT_SIZE), 
  run_and_time(["lrat-check ", CNF_FILE, " test.lrat"], DRAT_LRAT_CHK_TIME),
  delete_file("test.lrat"), % 

  format('DIMACS-to-FRAT time : ~w seconds\n', DIMACS_FRAT_TIME),
  format('FRAT file size : ~w bytes\n', FRAT_SIZE),
  format('Missing hints : ~w%\n', MISSING),
  format('FRAT-to-LRAT time : ~w seconds\n', FRAT_LRAT_TIME),
  % format('FRAT0-to-LRAT time : ~w seconds\n', FRAT0_LRAT_TIME),
  % format('FRAT1-to-LRAT time : ~w seconds\n', FRAT1_LRAT_TIME),
  format('TEMP file size : ~w bytes\n', TEMP_SIZE),
  format('LRAT-from-FRAT file size : ~w bytes\n', FRAT_LRAT_SIZE),
  format('LRAT-from-FRAT check time : ~w seconds\n', FRAT_LRAT_CHK_TIME),
  format('DIMACS-to-DRAT time : ~w seconds\n', DIMACS_DRAT_TIME),
  format('DRAT file size : ~w bytes\n', DRAT_SIZE),
  format('DRAT-to-LRAT time : ~w seconds\n', DRAT_LRAT_TIME),
  format('LRAT-from-DRAT file size : ~w bytes\n', DRAT_LRAT_SIZE),
  format('LRAT-from-DRAT check time : ~w seconds\n', DRAT_LRAT_CHK_TIME),

  atomic_list_concat(
    [ DIMACS_FRAT_TIME, FRAT_SIZE, MISSING, FRAT_LRAT_TIME, % FRAT0_LRAT_TIME, FRAT1_LRAT_TIME, 
      TEMP_SIZE, FRAT_LRAT_SIZE, FRAT_LRAT_CHK_TIME,
      DIMACS_DRAT_TIME, DRAT_SIZE, DRAT_LRAT_TIME, DRAT_LRAT_SIZE, DRAT_LRAT_CHK_TIME ], 
    ", ", 
    CSV
  ),
  format('CSV : ~w', CSV).
