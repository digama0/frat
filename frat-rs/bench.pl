#!/usr/bin/env swipl

:- initialization(main, main).

read_time_core(Stream, Time) :- 
  read_line_to_codes(Stream, Codes), 
  (
    Codes = end_of_file -> 
    Time = -1 ; 
    (
      append(TimeCodes, [117, 115, 101, 114 | _], Codes) -> 
      number_codes(Time, TimeCodes) ; 
      read_time_core(Stream, Time)
    )
  ).

read_time(File, Time) :- 
  open(File, read, Stream), 
  read_time_core(Stream, Time).

run_and_time(CMD, TIME) :- 
  atomic_list_concat(["time ", CMD, " 2> temp"], TIME_CMD),
  shell(TIME_CMD, _),
  read_time("temp", TIME).

main([CNF_FILE]) :- 
  atomic_list_concat(["hackdical -q ", CNF_FILE, " test.frat --lrat=true"], CNF_FRAT_CMD),
  run_and_time(CNF_FRAT_CMD, CNF_FRAT_TIME),
  size_file("test.frat", FRAT_SIZE), 
  atomic_list_concat(["cargo run --release elab ", CNF_FILE, " test.frat test0.lrat"], FRAT_LRAT_CMD),
  run_and_time(FRAT_LRAT_CMD, FRAT_LRAT_TIME),
  size_file("test.frat.temp", TEMP_SIZE), 
  size_file("test0.lrat", FRAT_LRAT_SIZE), 
  atomic_list_concat(["lrat-check ", CNF_FILE, " test0.lrat"], FRAT_LRAT_CHK_CMD),
  run_and_time(FRAT_LRAT_CHK_CMD, FRAT_LRAT_CHK_TIME),
  delete_file("test.frat"),
  delete_file("test.frat.temp"),
  delete_file("test0.lrat"),

  atomic_list_concat(["cadical -q ", CNF_FILE, " test.drat"], CNF_DRAT_CMD),
  run_and_time(CNF_DRAT_CMD, CNF_DRAT_TIME),
  size_file("test.drat", DRAT_SIZE), 
  atomic_list_concat(["drat-trim ", CNF_FILE, " test.drat -L test1.lrat"], DRAT_LRAT_CMD),
  run_and_time(DRAT_LRAT_CMD, DRAT_LRAT_TIME),
  size_file("test1.lrat", DRAT_LRAT_SIZE), 
  atomic_list_concat(["lrat-check ", CNF_FILE, " test1.lrat"], DRAT_LRAT_CHK_CMD),
  run_and_time(DRAT_LRAT_CHK_CMD, DRAT_LRAT_CHK_TIME),
  delete_file("test.drat"),
  delete_file("test1.lrat"),

  format('CNF-to-FRAT time : ~w seconds\n', CNF_FRAT_TIME),
  format('FRAT file size : ~w bytes\n', FRAT_SIZE),
  format('FRAT-to-LRAT time : ~w seconds\n', FRAT_LRAT_TIME),
  format('TEMP file size : ~w bytes\n', TEMP_SIZE),
  format('LRAT-from-FRAT file size : ~w bytes\n', FRAT_LRAT_SIZE),
  format('LRAT-from-FRAT check time : ~w bytes\n', FRAT_LRAT_CHK_TIME),

  format('CNF-to-DRAT time : ~w seconds\n', CNF_DRAT_TIME),
  format('DRAT file size : ~w bytes\n', DRAT_SIZE),
  format('DRAT-to-LRAT time : ~w seconds\n', DRAT_LRAT_TIME),
  format('LRAT-from-DRAT file size : ~w bytes\n', DRAT_LRAT_SIZE),
  format('LRAT-from-DRAT check time : ~w bytes\n', DRAT_LRAT_CHK_TIME),

  atomic_list_concat(
    [ CNF_FRAT_TIME, FRAT_SIZE, FRAT_LRAT_TIME, TEMP_SIZE, FRAT_LRAT_SIZE, FRAT_LRAT_CHK_TIME,
      CNF_DRAT_TIME, DRAT_SIZE, DRAT_LRAT_TIME, DRAT_LRAT_SIZE, DRAT_LRAT_CHK_TIME ], 
    ", ", 
    CSV
  ),
  format('CSV : ~w', CSV).
