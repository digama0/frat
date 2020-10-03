#!/usr/bin/env swipl

% Prolog script for running benchmarks comparing FRAT-rs with DRAT-trim. 
% The script calls the following programs, which should be available in your enviroment: 
%
%   cadical : the CaDiCaL SAT solver (https://github.com/arminbiere/cadical)
%   hackdical : the modified, FRAT-producing version of CaDiCaL (https://github.com/digama0/cadical)
%   drat-trim : the DRAT proof checker (https://github.com/marijnheule/drat-trim)
%   lrat-checker : the LRAT checker included in DRAT-trim
%   frat-rs : the FRAT toolchain (https://github.com/digama0/frat)
%
% In addition, you need SWI-Prolog to run the script itself (https://www.swi-prolog.org/).
%
% Usage : bench.pl /path/to/DIMACS/file

:- initialization(main, main).

:- [basic, probs].

read_time(String, Time) :- 
  string_concat("\tUser time (seconds): ", TimeString, String),
  number_string(Time, TimeString).

read_missing(String, Missing) :- 
  split_string(String, " ", "", [_, "missing", "proofs", Temp0]), 
  string_concat("(", Temp1, Temp0), 
  string_concat(MissingStr, "%)", Temp1), 
  number_string(Missing, MissingStr).

read_peak_mem(String, PeakMem) :- 
  string_concat("\tMaximum resident set size (kbytes): ", PeakMemStr, String), 
  number_string(PeakMem, PeakMemStr).

read_avg_mem(String, AvgMem) :- 
  string_concat("\tAverage resident set size (kbytes): ", AvgMemStr, String), 
  number_string(AvgMem, AvgMemStr).

read_item_core(Goal, Stream, Item) :- 
  read_line_to_string(Stream, String), 
  (
    String = end_of_file -> 
    (
      write("Read item fail, EOF\n"),
      false
    ) ; 
    (
      call(Goal, String, Item) ; 
      read_item_core(Goal, Stream, Item)
    )
  ).

read_item(Goal, File, Time) :- 
  open(File, read, Stream), 
  read_item_core(Goal, Stream, Time).

run(Strings) :- 
  atomic_list_concat(Strings, CMD),
  shell(CMD, _).

run_and_time(Strings, TIME) :- 
  atomic_list_concat(Strings, CMD),
  atomic_list_concat(["time -v ", CMD, " 2> temp"], TIME_CMD),
  shell(TIME_CMD, _),
  read_item(read_time, "temp", TIME),
  delete_file("temp").

run_and_measure(Strings, TIME, PEAK_MEM) :- 
  atomic_list_concat(Strings, CMD),
  format('Using command ~w\n', CMD),
  atomic_list_concat(["time -v ", CMD, " 2> temp"], TIME_CMD),
  shell(TIME_CMD, _),
  read_item(read_time, "temp", TIME),
  read_item(read_peak_mem, "temp", PEAK_MEM),
  delete_file("temp").

print_and_save(TERM) :- 
  open('result', append, STRM),
  write_term(TERM, [fullstop(true), nl(true), quoted(true)]),
  write_term(STRM, TERM, [fullstop(true), nl(true), quoted(true)]),
  close(STRM).

cleanup :- 
  delete_file_if_exists("temp"),
  delete_file_if_exists("frat_stats"),
  delete_file_if_exists("test.frat"),
  delete_file_if_exists("test.frat.temp"),
  delete_file_if_exists("test.lrat"),
  delete_file_if_exists("test.drat").
  
bench(CNF_NAME) :- 
  cleanup,
  atomic_list_concat(['probs/', CNF_NAME, '.cnf'], CNF_FILE),
  
  format("\n>>>>>>>>>> Begin bench with problem = ~w <<<<<<<<<<\n\n", CNF_NAME),

  write("\n------- Running Hackdical -------\n\n"),
  run_and_time(["./hackdical -t 5000 -q ", CNF_FILE, " test.frat --lrat=true"], DIMACS_FRAT_TIME),
  format('% DIMACS-to-FRAT time : ~w seconds\n', DIMACS_FRAT_TIME),
  size_file("test.frat", FRAT_SIZE), % test.frat
  format('% FRAT file size : ~w bytes\n', FRAT_SIZE),

  write("\n------- Obtaining FRAT file statistics  -------\n\n"),
  shell("./frat-rs fratchk test.frat > frat_stats", _),
  read_item(read_missing, "frat_stats", MISSING),
  format('% Missing hints : ~w%\n', MISSING),
  write("\nFrat statistics:\n\n"), 
  shell("cat frat_stats", _),
  delete_file("frat_stats"),

  write("\n------- Elaborating FRAT to LRAT -------\n\n"),
  run_and_measure(["./frat-rs elab ", CNF_FILE, " test.frat test.lrat"], FRAT_LRAT_TIME, FRAT_LRAT_PEAK_MEM), % test.frat, test.frat.temp, test.lrat
  delete_file("test.frat"), % test.frat.temp, test.lrat
  format('% FRAT-to-LRAT time : ~w seconds\n', FRAT_LRAT_TIME),
  format('% FRAT-to-LRAT peak memory usage : ~w kb\n', FRAT_LRAT_PEAK_MEM),

  size_file("test.frat.temp", TEMP_SIZE), 
  delete_file("test.frat.temp"), % test.lrat
  format('% TEMP file size : ~w bytes\n', TEMP_SIZE),
  size_file("test.lrat", FRAT_LRAT_SIZE), 
  format('% LRAT-from-FRAT file size : ~w bytes\n', FRAT_LRAT_SIZE),

  write("\n------- Checking LRAT from FRAT (C) -------\n\n"),
  run_and_time(["./lrat-check ", CNF_FILE, " test.lrat"], FRAT_LRAT_CHK_C_TIME),
  format('% LRAT-from-FRAT check time (C) : ~w seconds\n', FRAT_LRAT_CHK_C_TIME),

  write("\n------- Checking LRAT from FRAT (Rust) -------\n\n"),
  run(["./frat-rs lratchk ", CNF_FILE, " test.lrat 2>&1"]), 
  delete_file("test.lrat"), % test.frat

  write("\n------- Running Cadical -------\n\n"),
  run_and_time(["./cadical -t 5000 -q ", CNF_FILE, " test.drat"], DIMACS_DRAT_TIME),
  format('% DIMACS-to-DRAT time : ~w seconds\n', DIMACS_DRAT_TIME),
  size_file("test.drat", DRAT_SIZE), 
  format('% DRAT file size : ~w bytes\n', DRAT_SIZE),


  write("\n------- Elaborating DRAT to LRAT  -------\n\n"),
  run_and_measure(["./drat-trim ", CNF_FILE, " test.drat -L test.lrat"], DRAT_LRAT_TIME, DRAT_LRAT_PEAK_MEM),
  delete_file("test.drat"), % test.lrat
  format('% DRAT-to-LRAT time : ~w seconds\n', DRAT_LRAT_TIME),
  format('% DRAT-to-LRAT peak memory usage : ~w kb\n', DRAT_LRAT_PEAK_MEM),
  size_file("test.lrat", DRAT_LRAT_SIZE), 
  format('% LRAT-from-DRAT file size : ~w bytes\n', DRAT_LRAT_SIZE),

  write("\n------- Checking LRAT from DRAT (C) -------\n\n"),
  run_and_time(["./lrat-check ", CNF_FILE, " test.lrat"], DRAT_LRAT_CHK_C_TIME),
  format('% LRAT-from-DRAT check time (C) : ~w seconds\n', DRAT_LRAT_CHK_C_TIME),

  write("\n------- Checking LRAT from DRAT (Rust) -------\n\n"),
  run(["./frat-rs lratchk ", CNF_FILE, " test.lrat 2>&1"]),
  delete_file("test.lrat"), % 

  write("\n------- Bench Statistics -------\n\n"),
  format('Problem name : ~w\n', CNF_NAME),
  format('DIMACS-to-FRAT time : ~w seconds\n', DIMACS_FRAT_TIME),
  format('FRAT file size : ~w bytes\n', FRAT_SIZE),
  format('Missing hints : ~w%\n', MISSING),
  format('FRAT-to-LRAT time : ~w seconds\n', FRAT_LRAT_TIME),
  format('FRAT-to-LRAT peak memory usage : ~w kb\n', FRAT_LRAT_PEAK_MEM),
  format('TEMP file size : ~w bytes\n', TEMP_SIZE),
  format('LRAT-from-FRAT file size : ~w bytes\n', FRAT_LRAT_SIZE),
  format('LRAT-from-FRAT check time (C) : ~w seconds\n', FRAT_LRAT_CHK_C_TIME),
  format('DIMACS-to-DRAT time : ~w seconds\n', DIMACS_DRAT_TIME),
  format('DRAT file size : ~w bytes\n', DRAT_SIZE),
  format('DRAT-to-LRAT time : ~w seconds\n', DRAT_LRAT_TIME),
  format('DRAT-to-LRAT peak memory usage : ~w kb\n', DRAT_LRAT_PEAK_MEM),
  format('LRAT-from-DRAT file size : ~w bytes\n', DRAT_LRAT_SIZE),
  format('LRAT-from-DRAT check time (C) : ~w seconds\n', DRAT_LRAT_CHK_C_TIME),
  RESULT = 
    result(
      CNF_NAME, 
      DIMACS_FRAT_TIME, 
      FRAT_SIZE, 
      MISSING, 
      FRAT_LRAT_TIME, 
      FRAT_LRAT_PEAK_MEM, 
      TEMP_SIZE, 
      FRAT_LRAT_SIZE, 
      FRAT_LRAT_CHK_C_TIME,
      DIMACS_DRAT_TIME, 
      DRAT_SIZE, 
      DRAT_LRAT_TIME, 
      DRAT_LRAT_PEAK_MEM,
      DRAT_LRAT_SIZE, 
      DRAT_LRAT_CHK_C_TIME 
    ), 
  print_and_save(RESULT),
  true.

main([DROP, TAKE]) :- 
  probs(PROBS),
  atom_number(DROP, DROP_NUM),
  atom_number(TAKE, TAKE_NUM),
  slice(DROP_NUM, TAKE_NUM, PROBS, SET),
  format("Using test set = ~w\n", [SET]), !,
  cmap(bench, SET).
