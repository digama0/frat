#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic, problems, newprobs].

write_probs(_, _, []).
write_probs(STRM, NUM, [NAME | NAMES]) :- 
  write_term_punct(STRM, num_name(NUM, NAME)),
  num_suc(NUM, SUC),
  write_probs(STRM, SUC, NAMES).

loop(_, NUM) :- 97 < NUM, !.
loop(STRM, NUM) :- 
  result(
    NUM, pass, pass, 
    [ NAME, DIMACS_FRAT_TIME, FRAT_SIZE, 
      MISSING, FRAT_LRAT_TIME, FRAT_LRAT_PEAK_MEM, 
      TEMP_SIZE, FRAT_LRAT_SIZE, FRAT_LRAT_CHK_C_TIME,
      DIMACS_DRAT_TIME, DRAT_SIZE, DRAT_LRAT_TIME, 
      DRAT_LRAT_PEAK_MEM, DRAT_LRAT_SIZE, DRAT_LRAT_CHK_C_TIME ]
  ), !, 

  format(STRM, "\n% FRAT bench, problem ~w (~w)\n\n", [NUM, NAME]),
  write_term_punct(STRM, num_df_time(NUM, DIMACS_FRAT_TIME)),
  write_term_punct(STRM, num_frat_size(NUM, FRAT_SIZE)),
  write_term_punct(STRM, num_missing(NUM, MISSING)),
  write_term_punct(STRM, num_fl_time(NUM, FRAT_LRAT_TIME)),
  write_term_punct(STRM, num_fl_mem(NUM, FRAT_LRAT_PEAK_MEM)),
  write_term_punct(STRM, num_temp_size(NUM, TEMP_SIZE)),
  write_term_punct(STRM, num_lf_size(NUM, FRAT_LRAT_SIZE)),
  write_term_punct(STRM, num_lf_check_time(NUM, FRAT_LRAT_CHK_C_TIME)),
  
      
  format(STRM, "\n% DRAT bench, problem ~w (~w)\n\n", [NUM, NAME]),
  write_term_punct(STRM, num_dd_time(NUM, DIMACS_DRAT_TIME)),
  write_term_punct(STRM, num_drat_size(NUM, DRAT_SIZE)),
  write_term_punct(STRM, num_dl_time(NUM, DRAT_LRAT_TIME)),
  write_term_punct(STRM, num_dl_mem(NUM, DRAT_LRAT_PEAK_MEM)),
  write_term_punct(STRM, num_ld_size(NUM, DRAT_LRAT_SIZE)),
  write_term_punct(STRM, num_ld_check_time(NUM, DRAT_LRAT_CHK_C_TIME)),

  num_suc(NUM, SUC),
  loop(STRM, SUC).

loop(STRM, NUM) :- 
  % num_name(NUM, NAME),
  % format(STRM, "\n% FRAT bench, problem ~w (~w)\n\n", [NUM, NAME]),
  % write(STRM, "?\n\n"),
  % format(STRM, "\n% DRAT bench, problem ~w (~w)\n\n", [NUM, NAME]),
  % write(STRM, "?\n\n"),
  num_suc(NUM, SUC),
  loop(STRM, SUC).

main :- 
  open('results.pl', write, STRM),
  write(STRM, ":- discontiguous num_df_time/2.\n:- discontiguous num_frat_size/2.\n:- discontiguous num_missing/2.\n:- discontiguous num_fl_time/2.\n:- discontiguous num_fl_mem/2.\n:- discontiguous num_temp_size/2.\n:- discontiguous num_lf_size/2.\n:- discontiguous num_lf_check_time/2.\n:- discontiguous num_dd_time/2.\n:- discontiguous num_drat_size/2.\n:- discontiguous num_dl_time/2.\n:- discontiguous num_dl_mem/2.\n:- discontiguous num_ld_size/2.\n:- discontiguous num_ld_check_time/2.\n"),
  loop(STRM, 1),
  close(STRM).
