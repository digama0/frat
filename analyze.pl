#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic].
:- [probs].

well_formed(pass).
well_formed(fail(_)).
ill_formed(STAT) :- \+ well_formed(STAT).


num_name(NUM, NAME)    :- result(NUM, _, _, DATA), nth(0, DATA, NAME).
num_cftime(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(1, DATA, TIME).
num_missing(NUM, TIME) :- result(NUM, pass, pass, DATA), nth(3, DATA, TIME).
num_fltime(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(4, DATA, TIME).
num_lfc_time(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(8, DATA, TIME).
num_cdtime(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(9, DATA, TIME).
num_dltime(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(11, DATA, TIME).
num_ldc_time(NUM, TIME)  :- result(NUM, pass, pass, DATA), nth(14, DATA, TIME).

num_ftime(NUM, TIME) :- 
  num_cftime(NUM, X),
  num_fltime(NUM, Y),
  TIME is X + Y.
num_dtime(NUM, TIME) :- 
  num_cdtime(NUM, X),
  num_dltime(NUM, Y),
  TIME is X + Y.

print_num(NUM) :-
  result(NUM, _, _, DATA), 
  print_data(DATA).

cmp_fst('<', (X,_), (Y,_)) :- X < Y, !.
cmp_fst('=', (X,_), (Y,_)) :- X = Y, !.
cmp_fst('>', (X,_), (Y,_)) :- X > Y, !.

print_data(
 [ 
   NAME, 
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
 ]
) :- 
  format('Problem name : ~w\n', NAME),
  format('DIMACS-to-FRAT time : ~w seconds\n', DIMACS_FRAT_TIME),
  format('FRAT file size : ~w bytes\n', FRAT_SIZE),
  format('Missing hints : ~w%\n', MISSING),
  format('FRAT-to-LRAT time : ~w seconds\n', FRAT_LRAT_TIME),
  format('FRAT-to-LRAT peak memory usage : ~w kb\n', FRAT_LRAT_PEAK_MEM),
  format('TEMP file size : ~w bytes\n', TEMP_SIZE),
  format('LRAT-from-FRAT file size : ~w bytes\n', FRAT_LRAT_SIZE),
  format('LRAT-from-FRAT check time : ~w seconds\n', FRAT_LRAT_CHK_C_TIME),
  format('DIMACS-to-DRAT time : ~w seconds\n', DIMACS_DRAT_TIME),
  format('DRAT file size : ~w bytes\n', DRAT_SIZE),
  format('DRAT-to-LRAT time : ~w seconds\n', DRAT_LRAT_TIME),
  format('DRAT-to-LRAT peak memory usage : ~w kb\n', DRAT_LRAT_PEAK_MEM),
  format('LRAT-from-DRAT file size : ~w bytes\n', DRAT_LRAT_SIZE),
  format('LRAT-from-DRAT check time : ~w seconds\n', DRAT_LRAT_CHK_C_TIME).
  

% data_htime(DATA, HTIME) :- nth(1, DATA, HTIME).

probs(['11pipe_11_ooo-sc2011','6s126-opt-sc2014','6s133-sc2014','6s139-sc2013','6s166-sc2013','6s169-opt-sc2014','6s20-sc2013','9dlx_vliw_at_b_iq8-sc2007','9pipe_k-sc2012','ASG_96_len112_known_last13_2_u','Grain_no_init_ver1_out200_known_last104_0_u','Grain_no_init_ver1_out200_known_last105_0_u','Haystacks-ext-12_c18','LABS_n071_goal001-sc2013','MUS-v310-4-sc2013','Mickey_out250_known_last146_0_u','Mickey_out250_known_last147_0_u','Nb51T6-sc2018','QG7a-gensys-icl001.sat05-3822.reshuffled-07-sc2007','QG7a-gensys-ukn002.sat05-3842.reshuffled-07-sc2007','SAT_dat.k100-sc2012','SAT_dat.k85-sc2013','SGI_30_60_24_40_2-dir.shuffled-as.sat03-118-sc2002','T103.2.1-sc2017','Trivium_no_init_out350_known_last142_1_u','Trivium_no_init_out350_known_last143_1_u','UTI-20-10p0-sc2009','UTI-20-5p0-sc2009','aaai10-planning-ipc5-TPP-21-step11-sc2011','ablmulub16x4o-sc2016','ablmulub2x32o-sc2016','aes_equiv_encry_3_rounds.debugged-sc2012','atco_enc1_opt2_20_12-sc2014','atco_enc3_opt2_10_12-sc2014','b1904P3-8x8c11h7UNSAT','b_unsat-sc2013','blockpuzzle_5x10_s3_free4-sc2017','blocks-blocks-36-0.120-NOTKNOWN-sc2011','blocks-blocks-37-1.130-NOTKNOWN-sc2011','bob12s06-sc2013','c6288mul.miter.shuffled-as.sat03-346-sc2002','countbitssrl032-sc2009','countbitswegner128-sc2011','crafted_n11_d6_c3_num24-sc2013',cruxmiter28seed8,cruxmiter29seed4,cruxmiter29seed9,'ctl_4291_567_2_unsat-sc2013','ctl_4291_567_2_unsat_pre-sc2013','dist6.c-sc2018','dp12u11.used-as.sat04-358-sc2004','e_rphp035_05-sc2018',eqbpdtlf12bparrc12,eqbpdtlf14bpwtcl14,eqbpwtcl10spwtcl10,eqbpwtrc10bpdtlf10,eqbpwtrc10spctbk10,eqsparcl10bpwtrc10,'ex051_9-sc2018','f10nidw-sc2012','f6nidw-sc2012','gensys-icl005.shuffled-as.sat05-3826-sc2011','gto_p60c238-sc2018','hwb-n26-01-S1957858365.shuffled-as.sat03-1622-sc2002','hwb-n26-03-S540351185.sat05-490.reshuffled-07-sc2007','hwmcc10-timeframe-expansion-k45-pdtpmspalu-tseitin-sc2011','hwmcc15deep-6s516r-k18-sc2017','hwmcc15deep-oski15a10b10s-k22-sc2017','manthey_single-ordered-initialized-w50-b7-sr2015','maxxor032-sc2011','minxorminand128-sc2009','mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07-sc2007','pb_300_10_lb_08-sc2014','ps_5000_21250_3_0_0.8_0_1.55_2-sc2017','rubikcube701-sc2017',size_4_4_4_i0418_r8,size_4_4_4_i0566_r8,size_4_4_4_i2704_r8,size_4_4_4_i3499_r8,size_4_4_4_i4096_r8,size_4_4_4_i4295_r8,size_4_4_4_i4473_r8,size_4_4_4_i4828_r8,'slp-synthesis-aes-bottom13-sc2011','smtlib-qfbv-aigs-countbits128-tseitin-sc2011','smulo032-sc2012','snw_13_8_pre-sc2016','snw_16_8_nopre-sc2016','snw_16_8_pre-sc2016','sokoban-p16.sas.ex.15-sc2016','squ_any_s09x07_c27_abio_UNS-sc2017','sv-comp19_prop-reachsafety.newton_2_2_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.newton_2_3_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.newton_2_4_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.sine_8_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.square_5_true-unreach-call_true-termination.i-witness','uniqinv47prop-sc2018']).

% second_result(94, pass, pass, ['sv-comp19_prop-reachsafety.newton_2_4_true-unreach-call_true-termination.i-witness',414.51,1750333836,79.0,181.46,177888,128410267,258984057,6.68,659.92,429387123,50.49,550292,101235442,2.52]).


pass_pass_nums(NUMS) :- findall(NUM, result(NUM, pass, pass, _), NUMS). 
pass_fail_nums(NUMS) :- findall(NUM, result(NUM, pass, fail(_), _), NUMS). 
fail_pass_nums(NUMS) :- findall(NUM, result(NUM, fail(_), pass, _), NUMS). 
fail_fail_nums(NUMS) :- findall(NUM, result(NUM, fail(_), fail(_), _), NUMS). 

total(GOAL, TOTAL) :- 
  pass_pass_nums(NUMS),
  cmap(GOAL, NUMS, VALS), 
  sum_list(VALS, TOTAL).
  
cftime_total(TIME) :- total(num_cftime, TIME).
fltime_total(TIME) :- total(num_fltime, TIME).
ftime_total(TIME) :- cftime_total(X), fltime_total(Y), TIME is X + Y.
cdtime_total(TIME) :- total(num_cdtime, TIME).
dltime_total(TIME) :- total(num_dltime, TIME).
dtime_total(TIME) :- cdtime_total(X), dltime_total(Y), TIME is X + Y.

num_total_time(NUM, TOTAL) :- 
  num_cftime(NUM, CF),
  num_fltime(NUM, FL),
  num_lfc_time(NUM, LFC),
  num_cdtime(NUM, CD), 
  num_dltime(NUM, DL), 
  num_ldc_time(NUM, LDC), 
  TOTAL is CF + FL + LFC + CD + DL + LDC.

print_total_time(NUM) :- 
  num_name(NUM, NAME),
  (
    num_total_time(NUM, TIME) ->
    format("Problem ~w (~w) : ~w\n", [NUM, NAME, TIME])
  ;
    format("Problem ~w (~w) : NA\n", [NUM, NAME])
  ), 
  false.

main :- 
  ( 
    result(NUM, _, _, _), 
    print_total_time(NUM),
    false 
  ) 
; 
  true.
  
