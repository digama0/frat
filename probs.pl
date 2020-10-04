% AWS Instance used = c5a.large

probs(['11pipe_11_ooo-sc2011','6s126-opt-sc2014','6s133-sc2014','6s139-sc2013','6s166-sc2013','6s169-opt-sc2014','6s20-sc2013','9dlx_vliw_at_b_iq8-sc2007','9pipe_k-sc2012','ASG_96_len112_known_last13_2_u','Grain_no_init_ver1_out200_known_last104_0_u','Grain_no_init_ver1_out200_known_last105_0_u','Haystacks-ext-12_c18','LABS_n071_goal001-sc2013','MUS-v310-4-sc2013','Mickey_out250_known_last146_0_u','Mickey_out250_known_last147_0_u','Nb51T6-sc2018','QG7a-gensys-icl001.sat05-3822.reshuffled-07-sc2007','QG7a-gensys-ukn002.sat05-3842.reshuffled-07-sc2007','SAT_dat.k100-sc2012','SAT_dat.k85-sc2013','SGI_30_60_24_40_2-dir.shuffled-as.sat03-118-sc2002','T103.2.1-sc2017','Trivium_no_init_out350_known_last142_1_u','Trivium_no_init_out350_known_last143_1_u','UTI-20-10p0-sc2009','UTI-20-5p0-sc2009','aaai10-planning-ipc5-TPP-21-step11-sc2011','ablmulub16x4o-sc2016','ablmulub2x32o-sc2016','aes_equiv_encry_3_rounds.debugged-sc2012','atco_enc1_opt2_20_12-sc2014','atco_enc3_opt2_10_12-sc2014','b1904P3-8x8c11h7UNSAT','b_unsat-sc2013','blockpuzzle_5x10_s3_free4-sc2017','blocks-blocks-36-0.120-NOTKNOWN-sc2011','blocks-blocks-37-1.130-NOTKNOWN-sc2011','bob12s06-sc2013','c6288mul.miter.shuffled-as.sat03-346-sc2002','countbitssrl032-sc2009','countbitswegner128-sc2011','crafted_n11_d6_c3_num24-sc2013',cruxmiter28seed8,cruxmiter29seed4,cruxmiter29seed9,'ctl_4291_567_2_unsat-sc2013','ctl_4291_567_2_unsat_pre-sc2013','dist6.c-sc2018','dp12u11.used-as.sat04-358-sc2004','e_rphp035_05-sc2018',eqbpdtlf12bparrc12,eqbpdtlf14bpwtcl14,eqbpwtcl10spwtcl10,eqbpwtrc10bpdtlf10,eqbpwtrc10spctbk10,eqsparcl10bpwtrc10,'ex051_9-sc2018','f10nidw-sc2012','f6nidw-sc2012','gensys-icl005.shuffled-as.sat05-3826-sc2011','gto_p60c238-sc2018','hwb-n26-01-S1957858365.shuffled-as.sat03-1622-sc2002','hwb-n26-03-S540351185.sat05-490.reshuffled-07-sc2007','hwmcc10-timeframe-expansion-k45-pdtpmspalu-tseitin-sc2011','hwmcc15deep-6s516r-k18-sc2017','hwmcc15deep-oski15a10b10s-k22-sc2017','manthey_single-ordered-initialized-w50-b7-sr2015','maxxor032-sc2011','minxorminand128-sc2009','mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07-sc2007','pb_300_10_lb_08-sc2014','ps_5000_21250_3_0_0.8_0_1.55_2-sc2017','rubikcube701-sc2017',size_4_4_4_i0418_r8,size_4_4_4_i0566_r8,size_4_4_4_i2704_r8,size_4_4_4_i3499_r8,size_4_4_4_i4096_r8,size_4_4_4_i4295_r8,size_4_4_4_i4473_r8,size_4_4_4_i4828_r8,'slp-synthesis-aes-bottom13-sc2011','smtlib-qfbv-aigs-countbits128-tseitin-sc2011','smulo032-sc2012','snw_13_8_pre-sc2016','snw_16_8_nopre-sc2016','snw_16_8_pre-sc2016','sokoban-p16.sas.ex.15-sc2016','squ_any_s09x07_c27_abio_UNS-sc2017','sv-comp19_prop-reachsafety.newton_2_2_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.newton_2_3_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.newton_2_4_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.sine_8_true-unreach-call_true-termination.i-witness','sv-comp19_prop-reachsafety.square_5_true-unreach-call_true-termination.i-witness','uniqinv47prop-sc2018']).


result(3,  fail, '6s133-sc2014', ["bad LRAT proof"]).


result(6,  pass, '6s169-opt-sc2014', [13.3,74647474,7.2,1.29,17808,5710587,11854416,0.27,13.38,31779940,2.89,109316,12815434,0.28]). % 6
result(7,  pass, '6s20-sc2013', [476.18,1407095049,30.2,132.98,105952,455296630,938404857,19.82,446.32,522070738,573.25,1147440,983311521,21.51]). %7

result(9,  pass, '9pipe_k-sc2012', [149.96,799568860,29.8,448.78,573440,131885144,259688428,5.95,140.79,614210501,163.09,798864,259068768,5.88]).
result(10, pass, 'ASG_96_len112_known_last13_2_u', [472.95,1039615903,2.0,89.03,22192,926821766,1988383800,39.72,425.96,99511564,343.02,1416436,1879597208,39.11]).
result(11, redo, 'Grain_no_init_ver1_out200_known_last104_0_u', []).
result(12, pass, 'Grain_no_init_ver1_out200_known_last105_0_u',[328.98,797597935,0.8,54.02,38276,498093385,1030223801,22.14,312.53,317575705,530.75,1270992,1101518412,23.39]).
result(13, pass, 'Haystacks-ext-12_c18',[236.33,1076316068,0.1,46.39,78320,499351400,1077755946,24.47,221.78,832679184,344.39,1962832,1098475302,24.65]).


result(16, redo, 'Mickey_out250_known_last146_0_u', []).

result(21, fail, 'SAT_dat.k100-sc2012', ["Clause already watched"]).


result(31, pass, 'ablmulub2x32o-sc2016', [214.03, 1361518641, 3.0, 94.56, 46136, 905547190, 1929160191, 39.46, 192.53, 355909293, 455.22, 1813288, 2127147566, 42.25]).


result(42,pass,'countbitssrl032-sc2009',[79.26,566957064,26.1,51.0,39008,246031234,544633798,11.6,45.65,58865732,65.17,491808,647189009,13.37]).
result(43,pass,'countbitswegner128-sc2011',[979.51,6500565952,15.4,433.29,297196,1250511905,2490934104,49.26,921.14,3421873627,867.83,3609716,0,0.11]).
result(44,pass,'crafted_n11_d6_c3_num24-sc2013',[185.74,1188411153,30.7,200.05,838584,337423671,679208949,14.21,155.92,825607169,202.31,1401216,654108854,13.58]).
result(45,pass,cruxmiter28seed8,[249.95,653701812,0.4,47.73,38892,369231281,767291842,17.13,239.87,292254365,552.78,1105668,868709451,19.05]).
result(46,pass,cruxmiter29seed4,[662.12,1383070697,0.3,109.94,66700,767760625,1602315222,35.89,641.87,647372304,1562.44,2330176,1753174097,38.17]).



result(51, pass, 'dp12u11.used-as.sat04-358-sc2004', [139.4,399482586,5.9,27.83,47276,181746914,389690965,8.39,140.02,169822289,205.2,520156,426506330,9.22]).

result(56, pass, eqbpwtrc10bpdtlf10, [305.66,922578994,4.0,83.1,55516,534378976,1131635151,25.37,285.05,261206693,511.24,1219564,1234331511,26.85]).
result(57, pass, eqbpwtrc10spctbk10, [331.34,1189138741,1.8,100.96,45688,807685876,1714031765,38.59,308.4,237319721,610.87,1588096,1832607734,40.44]).
result(58, pass, eqsparcl10bpwtrc10, [304.26,1077162165,2.4,89.79,44912,667630912,1408422214,31.67,283.63,238036098,542.16,1396712,1536026189,33.42]).

result(61, pass, 'f6nidw-sc2012', [12.41,62403221,16.9,4.3,137704,3756323,6761181,0.37,10.34,32513391,3.53,131024,9705073,0.41]).
result(62, fail, 'gensys-icl005.shuffled-as.sat05-3826-sc2011', ["ERROR: using DELETED clause", "thread 'main' panicked at 'at Some(22613): Clause 18303 to be accessed does not exist'"]).
result(63, pass, 'gto_p60c238-sc2018', [300.07,1049191617,0.1,78.2,57180,635122738,1297997512,29.61,272.12,559309454,655.75,1826056,1354892953,29.85]).



result(71, redo, _, ["Insufficient space"]).
result(72, redo, _, ["Insufficient space"]).
result(73,pass,'pb_300_10_lb_08-sc2014',[121.66,292074679,21.7,27.81,180764,45741075,95239189,2.12,101.88,117957763,39.78,254976,87496371,1.92]).


result(74,pass,'ps_5000_21250_3_0_0.8_0_1.55_2-sc2017',[1595.94,2351802975,0.3,170.34,86272,1369478691,2903296337,67.34,1285.76,616076564,1088.53,3348752,2938197845,67.6]).

result(76, pass, size_4_4_4_i0418_r8, [196.18,417206246,3.8,46.06,52936,236536275,495839902,11.35,167.96,154081383,233.79,664912,528795242,11.5]).


result(81, fail, 'size_4_4_4_i4295_r8', ["fratchk fails : bad lrat proof"]).
result(82, pass, 'size_4_4_4_i4473_r8', [212.34,488681050,1.9,36.34,43368,245561341,509395576,11.54,198.87,175767911,274.63,720808,542739191,11.59]).
result(83, fail, 'size_4_4_4_i4828_r8', ["fratchk fails : bad lrat proof"]).
result(84, pass, 'slp-synthesis-aes-bottom13-sc2011', [29.69,117354372,17.5,7.09,32136,46806065,103169178,2.16,29.74,53723299,14.32,160728,71302414,1.43]).
result(85, redo, _, ["Insufficient space"]).
result(86,pass,'smulo032-sc2012',[132.92,482448122,6.5,25.13,47292,184363248,401377593,8.63,144.47,160016164,146.6,588972,477788483,10.38]).
result(87, fail, 'snw_13_8_pre-sc2016', ["Bad lrat proof"]).
result(88,pass,'snw_16_8_nopre-sc2016',[3147.06,753448575,81.2,417.6,828392,273842943,552598273,2.08,2989.06,307248330,2370.18,1201368,620803921,15.77]).
result(89,pass,'snw_16_8_pre-sc2016',[2979.93,675806533,83.7,201.72,683852,239230149,489779413,1.47,2819.46,283710907,1879.37,1083452,536712429,13.32]).


