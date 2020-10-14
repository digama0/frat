:- [basic, probs].

write_probs(_, _, []).
write_probs(STRM, NUM, [NAME | NAMES]) :- 
  write_term_punct(STRM, num_name(NUM, NAME)),
  num_suc(NUM, SUC),
  write_probs(STRM, SUC, NAMES).

write_probs :- 
  open('problems.pl', write, STRM),
  probs(PROBS), 
  write_probs(STRM, 1, PROBS),
  close(STRM).
