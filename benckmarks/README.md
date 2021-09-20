The software versions used for the FRAT vs. DRAT benchmark are as follows:

- DRAT-trim: commit [d13f761fbdacd052429f14421f95a7e8cd75deb1](https://github.com/marijnheule/drat-trim/tree/d13f761fbdacd052429f14421f95a7e8cd75deb1)
- Standard CaDiCaL: commit [92d72896c49b30ad2d50c8e1061ca0681cd23e60](https://github.com/arminbiere/cadical/tree/92d72896c49b30ad2d50c8e1061ca0681cd23e60)
- FRAT-rs: commit [d5c0cf3a149e2b59a1c81a90db05183fec8b861d](https://github.com/digama0/frat/tree/d5c0cf3a149e2b59a1c81a90db05183fec8b861d)
- Modified CaDiCaL: commit [925017ae2af3b9239f97ceb8e87d749082e6386d](https://github.com/digama0/cadical/tree/925017ae2af3b9239f97ceb8e87d749082e6386d)

Due to subsequent development, different versions of FRAT-rs were used for 
later benchmarks: 

- For FRAT0 vs. DRAT and FRAT elaborator vs. DPR-trim benchmarks: commit [07c73e215feee4e3990c54f9a3ca364e80e6fb98] (https://github.com/digama0/frat/tree/07c73e215feee4e3990c54f9a3ca364e80e6fb98)

- For FRAT elaborator vs. PR2DRAT + DPR-trim benchmark: commit [c4ce75cb830ede920fc9e2f4fbbf2cbecc58f4f9] (https://github.com/digama0/frat/tree/c4ce75cb830ede920fc9e2f4fbbf2cbecc58f4f9)

For most purposes the latest version of FRAT-rs is probably the best choice, 
but there may be cases where you need to use identical versions in order to 
reproduce the benchmark results.  In particular, LRAT proofs of the CNF instance 
[mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07-sc2007] (mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07-sc2007.cnf)
produced by _either_ DRAT or FRAT toolchain will cause SIGSEGV errors when checked by the standard 
LRAT checker included in DRAT-trim. This error does not occur when using later versions of CaDiCaL.
We believe that the error-causing LRAT proofs are still valid, as they can be verified by the LRAT
checker included in FRAT-rs.
