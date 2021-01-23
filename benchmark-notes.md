The software versions used for the benchmarks are as follows:

- DRAT-trim: commit d13f761fbdacd052429f14421f95a7e8cd75deb1
- Standard CaDiCaL: commit 92d72896c49b30ad2d50c8e1061ca0681cd23e60
- FRAT-rs: commit d5c0cf3a149e2b59a1c81a90db05183fec8b861d
- Modified CaDiCaL: commit 925017ae2af3b9239f97ceb8e87d749082e6386d

The benchmark results may not be reproducible if the same software versions are not used.
In particular, LRAT proofs of the CNF instance 'mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07-sc2007'
produced by _either_ DRAT or FRAT toolchain will cause SIGSEGV errors when checked by the standard 
LRAT checker included in DRAT-trim. This error does not occur when using later versions of CaDiCaL.
We believe that the error-causing LRAT proofs are still valid, as they can be verified by the LRAT
checker included in FRAT-rs.