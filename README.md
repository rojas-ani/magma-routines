# magma-routines
Some of the Magma scripts we use to compute decompositions of abelian varieties with group actions.

| File                  	| Remarks                                                                                                                                                                                                                             	|
|-----------------------	|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------	|
| polyIZ.m              	| Programmed by Antonio Behn in 2012. Minor change in 2020 by A. Rojas, in the algorithm to compute the Riemann Matrices invariants under G (MoebiusInvariantAni).                                                                    	|
| polyNoZ.m             	| Programmed by Antonio Behn in 2012. Minor change in 2020 by A. Rojas, to just work for finding the symplectic representation of G (to save memory).                                                                                 	|
| polyDZ.m              	| Upgrade by A. Rojas, in the algorithm to compute the Riemann Matrices invariants under G (MoebiusInvariantDZ), to compute fixed Riemann matrices for not necessarily principally polarized abelian varieties. Draft in preparation. 	|
| Polarizaciones_v2.mgm 	| By A. Rojas, to compute idempotents and induced polarizations given the symplectic representation od the action of G                                                                                                                 	|
| pHs.mgm 	| By A. Rojas, to compute idempotents for subgroups and coordinates of the basis of the lattice of Fix_H A                                                                                                                 	|

**Example** We illustrate a typical use of some of the functions in polyDZ.m by finding the symplectic representation of the action of $S_3$ in genus $3$ with signature (0;3,2,2,2,2). It goes as follows:
> Attach("polyDZ.m");  
> g:=Sym(3);  
> r:=RH(g,3);  
> p:=polygon(g,r[1]`gens);  
> p'x;  
