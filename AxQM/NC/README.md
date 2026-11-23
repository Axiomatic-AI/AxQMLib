# Nielsen & Chuang: the numbered items

Every numbered item of Nielsen & Chuang, *Quantum Computation and Quantum Information* (tenth-anniversary edition): its printed page, a one-line summary in our own words, and the Lean file that formalises it. Appendix items carry an `A` prefix (`Theorem A6.1` is `TheoremA6_1.lean`).

Of the 687 items, 505 are formalised. For 16 of these the file proves that the printed statement is false, usually by a counterexample, and proves a corrected one; for 12 more it proves a corrected statement only. The accompanying paper (Supplementary Note 2) describes each correction and where it was reported before. 148 items are not formalised, and 34 have no formal statement (open-ended prompts, numerical estimates and design tasks).

A file formalises its item with statements of its own and may draw on results elsewhere in the library; its docstring says where.

## Chapter 1 — Introduction and overview

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 1.1 | 36 | Performance of the best classical algorithm for the probabilistic (error < 1/2) version of Deutsch's problem. | — | no formal statement |
| Exercise 1.2 | 57 | A device distinguishing two non-orthogonal states could clone them (violating no-cloning), and conversely a cloner could distinguish them. | — | not formalised |
| Problem 1.1 | 58 | Feynman-Gates conversation: write an imaginary ~2000-word dialogue on the future of computation. | — | no formal statement |
| Problem 1.2 | 58 | Essay on the most significant discovery yet made in quantum computation and quantum information. | — | no formal statement |

## Chapter 2 — Introduction to quantum mechanics

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 2.1 | 63 | Show that (1,-1),(1,2),(2,1) are linearly dependent | [`Exercise2_1`](Ch2/Exercise2_1.lean) | formalised |
| Exercise 2.2 | 64 | Give a matrix representation for a swap-like operator A; find bases giving a different representation | [`Exercise2_2`](Ch2/Exercise2_2.lean) | formalised |
| Exercise 2.3 | 64 | Show matrix rep of composition BA is the matrix product of reps of B and A | [`Exercise2_3`](Ch2/Exercise2_3.lean) | formalised |
| Exercise 2.4 | 65 | Show the identity operator has the identity matrix representation | [`Exercise2_4`](Ch2/Exercise2_4.lean) | formalised |
| Exercise 2.5 | 66 | Verify that the defined (.,.) is an inner product on C^n | [`Exercise2_5`](Ch2/Exercise2_5.lean) | formalised |
| Exercise 2.6 | 66 | Show any inner product is conjugate-linear in the first argument | [`Exercise2_6`](Ch2/Exercise2_6.lean) | formalised |
| Exercise 2.7 | 66 | Verify (1,1) and (1,-1) are orthogonal; find normalized forms | [`Exercise2_7`](Ch2/Exercise2_7.lean) | formalised |
| Exercise 2.8 | 66 | Prove the Gram-Schmidt procedure produces an orthonormal basis for V | [`Exercise2_8`](Ch2/Exercise2_8.lean) | formalised |
| Exercise 2.9 | 68 | Express each Pauli matrix in the outer product notation | [`Exercise2_9`](Ch2/Exercise2_9.lean) | formalised |
| Exercise 2.10 | 68 | Matrix representation of the operator \|v_j><v_k\| in the \|v_i> basis | [`Exercise2_10`](Ch2/Exercise2_10.lean) | formalised |
| Exercise 2.11 | 69 | Find eigenvectors, eigenvalues, diagonal representations of X, Y, Z | [`Exercise2_11`](Ch2/Exercise2_11.lean) | formalised |
| Exercise 2.12 | 69 | Prove the matrix [[1,0],[1,1]] is not diagonalizable | [`Exercise2_12`](Ch2/Exercise2_12.lean) | formalised |
| Exercise 2.13 | 70 | Show (\|w><v\|)^dagger = \|v><w\| | [`Exercise2_13`](Ch2/Exercise2_13.lean) | formalised |
| Exercise 2.14 | 70 | Show the adjoint operation is anti-linear | [`Exercise2_14`](Ch2/Exercise2_14.lean) | formalised |
| Exercise 2.15 | 70 | Show that (A^dagger)^dagger = A | [`Exercise2_15`](Ch2/Exercise2_15.lean) | formalised |
| Exercise 2.16 | 70 | Show that any projector P satisfies P^2 = P | [`Exercise2_16`](Ch2/Exercise2_16.lean) | formalised |
| Exercise 2.17 | 70 | Show a normal matrix is Hermitian iff it has real eigenvalues | [`Exercise2_17`](Ch2/Exercise2_17.lean) | formalised |
| Exercise 2.18 | 71 | Show all eigenvalues of a unitary matrix have modulus 1 | [`Exercise2_18`](Ch2/Exercise2_18.lean) | formalised |
| Exercise 2.19 | 71 | Show the Pauli matrices are Hermitian and unitary | [`Exercise2_19`](Ch2/Exercise2_19.lean) | formalised |
| Exercise 2.20 | 71 | Characterize the relationship between two matrix reps A' and A'' under basis change | [`Exercise2_20`](Ch2/Exercise2_20.lean) | formalised |
| Exercise 2.21 | 71 | Repeat the spectral decomposition proof for the Hermitian case | [`Exercise2_21`](Ch2/Exercise2_21.lean) | formalised |
| Exercise 2.22 | 71 | Prove two eigenvectors of a Hermitian operator with different eigenvalues are orthogonal | [`Exercise2_22`](Ch2/Exercise2_22.lean) | formalised |
| Exercise 2.23 | 71 | Show the eigenvalues of a projector P are all 0 or 1 | [`Exercise2_23`](Ch2/Exercise2_23.lean) | formalised |
| Exercise 2.24 | 71 | Show a positive operator is necessarily Hermitian | [`Exercise2_24`](Ch2/Exercise2_24.lean) | formalised |
| Exercise 2.25 | 71 | Show that for any operator A, A^dagger A is positive | [`Exercise2_25`](Ch2/Exercise2_25.lean) | formalised |
| Theorem 2.1 | 72 | Spectral decomposition: normal operator M is diagonal in some orthonormal basis, and conversely | [`Theorem2_1`](Ch2/Theorem2_1.lean) | formalised |
| Exercise 2.26 | 74 | Write out \|psi>^{tensor2} and ^{tensor3} for \|psi>=(\|0>+\|1>)/sqrt2 | [`Exercise2_26`](Ch2/Exercise2_26.lean) | formalised |
| Exercise 2.27 | 74 | Matrix reps of tensor products X⊗Z, I⊗X, X⊗I; is tensor product commutative? | [`Exercise2_27`](Ch2/Exercise2_27.lean) | formalised |
| Exercise 2.28 | 74 | Show transpose, conjugation, adjoint distribute over the tensor product | [`Exercise2_28`](Ch2/Exercise2_28.lean) | formalised |
| Exercise 2.29 | 74 | Show the tensor product of two unitary operators is unitary | [`Exercise2_29`](Ch2/Exercise2_29.lean) | formalised |
| Exercise 2.30 | 74 | Show the tensor product of two Hermitian operators is Hermitian | [`Exercise2_30`](Ch2/Exercise2_30.lean) | formalised |
| Exercise 2.31 | 74 | Show the tensor product of two positive operators is positive | [`Exercise2_31`](Ch2/Exercise2_31.lean) | formalised |
| Exercise 2.32 | 74 | Show the tensor product of two projectors is a projector | [`Exercise2_32`](Ch2/Exercise2_32.lean) | formalised |
| Exercise 2.33 | 74 | Show H^{tensor n} = (1/sqrt(2^n)) sum (-1)^{x.y} \|x><y\|; write out H^{tensor2} | [`Exercise2_33`](Ch2/Exercise2_33.lean) | formalised |
| Exercise 2.34 | 75 | Find the square root and logarithm of the matrix [[4,3],[3,4]] | [`Exercise2_34`](Ch2/Exercise2_34.lean) | formalised |
| Exercise 2.35 | 75 | Prove exp(i theta v.sigma) = cos(theta) I + i sin(theta) v.sigma | [`Exercise2_35`](Ch2/Exercise2_35.lean) | formalised |
| Exercise 2.36 | 76 | Show the Pauli matrices except I have trace zero | [`Exercise2_36`](Ch2/Exercise2_36.lean) | formalised |
| Exercise 2.37 | 76 | Show tr(AB) = tr(BA) (cyclic property of trace) | [`Exercise2_37`](Ch2/Exercise2_37.lean) | formalised |
| Exercise 2.38 | 76 | Show tr(A+B)=tr(A)+tr(B) and tr(zA)=z tr(A) (linearity of trace) | [`Exercise2_38`](Ch2/Exercise2_38.lean) | formalised |
| Exercise 2.39 | 76 | Show (A,B)=tr(A^dagger B) is an inner product (Hilbert-Schmidt); dim L_V = d^2; orthonormal basis of Hermitian matrices | [`Exercise2_39`](Ch2/Exercise2_39.lean) | formalised |
| Theorem 2.2 | 77 | Simultaneous diagonalization: [A,B]=0 iff Hermitian A,B diagonal in a common basis | [`Theorem2_2`](Ch2/Theorem2_2.lean) | formalised |
| Exercise 2.40 | 77 | Verify commutation relations [X,Y]=2iZ etc for the Pauli matrices | [`Exercise2_40`](Ch2/Exercise2_40.lean) | formalised |
| Theorem 2.3 | 78 | Polar decomposition: A=UJ=KU with J=sqrt(A^dagger A), K=sqrt(AA^dagger) | [`Theorem2_3`](Ch2/Theorem2_3.lean) | formalised |
| Exercise 2.41 | 78 | Verify anti-commutation relations {sigma_i,sigma_j}=0 and sigma_i^2=I | [`Exercise2_41`](Ch2/Exercise2_41.lean) | formalised |
| Exercise 2.42 | 78 | Verify AB = ([A,B]+{A,B})/2 | [`Exercise2_42`](Ch2/Exercise2_42.lean) | formalised |
| Exercise 2.43 | 78 | Show sigma_j sigma_k = delta_jk I + i sum eps_jkl sigma_l | [`Exercise2_43`](Ch2/Exercise2_43.lean) | formalised |
| Exercise 2.44 | 78 | If [A,B]=0, {A,B}=0, A invertible, show B=0 | [`Exercise2_44`](Ch2/Exercise2_44.lean) | formalised |
| Exercise 2.45 | 78 | Show [A,B]^dagger = [B^dagger, A^dagger] | [`Exercise2_45`](Ch2/Exercise2_45.lean) | formalised |
| Exercise 2.46 | 78 | Show [A,B] = -[B,A] | [`Exercise2_46`](Ch2/Exercise2_46.lean) | formalised |
| Exercise 2.47 | 78 | If A,B Hermitian, show i[A,B] is Hermitian | [`Exercise2_47`](Ch2/Exercise2_47.lean) | formalised |
| Corollary 2.4 | 79 | Singular value decomposition: A=UDV with U,V unitary and D diagonal non-negative | [`Corollary2_4`](Ch2/Corollary2_4.lean) | formalised |
| Exercise 2.48 | 79 | Find the polar decomposition of a positive/unitary/Hermitian matrix | [`Exercise2_48`](Ch2/Exercise2_48.lean) | formalised |
| Exercise 2.49 | 79 | Express the polar decomposition of a normal matrix in outer product form | [`Exercise2_49`](Ch2/Exercise2_49.lean) | formalised |
| Exercise 2.50 | 79 | Find the left and right polar decompositions of [[1,0],[1,1]] | [`Exercise2_50`](Ch2/Exercise2_50.lean) | formalised |
| Exercise 2.51 | 82 | Verify the Hadamard gate H is unitary | [`Exercise2_51`](Ch2/Exercise2_51.lean) | formalised |
| Exercise 2.52 | 82 | Verify H^2 = I | [`Exercise2_52`](Ch2/Exercise2_52.lean) | formalised |
| Exercise 2.53 | 82 | What are the eigenvalues and eigenvectors of H? | [`Exercise2_53`](Ch2/Exercise2_53.lean) | formalised |
| Exercise 2.54 | 83 | For commuting Hermitian A,B prove exp(A)exp(B)=exp(A+B) | [`Exercise2_54`](Ch2/Exercise2_54.lean) | formalised |
| Exercise 2.55 | 84 | Prove U(t1,t2)=exp(-iH(t2-t1)/hbar) is unitary | [`Exercise2_55`](Ch2/Exercise2_55.lean) | formalised |
| Exercise 2.56 | 84 | Show K=-i log(U) is Hermitian for any unitary U, so U=exp(iK) | [`Exercise2_56`](Ch2/Exercise2_56.lean) | formalised |
| Exercise 2.57 | 86 | Show cascaded measurements {L_l} then {M_m} equal single measurement N_lm=M_m L_l | [`Exercise2_57`](Ch2/Exercise2_57.lean) | formalised |
| Exercise 2.58 | 88 | For an eigenstate of observable M, find the average value and standard deviation | [`Exercise2_58`](Ch2/Exercise2_58.lean) | formalised |
| Exercise 2.59 | 90 | For qubit \|0> measure observable X: find average value and standard deviation | [`Exercise2_59`](Ch2/Exercise2_59.lean) | formalised |
| Exercise 2.60 | 90 | Show v.sigma has eigenvalues ±1 and projectors P±=(I±v.sigma)/2 | [`Exercise2_60`](Ch2/Exercise2_60.lean) | formalised |
| Exercise 2.61 | 90 | Probability of +1 for measurement of v.sigma given state \|0>; post-measurement state | [`Exercise2_61`](Ch2/Exercise2_61.lean) | formalised |
| Exercise 2.62 | 92 | Show any measurement where measurement operators and POVM elements coincide is projective | [`Exercise2_62`](Ch2/Exercise2_62.lean) | formalised |
| Exercise 2.63 | 92 | Show measurement operators M_m = U_m sqrt(E_m) for some unitaries U_m | [`Exercise2_63`](Ch2/Exercise2_63.lean) | formalised |
| Exercise 2.64 | 93 | Construct a POVM distinguishing linearly independent states with certainty when E_i occurs | [`Exercise2_64`](Ch2/Exercise2_64.lean) | formalised |
| Exercise 2.65 | 93 | Express (\|0>±\|1>)/sqrt2 in a basis where not the same up to a relative phase | [`Exercise2_65`](Ch2/Exercise2_65.lean) | formalised |
| Exercise 2.66 | 94 | Show average value of X1 Z2 for two-qubit state (\|00>+\|11>)/sqrt2 is zero | [`Exercise2_66`](Ch2/Exercise2_66.lean) | formalised |
| Exercise 2.67 | 95 | Prove an inner-product-preserving U on subspace W extends to a unitary on V | [`Exercise2_67`](Ch2/Exercise2_67.lean) | formalised |
| Exercise 2.68 | 96 | Prove (\|00>+\|11>)/sqrt2 is not a product state \|a>\|b> | [`Exercise2_68`](Ch2/Exercise2_68.lean) | formalised |
| Exercise 2.69 | 98 | Verify the Bell basis forms an orthonormal basis for the two qubit state space | [`Exercise2_69`](Ch2/Exercise2_69.lean) | formalised |
| Exercise 2.70 | 98 | Show <psi\|E⊗I\|psi> is same for all four Bell states; can Eve infer Alice's bits? | [`Exercise2_70`](Ch2/Exercise2_70.lean) | formalised |
| Theorem 2.5 | 101 | Characterization of density operators: rho is a density operator iff trace one and positive | [`Theorem2_5`](Ch2/Theorem2_5.lean) | formalised |
| Theorem 2.6 | 103 | Unitary freedom in the ensemble: two sets generate the same density matrix iff unitarily related | [`Theorem2_6`](Ch2/Theorem2_6.lean) | formalised |
| Exercise 2.71 | 103 | Show tr(rho^2)<=1 with equality iff rho is a pure state | [`Exercise2_71`](Ch2/Exercise2_71.lean) | formalised |
| Exercise 2.72 | 105 | Bloch sphere for mixed states: rho=(I+r.sigma)/2, \|\|r\|\|<=1, pure iff \|\|r\|\|=1 | [`Exercise2_72`](Ch2/Exercise2_72.lean) | formalised |
| Exercise 2.73 | 105 | Minimal ensemble for rho containing \|psi> in support, with p_i=1/<psi\|rho^-1\|psi> | [`Exercise2_73`](Ch2/Exercise2_73.lean) | formalised |
| Exercise 2.74 | 106 | For product state \|a>\|b>, show reduced density operator of A is pure | [`Exercise2_74`](Ch2/Exercise2_74.lean) | formalised |
| Exercise 2.75 | 106 | For each Bell state, find the reduced density operator for each qubit | [`Exercise2_75`](Ch2/Exercise2_75.lean) | formalised |
| Theorem 2.7 | 109 | Schmidt decomposition: pure state of AB = sum lambda_i \|i_A>\|i_B> with orthonormal Schmidt bases | [`Theorem2_7`](Ch2/Theorem2_7.lean) | formalised |
| Exercise 2.76 | 110 | Extend the Schmidt decomposition proof to unequal-dimension A and B | [`Exercise2_76`](Ch2/Exercise2_76.lean) | formalised |
| Exercise 2.77 | 110 | Show by example a tripartite ABC state not expressible with a single Schmidt basis | [`Exercise2_77`](Ch2/Exercise2_77.lean) | formalised |
| Exercise 2.78 | 110 | Prove \|psi> is a product state iff Schmidt number 1 iff rho^A pure | [`Exercise2_78`](Ch2/Exercise2_78.lean) | formalised |
| Exercise 2.79 | 111 | Find the Schmidt decompositions of three specific two-qubit states | [`Exercise2_79`](Ch2/Exercise2_79.lean) | formalised |
| Exercise 2.80 | 111 | Two states with identical Schmidt coefficients related by (U⊗V) | [`Exercise2_80`](Ch2/Exercise2_80.lean) | formalised |
| Exercise 2.81 | 111 | Freedom in purifications: two purifications related by (I_A⊗U_R) | [`Exercise2_81`](Ch2/Exercise2_81.lean) | formalised |
| Exercise 2.82 | 111 | Purification of rho via reference R; measurement of R recovers ensemble | [`Exercise2_82`](Ch2/Exercise2_82.lean) | formalised |
| Problem 2.1 | 117 | Functions of the Pauli matrices: f(theta n.sigma) = ((f(theta)+f(-theta))/2)I + ((f(theta)-f(-theta))/2) n.sigma | [`Problem2_1`](Ch2/Problem2_1.lean) | formalised |
| Problem 2.2 | 117 | Properties of the Schmidt number: rank of rho^A, subadditivity over decompositions, Sch(psi)>=\|Sch(phi)-Sch(gamma)\| | [`Problem2_2`](Ch2/Problem2_2.lean) | formalised; corrected statement |
| Problem 2.3 | 118 | Tsirelson's inequality: (Q⊗S+R⊗S+R⊗T-Q⊗T)^2 = 4I+[Q,R]⊗[S,T]; bound 2sqrt2 | [`Problem2_3`](Ch2/Problem2_3.lean) | formalised |

## Chapter 3 — Introduction to computer science

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 3.1 | 125 | How might we recognize a process in Nature computing a function not Turing-computable? | — | no formal statement |
| Exercise 3.2 | 125 | Show single-tape Turing machines can each be assigned a unique number (Turing number). | — | not formalised |
| Exercise 3.3 | 127 | Describe a Turing machine that outputs the bits of input x in reverse order. | — | no formal statement |
| Exercise 3.4 | 127 | Describe a Turing machine to add two binary numbers x and y modulo 2. | — | no formal statement |
| Exercise 3.5 | 128 | Show there is no algorithm to decide whether M halts on a blank tape (halting, no inputs). | — | not formalised |
| Exercise 3.6 | 129 | Show no probabilistic TM outputs the probabilistic halting function h_p(x) with correctness >1/2 for all x. | — | not formalised |
| Exercise 3.7 | 129 | Is the halting problem undecidable for a TM augmented with a halting oracle? | — | not formalised |
| Exercise 3.8 | 134 | Show NAND simulates AND, XOR and NOT given wires, ancilla bits and FANOUT. | — | not formalised |
| Exercise 3.9 | 137 | Prove f(n)=O(g(n)) iff g(n)=Omega(f(n)); deduce Theta symmetry. | — | not formalised |
| Exercise 3.10 | 137 | Show a degree-k polynomial g(n) is O(n^l) for any l>=k. | — | not formalised |
| Exercise 3.11 | 137 | Show log n is O(n^k) for any k>0. | — | not formalised |
| Exercise 3.12 | 137 | Show n^k is O(n^{log n}) for any k, but n^{log n} is never O(n^k). | — | not formalised |
| Exercise 3.13 | 137 | Show c^n is Omega(n^{log n}) for c>1, but n^{log n} is never Omega(c^n). | — | not formalised |
| Exercise 3.14 | 137 | If e(n)=O(f(n)) and g(n)=O(h(n)) then e(n)g(n)=O(f(n)h(n)). | — | not formalised |
| Exercise 3.15 | 138 | Lower bound: after k compare-and-swaps at most 2^k orderings sorted; conclude Omega(n log n). | — | not formalised |
| Exercise 3.16 | 141 | Show there exist Boolean functions on n inputs requiring at least 2^n/log n gates. | — | not formalised |
| Exercise 3.17 | 142 | Poly-time factoring algorithm exists iff the factoring decision problem is in P. | — | not formalised |
| Exercise 3.18 | 142 | Prove that if coNP != NP then P != NP. | — | not formalised |
| Theorem 3.1 | 144 | Euler's theorem: a connected graph has an Euler cycle iff every vertex has even degree. | — | not formalised |
| Exercise 3.19 | 144 | Show REACHABILITY solvable in O(n) ops; deduce connectivity in O(n^2). | — | not formalised |
| Exercise 3.20 | 144 | Prove Euler's theorem; give a constructive procedure for finding an Euler cycle. | — | not formalised |
| Exercise 3.21 | 145 | Show reducibility is transitive: L1 red. L2 and L2 red. L3 implies L1 red. L3. | — | not formalised |
| Exercise 3.22 | 145 | If L is complete for a class and L reduces to L' in the class, then L' is complete. | — | not formalised |
| Theorem 3.2 | 146 | Cook-Levin: CSAT is NP-complete. | — | not formalised |
| Exercise 3.23 | 148 | Show SAT is NP-complete (SAT in NP and CSAT reduces to SAT). | — | not formalised |
| Exercise 3.24 | 149 | 2SAT has an efficient solution: build implication graph, poly-time reachability, solve 2SAT. | — | not formalised |
| Exercise 3.25 | 151 | Prove PSPACE is a subset of EXP. | — | not formalised |
| Exercise 3.26 | 151 | Prove L (logarithmic space) is a subset of P. | — | not formalised |
| Exercise 3.27 | 152 | Prove the given greedy algorithm finds a vertex cover within factor two of minimal. | — | not formalised |
| Exercise 3.28 | 153 | Show constant k in (1/2,1] in the BPP definition gives the same class L in BPP. | — | not formalised |
| Theorem 3.3 | 154 | Chernoff bound: P(sum X_i <= n/2) <= e^{-2 eps^2 n} for iid biased bits. | — | not formalised |
| Exercise 3.29 | 156 | Show the Fredkin gate is self-inverse: two consecutive gates give the same outputs. | — | not formalised |
| Exercise 3.30 | 156 | Verify the billiard-ball computer in Figure 3.14 computes the Fredkin gate. | — | no formal statement |
| Exercise 3.31 | 159 | Construct a reversible circuit outputting (x,y,c,x XOR y) with c the carry bit. | — | no formal statement |
| Exercise 3.32 | 161 | Smallest number of Fredkin gates to simulate a Toffoli gate, and vice versa. | — | no formal statement |
| Problem 3.1 | 165 | Minsky machines: prove they compute exactly the Turing-computable functions (both directions). | — | not formalised |
| Problem 3.2 | 166 | Vector games: prove every computable function is realized by a vector game (via Minsky sim). | — | not formalised |
| Problem 3.3 | 166 | Fractran: prove for every computable f a Fractran program maps 2^n to 2^{f(n)}. | — | not formalised |
| Problem 3.4 | 166 | Undecidability of dynamical systems: no algorithm decides if a Fractran system reaches 1. | — | not formalised |
| Problem 3.5 | 166 | Non-universality of two-bit reversible logic; deduce Toffoli not simulable by 1-/2-bit gates. | — | not formalised |
| Problem 3.6 | 166 | Hardness of approximating TSP: no factor-r approximation unless P=NP. | — | not formalised |
| Problem 3.7 | 166 | Reversible Turing machines: construct one computing all TM functions; give space/time bounds. | — | not formalised |
| Problem 3.8 | 167 | Research: find a natural class of n-input functions needing super-polynomially many gates. | — | no formal statement |
| Problem 3.9 | 167 | Reversible PSPACE=PSPACE: reversible poly-space TM solves QSAT; hence class equals PSPACE. | — | not formalised |
| Problem 3.10 | 167 | Ancilla bits: build reversible circuit for p_m p_n; O(log log n) ancillas would put factoring in P. | — | not formalised |

## Chapter 4 — Quantum circuits

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 4.1 | 174 | Find Bloch-sphere points for the normalized eigenvectors of the Pauli matrices. | [`Exercise4_1`](Ch4/Exercise4_1.lean) | formalised |
| Theorem 4.1 | 175 | Z-Y decomposition: any single-qubit unitary U=e^{i a}R_z(b)R_y(g)R_z(d). | [`Theorem4_1`](Ch4/Theorem4_1.lean) | formalised |
| Exercise 4.2 | 175 | For real x and A with A^2=I, show exp(iAx)=cos(x)I+i sin(x)A; verify rotation eqns. | [`Exercise4_2`](Ch4/Exercise4_2.lean) | formalised |
| Exercise 4.3 | 175 | Show that up to global phase the pi/8 gate satisfies T=R_z(pi/4). | [`Exercise4_3`](Ch4/Exercise4_3.lean) | formalised |
| Exercise 4.4 | 175 | Express Hadamard H as a product of R_x, R_z rotations and a phase e^{i phi}. | [`Exercise4_4`](Ch4/Exercise4_4.lean) | formalised |
| Exercise 4.5 | 175 | Prove (n.sigma)^2=I and use it to verify the rotation formula R_n(theta). | [`Exercise4_5`](Ch4/Exercise4_5.lean) | formalised |
| Exercise 4.6 | 175 | Show R_n(theta) rotates the Bloch vector by angle theta about the n axis. | [`Exercise4_6`](Ch4/Exercise4_6.lean) | formalised |
| Exercise 4.7 | 175 | Show XYX=-Y and use it to prove X R_y(theta) X = R_y(-theta). | [`Exercise4_7`](Ch4/Exercise4_7.lean) | formalised |
| Exercise 4.8 | 175 | Prove any single-qubit unitary U=e^{i alpha}R_n(theta); find params for H and S. | [`Exercise4_8`](Ch4/Exercise4_8.lean) | formalised |
| Corollary 4.2 | 176 | For single-qubit unitary U there exist A,B,C with ABC=I and U=e^{i a}AXBXC. | [`Corollary4_2`](Ch4/Corollary4_2.lean) | formalised |
| Exercise 4.9 | 176 | Explain why any single-qubit unitary may be written in the form (4.12). | [`Exercise4_9`](Ch4/Exercise4_9.lean) | formalised |
| Exercise 4.10 | 176 | Give an X-Y decomposition analogous to Theorem 4.1 using R_x instead of R_z. | [`Exercise4_10`](Ch4/Exercise4_10.lean) | formalised |
| Exercise 4.11 | 176 | For non-parallel unit vectors m,n show U=e^{i a}R_n(b)R_m(g)R_n(d). | [`Exercise4_11`](Ch4/Exercise4_11.lean) | formalised; printed statement refuted |
| Exercise 4.12 | 176 | Give A,B,C and alpha for the Hadamard gate in the ABC decomposition. | [`Exercise4_12`](Ch4/Exercise4_12.lean) | formalised |
| Exercise 4.13 | 177 | Prove the circuit identities HXH=Z, HYH=-Y, HZH=X. | [`Exercise4_13`](Ch4/Exercise4_13.lean) | formalised |
| Exercise 4.14 | 177 | Show HTH=R_x(pi/4) up to a global phase. | [`Exercise4_14`](Ch4/Exercise4_14.lean) | formalised |
| Exercise 4.15 | 177 | Compute composition of two Bloch-sphere rotations; simplify special case. | [`Exercise4_15`](Ch4/Exercise4_15.lean) | formalised; printed statement refuted |
| Exercise 4.16 | 178 | Find the 4x4 unitary matrix for H on one qubit of a two-qubit register. | [`Exercise4_16`](Ch4/Exercise4_16.lean) | formalised |
| Exercise 4.17 | 179 | Construct CNOT from one controlled-Z gate and two Hadamard gates. | [`Exercise4_17`](Ch4/Exercise4_17.lean) | formalised |
| Exercise 4.18 | 179 | Show controlled-Z is symmetric between control and target qubits. | [`Exercise4_18`](Ch4/Exercise4_18.lean) | formalised |
| Exercise 4.19 | 179 | Write out CNOT action on a density matrix explicitly in the computational basis. | [`Exercise4_19`](Ch4/Exercise4_19.lean) | formalised |
| Exercise 4.20 | 179 | Show CNOT conjugated by Hadamards swaps control/target; give +/- basis action. | [`Exercise4_20`](Ch4/Exercise4_20.lean) | formalised |
| Exercise 4.21 | 181 | Verify Figure 4.8 implements the C^2(U) operation. | [`Exercise4_21`](Ch4/Exercise4_21.lean) | formalised |
| Exercise 4.22 | 181 | Prove a C^2(U) gate needs at most eight one-qubit gates and six CNOTs. | [`Exercise4_22`](Ch4/Exercise4_22.lean) | formalised |
| Exercise 4.23 | 181 | Construct C^1(U) for U=R_x/R_y using CNOT and single-qubit gates; minimize. | [`Exercise4_23`](Ch4/Exercise4_23.lean) | formalised |
| Exercise 4.24 | 182 | Verify Figure 4.9 implements the Toffoli gate from H,S,CNOT,T gates. | [`Exercise4_24`](Ch4/Exercise4_24.lean) | formalised |
| Exercise 4.25 | 182 | Construct the Fredkin (controlled-swap) gate from Toffoli/CNOT; minimize gates. | [`Exercise4_25`](Ch4/Exercise4_25.lean) | formalised |
| Exercise 4.26 | 183 | Show a given circuit equals a Toffoli gate up to relative phases. | [`Exercise4_26`](Ch4/Exercise4_26.lean) | formalised |
| Exercise 4.27 | 183 | Using CNOTs and Toffoli gates, build a circuit for a partial cyclic permutation. | [`Exercise4_27`](Ch4/Exercise4_27.lean) | formalised |
| Exercise 4.28 | 184 | For U=V^2, construct a C^5(U) gate using no work qubits via controlled-V,V-dagger. | [`Exercise4_28`](Ch4/Exercise4_28.lean) | formalised |
| Exercise 4.29 | 184 | Find an O(n^2)-gate circuit implementing C^n(X) with no work qubits. | [`Exercise4_29`](Ch4/Exercise4_29.lean) | formalised |
| Exercise 4.30 | 184 | Find an O(n^2)-gate circuit implementing C^n(U) with no work qubits. | [`Exercise4_30`](Ch4/Exercise4_30.lean) | formalised |
| Exercise 4.31 | 185 | Prove eight CNOT-conjugation circuit identities (CX1C=X1X2, etc.). | [`Exercise4_31`](Ch4/Exercise4_31.lean) | formalised |
| Exercise 4.32 | 187 | Show unread measurement gives rho'=P0 rho P0+P1 rho P1 and preserves tr_2. | [`Exercise4_32`](Ch4/Exercise4_32.lean) | formalised |
| Exercise 4.33 | 187 | Show CNOT+H circuit implements measurement in the Bell basis; give operators. | [`Exercise4_33`](Ch4/Exercise4_33.lean) | formalised |
| Exercise 4.34 | 188 | Show a Hadamard-controlled-U circuit implements measurement of observable U. | [`Exercise4_34`](Ch4/Exercise4_34.lean) | formalised |
| Exercise 4.35 | 188 | Prove measurement commutes with a gate when the measured qubit is the control. | [`Exercise4_35`](Ch4/Exercise4_35.lean) | formalised |
| Exercise 4.36 | 189 | Construct a quantum circuit to add two two-bit numbers modulo 4. | [`Exercise4_36`](Ch4/Exercise4_36.lean) | formalised |
| Exercise 4.37 | 191 | Decompose the 4x4 QFT-like matrix into a product of two-level unitaries. | [`Exercise4_37`](Ch4/Exercise4_37.lean) | formalised |
| Exercise 4.38 | 191 | Prove there is a dxd unitary not decomposable into fewer than d-1 two-level unitaries. | [`Exercise4_38`](Ch4/Exercise4_38.lean) | formalised |
| Exercise 4.39 | 193 | Find a circuit of single-qubit and CNOT gates implementing a given two-level unitary. | [`Exercise4_39`](Ch4/Exercise4_39.lean) | formalised |
| Exercise 4.40 | 196 | Show E(R_n(a),R_n(a+b))=\|1-exp(i b/2)\| and use it to justify (4.76). | [`Exercise4_40`](Ch4/Exercise4_40.lean) | formalised |
| Exercise 4.41 | 197 | Show the circuit of Fig 4.17 applies R_z(theta) with cos theta=3/5 on success. | [`Exercise4_41`](Ch4/Exercise4_41.lean) | formalised |
| Exercise 4.42 | 198 | Prove that if cos theta=3/5 then theta is an irrational multiple of 2 pi. | [`Exercise4_42`](Ch4/Exercise4_42.lean) | formalised |
| Exercise 4.43 | 198 | Use prior results to show H, S, CNOT, Toffoli are universal for quantum computation. | [`Exercise4_43`](Ch4/Exercise4_43.lean) | formalised |
| Exercise 4.44 | 198 | Show the three-qubit gate G is universal whenever alpha is irrational. | [`Exercise4_44`](Ch4/Exercise4_44.lean) | formalised |
| Exercise 4.45 | 198 | Show U from H,S,CNOT,Toffoli has form 2^{-k/2}M with integer entries; T-gate variant. | [`Exercise4_45`](Ch4/Exercise4_45.lean) | formalised; printed statement refuted |
| Exercise 4.46 | 205 | Show describing an n-qubit density matrix requires 4^n-1 independent real numbers. | [`Exercise4_46`](Ch4/Exercise4_46.lean) | formalised |
| Theorem 4.3 | 207 | Trotter formula: lim (e^{iAt/n}e^{iBt/n})^n = e^{i(A+B)t} for Hermitian A,B. | [`Theorem4_3`](Ch4/Theorem4_3.lean) | formalised |
| Exercise 4.47 | 207 | For H=sum H_k with [H_j,H_k]=0, prove e^{-iHt}=prod e^{-iH_k t}. | [`Exercise4_47`](Ch4/Exercise4_47.lean) | formalised |
| Exercise 4.48 | 207 | Show restricting each H_k to at most c particles bounds L polynomially in n. | [`Exercise4_48`](Ch4/Exercise4_48.lean) | formalised |
| Exercise 4.49 | 208 | Prove the Baker-Campbell-Hausdorff formula (4.105) and Eqns (4.103)-(4.104). | [`Exercise4_49`](Ch4/Exercise4_49.lean) | formalised |
| Exercise 4.50 | 208 | For a Trotter step U_dt, prove U_dt=e^{-2iH dt}+O(dt^3) and bound error E(U^m,...). | [`Exercise4_50`](Ch4/Exercise4_50.lean) | formalised |
| Exercise 4.51 | 210 | Construct a circuit to simulate H=X1 (x) Y2 (x) Z3, giving e^{-i dt H}. | [`Exercise4_51`](Ch4/Exercise4_51.lean) | formalised |
| Problem 4.1 | 212 | Build a circuit with 2T+n gates implementing \|x> -> exp(-2pi i f(x)/2^n)\|x>. | [`Problem4_1`](Ch4/Problem4_1.lean) | formalised |
| Problem 4.2 | 212 | Find a depth O(log n) construction for the C^n(X) gate. | — | not formalised |
| Problem 4.3 | 212 | Alternate universality: expand H=i ln U in Pauli products; approximate U via Trotter. | [`Problem4_3`](Ch4/Problem4_3.lean) | formalised |
| Problem 4.4 | 213 | Minimal number of two-qubit / CNOT / controlled-Z gates to implement Toffoli. | — | no formal statement |
| Problem 4.5 | 213 | Construct Hamiltonians H_n requiring super-polynomial operations to simulate. | — | no formal statement |
| Problem 4.6 | 213 | Show single-qubit unitaries + Bell-basis measurement + 4-qubit-state prep is universal. | [`Problem4_6`](Ch4/Problem4_6.lean) | formalised |

## Chapter 5 — The quantum Fourier transform and its applications

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 5.1 | 217 | Give a direct proof that the linear transformation defined by the QFT (5.2) is unitary. | [`Exercise5_1`](Ch5/Exercise5_1.lean) | formalised |
| Exercise 5.2 | 217 | Explicitly compute the Fourier transform of the n-qubit state \|00...0>. | [`Exercise5_2`](Ch5/Exercise5_2.lean) | formalised |
| Exercise 5.3 | 221 | Classical FFT: DFT on 2^n numbers is Theta(2^2n) direct, reducible to Theta(n 2^n) via product form. | [`Exercise5_3`](Ch5/Exercise5_3.lean) | formalised |
| Exercise 5.4 | 221 | Give a decomposition of the controlled-R_k gate into single-qubit and CNOT gates. | [`Exercise5_4`](Ch5/Exercise5_4.lean) | formalised |
| Exercise 5.5 | 221 | Give a quantum circuit to perform the inverse quantum Fourier transform. | [`Exercise5_5`](Ch5/Exercise5_5.lean) | formalised |
| Exercise 5.6 | 221 | Approximate QFT: with R_k precision 1/p(n), error E(U,V)=max\|\|(U-V)\|psi>\|\| is Theta(n^2/p(n)). | [`Exercise5_6`](Ch5/Exercise5_6.lean) | formalised |
| Exercise 5.7 | 222 | Show the controlled-U sequence takes \|j>\|u> to \|j>U^j\|u>, not depending on \|u> being eigenstate. | [`Exercise5_7`](Ch5/Exercise5_7.lean) | formalised |
| Exercise 5.8 | 225 | Show phase estimation on superposition input measures phi_u accurate to n bits with prob >= \|c_u\|^2(1-eps). | [`Exercise5_8`](Ch5/Exercise5_8.lean) | formalised |
| Exercise 5.9 | 225 | For U with eigenvalues +-1, construct circuit collapsing \|psi> into one of the two eigenspaces with indicator. | [`Exercise5_9`](Ch5/Exercise5_9.lean) | formalised |
| Exercise 5.10 | 226 | Show that the order of x = 5 modulo N = 21 is 6. | [`Exercise5_10`](Ch5/Exercise5_10.lean) | formalised |
| Exercise 5.11 | 226 | Show that the order r of x satisfies r <= N. | [`Exercise5_11`](Ch5/Exercise5_11.lean) | formalised |
| Exercise 5.12 | 227 | Show that U\|y>=\|xy mod N> is unitary (x coprime to N has inverse mod N). | [`Exercise5_12`](Ch5/Exercise5_12.lean) | formalised |
| Exercise 5.13 | 227 | Prove (5.44) that the sum of eigenstates \|u_s> equals \|1>, and more generally (5.45). | [`Exercise5_13`](Ch5/Exercise5_13.lean) | formalised |
| Exercise 5.14 | 227 | Show V\|j>\|k>=\|j>\|k+x^j mod N> from \|0> gives same state as U^j from \|1>; construct V in O(L^3) gates. | [`Exercise5_14`](Ch5/Exercise5_14.lean) | formalised |
| Theorem 5.1 | 229 | If \|s/r - phi\| <= 1/(2r^2) then s/r is a convergent of phi's continued fraction, computable in O(L^3). | [`Theorem5_1`](Ch5/Theorem5_1.lean) | formalised; printed statement refuted |
| Exercise 5.15 | 231 | Show lcm(x,y)=xy/gcd(x,y), computable in O(L^2) operations for L-bit numbers. | [`Exercise5_15`](Ch5/Exercise5_15.lean) | formalised |
| Exercise 5.16 | 231 | For x>=2 prove int_x^{x+1} 1/y^2 dy >= 2/(3x^2), and sum_q 1/q^2 <= 3/2 int_2^inf 1/y^2 dy = 3/4. | [`Exercise5_16`](Ch5/Exercise5_16.lean) | formalised |
| Theorem 5.2 | 233 | For nontrivial x with x^2=1 mod N, at least one of gcd(x-1,N), gcd(x+1,N) is a nontrivial factor of N. | [`Theorem5_2`](Ch5/Theorem5_2.lean) | formalised |
| Theorem 5.3 | 233 | For odd composite N, random x coprime to N has order r even and x^{r/2}!=-1 mod N with prob >= 1-1/2^m. | [`Theorem5_3`](Ch5/Theorem5_3.lean) | formalised; printed statement refuted |
| Exercise 5.17 | 234 | Give an O(L^3) classical algorithm to determine whether N = a^b for integers a>=1, b>=2. | [`Exercise5_17`](Ch5/Exercise5_17.lean) | formalised |
| Exercise 5.18 | 234 | Factoring 91: with x=4, compute order r, show x^{r/2} mod 91 != -1, gcd(64-1,91)=7. | [`Exercise5_18`](Ch5/Exercise5_18.lean) | formalised; corrected statement |
| Exercise 5.19 | 234 | Show N=15 is the smallest composite not even and not a prime power (smallest needing order-finding). | [`Exercise5_19`](Ch5/Exercise5_19.lean) | formalised |
| Exercise 5.20 | 238 | For f(x+r)=f(x), N multiple of r, compute DFT f-hat(l) via (5.68) using the root-of-unity sum (5.69). | [`Exercise5_20`](Ch5/Exercise5_20.lean) | formalised; corrected statement |
| Exercise 5.21 | 238 | Period-finding & phase estimation: eigenvectors of U_y are \|f-hat(l)>; realize black box from \|f(x0)>. | [`Exercise5_21`](Ch5/Exercise5_21.lean) | formalised |
| Exercise 5.22 | 239 | Show the discrete-log Fourier state \|f-hat(l1,l2)> equals the (5.72) double sum / phase form. | [`Exercise5_22`](Ch5/Exercise5_22.lean) | formalised; corrected statement |
| Exercise 5.23 | 239 | Compute the inverse-Fourier double sum (5.73) using (5.70) and show the result is f(x1,x2). | [`Exercise5_23`](Ch5/Exercise5_23.lean) | formalised; corrected statement |
| Exercise 5.24 | 239 | Construct the generalized continued fractions algorithm to determine s from sl2/r and l2/r. | [`Exercise5_24`](Ch5/Exercise5_24.lean) | formalised |
| Exercise 5.25 | 240 | Construct quantum circuit for black box U:\|x1>\|x2>\|y> -> \|x1>\|x2>\|y XOR b^{x1}a^{x2}>; count operations. | [`Exercise5_25`](Ch5/Exercise5_25.lean) | formalised |
| Exercise 5.26 | 242 | Re-express (5.77) to show determining l'_i lets one sample from the cyclic subgroup K_{p_i} of K. | [`Exercise5_26`](Ch5/Exercise5_26.lean) | formalised; corrected statement |
| Exercise 5.27 | 242 | Explain how the chapter's quantum algorithms efficiently decompose a finite Abelian group G into cyclic factors. | — | no formal statement |
| Exercise 5.28 | 242 | Write out a detailed specification of the quantum algorithm solving the HSP for finite Abelian groups. | — | no formal statement |
| Exercise 5.29 | 242 | Give quantum algorithms solving the Deutsch and Simon problems using the HSP framework. | — | no formal statement |
| Problem 5.1 | 243 | Construct a quantum circuit performing the QFT \|j> -> (1/sqrt p) sum e^{2pi ijk/p}\|k> for p prime. | [`Problem5_1`](Ch5/Problem5_1.lean) | formalised |
| Problem 5.2 | 243 | Measured QFT: QFT then measurement equals a circuit of only one-qubit gates + measurement with classical control. | [`Problem5_2`](Ch5/Problem5_2.lean) | formalised |
| Problem 5.3 | 243 | Kitaev's algorithm: top qubit measured 0 with prob cos^2(pi phi); iterate U^k to extract bits of phi. | [`Problem5_3`](Ch5/Problem5_3.lean) | formalised |
| Problem 5.4 | 244 | Show factoring can achieve a better upper bound of O(L^2 log L log log L) operations. | [`Problem5_4`](Ch5/Problem5_4.lean) | formalised |
| Problem 5.5 | 244 | Non-Abelian HSP: prove m=4log\|G\|+2 coset samples identify K with prob >= 1-1/\|G\| (research). | [`Problem5_5`](Ch5/Problem5_5.lean) | formalised |
| Problem 5.6 | 244 | Addition by Fourier transforms: circuit for \|x> -> \|x+y mod 2^n> via QFT, phase shifts, inverse QFT. | [`Problem5_6`](Ch5/Problem5_6.lean) | formalised |

## Chapter 6 — Quantum search algorithms

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 6.1 | 251 | Show the unitary operator for the Grover phase shift is 2\|0><0\| - I. | [`Exercise6_1`](Ch6/Exercise6_1.lean) | formalised |
| Exercise 6.2 | 251 | Show (2\|psi><psi\| - I) applied to sum a_k\|k> gives sum (-a_k + 2<a>)\|k>. | [`Exercise6_2`](Ch6/Exercise6_2.lean) | formalised |
| Exercise 6.3 | 252 | Show that in the \|alpha>,\|beta> basis the Grover iteration is a 2x2 rotation matrix. | [`Exercise6_3`](Ch6/Exercise6_3.lean) | formalised |
| Exercise 6.4 | 254 | Give explicit steps for the quantum search algorithm for multiple solutions (1<M<N/2). | [`Exercise6_4`](Ch6/Exercise6_4.lean) | formalised |
| Exercise 6.5 | 255 | Show the augmented oracle O' can be built from one call to O and elementary gates using extra qubit. | [`Exercise6_5`](Ch6/Exercise6_5.lean) | formalised |
| Exercise 6.6 | 255 | Verify the gates in the dotted box perform conditional phase shift 2\|00><00\| - I up to global phase. | [`Exercise6_6`](Ch6/Exercise6_6.lean) | formalised |
| Exercise 6.7 | 258 | Verify circuits in Figs 6.4/6.5 implement exp(-i\|x><x\|dt) and exp(-i\|psi><psi\|dt). | [`Exercise6_7`](Ch6/Exercise6_7.lean) | formalised |
| Exercise 6.8 | 258 | For accuracy O(dt^r) show oracle calls to simulate H scale as O(N^{r/2(r-1)}). | [`Exercise6_8`](Ch6/Exercise6_8.lean) | formalised |
| Exercise 6.9 | 259 | Verify Equation (6.25), the explicit form of U(dt)=exp(-i\|psi><psi\|dt)exp(-i\|x><x\|dt). | [`Exercise6_9`](Ch6/Exercise6_9.lean) | formalised |
| Exercise 6.10 | 260 | Show a suitable dt gives O(sqrt N) query search with final state exactly \|x> (prob 1). | [`Exercise6_10`](Ch6/Exercise6_10.lean) | formalised |
| Exercise 6.11 | 261 | Guess a Hamiltonian solving the continuous-time search problem for M solutions. | [`Exercise6_11`](Ch6/Exercise6_11.lean) | formalised |
| Exercise 6.12 | 261 | For H=\|x><psi\|+\|psi><x\|: (1) show O(1) time to rotate \|psi> to \|x>; (2) simulate H and count oracle calls. | [`Exercise6_12`](Ch6/Exercise6_12.lean) | formalised |
| Exercise 6.13 | 261 | For classical sampling counting estimator, show std dev sqrt(M(N-M)/k) and need k=Omega(N). | [`Exercise6_13`](Ch6/Exercise6_13.lean) | formalised |
| Exercise 6.14 | 262 | Prove any classical counting algorithm at accuracy c*sqrt(M) with prob >=3/4 needs Omega(N) oracle calls. | [`Exercise6_14`](Ch6/Exercise6_14.lean) | formalised |
| Exercise 6.15 | 270 | Via Cauchy-Schwarz show sum_x \|\|psi - x\|\|^2 >= 2N - 2sqrt(N) for orthonormal basis {\|x>}. | [`Exercise6_15`](Ch6/Exercise6_15.lean) | formalised |
| Exercise 6.16 | 270 | Show O(sqrt N) oracle calls still needed when error is averaged uniformly over x (<1/2). | [`Exercise6_16`](Ch6/Exercise6_16.lean) | formalised |
| Exercise 6.17 | 271 | Show O(sqrt(N/M)) oracle applications required to find a solution when there are M solutions. | [`Exercise6_17`](Ch6/Exercise6_17.lean) | formalised |
| Exercise 6.18 | 273 | Prove the minimum-degree multilinear polynomial representing a Boolean function F is unique. | [`Exercise6_18`](Ch6/Exercise6_18.lean) | formalised |
| Exercise 6.19 | 273 | Show P(X)=1-(1-X0)(1-X1)...(1-X_{N-1}) represents the OR function. | [`Exercise6_19`](Ch6/Exercise6_19.lean) | formalised |
| Problem 6.1 | 274 | Finding the minimum: show O(log(N)sqrt(N)) memory accesses find the smallest element with prob >=1/2. | — | not formalised |
| Problem 6.2 | 274 | Generalized quantum searching: implement U_psi=I-2\|psi><psi\| from U; identify oracle among a set; research k-state case. | [`Problem6_2`](Ch6/Problem6_2.lean) | formalised |
| Exercise 6.20 | 274 | Show Q0(OR) >= N by building a polynomial representing OR from a zero-error quantum circuit. | [`Exercise6_20`](Ch6/Exercise6_20.lean) | formalised |
| Problem 6.3 | 275 | Database retrieval: show all N=2^n bits of X obtainable with N/2+sqrt(N) queries; gives Q2(F)<=N/2+sqrt(N). | — | not formalised |
| Problem 6.4 | 275 | Quantum searching and cryptography: explain why key search fails for Vernam cipher; when it works for DES. | — | no formal statement |

## Chapter 7 — Quantum computers: physical realization

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 7.1 | 284 | Using [x,p]=iℏ, show explicitly that a†a = H/ℏω − 1/2. | — | not formalised |
| Exercise 7.2 | 284 | Given [x,p]=iℏ, compute the commutator [a,a†]. | — | not formalised |
| Exercise 7.3 | 284 | Compute [H,a]; show aⁿ\|ψ⟩ is an eigenstate with energy E−nℏω if \|ψ⟩ has energy E. | — | not formalised |
| Exercise 7.4 | 284 | Show that \|n⟩ = (a†)ⁿ/√(n!) \|0⟩. | — | not formalised |
| Exercise 7.5 | 284 | Verify Eqs (7.11)-(7.12) are consistent with (7.10) and normalization ⟨n\|n⟩=1. | — | not formalised |
| Exercise 7.6 | 288 | Prove a coherent state is an eigenstate of the photon annihilation operator, a\|α⟩=λ\|α⟩. | — | not formalised |
| Exercise 7.7 | 291 | Show the phase-shift circuit transforms a dual-rail state by diag(e^{iπ},1). | [`Exercise7_7`](Ch7/Exercise7_7.lean) | formalised |
| Exercise 7.8 | 291 | Show P\|α⟩ = \|αe^{iΔ}⟩ for a coherent state \|α⟩ under a phase shifter. | — | not formalised |
| Exercise 7.9 | 292 | Show the given circuit acts as a Hadamard gate on dual-rail single-photon states. | [`Exercise7_9`](Ch7/Exercise7_9.lean) | formalised |
| Exercise 7.10 | 292 | Mach-Zehnder interferometer: show identity circuit and compute rotation as function of phase φ. | [`Exercise7_10`](Ch7/Exercise7_10.lean) | formalised |
| Exercise 7.11 | 293 | What is B\|2,0⟩ for θ=π/4 (beamsplitter on a two-photon Fock input)? | — | not formalised |
| Exercise 7.12 | 293 | Compute B\|α⟩\|β⟩ for two coherent-state inputs to a quantum beamsplitter. | — | not formalised |
| Exercise 7.13 | 294 | Optical Deutsch-Jozsa quantum circuit for single-photon dual-rail states using beamsplitters/phase shifters/Kerr media. | [`Exercise7_13`](Ch7/Exercise7_13.lean) | formalised |
| Exercise 7.14 | 296 | Show K\|α⟩\|n⟩=\|αe^{iχLn}⟩\|n⟩ and use it to compute ρ_a; show main term is m=\|β\|². | — | not formalised |
| Exercise 7.15 | 298 | Plot Fabry-Perot cavity power (7.55) as a function of field detuning for R1=R2=0.9. | — | no formal statement |
| Exercise 7.16 | 300 | Electric dipole selection rules: show the integral (7.60) is nonzero only for m2−m1=±1 and Δl=±1. | [`Exercise7_16`](Ch7/Exercise7_16.lean) | formalised |
| Exercise 7.17 | 302 | Show \|χ_n⟩,\|χ̄_n⟩ are eigenstates of the Jaynes-Cummings Hamiltonian with given eigenvalues. | — | not formalised |
| Exercise 7.18 | 303 | Rabi oscillations: show (7.77) by exponentiating H using e^{in·σ}=sin\|n\|+in̂·σ cos\|n\|. | [`Exercise7_18`](Ch7/Exercise7_18.lean) | formalised; corrected statement |
| Exercise 7.19 | 304 | Plot Lorentzian absorption profile (7.79) vs detuning for t=1, g=1.2; identify classical result. | — | no formal statement |
| Exercise 7.20 | 304 | Single photon phase shift: derive (7.80) from U, plot it, and compare with δ/Ω². | — | not formalised |
| Exercise 7.21 | 305 | Explicitly exponentiate (7.82) and show the two-photon phase φ_ab equals arg[e^{iδt}(cosΩ't−i(δ/Ω')sinΩ't)]. | [`Exercise7_21`](Ch7/Exercise7_21.lean) | formalised |
| Exercise 7.22 | 306 | Compute the photon-absorption loss probability 1−⟨110\|U\|110⟩ from (7.82); compare with 1−⟨100\|U\|100⟩. | [`Exercise7_22`](Ch7/Exercise7_22.lean) | formalised |
| Exercise 7.23 | 308 | Show the two-qubit gate (7.87) plus single-qubit ops realizes a controlled-NOT for any φ_a,φ_b, Δ=π. | [`Exercise7_23`](Ch7/Exercise7_23.lean) | formalised |
| Exercise 7.24 | 309 | Compute energy of a nuclear spin in B=10 T and compare with thermal energy k_BT at T=300 K. | — | no formal statement |
| Exercise 7.25 | 314 | Show total angular momenta operators obey SU(2) relations [j_i,j_k]=iε_{ikl}j_l. | [`Exercise7_25`](Ch7/Exercise7_25.lean) | formalised |
| Exercise 7.26 | 314 | Verify properties of \|j,m_j⟩ by writing the 4×4 matrices J² and j_z in that basis. | [`Exercise7_26`](Ch7/Exercise7_26.lean) | formalised |
| Exercise 7.27 | 314 | Three-spin angular momenta: show the listed states are the j=1/2 and j=3/2 total-momentum eigenstates. | [`Exercise7_27`](Ch7/Exercise7_27.lean) | formalised; corrected statement |
| Exercise 7.28 | 315 | Hyperfine states: show spin-3/2 i_x,i_y,i_z satisfy SU(2) rules; build 8×8 f_z,F² and diagonalize for \|F,m_F⟩. | [`Exercise7_28`](Ch7/Exercise7_28.lean) | formalised |
| Exercise 7.29 | 316 | Spontaneous emission: derive rate γ_rad (7.112) from (7.110)-(7.111) by integrating over modes and differentiating. | [`Exercise7_29`](Ch7/Exercise7_29.lean) | formalised; corrected statement |
| Exercise 7.30 | 316 | Electronic state lifetimes: give a value for γ_red^ed using \|⟨0\|μ_ed\|1⟩\|≈qa₀, ω₀/2π≈10¹⁵ Hz. | — | no formal statement |
| Exercise 7.31 | 319 | Construct a Hadamard gate from R_y and R_x rotations. | [`Exercise7_31`](Ch7/Exercise7_31.lean) | formalised |
| Exercise 7.32 | 324 | Show the ion-trap circuit of Fig 7.14 is equivalent (up to phases) to a controlled-NOT with phonon as control. | [`Exercise7_32`](Ch7/Exercise7_32.lean) | formalised |
| Exercise 7.33 | 327 | Magnetic resonance: show (7.128) simplifies to (7.129); find lab-frame Hamiltonian for rotating-frame (7.135). | — | not formalised |
| Exercise 7.34 | 328 | NMR frequencies: compute proton precession frequency in 11.8 T; find B1 gauss for 90° in 10 μs. | — | no formal statement |
| Exercise 7.35 | 328 | Motional narrowing: show the spherical average of the dipolar coupling H^D_{1,2} over n̂ is zero. | [`Exercise7_35`](Ch7/Exercise7_35.lean) | formalised |
| Exercise 7.36 | 329 | Thermal-equilibrium NMR state: show ρ≈1−(ℏω/2k_BT)Z for n=1 and the n=2 diagonal form. | [`Exercise7_36`](Ch7/Exercise7_36.lean) | formalised; corrected statement |
| Exercise 7.37 | 329 | NMR spectrum of coupled spins: compute V(t) for H=JZ1Z2; count spectral lines and magnitudes for H=JZ1(Z2+Z3+Z4). | [`Exercise7_37`](Ch7/Exercise7_37.lean) | formalised |
| Exercise 7.38 | 332 | Refocusing: explicitly show (7.150), R²x1 e^{-iaZ1t} R²x1 = e^{iaZ1t}, using Pauli anti-commutativity. | [`Exercise7_38`](Ch7/Exercise7_38.lean) | formalised; corrected statement |
| Exercise 7.39 | 332 | Three-dimensional refocusing: what set of pulses refocuses evolution under any single-spin H=Σ c_k σ_k? | [`Exercise7_39`](Ch7/Exercise7_39.lean) | formalised |
| Exercise 7.40 | 332 | Refocusing dipolar interactions: give a pulse sequence turning dipolar coupling H^D_{1,2} into the form (7.138). | [`Exercise7_40`](Ch7/Exercise7_40.lean) | formalised |
| Exercise 7.41 | 332 | NMR controlled-NOT: give explicit single-qubit rotation sequence realizing CNOT under Hamiltonian (7.147). | [`Exercise7_41`](Ch7/Exercise7_41.lean) | formalised |
| Exercise 7.42 | 334 | Permutations for temporal labeling: give a quantum circuit for permutations P,P† taking ρ1 to ρ2 of (7.154). | [`Exercise7_42`](Ch7/Exercise7_42.lean) | formalised |
| Exercise 7.43 | 335 | Permutations for logical labeling: give a circuit for permutation P taking ρ of (7.163) to ρ' of (7.165). | [`Exercise7_43`](Ch7/Exercise7_43.lean) | formalised |
| Exercise 7.44 | 335 | Logical labeling for n spins: what is the largest effective pure state constructible from ρ via logical labeling? | [`Exercise7_44`](Ch7/Exercise7_44.lean) | formalised |
| Exercise 7.45 | 336 | State tomography with NMR: show nine experiments (given M_k rotations) suffice to reconstruct two-spin ρ. | [`Exercise7_45`](Ch7/Exercise7_45.lean) | formalised |
| Exercise 7.46 | 337 | How many tomography experiments are sufficient/necessary for three spins? | [`Exercise7_46`](Ch7/Exercise7_46.lean) | formalised |
| Exercise 7.47 | 338 | NMR controlled-NOT gate: verify the Fig 7.19 circuit is a CNOT up to single-qubit phases; give a proper CNOT circuit. | [`Exercise7_47`](Ch7/Exercise7_47.lean) | formalised |
| Exercise 7.48 | 338 | Verify the bottom-left Fig 7.19 circuit creates the Bell state (\|00⟩−\|11⟩)/√2. | [`Exercise7_48`](Ch7/Exercise7_48.lean) | formalised; corrected statement |
| Exercise 7.49 | 338 | NMR swap gate: construct a quantum circuit using e^{-iH/2ℏJ}, R_x, R_y to implement a swap operation. | [`Exercise7_49`](Ch7/Exercise7_49.lean) | formalised |
| Exercise 7.50 | 339 | Find quantum circuits using single-qubit rotations and e^{-iH/2ℏJ} to implement the Grover oracle O for x0=0,1,2. | [`Exercise7_50`](Ch7/Exercise7_50.lean) | formalised |
| Exercise 7.51 | 339 | Show the Grover iteration can be simplified by canceling adjacent single-qubit rotations to obtain (7.172). | [`Exercise7_51`](Ch7/Exercise7_51.lean) | formalised |
| Exercise 7.52 | 345 | Universality of Heisenberg Hamiltonian: show swap U=exp(-iπ S1·S2), √SWAP is universal, and derive CNOT. | [`Exercise7_52`](Ch7/Exercise7_52.lean) | formalised |
| Problem 7.1 | 346 | Efficient temporal labeling: can one construct O(poly(n))-gate circuits cyclically permuting all diagonal elements except \|0ⁿ⟩⟨0ⁿ\|? | [`Problem7_1`](Ch7/Problem7_1.lean) | formalised |
| Problem 7.2 | 346 | Computing with linear optics: for unary photon encoding, show any unitary is built from beamsplitters/phase shifters; DJ + search circuits; and arbitrary U needs exponentially many components. | [`Problem7_2`](Ch7/Problem7_2.lean) | formalised |
| Problem 7.3 | 347 | Control via Jaynes-Cummings: compute A_n=⟨n\|U\|α⟩, large-α approximation p_L, matrix A_L, verify ∫A†A dL=I, estimate fidelity F to ideal U. | — | not formalised |
| Problem 7.4 | 348 | Ion-trap logic with two-level atoms: show S^j swaps spin/motion; find θ keeping computational subspace; build diagonal U (7.187); show it gives a nontrivial CNOT-yielding gate. | — | not formalised |

## Chapter 8 — Quantum noise and quantum operations

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 8.1 | 357 | Show unitary evolution \|ψ⟩→U\|ψ⟩ is equivalently ρ→UρU† for ρ=\|ψ⟩⟨ψ\| | [`Exercise8_1`](Ch8/Exercise8_1.lean) | formalised |
| Exercise 8.2 | 357 | Show measurement outcome state is E_m(ρ)/tr(E_m(ρ)) with p(m)=tr(E_m(ρ)) for E_m(ρ)=M_mρM_m† | [`Exercise8_2`](Ch8/Exercise8_2.lean) | formalised |
| Exercise 8.3 | 361 | Show discarding subsystems after unitary interaction gives operator-sum form with ΣE_k†E_k=I | [`Exercise8_3`](Ch8/Exercise8_3.lean) | formalised |
| Exercise 8.4 | 361 | Give operator-sum representation for U=P0⊗I+P1⊗X with environment starting in \|0⟩ | [`Exercise8_4`](Ch8/Exercise8_4.lean) | formalised |
| Exercise 8.5 | 361 | Give operator-sum representation for spin-flip interaction U=(X/√2)⊗I+(Y/√2)⊗X | [`Exercise8_5`](Ch8/Exercise8_5.lean) | formalised |
| Exercise 8.6 | 362 | Show composition F∘E of quantum operations is a quantum operation; extend to differing spaces | [`Exercise8_6`](Ch8/Exercise8_6.lean) | formalised |
| Exercise 8.7 | 364 | Find operator-sum reps for E_m from general measurement {M_m} on system+environment; probs tr[E(ρ)] | [`Exercise8_7`](Ch8/Exercise8_7.lean) | formalised |
| Exercise 8.8 | 365 | Explain construction of unitary for system-environment model of a non-trace-preserving operation | [`Exercise8_8`](Ch8/Exercise8_8.lean) | formalised |
| Exercise 8.9 | 366 | Construct measurement model: U with projectors P_m gives outcome m with prob tr(E_m(ρ)) and post-state | [`Exercise8_9`](Ch8/Exercise8_9.lean) | formalised |
| Theorem 8.1 | 368 | E satisfies axioms A1,A2,A3 iff E(ρ)=ΣE_iρE_i† with ΣE_i†E_i≤I | [`Theorem8_1`](Ch8/Theorem8_1.lean) | formalised |
| Theorem 8.2 | 372 | Unitary freedom: {E_i},{F_j} give the same quantum operation iff E_i=Σu_ij F_j for unitary u | [`Theorem8_2`](Ch8/Theorem8_2.lean) | formalised |
| Theorem 8.3 | 373 | Any quantum operation on dim-d system has operator-sum rep with at most d² elements | [`Theorem8_3`](Ch8/Theorem8_3.lean) | formalised |
| Exercise 8.10 | 373 | Prove Theorem 8.3 via W_jk=tr(E_j†E_k) Hermitian rank ≤d²; diagonalize to get ≤d² operation elements | [`Exercise8_10`](Ch8/Exercise8_10.lean) | formalised |
| Exercise 8.11 | 373 | Show a quantum operation from d-dim to d'-dim space needs at most dd' operation elements | [`Exercise8_11`](Ch8/Exercise8_11.lean) | formalised |
| Exercise 8.12 | 375 | Why can O have determinant 1 in the polar decomposition M=OS of the Bloch affine map | [`Exercise8_12`](Ch8/Exercise8_12.lean) | formalised |
| Exercise 8.13 | 375 | Show unitary transformations correspond to rotations of the Bloch sphere | [`Exercise8_13`](Ch8/Exercise8_13.lean) | formalised |
| Exercise 8.14 | 375 | Show det(S) need not be positive in the Bloch affine map decomposition | [`Exercise8_14`](Ch8/Exercise8_14.lean) | formalised |
| Exercise 8.15 | 378 | Illustrate on the Bloch sphere the \|±⟩-basis projective measurement map ρ→\|+⟩⟨+\|ρ\|+⟩⟨+\|+... | — | no formal statement |
| Exercise 8.16 | 378 | Find a non-trace-preserving operation not expressible as Bloch deformation+rotation+displacement | [`Exercise8_16`](Ch8/Exercise8_16.lean) | formalised |
| Exercise 8.17 | 379 | Verify I/2=(ρ+XρX+YρY+ZρZ)/4 via E(A)=(A+XAX+YAY+ZAZ)/4 and Bloch representation | [`Exercise8_17`](Ch8/Exercise8_17.lean) | formalised |
| Exercise 8.18 | 379 | For k≥1 show tr(ρ^k) is never increased by the depolarizing channel | [`Exercise8_18`](Ch8/Exercise8_18.lean) | formalised |
| Exercise 8.19 | 379 | Find an operator-sum representation for the generalized depolarizing channel on d-dim Hilbert space | [`Exercise8_19`](Ch8/Exercise8_19.lean) | formalised |
| Exercise 8.20 | 380 | Show the Figure 8.13 circuit models amplitude damping with sin²(θ/2)=γ | [`Exercise8_20`](Ch8/Exercise8_20.lean) | formalised |
| Exercise 8.21 | 381 | Show H=χ(a†b+b†a) gives amplitude-damping operation elements E_k and that they are trace-preserving | [`Exercise8_21`](Ch8/Exercise8_21.lean) | formalised |
| Exercise 8.22 | 381 | Show amplitude damping of general single-qubit ρ gives the stated damped density matrix | [`Exercise8_22`](Ch8/Exercise8_22.lean) | formalised |
| Exercise 8.23 | 381 | Show E_AD⊗E_AD on dual-rail \|ψ⟩=a\|01⟩+b\|10⟩ has operation elements E0dr, E1dr (error detection) | [`Exercise8_23`](Ch8/Exercise8_23.lean) | formalised; printed statement refuted |
| Exercise 8.24 | 381 | Show spontaneous emission (Jaynes-Cummings, δ=0) traced over field gives amplitude damping | [`Exercise8_24`](Ch8/Exercise8_24.lean) | formalised |
| Exercise 8.25 | 382 | Find temperature T describing stationary state ρ∞ of generalized amplitude damping via Boltzmann | [`Exercise8_25`](Ch8/Exercise8_25.lean) | formalised |
| Exercise 8.26 | 385 | Show the Figure 8.15 circuit models phase damping for appropriate θ | [`Exercise8_26`](Ch8/Exercise8_26.lean) | formalised |
| Exercise 8.27 | 385 | Give the unitary relating phase-damping operation elements (8.127)-(8.128) to (8.129)-(8.130) | [`Exercise8_27`](Ch8/Exercise8_27.lean) | formalised |
| Exercise 8.28 | 386 | Show a single CNOT with mixed environment state models phase damping | [`Exercise8_28`](Ch8/Exercise8_28.lean) | formalised |
| Exercise 8.29 | 386 | Show depolarizing and phase damping channels are unital (E(I)=I) but amplitude damping is not | [`Exercise8_29`](Ch8/Exercise8_29.lean) | formalised |
| Exercise 8.30 | 386 | Show amplitude damping has T2=T1/2, and combined amplitude+phase damping gives T2≤T1/2 | [`Exercise8_30`](Ch8/Exercise8_30.lean) | formalised; printed statement refuted |
| Exercise 8.31 | 386 | Show harmonic-oscillator element ρ_nm=⟨n\|ρ\|m⟩ decays as exp(-λ(n-m)²) under phase damping | [`Exercise8_31`](Ch8/Exercise8_31.lean) | formalised |
| Exercise 8.32 | 394 | Explain how to extend quantum process tomography to non-trace-preserving operations | — | no formal statement |
| Exercise 8.33 | 394 | Prove that specifying a single-qubit operation by Bloch-point transforms needs ≥4 points | [`Exercise8_33`](Ch8/Exercise8_33.lean) | formalised |
| Exercise 8.34 | 394 | Show two-qubit process χ2=Λ2 ρ̄' Λ2 with the stated block/permutation-matrix construction | [`Exercise8_34`](Ch8/Exercise8_34.lean) | formalised |
| Exercise 8.35 | 394 | Determine χ matrix for a one-qubit black box from four measured density matrices (amplitude damping) | [`Exercise8_35`](Ch8/Exercise8_35.lean) | formalised |
| Problem 8.1 | 395 | Solve the Lindblad differential equation and express ρ(0)→ρ(t) as ΣE_k(t)ρ(0)E_k†(t) | [`Problem8_1`](Ch8/Problem8_1.lean) | formalised |
| Problem 8.2 | 395 | Show teleportation via imperfect entanglement induces operation Ê_m reversible by R_m to recover ρ | [`Problem8_2`](Ch8/Problem8_2.lean) | formalised |
| Problem 8.3 | 396 | Show all unital channels are random-unitary averages for single qubits but not for larger systems | [`Problem8_3`](Ch8/Problem8_3.lean) | formalised |

## Chapter 9 — Distance measures for quantum information

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 9.1 | 400 | Compute trace distance between given probability distributions (1,0) vs (1/2,1/2) etc. | [`Exercise9_1`](Ch9/Exercise9_1.lean) | formalised |
| Exercise 9.2 | 400 | Show trace distance between (p,1-p) and (q,1-q) is \|p-q\|. | [`Exercise9_2`](Ch9/Exercise9_2.lean) | formalised |
| Exercise 9.3 | 400 | Compute fidelity of given probability distributions (1,0) vs (1/2,1/2) etc. | [`Exercise9_3`](Ch9/Exercise9_3.lean) | formalised |
| Exercise 9.4 | 401 | Prove D(p,q)=max_S \|p(S)-q(S)\| over subsets S. | [`Exercise9_4`](Ch9/Exercise9_4.lean) | formalised |
| Exercise 9.5 | 401 | Show absolute value may be removed: D(p,q)=max_S (p(S)-q(S)). | [`Exercise9_5`](Ch9/Exercise9_5.lean) | formalised |
| Exercise 9.6 | 403 | Compute trace distance between given qubit density operators. | [`Exercise9_6`](Ch9/Exercise9_6.lean) | formalised |
| Theorem 9.1 | 405 | D(rho,sigma) = max over POVMs of classical D(p_m,q_m) of measurement outcomes. | [`Theorem9_1`](Ch9/Theorem9_1.lean) | formalised |
| Exercise 9.7 | 405 | Show any states rho-sigma = Q-S with Q,S positive on orthogonal supports. | [`Exercise9_7`](Ch9/Exercise9_7.lean) | formalised |
| Theorem 9.2 | 406 | Trace-preserving quantum operations are contractive: D(E(rho),E(sigma))<=D(rho,sigma). | [`Theorem9_2`](Ch9/Theorem9_2.lean) | formalised |
| Theorem 9.3 | 407 | Strong convexity of trace distance for mixtures of states and probability distributions. | [`Theorem9_3`](Ch9/Theorem9_3.lean) | formalised |
| Exercise 9.8 | 408 | Show trace distance convex in first input over state mixtures. | [`Exercise9_8`](Ch9/Exercise9_8.lean) | formalised |
| Exercise 9.9 | 408 | Use Schauder fixed-point theorem to show any trace-preserving quantum op has a fixed point. | [`Exercise9_9`](Ch9/Exercise9_9.lean) | formalised |
| Exercise 9.10 | 408 | Show a strictly contractive trace-preserving quantum op has a unique fixed point. | [`Exercise9_10`](Ch9/Exercise9_10.lean) | formalised |
| Exercise 9.11 | 408 | Show a quantum op mixing in fixed state rho_0 is strictly contractive, hence unique fixed point. | [`Exercise9_11`](Ch9/Exercise9_11.lean) | formalised |
| Exercise 9.12 | 409 | For depolarizing channel, find D(E(rho),E(sigma)) via Bloch and prove strict contractivity. | [`Exercise9_12`](Ch9/Exercise9_12.lean) | formalised |
| Exercise 9.13 | 409 | Show bit flip channel is contractive not strictly; find its fixed points. | [`Exercise9_13`](Ch9/Exercise9_13.lean) | formalised |
| Theorem 9.4 | 410 | Uhlmann's theorem: F(rho,sigma)=max over purifications \|<psi\|phi>\|. | [`Theorem9_4`](Ch9/Theorem9_4.lean) | formalised |
| Lemma 9.5 | 410 | For any operator A and unitary U, \|tr(AU)\| <= tr\|A\|, equality at U=V† of polar decomposition. | [`Lemma9_5`](Ch9/Lemma9_5.lean) | formalised |
| Exercise 9.14 | 410 | Prove fidelity invariance under unitary transforms F(UrhoU†,UsigmaU†)=F(rho,sigma). | [`Exercise9_14`](Ch9/Exercise9_14.lean) | formalised |
| Exercise 9.15 | 411 | Show F(rho,sigma)=max over purifications of sigma with psi fixed purification of rho. | [`Exercise9_15`](Ch9/Exercise9_15.lean) | formalised |
| Exercise 9.16 | 411 | Show tr(A†B)=<m\|(A⊗B)\|m> for m=sum \|i_R>\|i_Q>, Hilbert-Schmidt inner product identity. | [`Exercise9_16`](Ch9/Exercise9_16.lean) | formalised; printed statement refuted |
| Exercise 9.17 | 413 | Show 0<=A(rho,sigma)<=pi/2 with equality in first iff rho=sigma (angle metric). | [`Exercise9_17`](Ch9/Exercise9_17.lean) | formalised |
| Theorem 9.6 | 414 | Monotonicity of fidelity: F(E(rho),E(sigma))>=F(rho,sigma) for trace-preserving E. | [`Theorem9_6`](Ch9/Theorem9_6.lean) | formalised |
| Theorem 9.7 | 414 | Strong concavity of fidelity for state mixtures with probability distributions. | [`Theorem9_7`](Ch9/Theorem9_7.lean) | formalised |
| Exercise 9.18 | 414 | Show angle A(E(rho),E(sigma))<=A(rho,sigma) is contractive under quantum operation. | [`Exercise9_18`](Ch9/Exercise9_18.lean) | formalised |
| Exercise 9.19 | 415 | Prove fidelity jointly concave. | [`Exercise9_19`](Ch9/Exercise9_19.lean) | formalised |
| Exercise 9.20 | 415 | Prove fidelity concave in first entry. | [`Exercise9_20`](Ch9/Exercise9_20.lean) | formalised |
| Exercise 9.21 | 416 | Prove 1-F(\|psi>,sigma)^2 <= D(\|psi>,sigma) for pure vs mixed states. | [`Exercise9_21`](Ch9/Exercise9_21.lean) | formalised |
| Exercise 9.22 | 418 | Chaining property for fidelity measures: E(VU,F∘E)<=E(U,E)+E(V,F). | [`Exercise9_22`](Ch9/Exercise9_22.lean) | formalised |
| Exercise 9.23 | 419 | Show ensemble average fidelity Fbar=1 iff E(rho_j)=rho_j for all j with p_j>0. | [`Exercise9_23`](Ch9/Exercise9_23.lean) | formalised |
| Problem 9.1 | 423 | Alternate characterization: F(rho,sigma)=inf_P tr(rho P)tr(sigma P^-1) over invertible positive P. | [`Problem9_1`](Ch9/Problem9_1.lean) | formalised; printed statement refuted |
| Problem 9.2 | 423 | Show for each rho there exist operation elements {E_i} with F(rho,E)=\|tr(rho E_1)\|^2. | [`Problem9_2`](Ch9/Problem9_2.lean) | formalised |
| Problem 9.3 | 423 | Prove fact (5): subspace fidelity >=1-eta implies entanglement fidelity >=1-(3eta/2). | [`Problem9_3`](Ch9/Problem9_3.lean) | formalised |

## Chapter 10 — Quantum error-correction

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 10.1 | 428 | Verify the encoding circuit of Fig 10.2 encodes a\|0>+b\|1> as a\|000>+b\|111> | [`Exercise10_1`](Ch10/Exercise10_1.lean) | formalised |
| Exercise 10.2 | 429 | Bit flip channel (1-p)rho+pXrhoX has alternate operator-sum rep (1-2p)rho+2pP+rhoP+ +2pP-rhoP- | [`Exercise10_2`](Ch10/Exercise10_2.lean) | formalised |
| Exercise 10.3 | 430 | Measuring Z1Z2 then Z2Z3 equals measuring the four bit-flip projectors, same statistics and post-states | [`Exercise10_3`](Ch10/Exercise10_3.lean) | formalised |
| Exercise 10.4 | 432 | Three qubit bit flip: eight computational-basis projectors; recovery works only for basis states; min fidelity | [`Exercise10_4`](Ch10/Exercise10_4.lean) | formalised |
| Exercise 10.5 | 433 | Shor code phase-flip syndrome corresponds to measuring X1X2X3X4X5X6 and X4X5X6X7X8X9 | [`Exercise10_5`](Ch10/Exercise10_5.lean) | formalised |
| Exercise 10.6 | 433 | Recovery from a phase flip on any of first three Shor-code qubits via applying Z1Z2Z3 | [`Exercise10_6`](Ch10/Exercise10_6.lean) | formalised |
| Theorem 10.1 | 436 | QEC conditions: R correcting E on C exists iff P Ei-dag Ej P = alpha_ij P for Hermitian alpha | [`Theorem10_1`](Ch10/Theorem10_1.lean) | formalised |
| Theorem 10.2 | 438 | Discretization: R correcting noise E also corrects any F whose op elements are linear combinations of Ei | [`Theorem10_2`](Ch10/Theorem10_2.lean) | formalised |
| Exercise 10.7 | 438 | Verify QEC conditions for three qubit bit flip code with given non-trace-preserving noise operation elements | [`Exercise10_7`](Ch10/Exercise10_7.lean) | formalised |
| Exercise 10.8 | 441 | Verify three qubit phase flip code satisfies QEC conditions for error set {I,Z1,Z2,Z3} | [`Exercise10_8`](Ch10/Exercise10_8.lean) | formalised |
| Exercise 10.9 | 441 | Prove three qubit phase flip code protects against error set {I,P1,Q1,P2,Q2,P3,Q3} | [`Exercise10_9`](Ch10/Exercise10_9.lean) | formalised |
| Exercise 10.10 | 441 | Explicitly verify QEC conditions for Shor code with error set I and Xj,Yj,Zj for j=1..9 | [`Exercise10_10`](Ch10/Exercise10_10.lean) | formalised |
| Exercise 10.11 | 441 | Construct operation elements for a single-qubit operation mapping any rho to I/2 | [`Exercise10_11`](Ch10/Exercise10_11.lean) | formalised |
| Exercise 10.12 | 441 | Fidelity between \|0> and E(\|0><0\|) for depolarizing channel is sqrt(1-2p/3); min fidelity argument | [`Exercise10_12`](Ch10/Exercise10_12.lean) | formalised |
| Exercise 10.13 | 443 | Min fidelity F(\|psi>,E(\|psi><psi\|)) for amplitude damping channel parameter gamma is sqrt(1-gamma) | [`Exercise10_13`](Ch10/Exercise10_13.lean) | formalised |
| Exercise 10.14 | 446 | Write generator matrix encoding k bits using r repetitions each ([rk,k] linear code, rk x k) | [`Exercise10_14`](Ch10/Exercise10_14.lean) | formalised |
| Exercise 10.15 | 446 | Adding one column of G to another gives a generator matrix generating the same code | [`Exercise10_15`](Ch10/Exercise10_15.lean) | formalised |
| Exercise 10.16 | 447 | Adding one row of parity check matrix to another leaves code unchanged; standard form [A\|I] | [`Exercise10_16`](Ch10/Exercise10_16.lean) | formalised |
| Exercise 10.17 | 447 | Find a parity check matrix for the [6,2] repetition code of (10.54) | [`Exercise10_17`](Ch10/Exercise10_17.lean) | formalised |
| Exercise 10.18 | 447 | Parity check matrix H and generator matrix G of a linear code satisfy HG=0 | [`Exercise10_18`](Ch10/Exercise10_18.lean) | formalised |
| Exercise 10.19 | 447 | For H=[A\|I], corresponding generator matrix is G=[I;-A] | [`Exercise10_19`](Ch10/Exercise10_19.lean) | formalised |
| Exercise 10.20 | 448 | If any d-1 columns of H independent but some d dependent, code defined by H has distance d | [`Exercise10_20`](Ch10/Exercise10_20.lean) | formalised |
| Exercise 10.21 | 449 | Singleton bound: an [n,k,d] code satisfies n-k >= d-1 | [`Exercise10_21_Singleton`](Ch10/Exercise10_21_Singleton.lean) | formalised |
| Exercise 10.22 | 449 | All Hamming codes have distance 3, correct a single-bit error; are [2^r-1,2^r-r-1,3] codes | [`Exercise10_22`](Ch10/Exercise10_22.lean) | formalised |
| Exercise 10.23 | 449 | Prove the Gilbert-Varshamov bound k/n >= 1 - H(2t/n) | [`Exercise10_23_GilbertVarshamov`](Ch10/Exercise10_23_GilbertVarshamov.lean) | formalised |
| Exercise 10.24 | 450 | A code with generator matrix G is weakly self-dual iff G^T G = 0 | [`Exercise10_24`](Ch10/Exercise10_24.lean) | formalised |
| Exercise 10.25 | 450 | For linear code C: sum_{y in C}(-1)^{x.y} equals \|C\| if x in C-perp, else 0 | [`Exercise10_25`](Ch10/Exercise10_25.lean) | formalised |
| Exercise 10.26 | 451 | Explain how to compute \|x>\|0> -> \|x>\|Hx> using a circuit of controlled-NOTs | [`Exercise10_26`](Ch10/Exercise10_26.lean) | formalised |
| Exercise 10.27 | 452 | Codes CSS_{u,v}(C1,C2) defined by (10.75) are equivalent to CSS(C1,C2) in error-correcting properties | [`Exercise10_27`](Ch10/Exercise10_27.lean) | formalised |
| Exercise 10.28 | 452 | Verify the transpose of matrix (10.77) is the generator of the [7,4,3] Hamming code | [`Exercise10_28`](Ch10/Exercise10_28.lean) | formalised |
| Exercise 10.29 | 454 | V_S is a subspace (closed under linear combos) and equals intersection of eigenvalue-1 eigenspaces of S | [`Exercise10_29`](Ch10/Exercise10_29.lean) | formalised |
| Exercise 10.30 | 455 | Show that -I not in S implies +-iI not in S | [`Exercise10_30`](Ch10/Exercise10_30.lean) | formalised |
| Exercise 10.31 | 455 | Subgroup S generated by g1..gl: all elements commute iff each pair gi,gj commutes | [`Exercise10_31`](Ch10/Exercise10_31.lean) | formalised |
| Exercise 10.32 | 456 | Verify the six generators of Fig 10.6 stabilize the Steane code codewords | [`Exercise10_32`](Ch10/Exercise10_32.lean) | formalised |
| Proposition 10.3 | 457 | For S=<g1..gl>, -I not in S: generators independent iff check-matrix rows linearly independent | [`Proposition10_3`](Ch10/Proposition10_3.lean) | formalised |
| Exercise 10.33 | 457 | g and g' commute iff r(g) Lambda r(g')^T = 0 (mod 2) | [`Exercise10_33`](Ch10/Exercise10_33.lean) | formalised |
| Exercise 10.34 | 457 | For S=<g1..gl>, -I not in S iff gj^2=I for all j and gj != -I for all j | [`Exercise10_34`](Ch10/Exercise10_34.lean) | formalised; printed statement refuted |
| Exercise 10.35 | 457 | For subgroup S of Gn with -I not in S, g^2=I for all g in S, thus g=g-dagger | [`Exercise10_35`](Ch10/Exercise10_35.lean) | formalised |
| Proposition 10.4 | 458 | For independent commuting S with -I not in S, exists g in Gn with g gi g-dag=-gi, g gj g-dag=gj (j!=i) | [`Proposition10_4`](Ch10/Proposition10_4.lean) | formalised |
| Proposition 10.5 | 458 | If S=<g1..g_{n-k}> is generated by n-k independent commuting elements, -I not in S, then V_S is 2^k-dimensional | [`Proposition10_5`](Ch10/Proposition10_5.lean) | formalised |
| Exercise 10.36 | 460 | Explicitly verify CNOT conjugation: UX1U-dag=X1X2, UX2U-dag=X2, UZ1U-dag=Z1, UZ2U-dag=Z1Z2 | [`Exercise10_36`](Ch10/Exercise10_36.lean) | formalised |
| Exercise 10.37 | 460 | Compute U Y1 U-dagger for the CNOT gate U | [`Exercise10_37`](Ch10/Exercise10_37.lean) | formalised |
| Theorem 10.6 | 461 | Any U with U Gn U-dag subset Gn is composable up to global phase from O(n^2) Hadamard/phase/CNOT gates | [`Theorem10_6`](Ch10/Theorem10_6.lean) | formalised |
| Exercise 10.38 | 461 | If two-qubit unitaries U,V conjugate Z1,Z2,X1,X2 identically then U=V | [`Exercise10_38`](Ch10/Exercise10_38.lean) | formalised; printed statement refuted |
| Exercise 10.39 | 461 | Verify phase gate conjugation SXS-dag=Y, SZS-dag=Z | [`Exercise10_39`](Ch10/Exercise10_39.lean) | formalised |
| Exercise 10.40 | 462 | Inductive proof that Hadamard, phase, CNOT generate the normalizer N(Gn) (proof of Thm 10.6) | [`Exercise10_40`](Ch10/Exercise10_40.lean) | formalised |
| Exercise 10.41 | 462 | Verify Eqs (10.92)-(10.95): pi/8 and Toffoli gate conjugation of Pauli matrices | [`Exercise10_41`](Ch10/Exercise10_41.lean) | formalised |
| Theorem 10.7 | 464 | Gottesman-Knill: stabilizer computations (prep, H, S, CNOT, Pauli, Pauli-group measurements) are classically efficiently simulable | [`Theorem10_7_GottesmanKnill`](Ch10/Theorem10_7_GottesmanKnill.lean) | formalised |
| Exercise 10.42 | 464 | Use stabilizer formalism to verify the circuit of Fig 1.13 teleports qubits | [`Exercise10_42`](Ch10/Exercise10_42.lean) | formalised |
| Exercise 10.43 | 465 | Show S subset N(S) for any subgroup S of Gn | [`Exercise10_43`](Ch10/Exercise10_43.lean) | formalised |
| Theorem 10.8 | 466 | Stabilizer QEC conditions: {Ej} with Ej-dag Ek not in N(S)-S for all j,k is a correctable error set for C(S) | [`Theorem10_8`](Ch10/Theorem10_8.lean) | formalised |
| Exercise 10.44 | 466 | Show N(S)=Z(S) for any subgroup S of Gn not containing -I | [`Exercise10_44`](Ch10/Exercise10_44.lean) | formalised |
| Exercise 10.45 | 467 | [n,k,d] stabilizer code can correct located errors on d-1 known-position qubits | [`Exercise10_45_LocatedErrors`](Ch10/Exercise10_45_LocatedErrors.lean) | formalised |
| Exercise 10.46 | 467 | Stabilizer for three qubit phase flip code is generated by X1X2 and X2X3 | [`Exercise10_46`](Ch10/Exercise10_46.lean) | formalised |
| Exercise 10.47 | 468 | Verify generators of Fig 10.11 generate the two Shor-code codewords of (10.13) | [`Exercise10_47`](Ch10/Exercise10_47.lean) | formalised |
| Exercise 10.48 | 468 | Show Zbar=X1..X9 and Xbar=Z1..Z9 act as logical Z,X on the Shor code | [`Exercise10_48`](Ch10/Exercise10_48.lean) | formalised |
| Exercise 10.49 | 469 | Use Theorem 10.8 to verify the five qubit code protects against an arbitrary single-qubit error | [`Exercise10_49`](Ch10/Exercise10_49.lean) | formalised |
| Exercise 10.50 | 469 | Show the five qubit code saturates the quantum Hamming bound (10.51 with equality) | [`Exercise10_50`](Ch10/Exercise10_50.lean) | formalised |
| Exercise 10.51 | 470 | Verify check matrix (10.106) is the stabilizer of CSS(C1,C2); use Thm 10.8 for t-qubit correction | [`Exercise10_51`](Ch10/Exercise10_51.lean) | formalised |
| Exercise 10.52 | 470 | Verify by direct operation on codewords that (10.107) operators act as logical Z and X | [`Exercise10_52`](Ch10/Exercise10_52.lean) | formalised |
| Exercise 10.53 | 471 | Prove the encoded Z operators (from standard-form check matrix) are independent of one another | [`Exercise10_53`](Ch10/Exercise10_53.lean) | formalised |
| Exercise 10.54 | 471 | Prove encoded X operators are independent, commute with generators, and Xbar_j anticommutes only with Zbar_j | [`Exercise10_54`](Ch10/Exercise10_54.lean) | formalised |
| Exercise 10.55 | 471 | Find the Xbar operator for the standard form of the Steane code | [`Exercise10_55`](Ch10/Exercise10_55.lean) | formalised |
| Exercise 10.56 | 471 | Replacing encoded X or Z operator by g times it (g in stabilizer) doesn't change its action on the code | [`Exercise10_56`](Ch10/Exercise10_56.lean) | formalised |
| Exercise 10.57 | 472 | Give the check matrices for the five and nine qubit codes in standard form | [`Exercise10_57`](Ch10/Exercise10_57.lean) | formalised |
| Exercise 10.58 | 474 | Verify circuits of Figs 10.13-10.15 measure operator M / X / Z, and the claimed equivalences | [`Exercise10_58`](Ch10/Exercise10_58.lean) | formalised |
| Exercise 10.59 | 474 | Using Figs 10.14/10.15 identities, replace syndrome circuit Fig 10.16 with Fig 10.17 | [`Exercise10_59`](Ch10/Exercise10_59.lean) | formalised |
| Exercise 10.60 | 474 | Construct a syndrome-measuring circuit (like Fig 10.16) for the nine and five qubit codes | [`Exercise10_60`](Ch10/Exercise10_60.lean) | formalised |
| Exercise 10.61 | 474 | Describe explicit recovery operations Ej-dagger for each syndrome measurable by circuit Fig 10.16 | [`Exercise10_61`](Ch10/Exercise10_61.lean) | formalised |
| Threshold theorem for quantum computation | 481 | A circuit of p(n) gates can be simulated with error <= eps using O(poly(log p(n)/eps) p(n)) gates on hardware failing at rate below threshold | — | not formalised |
| Exercise 10.62 | 482 | Show concatenating [n1,1] and [n2,1] stabilizer codes gives an [n1n2,1] stabilizer code | [`Exercise10_62`](Ch10/Exercise10_62.lean) | formalised |
| Exercise 10.63 | 482 | If U maps Steane code to itself with UZbarU-dag=Xbar, UXbarU-dag=Zbar, then U acts as encoded Hadamard | [`Exercise10_63`](Ch10/Exercise10_63.lean) | formalised |
| Exercise 10.64 | 484 | Z error on CNOT target propagates back to control; show via stabilizer formalism and circuit identities | [`Exercise10_64_BackPropagation`](Ch10/Exercise10_64_BackPropagation.lean) | formalised |
| Exercise 10.65 | 487 | Show two given CNOT+measurement+classically-controlled circuits accomplish qubit swap into \|0> | [`Exercise10_65`](Ch10/Exercise10_65.lean) | formalised |
| Exercise 10.66 | 487 | Using TX=exp(-ipi/4)SX and TU=UT, derive the pi/8 gate circuit of Fig 10.25 | [`Exercise10_66_FTpi8`](Ch10/Exercise10_66_FTpi8.lean) | formalised; printed statement refuted |
| Exercise 10.67 | 487 | Show the given circuit identities (a) and (b) hold (X/Z propagation through controlled gates) | [`Exercise10_67`](Ch10/Exercise10_67.lean) | formalised |
| Exercise 10.68 | 488 | Fault-tolerant Toffoli gate construction via swap+Toffoli circuit and commutation moves (Steane code) | [`Exercise10_68_FTToffoli`](Ch10/Exercise10_68_FTToffoli.lean) | formalised |
| Exercise 10.69 | 491 | Show a single failure in ancilla prep/verification causes at most one X or Y error in the ancilla output | [`Exercise10_69`](Ch10/Exercise10_69.lean) | formalised |
| Exercise 10.70 | 491 | Show Z errors in the ancilla do not propagate to encoded data but give an incorrect measurement result | [`Exercise10_70`](Ch10/Exercise10_70.lean) | formalised |
| Exercise 10.71 | 491 | Verify that for M=e^{-ipi/4}SX the described procedure is a fault-tolerant way to measure M | [`Exercise10_71`](Ch10/Exercise10_71.lean) | formalised |
| Exercise 10.72 | 491 | Show how to fault-tolerantly prepare the Toffoli ancilla state (\|000>+\|010>+\|100>+\|111>)/2 | [`Exercise10_72_ToffoliAncilla`](Ch10/Exercise10_72_ToffoliAncilla.lean) | formalised |
| Exercise 10.73 | 493 | Show the Steane code encoded \|0> can be constructed fault-tolerantly (cat-state ancillas, verify, error prob) | [`Exercise10_73_FTencodedState`](Ch10/Exercise10_73_FTencodedState.lean) | formalised |
| Exercise 10.74 | 493 | Construct a quantum circuit to fault-tolerantly generate the encoded \|0> for the five qubit code | [`Exercise10_74`](Ch10/Exercise10_74.lean) | formalised |
| Problem 10.1 | 495 | Channel equivalence E2=U∘E1∘V is an equivalence relation; turn EC code for E1 into one for E2 | [`Problem10_1`](Ch10/Problem10_1.lean) | formalised |
| Problem 10.2 | 495 | Prove Gilbert-Varshamov bound for CSS codes k/n>=1-2H(2t/n) (and general stabilizer form) | [`Problem10_2_GilbertVarshamov`](Ch10/Problem10_2_GilbertVarshamov.lean) | formalised |
| Problem 10.3 | 495 | Find a circuit taking the standard-form check matrix listing to the encoded form (encode stabilizer codes) | [`Problem10_3_EncodingStabilizer`](Ch10/Problem10_3_EncodingStabilizer.lean) | formalised |
| Problem 10.4 | 496 | Construct a circuit encoding an unknown qubit into a stabilizer code by teleportation | [`Problem10_4_EncodingByTeleportation`](Ch10/Problem10_4_EncodingByTeleportation.lean) | formalised |
| Problem 10.5 | 496 | For [n,1] stabilizer code, explain a fault-tolerant CNOT between two logical qubits using FT prep/measurement/normalizer gates | [`Problem10_5`](Ch10/Problem10_5.lean) | formalised |

## Chapter 11 — Entropy and information

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 11.1 | 501 | Compute Shannon entropy for a fair coin, a fair die, and discuss unfair cases | [`Exercise11_1`](Ch11/Exercise11_1.lean) | formalised |
| Exercise 11.2 | 501 | From axioms on an information function I, show I(p)=k log p, deriving Shannon entropy | [`Exercise11_2`](Ch11/Exercise11_2.lean) | formalised |
| Exercise 11.3 | 504 | Prove the binary entropy H_bin(p) attains its maximum value 1 at p=1/2 | [`Exercise11_3`](Ch11/Exercise11_3.lean) | formalised |
| Exercise 11.4 | 504 | Prove binary entropy is concave, and strictly concave except trivial cases | [`Exercise11_4`](Ch11/Exercise11_4.lean) | formalised |
| Theorem 11.1 | 505 | Non-negativity of relative entropy H(p\|\|q)>=0 with equality iff p=q | [`Theorem11_1`](Ch11/Theorem11_1.lean) | formalised |
| Theorem 11.2 | 505 | For X with d outcomes H(X)<=log d, equality iff uniform | [`Theorem11_2`](Ch11/Theorem11_2.lean) | formalised |
| Exercise 11.5 | 505 | Subadditivity of Shannon entropy via relative entropy identity; H(X,Y)<=H(X)+H(Y) | [`Exercise11_5`](Ch11/Exercise11_5.lean) | formalised |
| Theorem 11.3 | 506 | Basic properties of Shannon entropy: symmetry, conditioning, subadditivity, strong subadditivity, etc. | [`Theorem11_3`](Ch11/Theorem11_3.lean) | formalised |
| Exercise 11.6 | 507 | Prove classical strong subadditivity, equality iff Markov chain Z->Y->X | [`Exercise11_6`](Ch11/Exercise11_6.lean) | formalised |
| Exercise 11.7 | 507 | Express conditional entropy H(Y\|X) as a relative entropy and deduce H(Y\|X)>=0 | [`Exercise11_7`](Ch11/Exercise11_7.lean) | formalised |
| Theorem 11.4 | 508 | Chaining rule for conditional entropies: H(X1..Xn\|Y)=sum H(Xi\|Y,X1..Xi-1) | [`Theorem11_4`](Ch11/Theorem11_4.lean) | formalised |
| Theorem 11.5 | 509 | Data processing inequality: for Markov chain X->Y->Z, H(X)>=H(X:Y)>=H(X:Z) | [`Theorem11_5`](Ch11/Theorem11_5.lean) | formalised |
| Exercise 11.8 | 509 | Show mutual information is not always subadditive via a modulo-2 example | [`Exercise11_8`](Ch11/Exercise11_8.lean) | formalised |
| Exercise 11.9 | 509 | Show mutual information is not always superadditive via a copied-variable example | [`Exercise11_9`](Ch11/Exercise11_9.lean) | formalised |
| Exercise 11.10 | 510 | Show that if X->Y->Z is a Markov chain then so is Z->Y->X | [`Exercise11_10`](Ch11/Exercise11_10.lean) | formalised |
| Theorem 11.7 | 511 | Klein's inequality: quantum relative entropy S(rho\|\|sigma)>=0, equality iff rho=sigma | [`Theorem11_7`](Ch11/Theorem11_7.lean) | formalised |
| Exercise 11.11 | 511 | Calculate von Neumann entropy S(rho) for three specific 2x2 density matrices | [`Exercise11_11`](Ch11/Exercise11_11.lean) | formalised |
| Exercise 11.12 | 511 | Evaluate S(rho) for a specific mixed qubit state and compare to H(p,1-p) | [`Exercise11_12`](Ch11/Exercise11_12.lean) | formalised |
| Theorem 11.6 | 512 | Fannes' inequality: bound on \|S(rho)-S(sigma)\| by trace distance and dimension | [`Theorem11_6`](Ch11/Theorem11_6.lean) | formalised |
| Theorem 11.8 | 513 | Basic properties of von Neumann entropy: non-negativity, bound, purity, joint entropy theorem | [`Theorem11_8`](Ch11/Theorem11_8.lean) | formalised |
| Exercise 11.13 | 514 | Show S(rho⊗sigma)=S(rho)+S(sigma) via joint entropy theorem and directly | [`Exercise11_13`](Ch11/Exercise11_13.lean) | formalised |
| Exercise 11.14 | 514 | Show a pure bipartite state \|AB> is entangled iff S(B\|A)<0 | [`Exercise11_14`](Ch11/Exercise11_14.lean) | formalised |
| Theorem 11.9 | 515 | Projective measurements increase entropy: S(rho')>=S(rho), equality iff rho=rho' | [`Theorem11_9`](Ch11/Theorem11_9.lean) | formalised |
| Exercise 11.15 | 515 | Show a generalized measurement with given operators can decrease qubit entropy | [`Exercise11_15`](Ch11/Exercise11_15.lean) | formalised |
| Exercise 11.16 | 516 | Equality conditions for triangle inequality S(A,B)=S(B)-S(A) via eigenbasis/support | [`Exercise11_16`](Ch11/Exercise11_16.lean) | formalised; printed statement refuted |
| Exercise 11.17 | 516 | Find an explicit nontrivial mixed state for AB with S(A,B)=S(B)-S(A) | [`Exercise11_17`](Ch11/Exercise11_17.lean) | formalised |
| Exercise 11.18 | 517 | Prove equality in concavity inequality (11.79) iff all rho_i are the same | [`Exercise11_18`](Ch11/Exercise11_18.lean) | formalised |
| Exercise 11.19 | 517 | Show unitaries U_j and probs p_j exist with sum p_j U_j A U_j† = tr(A) I/d; deduce I/d is unique max-entropy state | [`Exercise11_19`](Ch11/Exercise11_19.lean) | formalised |
| Theorem 11.10 | 518 | Entropy of a mixture: S(rho)<=sum p_i S(rho_i)+H(p_i), equality iff orthogonal supports | [`Theorem11_10`](Ch11/Theorem11_10.lean) | formalised |
| Exercise 11.20 | 518 | Show P rho P + Q rho Q is a probabilistic unitary mixture; give alt proof of Thm 11.9 | [`Exercise11_20`](Ch11/Exercise11_20.lean) | formalised |
| Exercise 11.21 | 518 | Use concavity of von Neumann entropy to deduce Shannon entropy is concave | [`Exercise11_21`](Ch11/Exercise11_21.lean) | formalised |
| Exercise 11.22 | 518 | Alternate proof of concavity: show f(p)=S(p rho+(1-p)sigma) has f''(p)<=0 | [`Exercise11_22`](Ch11/Exercise11_22.lean) | formalised |
| Exercise 11.23 | 519 | Show joint concavity implies concavity in each input; find a per-input-concave non-jointly-concave function | [`Exercise11_23`](Ch11/Exercise11_23.lean) | formalised |
| Theorem 11.11 | 520 | Lieb's theorem: f(A,B)=tr(X† A^t X B^(1-t)) is jointly concave in positive matrices A,B | [`Theorem11_11`](Ch11/Theorem11_11.lean) | formalised |
| Theorem 11.12 | 520 | Convexity of the quantum relative entropy: S(rho\|\|sigma) is jointly convex | [`Theorem11_12`](Ch11/Theorem11_12.lean) | formalised |
| Corollary 11.13 | 520 | Concavity of the quantum conditional entropy S(A\|B) in the state rho^AB | [`Corollary11_13`](Ch11/Corollary11_13.lean) | formalised |
| Theorem 11.14 | 521 | Strong subadditivity: S(A)+S(B)<=S(A,C)+S(B,C) and S(A,B,C)+S(B)<=S(A,B)+S(B,C) | [`Theorem11_14`](Ch11/Theorem11_14.lean) | formalised |
| Exercise 11.24 | 521 | Show S(A)+S(B)<=S(A,C)+S(B,C) can be obtained as a consequence of strong subadditivity | [`Exercise11_24`](Ch11/Exercise11_24.lean) | formalised |
| Exercise 11.25 | 521 | Show concavity of the quantum conditional entropy follows from strong subadditivity | [`Exercise11_25`](Ch11/Exercise11_25.lean) | formalised |
| Theorem 11.15 | 522 | Reformulations of strong subadditivity: conditioning reduces entropy; discarding/operations never increase mutual info | [`Theorem11_15`](Ch11/Theorem11_15.lean) | formalised |
| Exercise 11.26 | 522 | Prove S(A:B)+S(A:C)<=2S(A); find an example where S(A:B)>S(A) | [`Exercise11_26`](Ch11/Exercise11_26.lean) | formalised |
| Theorem 11.16 | 523 | Subadditivity of the conditional entropy in first and second entries | [`Theorem11_16`](Ch11/Theorem11_16.lean) | formalised |
| Theorem 11.17 | 524 | Monotonicity of relative entropy: S(rho^A\|\|sigma^A)<=S(rho^AB\|\|sigma^AB) | [`Theorem11_17`](Ch11/Theorem11_17.lean) | formalised |
| Problem 11.1 | 525 | Generalized Klein's inequality tr(f(A)-f(B))>=tr((A-B)f'(B)) for convex f; deduce relative entropy non-negativity | [`Problem11_1`](Ch11/Problem11_1.lean) | formalised |
| Problem 11.2 | 525 | Generalized relative entropy for positive operators: scaling, subadditivity <-> joint convexity, mixture bound | [`Problem11_2`](Ch11/Problem11_2.lean) | formalised |
| Problem 11.3 | 525 | Show H(X,Y\|Z)>=H(X\|Z), that S(A,B\|C)>=S(A\|C) can fail, and prove S(A,B\|C)>=S(A\|C)-S(B\|C) | [`Problem11_3`](Ch11/Problem11_3.lean) | formalised; printed statement refuted |
| Problem 11.4 | 526 | Conditional forms of strong subadditivity: prove quantum form; show classical analogue can fail | [`Problem11_4`](Ch11/Problem11_4.lean) | formalised |
| Problem 11.5 | 526 | Research: find a simple proof of the strong subadditivity inequality for quantum entropies | — | no formal statement |

## Chapter 12 — Quantum information theory

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise 12.1 | 530 | Design a 2-qubit circuit copying orthogonal single-qubit states \|psi>,\|phi> | [`Exercise12_1`](Ch12/Exercise12_1.lean) | formalised |
| Theorem 12.1 | 531 | Holevo bound: H(X:Y) <= S(rho) - sum p_x S(rho_x) for any POVM | [`Theorem12_1`](Ch12/Theorem12_1.lean) | formalised |
| Exercise 12.2 | 533 | Show {sqrt(E_y) tensor U_y} defines a trace-preserving quantum operation matching (12.8) | [`Exercise12_2`](Ch12/Exercise12_2.lean) | formalised |
| Exercise 12.3 | 535 | Use Holevo bound to show n qubits carry no more than n bits of classical info | [`Exercise12_3`](Ch12/Exercise12_3.lean) | formalised |
| Exercise 12.4 | 535 | For four given pure states, show max mutual info < 1 bit; construct achieving POVM | [`Exercise12_4`](Ch12/Exercise12_4.lean) | formalised |
| Theorem 12.2 | 539 | Theorem of typical sequences: typicality prob, \|T(n,eps)\| bounds, small-set bound | [`Theorem12_2`](Ch12/Theorem12_2.lean) | formalised |
| Theorem 12.4 | 540 | Shannon's noiseless channel coding theorem: reliable compression iff R > H(X) | [`Theorem12_4`](Ch12/Theorem12_4.lean) | formalised |
| Theorem 12.3 | 541 | Law of large numbers: p(\|S_n - E(X)\| > eps) -> 0 | [`Theorem12_3`](Ch12/Theorem12_3.lean) | formalised |
| Exercise 12.5 | 542 | Variable-length zero-error data compression to any R > H(X) with zero error prob | [`Exercise12_5`](Ch12/Exercise12_5.lean) | formalised |
| Theorem 12.5 | 543 | Typical subspace theorem: tr(P rho^n) bounds, dim bounds, small-subspace bound | [`Theorem12_5`](Ch12/Theorem12_5.lean) | formalised |
| Theorem 12.6 | 544 | Schumacher's noiseless channel coding theorem: reliable compression iff R > S(rho) | [`Theorem12_6`](Ch12/Theorem12_6.lean) | formalised |
| Exercise 12.6 | 546 | Give explicit C_X for Box 12.4; construct circuit for U_n; count elementary ops | [`Exercise12_6`](Ch12/Exercise12_6.lean) | formalised |
| Exercise 12.7 | 546 | Outline circuit to compress qubit source rho = p\|0><0\|+(1-p)\|1><1\| into nR qubits | [`Exercise12_7`](Ch12/Exercise12_7.lean) | formalised |
| Exercise 12.8 | 546 | Ensemble-fidelity compression: show reliable rate R > S(rho) for ensemble source | [`Exercise12_8`](Ch12/Exercise12_8.lean) | formalised |
| Theorem 12.7 | 553 | Shannon's noisy channel coding theorem: C(N) = max_p(x) H(X:Y) | [`Theorem12_7`](Ch12/Theorem12_7.lean) | formalised |
| Exercise 12.9 | 553 | Erasure channel: capacity is 1-p; and exceeds binary symmetric channel capacity | [`Exercise12_9`](Ch12/Exercise12_9.lean) | formalised; printed statement refuted |
| Exercise 12.10 | 553 | Composed channels: C(N2 o N1) <= min(C(N1),C(N2)); strict example | [`Exercise12_10`](Ch12/Exercise12_10.lean) | formalised |
| Theorem 12.8 | 555 | HSW theorem: chi(E) equals product-state capacity C^(1)(E) | [`Theorem12_8`](Ch12/Theorem12_8.lean) | formalised |
| Exercise 12.11 | 555 | Show max in HSW chi expression achieved by ensemble of <=d^2 pure states | [`Exercise12_11`](Ch12/Exercise12_11.lean) | formalised |
| Exercise 12.12 | 561 | Adapt HSW proof to prove Shannon's noisy channel coding theorem | — | no formal statement |
| Theorem 12.9 | 563 | Quantum Fano inequality: S(rho,E) <= H(F)+(1-F)log(d^2-1) | [`Theorem12_9`](Ch12/Theorem12_9.lean) | formalised |
| Exercise 12.13 | 563 | Show entropy exchange S(rho,E) is concave in the quantum operation E | [`Exercise12_13`](Ch12/Exercise12_13.lean) | formalised |
| Theorem 12.10 | 564 | Quantum data processing inequality: S(rho) >= I(rho,E1) >= I(rho,E2 o E1) | [`Theorem12_10`](Ch12/Theorem12_10.lean) | formalised |
| Exercise 12.14 | 567 | Show rho^{RQ1}=rho^R tensor rho^{Q1} is sufficient to correct errors on Q1 | [`Exercise12_14`](Ch12/Exercise12_14.lean) | formalised |
| Exercise 12.15 | 568 | Derive all subadditivity/strong-subadditivity inequalities for two-stage process | [`Exercise12_15`](Ch12/Exercise12_15.lean) | formalised |
| Exercise 12.16 | 571 | Show S(rho)-S(rho')+S(rho',R) >= 0 holds with equality when R perfectly corrects E | [`Exercise12_16`](Ch12/Exercise12_16.lean) | formalised |
| Proposition 12.11 | 574 | x prec y iff x = sum p_j P_j y for probabilities p_j and permutation matrices P_j | [`Proposition12_11`](Ch12/Proposition12_11.lean) | formalised |
| Theorem 12.12 | 574 | Birkhoff's theorem: doubly stochastic iff convex combination of permutation matrices | [`Theorem12_12`](Ch12/Theorem12_12.lean) | formalised |
| Exercise 12.17 | 574 | Show x prec y iff sum max(x_j-t,0) <= sum max(y_j-t,0) for all t and equal sums | [`Exercise12_17`](Ch12/Exercise12_17.lean) | formalised |
| Exercise 12.18 | 574 | Show the set of x with x prec y is convex | [`Exercise12_18`](Ch12/Exercise12_18.lean) | formalised |
| Exercise 12.19 | 574 | Verify x' prec y' in the inductive step of Proposition 12.11 | [`Exercise12_19`](Ch12/Exercise12_19.lean) | formalised |
| Theorem 12.13 | 575 | H prec K (Hermitian) iff H = sum p_j U_j K U_j^dagger | [`Theorem12_13`](Ch12/Theorem12_13.lean) | formalised |
| Proposition 12.14 | 575 | LOCC transform reducible to Alice-measure, send j, Bob-unitary protocol | [`Proposition12_14`](Ch12/Proposition12_14.lean) | formalised |
| Theorem 12.15 | 576 | Bipartite pure \|psi> -> \|phi> by LOCC iff lambda_psi prec lambda_phi | [`Theorem12_15`](Ch12/Theorem12_15.lean) | formalised |
| Exercise 12.20 | 577 | Remove the invertibility assumption on rho_psi in converse of Theorem 12.15 | [`Exercise12_20`](Ch12/Exercise12_20.lean) | formalised |
| Exercise 12.21 | 577 | Entanglement catalysis: \|psi> cannot go to \|phi> by LOCC but \|psi>\|c> can | [`Exercise12_21`](Ch12/Exercise12_21.lean) | formalised |
| Exercise 12.22 | 577 | Entanglement conversion without communication possible iff lambda_psi ~= lambda_phi tensor x | [`Exercise12_22`](Ch12/Exercise12_22.lean) | formalised |
| Exercise 12.23 | 580 | Prove the described entanglement distillation procedure is optimal | [`Exercise12_23`](Ch12/Exercise12_23.lean) | formalised |
| Exercise 12.24 | 580 | Schmidt number cannot be increased by LOCC; Bell-state count non-increasing | [`Exercise12_24`](Ch12/Exercise12_24.lean) | formalised |
| Theorem 12.16 | 584 | Universal hash: H(G(X)\|G) >= Hc(G(X)\|G) >= m - 2^{m-Hc(X)} | [`Theorem12_16`](Ch12/Theorem12_16.lean) | formalised; printed statement refuted |
| Exercise 12.25 | 584 | Count keys needed for n users under public vs private key cryptography | [`Exercise12_25`](Ch12/Exercise12_25.lean) | formalised |
| Theorem 12.17 | 585 | With prob 1-2^{-s}, Hc(X\|U=u) >= Hc(X) - 2log\|U\| - 2s | [`Theorem12_17`](Ch12/Theorem12_17.lean) | formalised |
| Proposition 12.18 | 586 | Information gain implies disturbance for non-orthogonal quantum states | [`Proposition12_18`](Ch12/Proposition12_18.lean) | formalised |
| Exercise 12.26 | 588 | BB84: when b'_k != b_k, a'_k random & uncorrelated with a_k; when equal, a'_k=a_k | [`Exercise12_26`](Ch12/Exercise12_26.lean) | formalised |
| Exercise 12.27 | 589 | Random sampling tests: bound error prob on untested bits < exp(-O(eps^2 n)) | [`Exercise12_27`](Ch12/Exercise12_27.lean) | formalised |
| Exercise 12.28 | 591 | B92: show when b=1, a and a' are perfectly correlated | [`Exercise12_28`](Ch12/Exercise12_28.lean) | formalised |
| Exercise 12.29 | 591 | Give six-state protocol; argue security; discuss noise/eavesdropping sensitivity | [`Exercise12_29`](Ch12/Exercise12_29.lean) | formalised |
| Exercise 12.30 | 594 | Simplify (12.199) to obtain the S(rho) expression in Lemma 12.19 | [`Exercise12_30`](Ch12/Exercise12_30.lean) | formalised |
| Exercise 12.31 | 594 | Show S(rho) bounds Eve's mutual info by giving Eve full control of channel | [`Exercise12_31`](Ch12/Exercise12_31.lean) | formalised |
| Exercise 12.32 | 595 | Local X,Z measurements give same statistics as Bell-basis projectors Pi_bf,Pi_pf | [`Exercise12_32`](Ch12/Exercise12_32.lean) | formalised |
| Exercise 12.33 | 597 | Commuting measurement observables [M_i,M_j]=0 obey classical probability arguments | [`Exercise12_33`](Ch12/Exercise12_33.lean) | formalised |
| Exercise 12.34 | 597 | Entanglement distillation by error-correction: stabilizer measurements yield \|beta>^m | [`Exercise12_34`](Ch12/Exercise12_34.lean) | formalised |
| Exercise 12.35 | 598 | Show CSS states \|xi_{v,z,x}> form an orthonormal basis (sum of projectors = I) | [`Exercise12_35`](Ch12/Exercise12_35.lean) | formalised |
| Exercise 12.36 | 598 | Verify Equation (12.203) expressing \|beta>^n in the CSS state basis | [`Exercise12_36`](Ch12/Exercise12_36.lean) | formalised |
| Exercise 12.37 | 598 | Show measuring one EPR qubit in X (resp Z) collapses other into X (Z) eigenstate | [`Exercise12_37`](Ch12/Exercise12_37.lean) | formalised |
| Problem 12.1 | 602 | Alternate proof of Holevo bound via chi monotonicity and apparatus operation | [`Problem12_1`](Ch12/Problem12_1.lean) | formalised |
| Problem 12.2 | 602 | Prove no-cloning by showing cloning non-orthogonal pure states increases chi | [`Problem12_2`](Ch12/Problem12_2.lean) | formalised |
| Exercise 12.38 | 602 | Show ability to distinguish non-orthogonal states would break BB84 and QKD | [`Exercise12_38`](Ch12/Exercise12_38.lean) | formalised |
| Problem 12.3 | 603 | Design quantum circuit implementing rate R>S(rho) compression scheme | — | no formal statement |
| Problem 12.4 | 603 | Linearity forbids cloning: mixtures of rho1,rho2 not copied by linear procedure | [`Problem12_4`](Ch12/Problem12_4.lean) | formalised |
| Problem 12.5 | 603 | Research: is product-state capacity the true classical capacity with entangled inputs? | — | no formal statement |
| Problem 12.6 | 603 | Research: efficient code construction achieving product-state capacity | — | no formal statement |
| Problem 12.7 | 603 | Research: method to evaluate quantum channel capacity for quantum information | — | no formal statement |

## Appendices

| Item | Page | Summary | Lean file | Status |
|---|---:|---|---|---|
| Exercise A1.1 | 608 | Prove Bayes' rule p(x\|y)=p(y\|x)p(x)/p(y). | — | not formalised |
| Exercise A1.2 | 609 | Prove the law of total probability p(y)=sum_x p(y\|x)p(x). | — | not formalised |
| Exercise A1.3 | 609 | Prove there exists x >= E(X) with p(x) > 0. | — | not formalised |
| Exercise A1.4 | 609 | Prove E(X) is linear in X. | — | not formalised |
| Exercise A1.5 | 609 | For independent X,Y prove E(XY)=E(X)E(Y). | — | not formalised |
| Exercise A1.6 | 609 | Prove Chebyshev's inequality p(\|X-E(X)\|>=lambda*Delta) <= 1/lambda^2. | — | not formalised |
| Exercise A2.1 | 610 | Prove every element of a finite group has finite order (some r with g^r=e). | — | not formalised |
| Theorem A2.1 | 610 | Lagrange's theorem: if H is a subgroup of finite group G then \|H\| divides \|G\|. | — | not formalised |
| Exercise A2.2 | 610 | Prove Lagrange's theorem. | — | not formalised |
| Exercise A2.3 | 611 | Show the order of an element g in G divides \|G\|. | — | not formalised |
| Exercise A2.4 | 611 | Show if y is in conjugacy class G_x then G_y=G_x. | — | not formalised |
| Exercise A2.5 | 611 | Show that in an Abelian group the conjugacy class G_x = {x}. | — | not formalised |
| Exercise A2.6 | 612 | Show any group of prime order is cyclic. | — | not formalised |
| Exercise A2.7 | 612 | Show every subgroup of a cyclic group is cyclic. | — | not formalised |
| Exercise A2.8 | 612 | Show if g has order r then g^m=g^n iff m=n (mod r). | — | not formalised |
| Exercise A2.9 | 612 | Show g1,g2 in same coset of H iff exists h with g2=g1*h. | — | not formalised |
| Exercise A2.10 | 612 | How many cosets of H are there in G? | — | not formalised |
| Exercise A2.11 | 612 | Prove the six listed properties of characters of a matrix group. | — | not formalised |
| Exercise A2.12 | 612 | Show every matrix group is equivalent to a unitary matrix group. | — | not formalised |
| Lemma A2.2 | 613 | Schur's lemma: an intertwiner S is zero or (when n=k) square nonsingular. | — | not formalised |
| Theorem A2.3 | 613 | Matrix group G irreducible iff (1/\|G\|) sum \|chi(g)\|^2 = 1. | — | not formalised |
| Theorem A2.4 | 613 | Fundamental theorem: G has r inequivalent irreps; orthogonality relations for matrix elements. | — | not formalised |
| Exercise A2.13 | 613 | Show every irreducible Abelian matrix group is one-dimensional. | — | not formalised |
| Exercise A2.14 | 613 | Prove that if rho is an irreducible rep of G then \|G\|/d_rho is an integer. | — | not formalised |
| Exercise A2.15 | 613 | Prove characters are orthogonal (row and column orthogonality relations). | — | not formalised |
| Exercise A2.16 | 613 | Find and verify the irreducible representations of S_3 and their orthogonality. | — | not formalised |
| Theorem A2.5 | 614 | Decompose rep rho = sum c_p rho^p with c_p = (1/\|G\|) sum r_i (chi^p_i)* chi_i. | — | not formalised |
| Exercise A2.17 | 614 | Prove the regular representation is faithful. | — | not formalised |
| Exercise A2.18 | 614 | Show character of regular rep is zero except chi(I)=\|G\|. | — | not formalised |
| Exercise A2.19 | 614 | Use Theorem A2.5 to show regular rep contains d_{rho^p} copies of each irrep. | — | not formalised |
| Exercise A2.20 | 614 | Show character of regular rep zero except on identity class; derive sum d_rho chi^rho(g)=N delta_ge. | — | not formalised |
| Exercise A2.21 | 615 | Show sum over irreps d_rho^2 = \|G\|. | — | not formalised |
| Exercise A2.22 | 615 | Substitute inverse FT into FT and prove f-hat(rho) is recovered. | — | not formalised |
| Exercise A2.23 | 615 | For an Abelian group show Fourier relations reduce to the discrete Fourier transform. | — | not formalised |
| Exercise A2.24 | 616 | Construct the Fourier transform over S_3 as a 6x6 unitary matrix. | — | not formalised |
| Exercise A3.1 | 618 | For single-qubit rotations show trace distance D(U,V)=2E(U,V), so measures interchangeable. | — | not formalised |
| Theorem A3.1 | 618 | Solovay-Kitaev theorem: G_l is an epsilon-net in SU(2) for l=O(log^c(1/eps)). | — | not formalised |
| Lemma A3.2 | 619 | If G_l is eps^2-net for S_eps then G_5l is Ceps^3-net for a smaller-radius ball. | — | not formalised |
| Exercise A3.2 | 621 | For Hermitian A,B with tr\|A\|,tr\|B\|<=eps prove D([e^{-iA},e^{-iB}]_gp, e^{-[A,B]}) <= d eps^3. | — | not formalised |
| Exercise A3.3 | 622 | Prove trace-distance formula D(u(x),u(y)) in terms of angles and directions. | — | not formalised |
| Exercise A3.4 | 622 | Show for y=0 that D(u(x),I)=4\|sin(x/4)\|. | — | not formalised |
| Exercise A3.5 | 622 | Show for x,y<=eps that D(u(x),u(y))=\|\|x-y\|\|+O(eps^3). | — | not formalised |
| Problem A3.1 | 623 | Multi-part construction achieving O(log^2(1/eps) log^c log(1/eps)) gate bound for any c>2. | — | not formalised |
| Exercise A3.6 | 623 | Describe an efficient algorithm computing a gate sequence from G that eps-approximates U. | — | no formal statement |
| Problem A3.2 | 624 | Research: find an approximation procedure asymptotically faster than the previous problem's. | — | no formal statement |
| Problem A3.3 | 624 | Research: develop an efficient method for eps-approximating a gate from pi/8 and Hadamard. | — | no formal statement |
| Exercise A4.1 | 625 | Transitivity: show if a\|b and b\|c then a\|c. | — | not formalised |
| Theorem A4.1 | 625 | Fundamental theorem of arithmetic: unique prime factorization of any integer > 1. | — | not formalised |
| Exercise A4.2 | 625 | Show if d\|a and d\|b then d divides ax+by. | — | not formalised |
| Exercise A4.3 | 625 | For positive a,b: if a\|b then a<=b; conclude a\|b and b\|a imply a=b. | — | not formalised |
| Theorem A4.2 | 626 | gcd(a,b) is the least positive integer of the form ax+by. | — | not formalised |
| Exercise A4.4 | 626 | Find the prime factorizations of 697 and 36300. | — | not formalised |
| Corollary A4.3 | 627 | If c divides both a and b then c divides gcd(a,b). | — | not formalised |
| Corollary A4.4 | 627 | a has a multiplicative inverse mod n iff gcd(a,n)=1. | — | not formalised |
| Exercise A4.5 | 627 | For prime p show all 1..p-1 have inverses mod p; which 1..p^2-1 lack inverses mod p^2? | — | not formalised |
| Exercise A4.6 | 627 | Find the multiplicative inverse of 17 modulo 24. | — | not formalised |
| Exercise A4.7 | 627 | Find the multiplicative inverse of n+1 modulo n^2. | — | not formalised |
| Exercise A4.8 | 627 | Uniqueness of the inverse: if b,b' are inverses of a mod n then b=b' (mod n). | — | not formalised |
| Theorem A4.5 | 628 | Euclid step: for r the remainder of a mod b (r!=0), gcd(a,b)=gcd(b,r). | — | not formalised |
| Exercise A4.9 | 628 | Compute gcd from prime factorizations; find gcd(6825,1430). | — | not formalised |
| Theorem A4.6 | 629 | Chinese remainder theorem: pairwise-coprime moduli give a solution unique mod M. | — | not formalised |
| Lemma A4.7 | 630 | For prime p and 1<=k<=p-1, p divides binomial(p,k). | — | not formalised |
| Theorem A4.8 | 630 | Fermat's little theorem: a^p = a (mod p); if p does not divide a then a^{p-1}=1 (mod p). | — | not formalised |
| Theorem A4.9 | 631 | Euler's theorem: if a coprime to n then a^{phi(n)}=1 (mod n). | — | not formalised |
| Exercise A4.10 | 631 | Compute phi(187) (Euler totient). | — | not formalised |
| Exercise A4.11 | 631 | Prove n = sum over divisors d of n of phi(d). | — | not formalised |
| Theorem A4.10 | 632 | For odd prime p and positive alpha, Z*_{p^alpha} is cyclic. | — | not formalised |
| Exercise A4.12 | 632 | Verify Z*_n forms a group of size phi(n) under multiplication mod n. | — | not formalised |
| Exercise A4.13 | 632 | Show {1,a,a^2,...} is a subgroup of Z*_n of size the least r with a^r=1 (mod n). | — | not formalised |
| Exercise A4.14 | 632 | Show a generator g for Z*_n must have order phi(n). | — | not formalised |
| Exercise A4.15 | 632 | Use Lagrange's theorem to reprove a^{phi(n)}=1 (mod n) for a in Z*_n. | — | not formalised |
| Theorem A4.11 | 633 | If x is a nontrivial sqrt of 1 mod composite N then gcd(x+-1,N) gives a nontrivial factor. | — | not formalised |
| Lemma A4.12 | 633 | For odd prime p with 2^d \|\| phi(p^alpha), 2^d divides the order of a random element w.p. 1/2. | — | not formalised |
| Exercise A4.16 | 633 | Use Euler's theorem to show the order of x mod N divides phi(N). | — | not formalised |
| Theorem A4.13 | 634 | For odd composite N, random x has p(r even and x^{r/2}!=-1) >= 1-1/2^m. | — | not formalised |
| Theorem A4.14 | 635 | Any rational x>=1 has a finite simple continued fraction representation. | — | not formalised |
| Exercise A4.17 | 635 | Reduction of order-finding to factoring: efficient factoring gives efficient order-finding. | — | not formalised |
| Theorem A4.15 | 636 | Convergent [a_0..a_n]=p_n/q_n with the standard recurrences for p_n,q_n. | — | not formalised |
| Exercise A4.18 | 636 | Find the continued fraction expansions for 19/17 and 77/65. | — | not formalised |
| Theorem A4.16 | 637 | If \|p/q - x\| <= 1/(2q^2) then p/q is a convergent of the continued fraction for x. | — | not formalised |
| Exercise A4.19 | 637 | Show q_n p_{n-1} - p_n q_{n-1} = (-1)^n and conclude gcd(p_n,q_n)=1. | — | not formalised |
| Problem A4.1 | 638 | Prime number estimate: derive pi(2n) >= n/log(2n) via central binomial bounds. | — | not formalised |
| Exercise A5.1 | 642 | Work through an RSA example encoding 'QUANTUM' with p=3, q=11. | — | no formal statement |
| Exercise A5.2 | 643 | Show d is also an inverse of e modulo r, thus d=d' (mod r). | — | not formalised |
| Problem A5.1 | 644 | Write a program performing RSA encryption/decryption with 20-bit primes. | — | no formal statement |
| Exercise A6.1 | 645 | <= preserved under conjugation: if A<=B then X A X^dag <= X B X^dag for all X. | — | not formalised |
| Exercise A6.2 | 645 | Prove A>=0 iff A is a positive operator. | — | not formalised |
| Exercise A6.3 | 645 | Show <= is a partial order on operators (transitive, antisymmetric, reflexive). | — | not formalised |
| Exercise A6.4 | 645 | For norm \|\|A\|\| and lambda=max\|eigenvalue\|: show \|\|A\|\|>=lambda, equal when Hermitian, and a strict example. | — | not formalised |
| Theorem A6.1 | 646 | Lieb's theorem: f(A,B)=tr(X^dag A^t X B^{1-t}) is jointly concave in positive A,B. | — | not formalised |
| Lemma A6.2 | 646 | For commuting positive operators with R_i>=S_i+T_i, R1^t R2^{1-t} >= S1^t S2^{1-t} + T1^t T2^{1-t}. | — | not formalised |
| Exercise A6.5 | 646 | Prove AB and BA have the same eigenvalues. | — | not formalised |
| Exercise A6.6 | 646 | If AB is Hermitian show \|\|AB\|\| <= \|\|BA\|\|. | — | not formalised |
| Exercise A6.7 | 646 | For positive A show \|\|A\|\|<=1 iff A<=I. | — | not formalised |
| Exercise A6.8 | 646 | For positive A show the superoperators X->AX and X->XA are positive under Hilbert-Schmidt inner product. | — | not formalised |
