# 100 Important Facts About Quantum Error-Correcting Codes

Status legend: ✅ stated & proved · 🟡 proved in a restated or weaker form (each one says how) · ⬜ not stated

The Lean development contains **no `sorry`** and introduces no new axioms: every theorem below
marked ✅ or 🟡 compiles down to `propext`/`Classical.choice`/`Quot.sound` only.

Names in `code font` are the Lean identifiers (in `QuantumInfo/QECC/*` = `QuantumLib/QECC/*`).

## A. Pauli group structure
1. ✅ The `n`-qubit Paulis form a group. — `PauliOp`, `instGroup`
2. ✅ The Pauli group is finite of order `4^(n+1) = 4 · 4^n`. — `card_pauliOp`
3. ✅ Every Pauli is unitary. — `toMat_mem_unitaryGroup`
4. ✅ The representation `toMat` is faithful (injective). — `toMat_injective`, `toMat_inj_iff`
5. ✅ Two Paulis commute or anticommute. — `toMat_commute_or_anticommute`
6. ✅ Paulis commute iff the symplectic form vanishes. — `toMat_commute_iff`
7. ✅ A Pauli's matrix has trace 0 unless it is a phase. — `toMat_trace`
8. ✅ `toMat` is a monoid hom / respects inverse. — `toMatHom`, `toMat_inv`
9. ✅ The center of the Pauli group is the phases. — `mem_center_iff`
10. ✅ Every commutator of Paulis is `±I`. — `mul_comm_eq_phase`
11. ✅ A Hermitian Pauli squares to `I`. — `sq_eq_one_of_isHermitian`; stabilizer case `StabGroup.sq_eq_one`
12. ✅ Every Pauli has order dividing 4. — `pow_four`, `orderOf_dvd_four`
13. ✅ Pauli group modulo its center is elementary abelian `(ZMod 2)^{2n}`. — `pauliModCenter_equiv`, `toSymHom`, `ker_toSymHom`
14. ✅ `betaPair` is bilinear; the induced symplectic form is alternating and nondegenerate. — `betaPair_mul_left`, `betaPair_mul_right`, `sympForm_self`, `sympForm_nondegenerate`
15. ✅ Conjugation by a Pauli preserves the `x,z` support (only the phase moves). — `weight_conj`, `mem_center_iff_support_zero`

## B. Weight
16. ✅ `weight 1 = 0`. — `weight_one`
17. ✅ `weight P ≤ n`. — `weight_le`
18. ✅ `weight P⁻¹ = weight P`. — `weight_inv`
19. ✅ Weight is subadditive: `weight (P*Q) ≤ weight P + weight Q`. — `weight_mul_le`
20. ✅ `weight P = 0 ↔ P` is a phase. — `weight_eq_zero_iff`
21. ✅ Weight equals the size of the support of `(x,z)`. — `weight_eq_card_support`
22. ✅ Reverse triangle: `weight P − weight Q ≤ weight (P*Q)`. — `weight_sub_le_weight_mul`
23. ✅ Conjugation preserves weight. — `weight_conj`
24. ✅ Number of Paulis of weight `w` is `C(n,w)·3^w` (times phases). — `card_weight_eq`, `HammingCount.card_sphere`
25. ✅ `weight (P·Q⁻¹) ≤ weight P + weight Q`. — `weight_mul_inv_le`

## C. Stabilizer groups
26. ✅ A stabilizer group is abelian. — `StabGroup.isComm`
27. ✅ `-I ∉ S`. — `StabGroup.negI_notMem`
28. ✅ Every stabilizer element squares to `I`. — `sq_eq_one`
29. ✅ `|S|` is a power of 2. — `card_carrier_eq_two_pow`
30. ✅ Stabilizer elements are Hermitian. — `isHermitian_toMat`
31. ✅ `g ∈ S` has trace 0 unless `g = 1`. — `toMat_trace_of_mem`
32. ✅ `|S|` divides `2^n` (carrier order divides group order). — `card_carrier_dvd`
33. ✅ Each `g ∈ S` fixes the code space. — `stabProj_apply_of_mem`, `mem_codeSpace_iff`
34. ✅ For an independent generating family of size `r`, `|S| = 2^r` and `k = n − r`. — `IsGenFamily`, `card_carrier_of_gens`, `numLogical_of_gens`; every isotropic subspace is realized: `exists_stabGroup_symImage_eq`
35. ✅ Two stabilizer elements commute. — `mem_commute`

## D. The code space and its projector
36. ✅ `codeSpace` is the joint `+1`-eigenspace. — `codeSpace`, `mem_codeSpace_iff`
37. ✅ `stabProj = |S|⁻¹ ∑ g` is idempotent. — `stabProj_idem`
38. ✅ `stabProj` is Hermitian. — `stabProj_isHermitian`
39. ✅ `stabProj` is an (orthogonal) projector. — `stabProj_isProj`
40. ✅ range `stabProj` = code space. — `range_stabProj`
41. ✅ `trace stabProj = dim codeSpace`. — `stabProj_trace`
42. ✅ `g · stabProj = stabProj` for `g ∈ S`. — `toMat_mem_mul_stabProj`
43. ✅ `codeSpace ≠ ⊥`. — `codeSpace_ne_bot`
44. ✅ `|S| · dim codeSpace = 2^n`. — `card_mul_codeSpace_finrank`
45. ✅ `dim codeSpace = 2^(n − log₂|S|)`. — `finrank_codeSpace`

## E. Code parameters ⟦n,k,d⟧
46. ✅ `numPhysical S = n`. — `numPhysical`
47. ✅ `dim codeSpace = 2^k`. — `finrank_codeSpace_eq_two_pow`
48. ✅ `k ≤ n`. — `numLogical_le_numPhysical`
49. ✅ `codeSpace = ⊤ ↔ S` trivial. — `codeSpace_eq_top_iff`
50. ✅ `k = n ↔ S` trivial. — `numLogical_eq_numPhysical_iff`
51. ✅ `k = n − dim(symplectic image of S)`. — `numLogical_eq`
52. ✅ trivial code: `codeSpace = ⊤`. — `codeSpace_trivial`
53. ✅ trivial code has `k = n`. — `trivialStabilizer_numLogical`

## F. Distance, detection, correction
54. ✅ `weight E < d ⟹ E` detectable. — `detectable_of_weight_lt_distance`
55. ✅ `E ∈ S ⟹ E` detectable. — `detectable_of_mem`
56. ✅ `2·weight E < d ⟹ E⁻¹F` detectable (correctability). — `detectable_mul_of_weight_lt`
57. ✅ `d ≤ weight` of any logical. — `distance_le_weight_of_logical`
58. ✅ `E` detectable or `E` centralizes `S`. — `detectable_or_mem_centralizer`
59. ✅ no logical of weight `< d ⟹ distance ≥ d`. — `lt_distance_of_no_logical`
60. ✅ distance = min weight over logicals, and the min is attained. — `distance`, `distance_le_weight_of_logical`, `exists_logical_weight_eq_distance`, `distance_eq`
61. ✅ `2t < distance ⟹` the code corrects `t` errors: pairwise detectability of `E⁻¹F`, and — through Knill–Laflamme — an explicit recovery channel, realized as a `QECC` whose single decoder undoes *every* channel error acting on at most `t` qubits (`CorrectsChannelErrors t`, hence also `CorrectsErrors t` and `Decodes`). Arbitrary errors are reduced to Paulis by the discretisation step, `QECC.errMat_mem_span_pauli`. The converse, `corrects t ⟹ 2t < distance`, is not stated. — `corrects_of_two_mul_lt_distance`, `detectable_of_le_half_distance`, `StabGroup.exists_recovery_of_pauli_kraus`, `StabGroup.exists_qecc_corrects_pauli`, `StabGroup.exists_recovery_correctsChannelErrors`, `StabGroup.exists_qecc_correctsChannelErrors`
62. ✅ `weight E < distance ⟹ E` detectable, and no logical below weight `d` forces `distance ≥ d`. — `detectable_of_weight_lt_distance`, `lt_distance_of_no_logical`
63. ✅ Knill–Laflamme (stabilizer form): `E` detectable ⟺ `Π E Π = c Π`. — `knill_laflamme`
64. ✅ `2·weight E < d ⟹ E⁻¹F` detectable, and conversely: for a code with a logical operator, every pair of errors of weight `≤ t` has detectable difference **iff** `2t < d`, so `⌊(d−1)/2⌋` is exactly the correction radius. — `detectable_mul_of_weight_lt`, `exists_undetectable_mul_of_distance_le`, `forall_detectable_mul_iff`
65. ✅ Degeneracy defined and used. — `IsDegenerate`, `SyndromeEq`
66. ✅ Nondegenerate ⟹ equal syndromes force equal errors. — `eq_of_syndromeEq_of_nondegenerate`
67. ✅ The syndrome of an error against `m` generators is an explicit group homomorphism `PauliOp n →* Multiplicative ((ZMod 2)^m)`, bit `j` being the symplectic pairing with generator `j`. Its kernel is the centralizer of the stabilizer, syndromes are constant on stabilizer cosets, and equality of syndromes is exactly the relation `SyndromeEq`; a nonzero syndrome detects the error, logical operators are the nontrivial errors of zero syndrome, and for independent generators the map is onto, so all `2^m` syndromes occur. — `syndrome`, `syndromeHom`, `syndrome_mul`, `ker_syndromeHom`, `syndromeEq_iff_syndrome_eq`, `syndrome_mul_mem`, `detectable_of_syndrome_ne_zero`, `isLogical_iff_syndrome`, `syndrome_surjective`, `syndromeHom_surjective`, `SyndromeEq`, `syndromeEq_equivalence`
68. ✅ Error and error·(stabilizer) have the same syndrome. — `syndromeEq_mul_mem`

## G. Bounds
69. ✅ Quantum Singleton for stabilizer codes: `dim codeSpace ≤ 2^(n − 2(d−1))`, i.e. `k + 2(d−1) ≤ n`. — `singleton_bound`, `numLogical_add_two_mul_distance_le`, `numPhysical_ge_of_one_logical`
70. ✅ General-QECC Singleton: `|d1|·|d2|^{2d} ≤ |d2|^n`, both from correction of an erasure of `2d` qudits and — for a code with an isometric encoder — from `CorrectsErrors d`. The bridge is that a decoder correcting each of two unitary errors also corrects their mixture, which makes the Knill–Laflamme cross terms scalar; discretisation into unitaries then makes *every* operator supported on `2d` qudits compress to a scalar, so the erasure of those qudits is correctable. — `QECC.singleton_bound`, `QECC.singleton_bound_of_erasure`, `QECC.singleton_bound_of_correctsErrors`, `QECC.correctsErasure_of_correctsErrors`, `QECC.exists_scalar_piKron_of_correctsErrors`, `QECC.errMat_mem_of_unitary_mem`, `QECC.CorrectsErasure`, `QECC.card_le_of_recovery`
71. ✅ Quantum Hamming bound (nondegenerate `t`-error code). — `hamming_bound`, `card_ball`, `card_fiber`
72. ✅ Quantum Gilbert–Varshamov existence bound. — `gilbert_varshamov`
73. ✅ `⟦5,1,3⟧` saturates the Hamming bound (perfect). — `fiveQubitCode_perfect`
74. ✅ Rate `k/n ≤ 1 − (2d−2)/n` (Singleton restated). — `rate_le`
75. ✅ No-cloning obstructs `d > n/2`: `2d ≤ n+1` for a stabilizer code with `k ≥ 1`, and `2t < n` for any code with an isometric encoder correcting `t` errors. — `no_cloning_bound`, `QECC.two_mul_lt_card_of_correctsErrors`

## H. CSS codes
76. ✅ CSS construction from orthogonal `X`/`Z` check families. — `cssCode`, `cssElem`, `mem_cssCode_iff`
77. ✅ CSS stabilizers commute — discharged inside `cssCode` from the orthogonality hypothesis. — `cssCode`, `cssCode_xcheck_mem`, `cssCode_zcheck_mem`
78. ✅ CSS logical count. — `cssCode_numLogical`, `cssCode_numLogical_le`, `cssCode_card_carrier`
79. ✅ CSS distance lower bound. — `cssCode_distance_ge`, `cssCode_le_weight_of_isLogical`
80. ✅ CSS is a genuine stabilizer group (`-I ∉ S`) — discharged inside `cssCode`. — `cssCode`
81. ✅ Self-dual CSS from a single self-orthogonal code. — `cssCode_selfDual_isComm` (used for `steaneCode`)
82. ✅ Transversal CNOT is logical CNOT for CSS: it fixes the projector onto the two-block code space, and conjugation acts on two-block Paulis by the four Heisenberg relations of CNOT. — `transversalCNOT`, `transversalCNOT_mem_unitaryGroup`, `transversalCNOT_conj_biMat`, `transversalCNOT_conj_x_control`, `transversalCNOT_conj_x_target`, `transversalCNOT_conj_z_control`, `transversalCNOT_conj_z_target`, `cnotPair_mem_cssCode`, `css_transversal_cnot`
83. ⬜ CSS code space = intersection of two classical code spaces (X/Z). — `css_codeSpace`

## I. Specific codes
84. ✅ Bit-flip repetition code `⟦n,1,1⟧`: a single `Z` is logical, so the quantum distance is `1`. — `repetitionCode`, `repetitionCode_numLogical`, `repetitionCode_card_carrier`, `repetitionCode_isLogical`, `repetitionCode_distance`
85. ⬜ Phase-flip repetition code (X-stabilizers). — `phaseRepetitionCode`
86. ✅ Shor code `⟦9,1,3⟧`. — `shorCode`, `shorCode_numLogical`, `shorCode_distance`
87. ✅ Steane code `⟦7,1,3⟧` (CSS from `[7,4,3]` Hamming). — `steaneCode`, `steaneCode_numLogical`, `steaneCode_distance`
88. ✅ Five-qubit code `⟦5,1,3⟧`. — `fiveQubitCode`, `fiveQubitCode_numLogical`, `fiveQubitCode_distance`
89. ✅ Trivial code has `k = n` and full code space. — `trivialStabilizer`, `trivialStabilizer_numLogical`, `StabGroup.trivial`, `codeSpace_trivial`
90. ⬜ Toric code `⟦2L²,2,L⟧` (statement of parameters). — `toricCode`

## J. Concatenation
91. ✅ Concatenation of codes as a `QECC` composite. — `QECC.concat`, `QECC.parallel`, `concat_decodes`
92. ✅ Concatenation multiplies the correction radius — correcting `a` and `b` errors gives `(a+1)(b+1)−1` — and multiplies the distance. A stabilizer code of distance `d` recovers from an arbitrary error on any *known* set of `d−1` qubits (`CorrectsLocatedErrors`, the erasure model), and located radii multiply, so concatenating codes of distances `d₁` and `d₂` gives a code on `n₁·n₂` qubits recovering from every located error on `d₁·d₂−1` of them; Steane∘Steane is a 49-qubit example correcting 8. — `concat_correctsErrors_mul`, `concat_correctsChannelErrors_mul`, `concat_correctsPattern`, `concat_correctsLocatedErrors_mul`, `exists_qecc_correctsLocatedErrors`, `exists_qubit_qecc_correctsLocatedErrors`, `exists_qecc_concat_distance_mul`, `exists_steane_concat_correctsLocatedErrors`
93. ✅ Concatenation multiplies length: `|io × ii| = |io|·|ii|`. — `concat_card_index`
94. ✅ Concatenation keeps the outer logical register, and its encoder/decoder factor accordingly. — `concat_encoder`, `concat_decoder`
95. ✅ Threshold theorem. One level: a code correcting `1` error concatenated with itself corrects `3`. `L` levels: `m^(L+1)` qudits with correction radius `(t+1)^(L+1)−1` (and distance `d^(L+1)` for located errors). Probabilistically, with each qudit failing independently at rate `p`, the tower fails only if the recursive failure predicate fires, one level renormalises the rate through `p ↦ P(Binom(m,p) > t) ≤ C(m,t+1)·p^(t+1)`, and the level-`L` failure probability is at most `(C(m,t+1)·p^t)^((t+1)^L)` — doubly exponential suppression below the threshold `C(m,t+1)·p^t < 1`, where enough levels push the failure probability below any `ε > 0`. — `concat_threshold_step`, `iterConcat`, `card_iterIdx`, `iterConcat_correctsChannelErrors`, `iterConcat_correctsLocatedErrors`, `FailsPat`, `iterConcat_correctsPattern`, `patWeight`, `patProb`, `blockFailProb`, `patProb_badPat`, `blockFailProb_le`, `patProb_failsPat`, `patProb_failsPat_le`, `exists_correctable_event_ge`, `exists_level_patProb_lt`

## K. Transversal gates & Eastin–Knill
96. ✅ Transversal unitaries: defined, closed under multiplication, unitary. — `IsTransversal`, `isTransversal_one`, `IsTransversal.mul`, `IsTransversal.mem_unitaryGroup`
97. ✅ The transversal logicals of a fixed encoding contain `1` and are closed under multiplication. — `transversalLogicalsWith`, `one_mem_transversalLogicalsWith`, `mul_mem_transversalLogicalsWith`
98. ✅ A transversal gate preserving the code space implements a logical unitary; every code has an encoding isometry. — `exists_logical_of_transversal_preserving`, `exists_isEncoding`, `exists_isometry_stabProj`
99. ✅ **Eastin–Knill**: for a code with at least one logical qubit and distance at least two, the transversal gates are not universal. Cartan's closed-subgroup theorem is proved from scratch (`IsMulSubgroup.exists_exp_eq_of_mem_ball`, `IsMulSubgroup.exists_finset_mul_exp`) and applied to the tuples of single-qubit unitaries whose Kronecker product preserves the code space, a compact subgroup of `Fin n → Matrix (ZMod 2) (ZMod 2) ℂ`. Its Lie algebra elements exponentiate to transversal gates `exp(∑ᵢ 1 ⊗ ⋯ ⊗ aᵢ ⊗ ⋯ ⊗ 1)`, whose generators have weight one and hence lie below the distance; differentiating code preservation at `t = 0` gives `Π·A·Π = A·Π`, which with the distance bound `Π·A·Π = c·Π` yields `A·Π = c·Π`, so the whole flow acts on the code space by the phase `e^{tc}` and contributes no new logical. Finitely many components then bound the transversal logicals up to phase, while the logical unitary group has an infinite pairwise-non-proportional family. A second, independent route assumes discreteness up to phase directly (`SeparatedTransversalLogicals`). — `eastin_knill`, `finitelyManyTransversalComponents`, `isCompact_codePreservingTuples`, `isMulSubgroup_codePreservingTuples`, `exp_transversalHam`, `siteEmbed`, `eastin_knill_of_components`, `transversal_logical_finite_of_components`, `FinitelyManyTransversalComponents`, `exists_scalar_of_lowWeightGen_flow`, `mul_stabProj_of_preservesCodeFlow`, `exp_smul_mul_stabProj`, `actsByScalar_of_isFlowGate`, `IsFullEncoding`, `preservesCode_of_implementsLogicalWith`, `eastin_knill_of_separated`, `transversal_logical_finite`, `SeparatedTransversalLogicals`, `compress_scalar_of_weight_lt`, `implementsLogical_isScalar_of_lowWeight_sum`
100. ✅ Knill–Laflamme ⟺ exact correctability for a general channel (the fundamental theorem, in `QECC`/`CPTPMap` terms): for an encoding isometry `W` and a noise channel `N` with Kraus operators `E`, a recovery channel undoing `N` on the code space exists iff `Wᴴ (E a)ᴴ (E b) W = c a b • 1`. Both directions are proved, plus the corollary that the condition is independent of the Kraus representation. A single recovery channel works for every noise channel whose Kraus operators lie in the span of the errors, so correctability depends on the errors only through that span. — `knill_laflamme_iff`, `IsKnillLaflamme`, `isKnillLaflamme_of_recovery`, `exists_recovery_of_isKnillLaflamme`, `exists_recovery_bilinear`, `exists_recovery_span`, `isKnillLaflamme_congr`, `QECC.exists_decoder_iff_isKnillLaflamme`

## Assumptions, restatements, and what is genuinely missing

The development has no `sorry` and no new axioms. One place deviates from the "textbook"
statement, deliberately and documented at the declaration:

* **`StabGroup.exists_qecc_decodes`** (realization bridge) — produces a `QECC` from a stabilizer
  group whose encoder is the code-space isometry and whose decoder inverts it (`Decodes`), under
  the necessary extra hypothesis `k ≤ m`, which cannot be dropped (`m = 1, k = 2` with the trivial
  stabilizer satisfies the order condition but contradicts `QECC.card_le_of_decodes`).
  `StabGroup.exists_qecc_correctsChannelErrors` strengthens it: with `2t < d` the decoder is the
  Knill–Laflamme recovery, so the code corrects every channel error acting on at most `t` qubits.

Two modelling choices are worth spelling out, since they are what the concatenation results (#92,
#95) quantify over:

* **Distance multiplication (#92) is proved operationally, not via a concatenated stabilizer
  group.** The concatenated group is never constructed; instead the codes are compared through what
  they correct. The relevant notion is `CorrectsLocatedErrors` — the erasure model, in which the
  recovery channel may depend on which qudits were hit — because that is the radius that equals
  `d−1` and that multiplies. For errors at unknown locations a single fixed decoder is forced, and
  the radius is `⌊(d−1)/2⌋` exactly (#64); those radii compose too, one factor of two worse in each
  code.
* **The threshold theorem (#95) assumes i.i.d. errors on the physical qudits and noiseless
  recovery.** Each qudit fails independently with probability `p`, and encoding, decoding and the
  recovery maps themselves are exact; there is no fault-tolerant gadget analysis and no noise in the
  syndrome extraction. Within that model the suppression is proved in full: the failure event is the
  recursive `FailsPat`, each level renormalises the rate exactly (`patProb_badPat`), and the level-`L`
  failure probability is at most `(C(m,t+1)·p^t)^((t+1)^L)`.

The Knill–Laflamme theorem (#100) is proved in both directions and applied to stabilizer codes. The
discretisation of errors is now formalised in both forms it is used in: into unitaries
(`QECC.errMat_mem_of_mem` with the spanning family `unitaryBasis`), which converts `d`-error
correction into `2d`-erasure correction and so gives the general Singleton bound; and into Paulis
(`QECC.errMat_mem_span_pauli`), which converts the stabilizer Knill–Laflamme conditions into
correction of the `piProd`-style error channels `unitaryError` and `channelError`.
