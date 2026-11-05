# hypercharge-nonembedding

Lean 4 + Mathlib. The Standard-Model hypercharge operator, written on the one-generation
Pati–Salam content `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)` of `su(4) ⊕ su(2)_L`, is not an element of
`sl₄(K) ⊕ sl₂(K)` (nor of `gl₄(K) ⊕ gl₂(K)`) acting on that content; the commutant of the colour
`sl₃` in `sl₄` is the `B − L` line; and hypercharge is `(1/2)(B − L)` plus a generator acting by
`0` on the left-handed block and by `∓1/2` on the two right-handed conjugate copies. Finite linear
algebra over a field `K` of characteristic zero, explicit in matrix entries, kernel-checked. This is a
kernel-checked instance of textbook representation theory (the Pati–Salam decomposition), not a new
theorem: the sharpest statement is a `4 × 4` trace computation, and the entry's value is that the
non-embedding, the commutant and the decomposition `Y = (1/2)(B − L) + T₃R` are fixed for exactly this
content and normalisation so that they can be cited exactly.

* `Challenge.lean` — the trusted surface: the nine definitions and the seven compared statements,
  each left as a `sorry` placeholder. Imports Mathlib only.
* `Solution.lean` — the same definitions verbatim and a proof of each statement with the identical
  text, plus eight auxiliary lemmas (not compared).
* `Axioms.lean` — `#print axioms` on every compared declaration and every auxiliary lemma.
* `comparator.json` — the Palomar comparator configuration (seven theorem names in Challenge order,
  nine definition names, permitted axioms `propext`, `Quot.sound`, `Classical.choice`).
* `BUILD.txt` — toolchain, Mathlib revision, build output, axiom printout, token census, comparator
  run; `SHA256SUMS` — hashes of the source and metadata files.

## Setting

`K` is a field; `[CharZero K]` is assumed where a numeral must be non-zero (statements 1, 3, 4, 5,
7); statement 2 needs no characteristic assumption; statement 6 is in `ℚ`. The space is
`V = (K⁴ ⊗ K²) ⊕ K⁴ ⊕ K⁴`, indexed by `Fin 4 × Fin 2`, `Fin 4`, `Fin 4`; colour is `0, 1, 2` of
`Fin 4`, the lepton index is `3`. A pair `(X, Y)` with `X : Matrix (Fin 4) (Fin 4) K`,
`Y : Matrix (Fin 2) (Fin 2) K` acts by

* `rhoL X Y = X ⊗ₖ 1₂ + 1₄ ⊗ₖ Y` on the first summand (the left-handed doublets `(u, d, ν, e)_L`),
* `rhoR X = −Xᵀ` on EACH of the two remaining summands (the dual representation; the conjugate
  up-type copy `(u_R, ν_R)ᶜ` and the conjugate down-type copy `(d_R, e_R)ᶜ` carry the same matrix).

The fixed operators (normalisation `Q = T₃ + Y`): `YL = diag(1/6, 1/6, 1/6, −1/2) ⊗ₖ 1₂`,
`Yuc = diag(−2/3, −2/3, −2/3, 0)`, `Ydc = diag(1/3, 1/3, 1/3, 1)`; `BmL = diag(1/3, 1/3, 1/3, −1)`
(`B − L` on the fundamental), `BmLL = BmL ⊗ₖ 1₂`; `D = diag(1, 1, 1, −3) = 3 · BmL`; `emb A` is a
`3 × 3` matrix placed in the colour block of a `4 × 4` matrix.

## The seven compared statements (namespace `Hypercharge`)

1. `hypercharge_not_in_image` — for all `X`, `Y` (not assumed traceless):
   `¬ (rhoL X Y = YL ∧ rhoR X = Yuc ∧ rhoR X = Ydc)`.
2. `centralizer_sl3_in_sl4` — if `trace X = 0` and `X * emb A = emb A * X` for every `A` with
   `trace A = 0`, then `∃ a, X = a • D`.
3. `centralizer_sl2_trivial` — if `trace Y = 0` and `Y * A = A * Y` for every `2 × 2` `A` with
   `trace A = 0`, then `Y = 0`.
4. `BminusL_same_scalar_on_conjugate_copies` — for every `a`, `rhoR (a • D) ≠ Yuc` and
   `rhoR (a • D) ≠ Ydc`.
5. `hypercharge_decomposition` — `YL = (1/2) • BmLL`, `Yuc = (1/2) • rhoR BmL + (−1/2) • 1`,
   `Ydc = (1/2) • rhoR BmL + (1/2) • 1`.
6. `u1R_one_loop_coefficient` — `−(2/3) · (3 · (8 · (1/2)²)) = −4` in `ℚ`.
7. `hypercharge_not_in_image_on_either_copy` — if `trace X = 0` then `rhoR X ≠ Yuc` and
   `rhoR X ≠ Ydc`.

Proofs. 1: the `(0,0)` entries of `Yuc = Ydc` give `−2/3 = 1/3`. 2: commutation with the three
elementary matrices `E₀₁, E₁₂, E₂₀` of the colour block kills every off-diagonal entry in rows and
columns `0, 1, 2` and equates the three colour diagonal entries; trace zero gives the lepton entry
`−3a`. 3: the same with `E₀₁, E₁₀`, then `2a = 0`. 4 and 7: `trace (−Xᵀ) = −trace X = 0` while
`trace Yuc = −2`, `trace Ydc = 2`. 5: entrywise. 6: `norm_num`. Statement 3 is also a corollary of
Mathlib's `Matrix.mem_range_scalar_of_commute_single`; the elementary-matrix proof is kept so that 2 and 3
read alike.

Statement 7 is the sharpest form of the non-embedding: every traceless `X` fails on each conjugate
copy separately, with no appeal to the commutant or to the pairing of the two copies (the two
copies have opposite traces, so the obstruction is invisible to the total trace on `V`). Statements
2–5 record the structure: the only generators commuting with colour and with `sl₂` are the
multiples of `B − L`, and the difference `Y − (1/2)(B − L)` is a scalar of opposite sign on the two
conjugate copies and zero on the left block. Statement 1 is the version for `gl₄ ⊕ gl₂` (no trace
condition), where only the pairing of the copies obstructs; the fact that both copies receive the
same matrix is the definition of the action and is not a compared statement (an `example` with
`rfl` in `Solution.lean`).

## Prior art

The mathematics is textbook representation theory of the Pati–Salam decomposition: J. C. Pati and
A. Salam, "Lepton number as the fourth 'color'", Phys. Rev. D 10 (1974) 275–289,
doi:10.1103/PhysRevD.10.275; H. Georgi and S. L. Glashow, "Unity of all elementary-particle forces",
Phys. Rev. Lett. 32 (1974) 438–441, doi:10.1103/PhysRevLett.32.438; R. Slansky, "Group theory for
unified model building", Phys. Rep. 79 (1981) 1–128, doi:10.1016/0370-1573(81)90092-2; and, as the
modern exposition for mathematicians of exactly this decomposition and the source this entry
formalises in Lie-algebra form, J. C. Baez and J. Huerta, "The algebra of grand unified theories",
Bull. Amer. Math. Soc. 47 (2010) 483–552, doi:10.1090/S0273-0979-10-01294-2, arXiv:0904.1556, §3.3,
which writes the Standard-Model `U(1)` inside `SU(2) × SU(2) × SU(4)` as `diag(α, α, α, α⁻³)` in
`SU(4)` together with a twist `k` on the right-handed `SU(2)`, finds that `k = 0` (the `SU(4)` factor
alone) fails on the right-handed particles, and that all the hypercharges match for `k = 3` — the
group-level form of statements 5 and 7 (their hypercharge is twice ours, `Q = I₃ + Y/2`). The
relation `Y = (1/2)(B − L) + T₃R` and the need for a generator outside `su(4) ⊕ su(2)_L` are standard;
the entry claims only the kernel-checked instance: this content, these operators, this normalisation,
over a field of characteristic zero. No general theorem (commutants of Levi subalgebras, the trace
criterion for semisimple actions) is formalised.

Search for prior formalizations (all on 2026-11-05). Mathlib at the pin `065356127b1d`: no occurrence
of "Pati", "hypercharge", "Slansky" or "Georgi" in `Mathlib/`; the library objects nearest to the
statements are `LieAlgebra.SpecialLinear.sl` (`Mathlib/Algebra/Lie/Classical.lean`; not used — the
statements carry `trace = 0` on raw matrices) and `Matrix.mem_range_scalar_of_commute_single`
(`Mathlib/Data/Matrix/Basis.lean`; also `Matrix.mem_range_scalar_iff_commute_transvectionStruct`,
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`): statement 3 is a corollary of it (the off-diagonal
`single i j 1` are traceless, so the hypothesis of statement 3 already forces a scalar matrix, and
trace zero in characteristic zero forces zero); statement 2 is not an instance (the test matrices are
confined to the `3 × 3` colour block). Physlib (`leanprover-community/physlib`, formerly
`HEPLean/PhysLean`), master `69f7d2a7`: the Standard-Model hypercharge assignments are formalised as
representations of `SU(3) × SU(2) × U(1)` (`Physlib.Particles.StandardModel.Fermions.*`, e.g.
`UpSinglet.repGaugeGroupI` with `U(1)` exponent `4`, `LeptonDoublet.repGaugeGroupI` with exponent
`−3`), and the hypercharge and `B − L` charge vectors `SMRHN.PlusU1.Y₁ = (1, −4, 2, −3, 6, 0)`,
`SMRHN.PlusU1.BL₁ = (1, −1, −1, −3, 3, 3)` are proved anomaly-free
(`…/RHN/AnomalyCancellation/PlusU1/HyperCharge.lean`, `BMinusL.lean`); the Pati–Salam embedding
`PatiSalam.inclSM`, `(h, g, α) ↦ (blockdiag(α h, α⁻³), g, diag(α³, α⁻³))`, exists only as an
`informal_definition` (no Lean term, no theorem). No declaration there concerns an `sl₄`-action, the
commutant of `sl₃` in `sl₄`, the dual-representation trace, or hypercharge lying outside
`su(4) ⊕ su(2)_L`. The openai/math catalogue (`CONTENTS.md` at `42907c9e`, 2026-10-26; 721
manuscripts, 373 families): no Standard-Model, hypercharge, Pati–Salam or gauge-theory entry. The
Palomar registry (983 results, 753 projects on 2026-11-05): queries `hypercharge`, `Pati Salam`,
`gauge group`, `B-L`, `centralizer Lie algebra` return nothing; the hits for `Standard Model`,
`special linear`, `commutant` are unrelated. Zenodo record 10.5281/zenodo.19910097 (anonymous,
2026-04-29, by its own description unreviewed and written by an AI model as primary author): its
`MetricOrigin/Hypercharge.lean` defines `hypercharge f := f.BmL / 2 + f.T₃R` on a sixteen-row table in
which `T₃L`, `T₃R` and `B − L` are entered as data and checks `Q = T₃L + Y` by `native_decide`; it
formalises no Lie algebra, no action and no non-embedding. No prior formalization of statements 1,
2, 4 or 7 was found in any of these; statements 3, 5 and 6 are elementary and claimed only as
kernel-checked instances. This is a record of what was searched, not a claim that nothing exists
elsewhere.

## Physics reading (a cited application; no compared statement asserts it)

In the author's canon (Pisot Dimensional Theory; a private working record, cited by entry number)
the gauge Lie algebra `su(3) ⊕ su(4)` is derived by a Galois-as-Weyl mechanism (Findings Registry
F:60); given the theory's canonical modulus rule, exactly one `su(2)_L` is forced, acting on
left-handed fields — the chiral gauge structure of V − A (F:75) — and a gauged `su(2)_R` is excluded
at any scale (F:77; Ratified Identifications entry 2, the identification that carries it). The
question, posed in the author's working notes of 2026-10-26, is whether hypercharge can be an element
of `su(4) ⊕ su(2)_L` on the one-generation content `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)`. Statements 1, 4 and 7
answer no; statements 2–3 identify the commutant of `su(3)_c ⊕ su(2)_L` as the `B − L` line, so the
`B − L` half of hypercharge (statement 5's first conjunct) already lies inside the derived `su(4)`;
statement 5 identifies what must be added beyond it: a generator
acting by `0` on the left-handed block and by `∓1/2` on the two right-handed conjugate copies, a
`T₃`-type generator on right-handed fields. Whether that generator is a `u(1)` or the Cartan
element of an `su(2)_R` is not decided by any statement here. Statement 6 is the arithmetic of the
one-loop coefficient `b₀ = −(2/3) Σ_Weyl q²` for such a `u(1)` with the eight right-handed Weyl
fermions of charge `±1/2` per generation and three generations; the formula is sourced physics
and is not proved here.

## Why now (context; no compared statement depends on it)

A shepherding committee (M. R. Douglas, D. J. Gross, A. Jaffe, I. R. Klebanov, N. Nekrasov; KITP,
statements of October 2026 and 3 November 2026) holds custody of a claimed existence proof, produced
by an OpenAI model, of quantum Yang–Mills theory "including coupling to fermions", is checking "the
Lean proof of the existence of pure Yang-Mills theory" for release, and the KITP working-group page
names the larger object as the existence of QCD and "completions of the Standard Model". OpenAI's announcement of 26 October
2026 describes "a unified completion of the Standard Model of particle physics" without naming its
gauge group or representation content. The statements of this entry are a constraint that any such
completion whose gauge algebra contains `su(4) ⊕ su(2)_L` acting on the one-generation Pati–Salam
content must satisfy: hypercharge requires a generator outside that algebra, acting by `∓1/2` on the
two right-handed conjugate copies. They are not derived from, and say nothing about the correctness
of, the announced proof, whose artifacts are unreleased at the time of writing. The committee's own
words, and the KITP page's phrase quoted above, are the only things cited from these documents.

## Building

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55`
(pinned in `lakefile.toml` and `lake-manifest.json`). `lake exe cache get && lake build`;
`lake env lean Axioms.lean` prints the axioms; `lake comparator` (Palomar) checks Challenge against
Solution with both the nanoda and the Lean kernels. See `BUILD.txt` for the recorded run.

## License

MIT (see `LICENSE`).
