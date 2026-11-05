# hypercharge-nonembedding

Lean 4 + Mathlib. The Standard-Model hypercharge operator, written on the one-generation
Pati–Salam content `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)` of `su(4) ⊕ su(2)_L`, is not an element of
`sl₄(K) ⊕ sl₂(K)` (nor of `gl₄(K) ⊕ gl₂(K)`) acting on that content; the commutant of the colour
`sl₃` in `sl₄` is the `B − L` line; and hypercharge is `(1/2)(B − L)` plus a generator acting by
`0` on the left-handed block and by `∓1/2` on the two right-handed conjugate copies. Finite linear
algebra over a field `K` of characteristic zero, explicit in matrix entries, kernel-checked.

* `Challenge.lean` — the trusted surface: the nine definitions and the seven compared statements,
  each left as a `sorry` placeholder. Imports Mathlib only.
* `Solution.lean` — the same definitions verbatim and a proof of each statement with the identical
  text, plus eight auxiliary lemmas (not compared).
* `Axioms.lean` — `#print axioms` on every compared declaration and every auxiliary lemma.
* `comparator.json` — the Palomar comparator configuration (seven theorem names in Challenge order,
  nine definition names, permitted axioms `propext`, `Quot.sound`, `Classical.choice`).
* `BUILD.txt` — toolchain, Mathlib revision, build output, axiom printout, token census, comparator
  run; `SHA256SUMS` — hashes of the source files.

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
`trace Yuc = −2`, `trace Ydc = 2`. 5: entrywise. 6: `norm_num`.

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

This is textbook representation theory of the Pati–Salam decomposition: J. C. Pati and A. Salam,
Phys. Rev. D 10 (1974) 275; H. Georgi and S. L. Glashow, Phys. Rev. Lett. 32 (1974) 438;
R. Slansky, "Group theory for unified model building", Phys. Rep. 79 (1981) 1. The relation
`Y = (1/2)(B − L) + T₃R` and the fact that hypercharge requires a generator outside
`su(4) ⊕ su(2)_L` are standard. The entry claims only the kernel-checked instance stated above:
the specific content, operators, and normalisation, over a field of characteristic zero. No
general theorem (commutants of Levi subalgebras, the trace criterion for semisimple actions) is
formalised.

## Physics reading (a cited application; no compared statement asserts it)

In the author's canon (Pisot Dimensional Theory) the gauge Lie algebra `su(3) ⊕ su(4)` is derived
by a Galois-as-Weyl mechanism (Findings Registry F:60), exactly one `su(2)_L` acts, on left-handed
fields (the V − A structure, F:75), and a gauged `su(2)_R` is excluded at any scale (Ratified
Identifications entry 2). The question examined by the 2026-10-26 panel (its §2.3 and §7(ii)) is
whether hypercharge can be an element of `su(4) ⊕ su(2)_L` on the one-generation content
`(4,2) ⊕ (4̄,1) ⊕ (4̄,1)`. Statements 1, 4 and 7 answer no; statements 2–3 identify the commutant of
`su(3)_c ⊕ su(2)_L` as the `B − L` line; statement 5 identifies what must be added: a generator
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
Lean proof of the existence of pure Yang-Mills theory" for release, and names the larger object as
the existence of QCD and "completions of the Standard Model". OpenAI's announcement of 26 October
2026 describes "a unified completion of the Standard Model of particle physics" without naming its
gauge group or representation content. The statements of this entry are a constraint that any such
completion whose gauge algebra contains `su(4) ⊕ su(2)_L` acting on the one-generation Pati–Salam
content must satisfy: hypercharge requires a generator outside that algebra, acting by `∓1/2` on the
two right-handed conjugate copies. They are not derived from, and say nothing about the correctness
of, the announced proof, whose artifacts are unreleased at the time of writing. The committee's own
words are the only thing cited from these documents.

## Building

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55`
(pinned in `lakefile.toml` and `lake-manifest.json`). `lake exe cache get && lake build`;
`lake env lean Axioms.lean` prints the axioms; `lake comparator` (Palomar) checks Challenge against
Solution with both the nanoda and the Lean kernels. See `BUILD.txt` for the recorded run.

## License

MIT (see `LICENSE`).
