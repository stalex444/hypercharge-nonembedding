module
public import Mathlib

@[expose] public section
/-!
# Hypercharge is not an element of `sl₄ ⊕ sl₂` acting on `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)`

Let `K` be a field of characteristic zero. On `V = (K⁴ ⊗ K²) ⊕ K⁴ ⊕ K⁴` the Lie algebra
`gl₄(K) ⊕ gl₂(K)` acts by `(X, Y) ↦ (X ⊗ 1₂ + 1₄ ⊗ Y, −Xᵀ, −Xᵀ)`: the defining representation
tensored with the defining representation on the first summand, and the dual of the defining
representation of `gl₄` on each of the two remaining summands, which carry the SAME matrix. The
entry asks whether one fixed diagonal operator on `V` — the triple `(YL, Yuc, Ydc)` defined
below, the Standard-Model hypercharge operator (extended by a right-handed neutrino of hypercharge
`0`, which the `(4̄,1)` content contains) written on the Pati–Salam one-generation content
`(4,2) ⊕ (4̄,1) ⊕ (4̄,1)` of `su(4) ⊕ su(2)_L` — lies in the image of this action, and what the
commutant of the colour `sl₃ ⊂ sl₄` and of `sl₂` looks like. This content is the restriction to
`su(4) ⊕ su(2)_L` of the Pati–Salam content `(4,2,1) ⊕ (4̄,1,2)` of `su(4) ⊕ su(2)_L ⊕ su(2)_R`: the
two `(4̄,1)` copies are the two components of the `su(2)_R` doublet, and the generator that
statement 4 isolates is `T₃R`, the reason Pati and Salam include `su(2)_R`. Everything is finite
linear algebra over `K`, explicit in matrix entries.
The entry compares exactly these five statements.

Vocabulary (the definitions below, repeated verbatim in `Solution.lean`). `rhoL X Y` is the
`8 × 8` matrix `X ⊗ₖ 1₂ + 1₄ ⊗ₖ Y` on `K⁴ ⊗ K²` (indices `Fin 4 × Fin 2`); `rhoR X = −Xᵀ` is the
dual representation on a `4̄` copy; `emb A` places a `3 × 3` matrix in the top-left (colour,
indices `0, 1, 2`) block of a `4 × 4` matrix, zero elsewhere (index `3` is the lepton index).
The fixed operators: `YL = diag(1/6, 1/6, 1/6, −1/2) ⊗ₖ 1₂` (hypercharge on the left-handed
doublets `(u, d, ν, e)_L`, normalisation `Q = T₃ + Y`), `Yuc = diag(−2/3, −2/3, −2/3, 0)` (on the
conjugate up-type copy `(u_R, ν_R)ᶜ`), `Ydc = diag(1/3, 1/3, 1/3, 1)` (on the conjugate down-type
copy `(d_R, e_R)ᶜ`), `BmL = diag(1/3, 1/3, 1/3, −1)` (`B − L` on the fundamental),
`BmLL = BmL ⊗ₖ 1₂`, and `D = diag(1, 1, 1, −3) = 3 · BmL`, the traceless generator of the
commutant of `sl₃` in `sl₄`.

The statements:

1. `hypercharge_not_in_image` — for ALL `X : Matrix (Fin 4) (Fin 4) K` and
   `Y : Matrix (Fin 2) (Fin 2) K` (traceless or not, so for `gl₄ ⊕ gl₂`, which contains
   `sl₄ ⊕ sl₂`): not (`rhoL X Y = YL` and `rhoR X = Yuc` and `rhoR X = Ydc`). The two conjugate
   copies receive one matrix `−Xᵀ`, and `Yuc ≠ Ydc`.
2. `centralizer_sl3_in_sl4` — if `X : Matrix (Fin 4) (Fin 4) K` has trace `0` and commutes with
   `emb A` for every traceless `A : Matrix (Fin 3) (Fin 3) K`, then `X = a • D` for some `a : K`.
   The commutant of `sl₃` in `sl₄` is the line through `D` (the `B − L` direction). No
   characteristic assumption.
3. `centralizer_sl2_trivial` — if `Y : Matrix (Fin 2) (Fin 2) K` has trace `0` and commutes with
   every traceless `2 × 2` matrix, then `Y = 0`. The commutant of `sl₂` in `sl₂` is zero.
4. `hypercharge_decomposition` — `YL = (1/2) • BmLL`, `Yuc = (1/2) • rhoR BmL + (−1/2) • 1₄`,
   `Ydc = (1/2) • rhoR BmL + (1/2) • 1₄`: hypercharge is `(1/2)(B − L)` plus an operator that is
   `0` on the left block and the scalars `−1/2`, `+1/2` on the two conjugate copies — `T₃R` on
   this content.
5. `hypercharge_not_in_image_on_either_copy` — for every `X : Matrix (Fin 4) (Fin 4) K` with
   trace `0`: `rhoR X ≠ Yuc` and `rhoR X ≠ Ydc`. Each conjugate copy separately already excludes
   hypercharge from `sl₄`: `trace Yuc = −2`, `trace Ydc = 2`, and `trace (−Xᵀ) = 0`. (The two
   blocks have opposite traces, so hypercharge is traceless on `V` as a whole — the usual
   `Σ Y = 0` — and the obstruction is invisible to the total trace; it is seen summand by
   summand.) This is the sharpest form of the non-embedding and needs neither the commutant nor
   the pairing of the two copies; statements 2–4 record the structure behind it. (That no multiple
   of `D` restricts to either hypercharge block follows at once, since `a • D` is traceless; it is
   proved in `Solution.lean` as a non-compared lemma.)

Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement.

Physics reading (no compared statement asserts it; it is the cited application). In the author's
canon (Pisot Dimensional Theory; a private working record, cited by entry number) the Galois
groups `S₃` and `S₄` of `x³ − x − 1` and `x⁴ − x − 1` are theorems, and reading them as the Weyl
groups of `su(3) ⊕ su(4)` is the theory's identification (its findings log, entry F:60); given
its canonical modulus rule the theory forces exactly one `su(2)_L`, acting on left-handed fields —
the chiral gauge structure of V − A (F:75) — and the exact absence of a gauged `su(2)_R` at any
scale (F:77; Ratified Identifications entry 2, the identification that carries it). Read on the
one-generation content `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)` of `su(4) ⊕ su(2)_L`, statements 1 and 5 say that
the hypercharge operator is not an element of `su(4) ⊕ su(2)_L`; statements 2–3 say that the only
generators of `su(4) ⊕ su(2)_L` commuting with colour `su(3)` and with `su(2)_L` are the multiples
of `B − L`, so the `B − L` half of hypercharge already lies inside the derived `su(4)`; and
statement 4 says that the generator which must be added beyond `su(4) ⊕ su(2)_L` to obtain
hypercharge acts trivially on the left-handed block and by opposite scalars `∓1/2` on the two
right-handed conjugate copies — `T₃R`, as in the Pati–Salam model. Whether that generator is
gauged as a `u(1)` or as the Cartan element of an `su(2)_R` is NOT decided by any statement here.
The mathematics is textbook representation theory of the Pati–Salam decomposition (Pati–Salam
1974; Georgi–Glashow 1974; Slansky, Phys. Rep. 79 (1981); Baez–Huerta, Bull. AMS 47 (2010) §3.3,
the source this entry formalises in Lie-algebra form); the entry claims only this kernel-checked
instance, stated for the specific content and operators above.
-/

open Matrix Kronecker

namespace Hypercharge

variable {K : Type*} [Field K]

/-- The left block of the action: `X ⊗ₖ 1₂ + 1₄ ⊗ₖ Y` on `K⁴ ⊗ K²`, indexed by `Fin 4 × Fin 2`. -/
def rhoL (X : Matrix (Fin 4) (Fin 4) K) (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) K :=
  X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K) + (1 : Matrix (Fin 4) (Fin 4) K) ⊗ₖ Y

/-- The dual (conjugate) representation of `gl₄` on a `4̄` copy: `X ↦ −Xᵀ`. The same matrix acts
on both conjugate copies. -/
def rhoR (X : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K := -Xᵀ

/-- A `3 × 3` matrix placed in the colour block (indices `0, 1, 2`) of a `4 × 4` matrix, zero in
row and column `3`. -/
def emb (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if h : i.val < 3 ∧ j.val < 3 then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

variable (K)

/-- Hypercharge on the left-handed block: `diag(1/6, 1/6, 1/6, −1/2) ⊗ₖ 1₂`. -/
def YL : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) K :=
  Matrix.diagonal (![1/6, 1/6, 1/6, -1/2] : Fin 4 → K) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

/-- Hypercharge on the conjugate up-type copy `(u_R, ν_R)ᶜ`: `diag(−2/3, −2/3, −2/3, 0)`. -/
def Yuc : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (![-2/3, -2/3, -2/3, 0] : Fin 4 → K)

/-- Hypercharge on the conjugate down-type copy `(d_R, e_R)ᶜ`: `diag(1/3, 1/3, 1/3, 1)`. -/
def Ydc : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (![1/3, 1/3, 1/3, 1] : Fin 4 → K)

/-- `B − L` on the fundamental of `gl₄`: `diag(1/3, 1/3, 1/3, −1)`. -/
def BmL : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (![1/3, 1/3, 1/3, -1] : Fin 4 → K)

/-- `B − L` on the left-handed block: `BmL ⊗ₖ 1₂`. -/
def BmLL : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) K := BmL K ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

/-- The traceless generator `diag(1, 1, 1, −3) = 3 · (B − L)` of the commutant of `sl₃` in
`sl₄`. -/
def D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (![1, 1, 1, -3] : Fin 4 → K)

variable {K}

/-- **1. Hypercharge is not in the image of `gl₄ ⊕ gl₂`** on `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)`: no pair
`(X, Y)` acts as `(YL, Yuc, Ydc)`, because the two conjugate copies receive the same matrix
`−Xᵀ` and `Yuc ≠ Ydc`. -/
theorem hypercharge_not_in_image [CharZero K] (X : Matrix (Fin 4) (Fin 4) K)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    ¬ (rhoL X Y = YL K ∧ rhoR X = Yuc K ∧ rhoR X = Ydc K) := by
  sorry

/-- **2. The commutant of `sl₃` in `sl₄` is the `B − L` line.** A traceless `4 × 4` matrix that
commutes with every traceless `3 × 3` matrix embedded in the colour block is a multiple of
`D = diag(1, 1, 1, −3)`. -/
theorem centralizer_sl3_in_sl4 (X : Matrix (Fin 4) (Fin 4) K) (htr : X.trace = 0)
    (hc : ∀ A : Matrix (Fin 3) (Fin 3) K, A.trace = 0 → X * emb A = emb A * X) :
    ∃ a : K, X = a • D K := by
  sorry

/-- **3. The commutant of `sl₂` in `sl₂` is zero.** A traceless `2 × 2` matrix that commutes with
every traceless `2 × 2` matrix is zero. -/
theorem centralizer_sl2_trivial [CharZero K] (Y : Matrix (Fin 2) (Fin 2) K) (htr : Y.trace = 0)
    (hc : ∀ A : Matrix (Fin 2) (Fin 2) K, A.trace = 0 → Y * A = A * Y) : Y = 0 := by
  sorry

/-- **4. Hypercharge is `(1/2)(B − L)` plus a right-handed `T₃`-type scalar.** On the left block
the extra piece is `0`; on the conjugate up-type copy it is `−1/2 · 1₄`; on the conjugate
down-type copy it is `+1/2 · 1₄`. -/
theorem hypercharge_decomposition [CharZero K] :
    YL K = (1/2 : K) • BmLL K ∧
    Yuc K = (1/2 : K) • rhoR (BmL K) + (-(1/2) : K) • (1 : Matrix (Fin 4) (Fin 4) K) ∧
    Ydc K = (1/2 : K) • rhoR (BmL K) + (1/2 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  sorry

/-- **5. Each conjugate copy separately excludes hypercharge from `sl₄`.** For every traceless
`X`, `−Xᵀ` is traceless, while `trace Yuc = −2` and `trace Ydc = 2`. -/
theorem hypercharge_not_in_image_on_either_copy [CharZero K] (X : Matrix (Fin 4) (Fin 4) K)
    (htr : X.trace = 0) : rhoR X ≠ Yuc K ∧ rhoR X ≠ Ydc K := by
  sorry

end Hypercharge
