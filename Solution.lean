module
public import Mathlib

@[expose] public section
/-!
# Hypercharge is not an element of `sl₄ ⊕ sl₂`: proofs of the compared statements

Each of the five statements of `Challenge.lean` is proved here, with the identical statement,
and the definitions of `Challenge.lean` are repeated verbatim. All proofs are explicit in matrix
entries (`Matrix.ext`, `fin_cases`, `simp`, `norm_num`, `linear_combination`).

* Statement 1: from `rhoR X = Yuc` and `rhoR X = Ydc`, `Yuc = Ydc`; the `(0,0)` entries give
  `−2/3 = 1/3`, false in characteristic zero.
* Statement 2: commutation with the three elementary matrices `E₀₁, E₁₂, E₂₀` of the colour block
  forces every off-diagonal entry in rows and columns `0, 1, 2` to vanish and the three colour
  diagonal entries to agree; trace zero then gives the lepton entry `−3a`.
* Statement 3: commutation with `E₀₁` and `E₁₀` forces the off-diagonal entries to vanish and the
  diagonal entries to agree; trace zero gives `2a = 0`, so `a = 0`.
* Statement 4: entrywise.
* Statement 5: apply `Matrix.trace` to the supposed equality: `trace (−Xᵀ) = −trace X = 0`,
  `trace Yuc = −2`, `trace Ydc = 2`.
* Not compared: `BminusL_restriction_ne` (no multiple of `D` restricts to either hypercharge
  block) — `a • D` is traceless, so the two trace inequalities of statement 5 apply.
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

/-- `diag(1, 1, 1, −3)`, the traceless generator of the commutant of `sl₃` in `sl₄` over every
field. When `(3 : K) ≠ 0` it equals `3 · BmL`, the `B − L` direction; in characteristic 3 it is
`diag(1, 1, 1, 0)`, and `BmL` (with `1/3 = 0` in Lean) is not on its line. -/
def D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (![1, 1, 1, -3] : Fin 4 → K)

variable {K}

/-! ### Auxiliary computations (not compared) -/

theorem emb_e01 :
    emb (!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem emb_e12 :
    emb (!![0, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem emb_e20 :
    emb (!![0, 0, 0; 0, 0, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem trace_Yuc [CharZero K] : (Yuc K).trace = -2 := by
  norm_num [Yuc, Matrix.trace_diagonal, Fin.sum_univ_four]

theorem trace_Ydc [CharZero K] : (Ydc K).trace = 2 := by
  norm_num [Ydc, Matrix.trace_diagonal, Fin.sum_univ_four]

theorem trace_rhoR (X : Matrix (Fin 4) (Fin 4) K) : (rhoR X).trace = -X.trace := by
  simp [rhoR]

theorem rhoR_ne_Yuc [CharZero K] (X : Matrix (Fin 4) (Fin 4) K) (htr : X.trace = 0) :
    rhoR X ≠ Yuc K := by
  intro h
  have h' := congrArg Matrix.trace h
  rw [trace_rhoR, htr, trace_Yuc] at h'
  norm_num at h'

theorem rhoR_ne_Ydc [CharZero K] (X : Matrix (Fin 4) (Fin 4) K) (htr : X.trace = 0) :
    rhoR X ≠ Ydc K := by
  intro h
  have h' := congrArg Matrix.trace h
  rw [trace_rhoR, htr, trace_Ydc] at h'
  norm_num at h'

/-! ### The compared statements -/

/-- **1. Hypercharge is not in the image of `gl₄ ⊕ gl₂`** on `(4,2) ⊕ (4̄,1) ⊕ (4̄,1)`: no pair
`(X, Y)` acts as `(YL, Yuc, Ydc)`, because the two conjugate copies receive the same matrix
`−Xᵀ` and `Yuc ≠ Ydc`. -/
theorem hypercharge_not_in_image [CharZero K] (X : Matrix (Fin 4) (Fin 4) K)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    ¬ (rhoL X Y = YL K ∧ rhoR X = Yuc K ∧ rhoR X = Ydc K) := by
  rintro ⟨-, h2, h3⟩
  have h := congrFun (congrFun (h2.symm.trans h3) 0) 0
  norm_num [Yuc, Ydc] at h

/-- **2. The commutant of `sl₃` in `sl₄` is the line through `D`** (the `B − L` line when
`(3 : K) ≠ 0`). A traceless `4 × 4` matrix that
commutes with every traceless `3 × 3` matrix embedded in the colour block is a multiple of
`D = diag(1, 1, 1, −3)`. -/
theorem centralizer_sl3_in_sl4 (X : Matrix (Fin 4) (Fin 4) K) (htr : X.trace = 0)
    (hc : ∀ A : Matrix (Fin 3) (Fin 3) K, A.trace = 0 → X * emb A = emb A * X) :
    ∃ a : K, X = a • D K := by
  have e01 := hc !![0, 1, 0; 0, 0, 0; 0, 0, 0] (by simp [Matrix.trace, Fin.sum_univ_three])
  have e12 := hc !![0, 0, 0; 0, 0, 1; 0, 0, 0] (by simp [Matrix.trace, Fin.sum_univ_three])
  have e20 := hc !![0, 0, 0; 0, 0, 0; 1, 0, 0] (by simp [Matrix.trace, Fin.sum_univ_three])
  rw [emb_e01] at e01
  rw [emb_e12] at e12
  rw [emb_e20] at e20
  have t01 := fun i j => congrFun (congrFun e01 i) j
  have t12 := fun i j => congrFun (congrFun e12 i) j
  have t20 := fun i j => congrFun (congrFun e20 i) j
  -- from E₀₁: (X E₀₁)ᵢⱼ = Xᵢ₀ δⱼ₁, (E₀₁ X)ᵢⱼ = δᵢ₀ X₁ⱼ
  have h10 : X 1 0 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t01 1 1
  have h20 : X 2 0 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t01 2 1
  have h30 : X 3 0 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t01 3 1
  have h12 : X 1 2 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t01 0 2).symm
  have h13 : X 1 3 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t01 0 3).symm
  have h11 : X 1 1 = X 0 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t01 0 1).symm
  -- from E₁₂: (X E₁₂)ᵢⱼ = Xᵢ₁ δⱼ₂, (E₁₂ X)ᵢⱼ = δᵢ₁ X₂ⱼ
  have h01 : X 0 1 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t12 0 2
  have h21 : X 2 1 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t12 2 2
  have h31 : X 3 1 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t12 3 2
  have h23 : X 2 3 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t12 1 3).symm
  have h22' : X 2 2 = X 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t12 1 2).symm
  -- from E₂₀: (X E₂₀)ᵢⱼ = Xᵢ₂ δⱼ₀, (E₂₀ X)ᵢⱼ = δᵢ₂ X₀ⱼ
  have h02 : X 0 2 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t20 0 0
  have h32 : X 3 2 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using t20 3 0
  have h03 : X 0 3 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_four] using (t20 2 3).symm
  have h22 : X 2 2 = X 0 0 := h22'.trans h11
  have htr' : X 0 0 + X 1 1 + X 2 2 + X 3 3 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_four] using htr
  have h33 : X 3 3 = X 0 0 * -3 := by linear_combination htr' - h11 - h22
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, h10, h20, h30, h12, h13, h11, h01, h21, h31, h23, h22, h02, h32, h03, h33]

/-- **3. The commutant of `sl₂` in `sl₂` is zero.** A traceless `2 × 2` matrix that commutes with
every traceless `2 × 2` matrix is zero. -/
theorem centralizer_sl2_trivial [CharZero K] (Y : Matrix (Fin 2) (Fin 2) K) (htr : Y.trace = 0)
    (hc : ∀ A : Matrix (Fin 2) (Fin 2) K, A.trace = 0 → Y * A = A * Y) : Y = 0 := by
  have e01 := hc !![0, 1; 0, 0] (by simp [Matrix.trace, Fin.sum_univ_two])
  have e10 := hc !![0, 0; 1, 0] (by simp [Matrix.trace, Fin.sum_univ_two])
  have t01 := fun i j => congrFun (congrFun e01 i) j
  have t10 := fun i j => congrFun (congrFun e10 i) j
  have h10 : Y 1 0 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_two] using t01 1 1
  have h11 : Y 1 1 = Y 0 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_two] using (t01 0 1).symm
  have h01 : Y 0 1 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_two] using t10 0 0
  have htr' : Y 0 0 + Y 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using htr
  have h2 : (2 : K) * Y 0 0 = 0 := by linear_combination htr' - h11
  have h00 : Y 0 0 = 0 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h11' : Y 1 1 = 0 := h11.trans h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11', h01, h00]

/-- **4. Hypercharge is `(1/2)(B − L)` plus a right-handed `T₃`-type scalar.** On the left block
the extra piece is `0`; on the conjugate up-type copy it is `−1/2 · 1₄`; on the conjugate
down-type copy it is `+1/2 · 1₄`. -/
theorem hypercharge_decomposition [CharZero K] :
    YL K = (1/2 : K) • BmLL K ∧
    Yuc K = (1/2 : K) • rhoR (BmL K) + (-(1/2) : K) • (1 : Matrix (Fin 4) (Fin 4) K) ∧
    Ydc K = (1/2 : K) • rhoR (BmL K) + (1/2 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases i <;> fin_cases j <;>
      simp [YL, BmLL, BmL, Matrix.kroneckerMap_apply, Matrix.one_apply] <;>
      split_ifs <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Yuc, BmL, rhoR] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ydc, BmL, rhoR] <;> norm_num

/-- **5. Each conjugate copy separately excludes hypercharge from `sl₄`.** For every traceless
`X`, `−Xᵀ` is traceless, while `trace Yuc = −2` and `trace Ydc = 2`. -/
theorem hypercharge_not_in_image_on_either_copy [CharZero K] (X : Matrix (Fin 4) (Fin 4) K)
    (htr : X.trace = 0) : rhoR X ≠ Yuc K ∧ rhoR X ≠ Ydc K :=
  ⟨rhoR_ne_Yuc X htr, rhoR_ne_Ydc X htr⟩

/-! ### Further consequences (not compared) -/

/-- No multiple of `D = diag(1, 1, 1, −3)` restricts to either hypercharge block: `a • D` is
traceless, so statement 5 applies. Not a compared statement. -/
theorem BminusL_restriction_ne [CharZero K] (a : K) :
    rhoR (a • D K) ≠ Yuc K ∧ rhoR (a • D K) ≠ Ydc K := by
  have htr : (a • D K).trace = 0 := by
    norm_num [D, Matrix.trace_smul, Matrix.trace_diagonal, Fin.sum_univ_four]
  exact ⟨rhoR_ne_Yuc _ htr, rhoR_ne_Ydc _ htr⟩

/-- The two conjugate copies receive the same matrix: this is the definition of the action
(`rhoR` applied to both), recorded here as an `example`, not a compared statement. -/
example (X : Matrix (Fin 4) (Fin 4) K) : rhoR X = rhoR X := rfl

end Hypercharge
