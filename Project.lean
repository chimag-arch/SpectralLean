import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.Basic



variable {n : Type*} [Fintype n] [DecidableEq n]

def IsReal (x : ℂ) : Prop :=
  x.im = 0

namespace Matrix
  def IsEigenvalue (A: Matrix n n ℂ) (l : ℂ) : Prop :=
  ∃ v : n → ℂ, v ≠ 0 ∧ (Matrix.mulVec A v = l • v)

  def toComplex (A : Matrix n n ℝ) : Matrix n n ℂ :=
  A.map Complex.ofReal

  def CInner (x y : n → ℂ) : ℂ :=
    dotProduct (star x) y
end Matrix

lemma complex_inner_mulVec_eq
  {A : Matrix n n ℂ} (hA : A.IsHermitian)
  (v w : n → ℂ) :
  Matrix.CInner (A.mulVec v) w = Matrix.CInner v (A.mulVec w) := by
    dsimp[Matrix.CInner]
    rw[Matrix.star_mulVec]
    rw[hA]
    rw[Matrix.dotProduct_mulVec]

lemma CInner_smul_right
  (x y : n → ℂ) (a : ℂ) :
  Matrix.CInner x (a • y) = a * Matrix.CInner x y := by
    dsimp[Matrix.CInner]
    simp


lemma CInner_smul_left
  (x y : n → ℂ) (a : ℂ) :
  Matrix.CInner (a • x) y = (star a) * Matrix.CInner x y := by
    dsimp[Matrix.CInner]
    rw[star_smul]
    simp

open scoped BigOperators
lemma CInner_self_eq_sum_normSq
  (v : n → ℂ):
  Matrix.CInner v v = ∑ i, Complex.normSq (v i) := by
    dsimp[Matrix.CInner]
    dsimp[Matrix.dotProduct]
    have H (z : ℂ): (starRingEnd ℂ) z * z = ↑(Complex.normSq z) := by
      rw[Complex.normSq_eq_conj_mul_self]

    have h2 :
      ∑ i : n, (starRingEnd ℂ) (v i) * v i
        = ∑ i : n, (↑(Complex.normSq (v i)) : ℂ) := by
      apply Finset.sum_congr
      rfl
      intro i hi
      apply H (v i)
    simp
    apply h2

lemma CInner_self_eq_zero_iff_zero
  (v : n → ℂ):
  Matrix.CInner v v = 0 ↔ v = 0 := by
    constructor
    · intro h
      rw[CInner_self_eq_sum_normSq v] at h
      have h' : ∑ i : n, Complex.normSq (v i) = 0 := Complex.ofReal_eq_zero.mp h
      have normNonNeg (z : ℂ) := (Complex.normSq_nonneg z)
      have h'': ∑ i, Complex.normSq (v i) = 0 ↔ ∀ i ∈ Finset.univ, Complex.normSq (v i) = 0 := by
        apply Finset.sum_eq_zero_iff_of_nonneg
        intro i hi
        exact normNonNeg (v i)
      have h''' := h''.mp h'
      simp[Complex.normSq_zero] at h'''
      ext i
      dsimp
      rw[h''' i]
      exact Complex.zero_re
      dsimp
      rw[h''' i]
      exact Complex.zero_im
    · intro h
      dsimp[Matrix.CInner]
      rw[h]
      simp

theorem eigenvalues_real_of_symmetric
  (A : Matrix n n ℝ) (hA : A.IsSymm) :
  ∀ l : ℂ, (A.toComplex).IsEigenvalue l → IsReal l  := by
    intro l he
    dsimp[Matrix.IsEigenvalue] at he
    obtain ⟨v, ⟨he1,he2⟩⟩ := he
    have hAherm: (A.toComplex).IsHermitian := by
      dsimp[Matrix.IsHermitian]
      dsimp[Matrix.conjTranspose]
      ext i j
      dsimp [Matrix.toComplex]
      have := Matrix.IsSymm.apply hA i j
      exact this
      dsimp [Matrix.toComplex]
      ring
    have herm_non_zero_imp: ¬ v = 0 → ¬ Matrix.CInner v v = 0 := by
      intro h hA
      have hcontra := (CInner_self_eq_zero_iff_zero v).mp hA
      contradiction
    have herm_non_zero: Matrix.CInner v v ≠ 0 := by
      apply herm_non_zero_imp he1
    have heq := complex_inner_mulVec_eq hAherm v v
    have h1 : Matrix.CInner (Matrix.mulVec (Matrix.toComplex A) v) v = (star l) * Matrix.CInner v v:= by
      rw[he2]
      rw[CInner_smul_left]
    have h2: Matrix.CInner v (Matrix.mulVec (Matrix.toComplex A) v) = l * Matrix.CInner v v := by
      rw[he2]
      rw[CInner_smul_right]
    have h3: Matrix.CInner v v * l = Matrix.CInner v v * (star l):= by
      calc
        Matrix.CInner v v * l = l * Matrix.CInner v v := by ring
        _ = Matrix.CInner v (Matrix.mulVec (Matrix.toComplex A) v) := by rw[h2]
        _ = Matrix.CInner (Matrix.mulVec (Matrix.toComplex A) v) v := by rw[heq]
        _ = star l * Matrix.CInner v v := by rw[h1]
        _ = Matrix.CInner v v * star l := by ring
    have hfin: l = star l := mul_left_cancel₀ herm_non_zero h3
    have hfin': star l = l := hfin.symm
    apply Complex.conj_eq_iff_im.mp
    exact hfin'

variable {n : Type*} [Fintype n] [DecidableEq n]
open Matrix Complex
-- 定义正规矩阵 (A* A = A A*)
def Matrix.IsNormal (A : Matrix n n ℂ) : Prop :=
  A.conjTranspose * A = A * A.conjTranspose

-- 定义对角矩阵
def Matrix.IsDiagonal (A : Matrix n n ℂ) : Prop :=
  ∀ i j, i ≠ j → A i j = 0

-- 定义可酉对角化
def IsUnitarilyDiagonalizable (A : Matrix n n ℂ) : Prop :=
  ∃ (U : Matrix n n ℂ) (Λ : Matrix n n ℂ),
    U.conjTranspose * U = 1 ∧
    Λ.IsDiagonal ∧
    A = U * Λ * U.conjTranspose

-- ==========================================
-- 2. 核心假设
-- ==========================================

-- 假设：正规矩阵谱定理 (作为已知条件)
variable (NormalSpectralTheorem : ∀ (A : Matrix n n ℂ), A.IsNormal → IsUnitarilyDiagonalizable A)

-- ==========================================
-- 3. 证明过程
-- ==========================================

-- 【关键步骤 1】辅助引理：证明 Hermitian 矩阵一定是 Normal 矩阵
-- 这就是你要求的 "已知 Hermitian 证明 Normal"
lemma hermitian_implies_normal (A : Matrix n n ℂ) (h : A.IsHermitian) : A.IsNormal := by
  dsimp [Matrix.IsNormal]
  rw [h] -- 因为 A* = A，等式自动成立

-- 【最终定理】厄米矩阵谱定理
theorem hermitian_spectral_theorem
  (A : Matrix n n ℂ) (hA : A.IsHermitian) :
  ∃ (U : Matrix n n ℂ) (Λ : Matrix n n ℂ),
    U.conjTranspose * U = 1 ∧
    Λ.IsDiagonal ∧
    (∀ i, (Λ i i).im = 0) ∧     -- 结论：特征值是实数
    A = U * Λ * U.conjTranspose := by

  -- 第一步：引用上面的引理，由 Hermitian 推出 Normal
  have hNormal : A.IsNormal := hermitian_implies_normal A hA

  -- 第二步：应用正规矩阵谱定理，得到分解 A = U Λ U*
  obtain ⟨U, Λ, hU_unitary, hΛ_diag, h_decomp⟩ := NormalSpectralTheorem A hNormal

  use U, Λ
  constructor; exact hU_unitary
  constructor; exact hΛ_diag
  constructor
  · -- 第三步：证明 Λ 是实矩阵
    intro i

    -- (a) 用 calc 证明 Λ = U* A U
    -- 这种写法非常符合教材风格，一步步展示变换过程
    have h_Λ_eq : U.conjTranspose * A * U = Λ := by
      calc
        U.conjTranspose * A * U
        _ = U.conjTranspose * (U * Λ * U.conjTranspose) * U := by rw [h_decomp]
        _ = (U.conjTranspose * U) * Λ * (U.conjTranspose * U) := by simp only [Matrix.mul_assoc]
        _ = 1 * Λ * 1 := by rw [hU_unitary]
        _ = Λ := by simp

    -- (b) 利用 A = A* 证明 Λ = Λ*
    have h_Λ_herm : Λ.conjTranspose = Λ := by
      calc
        Λ.conjTranspose
        _ = (U.conjTranspose * A * U).conjTranspose := by rw [h_Λ_eq]
        _ = U.conjTranspose * (A.conjTranspose * U) := by simp
        _ = U.conjTranspose * A.conjTranspose * U := by rw[mul_assoc]
        _ = U.conjTranspose * A * U := by rw [hA] -- 【核心】这里用到了 A 是 Hermitian
        _ = Λ := by rw [h_Λ_eq]

    -- (c) 既然 Λ = Λ*，那么对角元也是实数
    have h_diag_val : Λ i i = (Λ.conjTranspose) i i := by rw [h_Λ_herm]

    dsimp [Matrix.conjTranspose] at h_diag_val
    have h_diag_val := Complex.conj_eq_iff_im.mp h_diag_val.symm
    exact h_diag_val

  · -- 第四步：最后补上分解式 A = U Λ U*
    exact h_decomp
