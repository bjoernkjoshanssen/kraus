import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
-- import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Reflection
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic --  Orientation.oangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine --  EuclideanGeometry.oangle
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Reflection

import Mathlib.Probability.Distributions.Uniform
import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Matrix.Order

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Trace

/-!

# Automatic complexity using linear algebra

We define

 * `Al` (linear algebra automatic complexity over a semiring `R`, allowing any vector to be
  initial or final state)

 * `As` (semi-classical automatic complexity over a semiring `R`, allowing only
  standard basis vectors to be initial or final state)

and prove `log_|R| A ≤ Al < As ≤ A`.

The closest of the newcomers to `A` is probably `As ℕ`.
-/

/-- ast for "asterisk": ast δ is what we in mathematics articles would
 call δ^*, the iteration of the transition function δ over a word in.
 To be able to talk about the identity matrix intelligently,
 we assume the field is at least `ℤ / 2ℤ`.
-/
def myf : ℝ × ℝ → ℝ := by
    intro x
    exact x.fst^2+x.snd^2




noncomputable def partial_deriv_x
    (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f x y

noncomputable def partial_deriv_y
    (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
    fun x => deriv fun y => f x y

noncomputable def part_deriv_x
    (f : (Fin 2 → ℝ) → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f ![x, y]

noncomputable def partDeriv_x
    (f : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
    fun x => part_deriv_x f (x 0) (x 1)



theorem suggestion (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ)
    (h : IsLocalExtr f (WithLp.toLp 2 a)) : fderiv ℝ f (WithLp.toLp 2 a) =0 :=
      IsLocalExtr.fderiv_eq_zero h



-- make a repo with this
theorem grad_zero_of_extr (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ) (h₀ : DifferentiableAt ℝ f (WithLp.toLp 2 a))
    (h : IsLocalExtr f (WithLp.toLp 2 a)) : gradient f (WithLp.toLp 2 a) =0 := by
    apply HasGradientAt.gradient
    have h₁ := (hasFDerivAt_iff_hasGradientAt).mp
        (DifferentiableAt.hasFDerivAt h₀)
    rw [IsLocalExtr.fderiv_eq_zero h] at h₁
    simp only [map_zero] at h₁
    exact h₁





-- example : (!![(1:ℝ),0;0,1]).det = 0 := sorry

def f0 : (Fin 2 → ℝ) → ℝ := by
    intro x
    have := x 0
    have := x 1
    exact (x 0)^2 + (x 1)^2
def f₀ : EuclideanSpace ℝ (Fin 2) → ℝ := by
    intro x
    have := x 0
    have := x 1
    exact (x 0)^2 + (x 1)^2

-- Function of two variables first partial derivative test
-- example (f₀ : EuclideanSpace ℝ (Fin 2) → ℝ) :
--     (hf₀ : )

-- example : f0 ![2,2] = 8 := by
--     simp [f0]
--     linarith

-- def myf'' : ℝ → ℝ → ℝ := by
--     intro x y
--     exact x^2+y^2

-- def myf' : EuclideanSpace ℝ (Fin 2) → ℝ := by
--     intro x y
--     exact x^2+y^2











def astMat {α : Type*} {R : Type*} [Add R] [Mul R] [Zero R] [One R]
  {n q : ℕ} (word : Fin n → α) (matrices : α → Matrix (Fin q) (Fin q) R) :
  Fin q → Fin q → R := match n with
| 0 => fun x y => ite (x=y) 1 0
| Nat.succ m => Matrix.mulᵣ (matrices (word ⟨m,by simp⟩)) (astMat (Fin.init word) matrices)

open Matrix

example {R : Type*} [Mul R] [AddCommMonoid R]
  (q : ℕ) (A B : Matrix (Fin q) (Fin q) R) :
  mulᵣ A B = A * B := by simp only [mulᵣ_eq]

-- /-- Completely positive map in Kraus operator form. -/
-- def CP_apply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
--   {q krausDecompositionLength : ℕ}
--   (krausOperator : Fin krausDecompositionLength → Matrix (Fin q) (Fin q) R)
--   (ρ : Matrix (Fin q) (Fin q) R) : Matrix (Fin q) (Fin q) R :=
--     ∑ i : Fin krausDecompositionLength,
--       krausOperator i * ρ * (krausOperator i).conjTranspose

/-- Completely positive map given by a (not necessarily minimal) Kraus family. -/
def krausApply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (ρ : Matrix (Fin q) (Fin q) R) : Matrix (Fin q) (Fin q) R :=
  ∑ i : Fin r, K i * ρ * (K i)ᴴ

def quantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R) : Prop :=
    ∑ i : Fin r, (K i)ᴴ * K i = fun i j => ite (i=j) 1 0


/-- Transition function `δ^*` corresponding to a word `word` over an alphabet `α`,
  where each symbol `a:α` is mapped to a completely positive map in Kraus form,
  of rank at most `r`.
-/
def krausApplyWord {α : Type*} {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
  (ρ : Matrix (Fin q) (Fin q) R) :
  Matrix (Fin q) (Fin q) R := match n with
| 0 => ρ
| Nat.succ m => krausApply (𝓚 (word ⟨m,by simp⟩))
        (krausApplyWord (Fin.init word) 𝓚 ρ)

/-- The example Kraus operators from QCNC submission. -/
def grudka_Z : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℤ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![0,-1,0;
       1,0,0;
       0,0,1],
    0
  ] -- B
]

def grudka_R : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![0,-1,0;
       1,0,0;
       0,0,1],
    0
  ] -- B
]
open Real
noncomputable def grudka_R' (θ : ℝ) : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![cos θ, -sin θ, 0;
       sin θ, cos θ,  0;
       0,     0,      1],
    0
  ] -- B
]

example (θ : ℝ) : (grudka_R' θ 0 0).trace = 0 := by simp [grudka_R']

open Matrix

example (θ : ℝ) {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
    (krausApply (grudka_R' θ 1) ρ).trace = 1 := by
  rw [krausApply, trace]
  unfold grudka_R'
  simp only [diag, sum_apply, mul_apply, conjTranspose_apply]
  simp [Fin.sum_univ_succ]
  rw [trace] at hρ
  simp [Fin.sum_univ_succ] at hρ
  ring_nf
  have := cos_sq_add_sin_sq θ
  have := sin_sq_add_cos_sq θ
  generalize cos θ ^ 2 = c at *
  generalize sin θ ^ 2 = s at *
  have : c = 1 - s := by linarith
  subst this
  linarith


example : quantumChannel (grudka_Z 0) := by
  simp only [quantumChannel, grudka_Z, Int.reduceNeg, Fin.isValue, cons_val', cons_val_fin_one,
    cons_val_zero, conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_transpose,
    Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : quantumChannel (grudka_Z 1) := by
  simp only [quantumChannel, grudka_Z, Int.reduceNeg, Fin.isValue, cons_val', cons_val_fin_one,
    cons_val_one, conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_val_zero,
    cons_transpose, Nat.succ_eq_add_one, Nat.reduceAdd, transpose_zero, mul_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : quantumChannel (grudka_R 1) := by
  unfold quantumChannel grudka_R
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ]

example (θ : ℝ) : quantumChannel (grudka_R' θ 1) := by
  unfold quantumChannel grudka_R'
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> all_goals
      simp
      try linarith
      try repeat rw [← pow_two]
      try exact cos_sq_add_sin_sq θ
      try exact sin_sq_add_cos_sq θ
      sorry

def e₁ : Matrix (Fin 3) (Fin 1) ℝ := ![1, 0, 0]
def e₂ : Matrix (Fin 3) (Fin 1) ℝ := ![0, 1, 0]
def e₃ : Matrix (Fin 3) (Fin 1) ℝ := ![0, 0, 1]
def e {k : ℕ} : Fin k → Matrix (Fin k) (Fin 1) ℝ :=
  fun i => single i 0 1
def pureState {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) := mulᵣ e e.transpose

lemma pureState_selfAdjoint {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) :
  Matrix.IsHermitian (pureState e) := by
    unfold pureState
    norm_num [ Matrix.PosSemidef ] at *;
    simp +decide [ Matrix.IsHermitian, Matrix.transpose_mul ];

def pureState_projection' {k : ℕ} (e : EuclideanSpace ℝ (Fin k)) (he : ‖e‖ = 1) :
  IsStarProjection (pureState (fun (i : Fin k) (_ : Fin 1) => e i)) := {
      isIdempotentElem := by
        unfold pureState
        simp
        simp +decide [ IsIdempotentElem];
        simp +decide [ ← Matrix.ext_iff, Matrix.mul_apply ];
        simp +decide [ ← mul_assoc,
          ← Finset.sum_mul];
        simp +decide [ mul_assoc, ← Finset.mul_sum _ _ _,
          EuclideanSpace.norm_eq ] at he ⊢;
        simp +decide [ ← sq, he ]
      isSelfAdjoint := by apply pureState_selfAdjoint
  }

lemma pureState_projection {k : ℕ} (i : Fin k) :
  IsStarProjection (pureState (e i)) := {
      isIdempotentElem := by
        unfold IsIdempotentElem pureState e
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint
  }

/-- Projection onto span ⟨e₁, e₂⟩ is indeed a star-projection.
So we could form a PMF with two outcomes (e₁,e₂) vs. e₃.
-/
lemma pureState_projection'' :
  IsStarProjection (pureState (e (0:Fin 3)) + pureState (e (1 : Fin 3))) := {
      isIdempotentElem := by
        unfold IsIdempotentElem
        rw [mul_add]
        repeat rw [add_mul]
        have : pureState (e (0:Fin 3)) * pureState (e 0) =
          pureState (e 0) := by
          have := @pureState_projection 3 0
          exact this.isIdempotentElem
        rw [this]
        have : pureState (e (1:Fin 3)) * pureState (e 1) =
          pureState (e 1) := by
          have := @pureState_projection 3 1
          exact this.isIdempotentElem
        rw [this]
        have : pureState (e (1:Fin 3)) * pureState (e 0) =
          0 := by
          unfold pureState e
          simp
        rw [this]
        have : pureState (e (0:Fin 3)) * pureState (e 1) =
          0 := by
          unfold pureState e
          simp
        rw [this]
        simp
      isSelfAdjoint := by
        refine IsSelfAdjoint.add ?_ ?_
        · apply (@pureState_projection 3 0).isSelfAdjoint
        · apply (@pureState_projection 3 1).isSelfAdjoint
  }


theorem psd_versions {k : ℕ} (e : Matrix (Fin k) (Fin k) ℝ) (x : Fin k →₀ ℝ)
  (this : 0 ≤ ⇑x ⬝ᵥ e *ᵥ ⇑x) :
  0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * e i j * xj := by
      convert this
      rw [Finsupp.sum]
      simp only [star_trivial]
      change ∑ i ∈ x.1, ∑ j ∈ x.1, x i * e i j * x j =
        ∑ i : Fin k, x i * ∑ j : Fin k, e i j * x j
      have (i : Fin k) : x i * ∑ j : Fin k, e i j * x j
                      = ∑ j : Fin k, x i *  e i j * x j := by
          simp_rw [mul_assoc]
          exact Finset.mul_sum Finset.univ _ _
      simp_rw [this]
      rw [ ← Finset.sum_subset ( Finset.subset_univ x.support ) ];
      · exact Finset.sum_congr rfl fun i hi =>
          Finset.sum_subset ( Finset.subset_univ _ ) fun j hj₁ hj₂ => by aesop;
      · aesop

lemma pureState_psd {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) :
  Matrix.PosSemidef (mulᵣ e e.transpose) := by
  constructor
  · exact pureState_selfAdjoint _
  · intro x
    suffices 0 ≤ x ⬝ᵥ (e * e.transpose).mulVec x by
      apply psd_versions
      rw [mulᵣ_eq]
      convert this
    have h_expand : x ⬝ᵥ (e * e.transpose).mulVec x =
      (e.transpose.mulVec x) ⬝ᵥ (e.transpose.mulVec x) := by
      simp +decide [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    rw [h_expand, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact mul_self_nonneg _


example : pureState e₁ = !![1,0,0;0,0,0;0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureState, e₁, pureState, mulᵣ]

-- Trace exercise: probability of being in the state e₁.
example : (pureState e₁ * (grudka_R' θ 1 0)).trace = cos θ := by
  unfold e₁ grudka_R' pureState
  simp only [mulᵣ_eq, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₂ * (grudka_R' θ 1 0)).trace = cos θ := by
  unfold e₂ grudka_R' pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₃ * (grudka_R' θ 1 0)).trace = 1 := by
  unfold e₃ grudka_R' pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

/-- The positive operator `pureState e₁` is chosen
with probability `(pureState e₁ * ρ).trace`. -/
lemma POVM {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
      (pureState e₁ * ρ).trace
    + (pureState e₂ * ρ).trace
    + (pureState e₃ * ρ).trace = 1 := by
  unfold pureState e₁ e₂ e₃
  simp only [transpose, cons_val', Pi.one_apply, Pi.zero_apply, cons_val_fin_one, mulᵣ_eq]
  repeat rw [trace]
  simp only [diag, mul_apply] at hρ ⊢
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, cons_val', Pi.one_apply,
    Pi.zero_apply, cons_val_fin_one, of_apply, Finset.sum_const, Finset.card_singleton, one_smul,
    Fin.sum_univ_succ, cons_val_zero, mul_one, cons_val_succ, mul_zero, Fin.succ_zero_eq_one,
    zero_mul, add_zero, one_mul, zero_add, Finset.sum_singleton,
    Fin.succ_one_eq_two] at hρ ⊢
  rw [trace] at hρ
  simp only [diag_apply] at hρ
  rw [← hρ]
  exact Eq.symm (Fin.sum_univ_three fun i ↦ ρ i i)


lemma pure_state_eq {k : ℕ} (i : Fin k) :
    (single i (0 : Fin 1) (1 : ℝ)).mulᵣ (single i 0 1)ᵀ
    = Matrix.single i i 1 := by
  have : (single i (0:Fin 1) (1:ℝ))ᵀ = single 0 i 1 := by
    simp
  rw [this]
  simp

-- noncomputable instance : CStarAlgebra ℂ := instCommCStarAlgebraComplex.toCStarAlgebra

-- instance : StarOrderedRing ℂ := by apply?

-- noncomputable instance : CStarAlgebra (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
--   apply CStarMatrix.instCStarAlgebra
--   sorry

-- example (n : ℕ) : Unit := by
--   have := ContinuousLinearMap
--     (RingHom.id ℝ) (EuclideanSpace ℝ (Fin n))
--     (EuclideanSpace ℝ (Fin n))
--   sorry
open MatrixOrder

-- Works, but deprecated
-- theorem matrix_posSemidef_eq_star_mul_self {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
-- (hP : P.PosSemidef) : ∃ B, P = star B * B := by
--   exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hP

/-- Jireh recommends this approach. -/
theorem matrix_posSemidef_eq_star_mul_self' {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
(hP : 0 ≤ P) : ∃ B, P = star B * B := by
  use CFC.sqrt P
  have h₀ : (CFC.sqrt P)ᴴ = CFC.sqrt P := by
    have := hP.1
    simp only [IsHermitian, sub_zero, conjTranspose_eq_transpose_of_trivial] at this ⊢
    nth_rw 2 [← this]
    symm
    rw [@CFC.sqrt_eq_iff]
    · rw [← transpose_mul]
      congr
      apply @CFC.sqrt_mul_sqrt_self (a := P)
      · exact topologicalRing
      · exact instT2SpaceMatrix
      · exact hP
    · exact star_nonneg_iff.mp hP
    · exact star_nonneg_iff.mp <| CFC.sqrt_nonneg P
  have : star (CFC.sqrt P) = CFC.sqrt P := by
    have := hP.1
    simp only [IsHermitian, sub_zero, conjTranspose_eq_transpose_of_trivial] at this ⊢
    nth_rw 2 [← h₀]
    congr
  rw [this]
  symm
  rw [← @CFC.sqrt_eq_iff (a := P) (b := CFC.sqrt P)]
  · exact topologicalRing
  · exact instT2SpaceMatrix
  · simp;tauto
  · exact CFC.sqrt_nonneg P

  -- exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hP


-- theorem trace_mul_posSemidef_nonneg' {n : ℕ}
--   {ρ P : ContinuousLinearMap
--     (RingHom.id ℝ) (EuclideanSpace ℝ (Fin n))
--     (EuclideanSpace ℝ (Fin n))}
--     (hρ : ρ.IsPositive) (hP : P.IsPositive) :
--     0 ≤ LinearMap.trace _ _ (P * ρ).toLinearMap := by
--   simp


--   have : ∃ B, P = star B * B := by
--     have := @matrix_posSemidef_eq_star_mul_self n
--     exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hP
--     sorry
--   sorry

theorem trace_mul_posSemidef_nonneg {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ : ρ.PosSemidef) (hP : P.PosSemidef) : 0 ≤ (P * ρ).trace := by
      -- Use `Matrix.posSemidef_iff_eq_transpose_mul_self` to write $P = Bᵀ * B$.
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, P = star B * B := by
        apply matrix_posSemidef_eq_star_mul_self'
        exact nonneg_iff_posSemidef.mpr hP
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, P = B.transpose * B := by
        use B
        rw [hB]
        congr
      have h_trace_cyclic : Matrix.trace (P * ρ) = Matrix.trace (B * ρ * B.transpose) := by
        simp +decide only [hB, Matrix.mul_assoc, Matrix.trace_mul_comm B];
        exact trace_mul_cycle' Bᵀ B ρ;
      have h_pos_semidef : Matrix.PosSemidef (B * ρ * B.transpose) := by
        apply Matrix.PosSemidef.mul_mul_conjTranspose_same hρ
      exact h_trace_cyclic ▸ h_pos_semidef.trace_nonneg


/-
A real matrix that is a star projection (symmetric and idempotent) is positive semidefinite.
-/
theorem isStarProjection_matrix_posSemidef {n : ℕ}
  (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsStarProjection P) : P.PosSemidef := by
  revert hP;
  rintro ⟨ h₁, h₂ ⟩;
  refine ⟨ h₂, ?_ ⟩;
  intro x
  have h_pos_semi_def : (P.mulVec x) ⬝ᵥ (P.mulVec x) ≥ 0 := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp_all +decide only [dotProduct_mulVec, vecMul_mulVec, ge_iff_le, star_trivial];
  simp_all +decide only [IsIdempotentElem, dotProduct_comm];
  simp_all +decide only [IsSelfAdjoint];
  simp_all +decide only [star, conjTranspose_eq_transpose_of_trivial]
  apply @psd_versions
  convert h_pos_semi_def
  generalize ⇑x = β at *
  clear h_pos_semi_def h₁
  unfold mulVec vecMul
  simp only
  ext i
  unfold dotProduct
  simp only
  congr
  ext j
  rw [mul_comm]
  suffices P i j = P j i by rw [this]
  exact congrFun (congrFun (id (Eq.symm h₂)) i) j

lemma nonneg_trace''' {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg hρ'
  apply isStarProjection_matrix_posSemidef
  exact hP

lemma nonneg_trace'' {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
    -- this proof is too complicated but at least it's not deprecated
  suffices 0 ≤ (P * ρ * Pᴴ).trace by
    simp only [conjTranspose_eq_transpose_of_trivial] at this
    have : 0 ≤ (Pᴴ * P * ρ).trace := by
      convert this using 1
      exact (trace_mul_cycle _ ρ _).symm
    have h₀ : Pᴴ * P = P := by
      have : star P = Pᴴ := rfl
      rw [← this,hP.2,hP.1]
    rw [h₀] at this
    exact this
  apply PosSemidef.trace_nonneg
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hρ' _



/-- A general reason why `nonneg_trace` below holds.
Can be generalized to let `(e * eᵀ)` be any projection, see above ^^.
-/
lemma nonneg_trace' {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ} (hρ' : ρ.PosSemidef)
  (e : Matrix (Fin n) (Fin 1) ℝ)
  (he : ‖WithLp.toLp 2 fun i ↦ e i 0‖ = 1) -- not really necessary
  : 0 ≤ (pureState e * ρ).trace := by
      apply nonneg_trace'' hρ'
      have := @pureState_projection' n {ofLp := fun i => e i 0} he
      convert this

      -- unfold pureState
      -- simp only [mulᵣ_eq]
      -- suffices 0 ≤ (e * eᵀ * ρ * (e * eᵀ)ᴴ).trace by
      --   simp only [conjTranspose_eq_transpose_of_trivial, transpose_mul,
      --     transpose_transpose] at this
      --   have : 0 ≤ ((e * eᵀ) * (e * eᵀ) * ρ).trace := by
      --     convert this using 1
      --     exact (trace_mul_cycle (e * eᵀ) ρ (e * eᵀ)).symm
      --   have h₀ : (e * eᵀ) * (e * eᵀ) = e * eᵀ := by
      --     have := @pureState_projection' n ({ofLp := fun i => e i 0})
      --     simp only [Fin.isValue] at this
      --     specialize this he
      --     have := this.1
      --     unfold pureState IsIdempotentElem at this
      --     simp only [Fin.isValue, mulᵣ_eq] at this
      --     convert this
      --   rw [h₀] at this
      --   exact this
      -- exact PosSemidef.trace_nonneg <| Matrix.PosSemidef.mul_mul_conjTranspose_same hρ' _


lemma nonneg_trace {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ} (hρ' : ρ.PosSemidef) (i : Fin n) :
  0 ≤ (pureState (e i) * ρ).trace := by
      apply nonneg_trace' hρ'
      simp [e, single, PiLp.instNorm]

      -- have := @Orthonormal.norm_eq_one ℝ ℝ _ _ _ (Fin n)


      -- suffices 0 ≤ (Matrix.mulᵣ (pureState (e i)) ρ).trace by
      --   convert this
      --   aesop
      -- -- also use identity matrix instead of ite
      -- unfold pureState
      -- unfold PosSemidef at hρ'
      -- have hh (k : Fin n) := hρ'.2 ({
      --   toFun := fun j => e k j 0
      --   support := {k}
      --   mem_support_toFun := by
      --     intro a
      --     unfold e
      --     unfold single
      --     simp
      --     tauto
      -- })
      -- unfold e Finsupp.sum at hh
      -- unfold e trace diag
      -- -- simp
      -- apply Finset.sum_nonneg
      -- -- simp at hh
      -- intro l hl
      -- have : (single i (0 : Fin 1) (1 : ℝ)).mulᵣ (single i 0 1)ᵀ
      --   = Matrix.single i i 1 := by
      --     apply pure_state_eq
      -- rw [this]
      -- -- simp
      -- have : Matrix.mulᵣ (single i i (1 : ℝ)) ρ
      --   = of (Function.update 0 i (ρ.row i)) := by
      --   simp only [mulᵣ_eq]
      --   rw [@Matrix.single_mul_eq_updateRow_zero]
      --   unfold updateRow
      --   simp
      -- rw [this]
      -- simp only [Fin.isValue, Finsupp.coe_mk, star_trivial,
      -- Finset.sum_singleton, single_apply_same,
      --   mul_one, one_mul] at hh
      -- unfold Function.update
      -- simp only [eq_rec_constant, Pi.zero_apply, dite_eq_ite, of_apply, ge_iff_le]
      -- by_cases H : l = i
      -- · subst H
      --   simp only [↓reduceIte, row_apply]
      --   apply hh
      -- · rw [if_neg H]
      --   simp

lemma sum_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, of (Function.update 0 x (ρ.row x)) = ρ := by
      ext i j
      rw [Finset.sum_apply]
      simp only [row, Finset.sum_apply, of_apply, Function.update,
        eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      rw [← congrFun (Fintype.sum_ite_eq i fun j ↦ ρ i) j]
      aesop

lemma single_row {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ} (x : Fin k) :
  single x x 1 * ρ = of (Function.update 0 x (ρ.row x)) := by
        rw [@Matrix.single_mul_eq_updateRow_zero]
        unfold updateRow
        simp

lemma combined_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, single x x 1 * ρ = ρ := by
      have := @sum_rows k ρ
      nth_rw 2 [← this]
      have := @single_row k ρ
      simp_rw [this]


theorem POVM_PMF.aux₀ {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
  (hρ : ρ.trace = 1) (hρ' : ρ.PosSemidef) :
  (∑ a, ⟨
    (pureState (e a) * ρ).trace,
    nonneg_trace hρ' a⟩) = ENNReal.toNNReal 1 := by
  apply NNReal.eq
  unfold pureState e
  simp_rw [pure_state_eq]
  simp_rw [single_row]
  rw [← sum_rows ρ] at hρ
  simp only [trace_sum, NNReal.coe_sum, NNReal.coe_mk, ENNReal.toNNReal_one, NNReal.coe_one] at hρ ⊢
  exact hρ

open ENNReal

lemma standard_basis_probability_one {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) ℝ} (hUT : ρ.trace = 1) (hPS : ρ.PosSemidef) :
  ∑ a, ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace hPS _⟩ = 1 := by
    exact
      (toNNReal_eq_one_iff _).mp
      <| ENNReal.toNNReal_one ▸ POVM_PMF.aux₀ hUT hPS
       ▸ toNNReal_sum (by simp)

/-- Positive operator (or projection) valued measure
as a probability mass function.
Technically the measure is valued in `Fin k`
although `pureState (e i)` can stand for `i`.
Could be generalized to let `e` be any orthonormal basis.

`pureState_psd` shows that it is a POVM.
`pureState_projection` shows that it is in fact a PVM for the standard
basis.
In fact `pureState_projection'` shows it's a projection
whenever the vectors have length 1.
-/
def POVM_PMF {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin k) := by
    apply PMF.ofFintype
     (fun i => ofNNReal
      ⟨
        (pureState (e i) * ρ).trace, -- the probability of `i` acc. to ρ
        -- in JL's case the accepting subspace is always a projection
        nonneg_trace hPS _⟩) <| standard_basis_probability_one hUT hPS

lemma PMF₂₃help {ρ : Matrix (Fin 3) (Fin 3) ℝ}
  (hPS : ρ.PosSemidef) :
  0 ≤ ((pureState (e 0) + pureState (e 1)) * ρ).trace := by
        refine trace_mul_posSemidef_nonneg hPS ?_
        refine PosSemidef.add (pureState_psd _) (pureState_psd _)


/-- A probability measure that gives the probability
of being in the xy-plane, or the z-axis,
for a given PSD trace-one matrix `ρ`.
See `myPVM₂₃` below.
-/
def PVM_PMF₂₃ {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((pureState (e 0) + pureState (e 1)) * ρ).trace, PMF₂₃help hPS⟩
      ⟨(                   pureState (e 2)  * ρ).trace, nonneg_trace hPS _⟩)
  rw [← standard_basis_probability_one hUT hPS]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp_rw [add_mul, trace_add]
  simp
  rfl


/-- Projection-valued measure. -/
structure PVM where
  k : ℕ -- the dimension
  ρ : Matrix (Fin k) (Fin k) ℝ          -- the state we're in
  hρ : ρ.PosSemidef
  t : ℕ -- the number of projections (states)
  op : Fin t → Matrix (Fin k) (Fin k) ℝ -- the projections

  pf : ∀ i, IsStarProjection (op i)     -- ... are projections

  p : PMF (Fin t)                                       -- the measure
  pf' : ∀ i, p i = ofNNReal ⟨(op i * ρ).trace, by
      apply nonneg_trace'' hρ
      apply pf
    ⟩  -- is given by the probs.
       -- will usually be by `rfl`
       -- so instead say that p = POVM_PMF

def myPVM {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := k
  t := k
  p := POVM_PMF hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState (e i)
  pf := by exact fun i ↦ pureState_projection i
  pf' := by intro i; rfl
}

def myPVM₂₃ {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := 3
  t := 2
  p := PVM_PMF₂₃ hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (pureState (e 0) + pureState (e 1)) <| pureState (e 2)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; exact pureState_projection''
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; exact pureState_projection 2
  pf' := by
    intro i
    fin_cases i
    · rfl
    · rfl
}

-- Now `pureState e₁`, `pureState e₂`, `pureState e₃` form a POVM.


example : krausApplyWord ![0,1] grudka_R (pureState e₁) =
  pureState e₁ := by
  unfold krausApplyWord
  have : Fin.init ![(0:Fin 2),1] = ![0] := by
    ext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [this]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  unfold krausApplyWord
  have : Fin.init ![(0 : Fin 2)] = ![] := by
    ext i
    have := i.2
    simp at this
  rw [this]
  unfold krausApplyWord
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    cons_val_fin_one]
  have : ![(0:Fin 2),1] ⟨1, (by simp : 1 < 1 + 1)⟩ = 1 := by simp
  rw [this]
  have : krausApply (grudka_R 0) (pureState e₁)
    =  (pureState e₂) := by
    unfold krausApply pureState e₁ e₂
    unfold grudka_R
    simp
    sorry
  rw [this]
  unfold krausApply
  unfold grudka_R

  simp

  sorry
