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

def densityMatrix (q : ℕ) : Type :=
{ρ : Matrix (Fin q) (Fin q) ℝ // ρ.PosSemidef ∧ ρ.trace = 1}


/-- 1/24/26. Kraus operator preserves PSD property. -/
lemma krausApply_psd
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) ℝ)
  (ρ : Matrix (Fin q) (Fin q) ℝ) (hρ : ρ.PosSemidef) :
  (krausApply K ρ).PosSemidef := by
  unfold krausApply
  refine posSemidef_sum Finset.univ ?_
  intro i _
  have := @Matrix.PosSemidef.mul_mul_conjTranspose_same (Fin q) (Fin q) ℝ
    _ _ _ _ _ ρ hρ (K i)
  convert this

def quantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R) : Prop :=
    ∑ i : Fin r, (K i)ᴴ * K i = 1

def quantum_channel (q r : ℕ) : Type :=
  {K : Fin r → Matrix (Fin q) (Fin q) ℝ // ∑ i : Fin r, (K i)ᴴ * K i = 1 }

/-- This proves a claim by ChatGPT
in the chat Kraus operator conditions. -/
lemma quantumChannel_preserves_trace
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) ℝ)
  (hq : quantumChannel K)
  (ρ : Matrix (Fin q) (Fin q) ℝ) :
  (krausApply K ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  rw [hq]
  simp

lemma quantum_channel_preserves_trace
  {q r : ℕ}
  (K : quantum_channel q r)
  (ρ : Matrix (Fin q) (Fin q) ℝ) :
  (krausApply K.1 ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K.1 i)ᴴ) (B := ρ) (A := K.1 i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  rw [K.2]
  simp


lemma quantumChannel_preserves_trace_one
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) ℝ)
  (hq : quantumChannel K)
  (ρ : Matrix (Fin q) (Fin q) ℝ) (hρ : ρ.trace = 1) :
  (krausApply K ρ).trace = 1 := by
  rw [@quantumChannel_preserves_trace q r K hq ρ]
  exact hρ

/-- Realizing a quantumChannel as a map on densityMatrices. -/
def krausApply_densityMatrix
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) ℝ)
  (hq : quantumChannel K)
  (ρ : densityMatrix q) : densityMatrix q :=
  ⟨krausApply K ρ.1, ⟨krausApply_psd K ρ.1 ρ.2.1,
   quantumChannel_preserves_trace_one K hq ρ.1 ρ.2.2⟩⟩


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

theorem krausApplyWord_densityMatrix.{u_1} {α : Type u_1}
{n q r : ℕ} (word : Fin n → α)
  {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) ℝ}
  (hq : ∀ (a : α), quantumChannel (𝓚 a)) (ρ : densityMatrix q) :
  (krausApplyWord word 𝓚 ρ.1).PosSemidef ∧ (krausApplyWord word 𝓚 ρ.1).trace = 1 := by
    induction n with
    | zero => exact ρ.2
    | succ n ih =>
      exact (krausApply_densityMatrix (𝓚 (word (Fin.last n))) (hq _)
        ⟨krausApplyWord (Fin.init word) 𝓚 ρ.1, ih (Fin.init word)⟩).2

/-- If each letter is a quantum channel
then the whole word maps density matrices to density matrices. -/
def krausApplyWord_map {α : Type*}
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) ℝ)
  (hq : ∀ a, quantumChannel (𝓚 a))
  (ρ : densityMatrix q) : densityMatrix q :=
  ⟨krausApplyWord word 𝓚 ρ.1, krausApplyWord_densityMatrix _ hq _⟩


def krausApplyWord_channel {α : Type*}
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → quantum_channel q r)
  (ρ : densityMatrix q) : densityMatrix q := by
  exact krausApplyWord_map word
    (fun a => (𝓚 a).1)
    (fun a => (𝓚 a).2) ρ



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

def grudka_R₀ : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
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
noncomputable def grudka_R (θ : ℝ) : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
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

example (θ : ℝ) : (grudka_R θ 0 0).trace = 0 := by simp [grudka_R]

open Matrix

example (θ : ℝ) {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
    (krausApply (grudka_R θ 1) ρ).trace = 1 := by
  rw [krausApply, trace]
  unfold grudka_R
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

example : quantumChannel (grudka_R₀ 1) := by
  unfold quantumChannel grudka_R₀
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ]

/-- 1/24/26 -/
lemma grudka_B_quantumChannel (θ : ℝ) : quantumChannel (grudka_R θ 1) := by
  apply ext
  intro i j
  unfold grudka_R
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  rw [Fin.sum_univ_two]
  repeat rw [Fin.sum_univ_three]
  simp only [cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, of_apply,
    star_trivial, cons_val, zero_apply, mul_zero, add_zero]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, zero_mul, add_zero]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, one_apply_eq]
      repeat rw [← pow_two]
      exact cos_sq_add_sin_sq θ
    · simp
      linarith
    · simp
  · simp only [Fin.mk_one, cons_val_one, cons_val_zero, neg_mul, zero_mul, add_zero]
    fin_cases j
    · simp
      linarith
    · simp only [Fin.mk_one, cons_val_one, cons_val_zero, mul_neg, neg_neg,
      one_apply_eq]
      repeat rw [← pow_two]
      exact sin_sq_add_cos_sq θ
    · simp
  · fin_cases j <;> simp

lemma grudka_A_quantumChannel (θ : ℝ) : quantumChannel (grudka_R θ 0) := by
  unfold grudka_R
  unfold quantumChannel
  simp only [Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
    conjTranspose_eq_transpose_of_trivial]
  simp only [Fin.sum_univ_two, cons_val_one]
  -- "use the definition of matrix multiplication":
  repeat rw [← mulᵣ_eq]
  unfold mulᵣ dotProductᵣ
  simp only [FinVec.map_eq, FinVec.seq_eq, Function.comp_apply, FinVec.sum_eq, Fin.isValue,
    cons_val_zero, cons_transpose, Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_fin_one, of_add_of]
  repeat simp_rw [Fin.sum_univ_three]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp

lemma grudka_quantumChannel (θ : ℝ) (i : Fin 2) : quantumChannel (grudka_R θ i) := by
  fin_cases i
  · exact grudka_A_quantumChannel θ
  · exact grudka_B_quantumChannel θ

/-- Grudka et al.' map does indeed map density matrices to density matrices. -/
noncomputable def grudka_map (θ : ℝ) {n : ℕ} (word : Fin n → Fin 2) :
  densityMatrix 3 → densityMatrix 3 :=
  krausApplyWord_map word _ fun i ↦ grudka_quantumChannel θ i





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
example : (pureState e₁ * (grudka_R θ 1 0)).trace = cos θ := by
  unfold e₁ grudka_R pureState
  simp only [mulᵣ_eq, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₂ * (grudka_R θ 1 0)).trace = cos θ := by
  unfold e₂ grudka_R pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₃ * (grudka_R θ 1 0)).trace = 1 := by
  unfold e₃ grudka_R pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

/-- The positive operator `pureState e₁` is chosen
with probability `(pureState e₁ * ρ).trace`. -/
lemma pureState_probability_one {ρ : Matrix (Fin 3) (Fin 3) ℝ}
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

open MatrixOrder


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
theorem posSemidef_of_isStarProjection {n : ℕ}
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

lemma trace_mul_nonneg {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg hρ'
  apply posSemidef_of_isStarProjection
  exact hP

-- lemma nonneg_trace'' {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
--     (hρ' : ρ.PosSemidef)
--     (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
--     -- this proof is too complicated but at least it's not deprecated
--   suffices 0 ≤ (P * ρ * Pᴴ).trace by
--     simp only [conjTranspose_eq_transpose_of_trivial] at this
--     have : 0 ≤ (Pᴴ * P * ρ).trace := by
--       convert this using 1
--       exact (trace_mul_cycle _ ρ _).symm
--     have h₀ : Pᴴ * P = P := by
--       have : star P = Pᴴ := rfl
--       rw [← this,hP.2,hP.1]
--     rw [h₀] at this
--     exact this
--   apply PosSemidef.trace_nonneg
--   exact Matrix.PosSemidef.mul_mul_conjTranspose_same hρ' _

/-- A general reason why `nonneg_trace` below holds.
Can be generalized to let `(e * eᵀ)` be any projection, see above ^^.
-/
lemma nonneg_trace' {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ} (hρ' : ρ.PosSemidef)
  (e : Matrix (Fin n) (Fin 1) ℝ)
  (he : ‖WithLp.toLp 2 fun i ↦ e i 0‖ = 1) -- not really necessary
  : 0 ≤ (pureState e * ρ).trace := by
      apply trace_mul_nonneg hρ'
      have := @pureState_projection' n {ofLp := fun i => e i 0} he
      convert this

lemma nonneg_trace {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ} (hρ' : ρ.PosSemidef) (i : Fin n) :
  0 ≤ (pureState (e i) * ρ).trace := by
      apply nonneg_trace' hρ'
      simp [e, single, PiLp.instNorm]

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

lemma one_eq_sum_pureState {k : ℕ} :
    1 = ∑ i : Fin k, pureState (e i) := by
  unfold pureState e
  ext i j
  simp only [Fin.isValue, transpose_single, mulᵣ_eq, single_mul_single_same, mul_one]
  by_cases H : i = j
  · subst H
    simp only [one_apply_eq, single]
    rw [Finset.sum_apply] -- !
    simp
  · simp only [single]
    rw [Finset.sum_apply] -- !
    symm
    have : (1 : Matrix (Fin k) (Fin k) ℝ) i j = 0 := by
        exact one_apply_ne' fun a ↦ H (id (Eq.symm a))
    rw [this]
    simp only [Finset.sum_apply, of_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, forall_const, forall_eq, ne_eq]
    exact H

def PMF_of_state {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((1 - (pureState (e acc))) * ρ).trace, by
        rw [one_eq_sum_pureState]
        have : ∑ i, pureState (e i) - pureState (e acc) =
            ∑ i, ite (i = acc) 0 (pureState (e i)) := by
                suffices ∑ i, pureState (e i)
                = ∑ i, (if i = acc then 0 else (pureState (e i))) + pureState (e acc) by
                    rw [this]
                    simp
                rw [← Finset.sum_add_sum_compl (s := {i | i ≠ acc})]
                simp only [ne_eq, Finset.compl_filter, Decidable.not_not]
                have : ∑ i with i = acc, pureState (e i) =
                    pureState (e acc) := by
                    have :  ∑ i with i = acc, pureState (e i)
                        =  ∑ i ∈ {acc}, pureState (e i) := by
                        congr
                        ext;simp
                    rw [this]
                    rw [@Finset.sum_singleton]
                rw [this]
                simp only [_root_.add_left_inj]
                refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_
                · simp
                · intro i _
                  simp
                  tauto
                · intro i hi _
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                  rw [if_neg hi]
        rw [this]
        refine trace_mul_posSemidef_nonneg hPS ?_
        refine posSemidef_sum Finset.univ ?_
        intro i _
        by_cases H : i = acc
        · subst H
          simp only [↓reduceIte]
          exact PosSemidef.zero
        · rw [if_neg H]
          refine posSemidef_of_isStarProjection (pureState (e i)) ?_
          exact pureState_projection i⟩
      ⟨(                   pureState (e acc)  * ρ).trace, nonneg_trace hPS _⟩)
  rw [← standard_basis_probability_one hUT hPS]
  rw [Fin.sum_univ_two]
  simp_rw [one_eq_sum_pureState]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero]
  simp_rw [sub_mul]
  simp_rw [trace_sub]
  refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
  · simp
  · simp
  have h₀ : ((∑ i, pureState (e i) - pureState (e acc)) * ρ).trace +
    (pureState (e acc) * ρ).trace =
  ∑ a, (pureState (e a) * ρ).trace := by
    rw [sub_mul]
    rw [trace_sub]
    simp only [sub_add_cancel]
    rw [← trace_sum]
    congr
    exact Matrix.sum_mul Finset.univ (fun a ↦ pureState (e a)) ρ
  have h₁ : (∑ a, ENNReal.ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace hPS a⟩ ).toReal
    = ∑ a, (pureState (e a) * ρ).trace := by
        refine toReal_sum ?_
        simp
  rw [h₁]
  rw [← h₀]
  rw [toReal_add (by simp) (by simp)]
  have : (ofNNReal (⟨(pureState (e acc) * ρ).trace, nonneg_trace hPS acc⟩)).toReal
    = (pureState (e acc) * ρ).trace := by exact rfl
  rw [this]
  have (a b c : ℝ) (h : a = c)  : a + b = c + b := by
    linarith
  apply this
  simp_rw [sub_mul]
  simp_rw [trace_sub]
  congr


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
      apply trace_mul_nonneg hρ
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

def PVM_of_state {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := k
  t := 2
  p := PMF_of_state acc hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (1 - pureState (e acc)) <| pureState (e acc)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte];
      refine IsStarProjection.one_sub ?_
      exact pureState_projection _
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte];
      exact pureState_projection acc
  pf' := by
    intro i
    fin_cases i
    · unfold PMF_of_state
      simp
    · rfl
}


/-- 1/24/26 -/
def languageAcceptedBy {α : Type*}
  {q r : ℕ} (acceptStateIndex : Fin q.succ)
  (𝓚 : α → Fin r → Matrix (Fin q.succ) (Fin q.succ) ℝ) :=
  {word : Σ n : ℕ, (Fin n → α) |
    krausApplyWord word.2 𝓚 (pureState (e 0)) = pureState (e acceptStateIndex)}
-- now make this probabilistic: PVM_PMF (pureState (e acceptStateIndex)) > 1/2

lemma grudka_helper : mulᵣ ![(1: Fin 1 → ℝ), 0, 0] ![1, 0, 0]ᵀ =
      !![1,0,0;0,0,0;0,0,0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp

theorem pureState_trace₃ : (pureState (e (0 : Fin 3))).trace = 1 := by
  unfold pureState e
  suffices (mulᵣ ![(1 : Fin 1 → ℝ), 0, 0] ![1, 0, 0]ᵀ).trace = 1 by
    convert this <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp)
  rw [grudka_helper]
  simp

theorem basisState_trace_one {k : ℕ} : (pureState (e (0 : Fin k.succ))).trace = 1 := by
    unfold pureState e
    have : ((single (0:Fin k.succ) (0:Fin 1) (1:ℝ)).mulᵣ
            (single (0:Fin k.succ) (0:Fin 1) 1)ᵀ)
        = Matrix.of (fun i j => ite (i = 0) (ite (j = 0) 1 0) 0
        ) := by
        ext i j
        unfold mulᵣ dotProductᵣ single
        simp
        split_ifs
        all_goals tauto
    simp_rw [this, trace]
    simp

/-- The projection-valued measure corresponding to `word`
belong to the measure-once language of KOA `𝓚`.
-/
def PVM_of_word_of_channel {α : Type u_1} {r k : ℕ} (acc : Fin k.succ)
(𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ)
(h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM := by
have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
    (ρ := ⟨pureState (e 0),⟨pureState_psd _, basisState_trace_one⟩⟩) (hq := h𝓚)
exact @PVM_of_state k.succ acc
    (@krausApplyWord α ℝ _ _ _ word.1 k.succ r word.2 𝓚 (pureState (e 0)))
    this.2 this.1

def getPVM₃ {α : Type u_1} {r : ℕ}
(𝓚 : α → Fin r → Matrix (Fin (Nat.succ 2)) (Fin (Nat.succ 2)) ℝ)
(h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM :=
    @PVM_of_word_of_channel α r 2 2 𝓚 h𝓚 word



/-- 1/25/26
We accept `word` if starting in `e₀` we end up in `e₁` with probability at least 1/2.
-/
def MOlanguageAcceptedBy {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    (𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (PVM_of_word_of_channel acc 𝓚 (h𝓚) word).p
    (by simp only [PVM_of_word_of_channel, PVM_of_state]; exact 1) > 1/2}

/-- Measure-Once language accepted by 𝓚 is
{word | Probability that we are in state e₃, and not in the span of e₁,e₂, > 1/2}.
`q = 2` because we haven't generalized myPVM₂₃ yet
-/
def MOlanguageAcceptedBy₃ {α : Type*} {r : ℕ}
    (𝓚 : α → Fin r → Matrix (Fin 3) (Fin 3) ℝ)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
    @MOlanguageAcceptedBy α r 2 1 𝓚 h𝓚



def MOlanguageAcceptedBy' {α : Type*} {r : ℕ}
    (𝓚 : α → quantum_channel 3 r) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (getPVM₃ (fun a => (𝓚 a).1) (fun a => (𝓚 a).2) word).p
  (by simp only [getPVM₃, PVM_of_word_of_channel, PVM_of_state]; exact 1) > 1/2}


lemma grudka_language_nonempty :
  languageAcceptedBy 0 (grudka_R (θ := 0)) ≠ ∅ := by
    refine Set.nonempty_iff_ne_empty'.mp ?_
    refine nonempty_subtype.mpr ?_
    use ⟨0, ![]⟩
    unfold languageAcceptedBy
    simp only [Set.mem_setOf_eq]
    unfold krausApplyWord
    unfold pureState e single
    ext i j
    unfold mulᵣ
    simp

-- Now `pureState e₁`, `pureState e₂`, `pureState e₃` form a POVM.


lemma grudka_basic_operation : krausApply (grudka_R₀ 0)
  (pureState e₁) = pureState e₂ := by
    unfold krausApply pureState e₁ e₂
    have : mulᵣ ![(0: Fin 1 → ℝ), 1, 0] ![0, 1, 0]ᵀ =
      !![0,0,0;0,1,0;0,0,0] := by
      -- this could be generalized
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp
    rw [this]
    have : mulᵣ ![(1: Fin 1 → ℝ), 0, 0] ![1, 0, 0]ᵀ =
      !![1,0,0;0,0,0;0,0,0] := by
        apply grudka_helper
    rw [this]
    unfold grudka_R₀
    simp only [Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
      conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, empty_vecMul, add_zero, one_smul,
      empty_mul, Equiv.symm_apply_apply, cons_transpose, zero_vecMul, cons_vecMul, cons_val_one,
      neg_smul, neg_cons, neg_zero, neg_empty, zero_add, of_add_of, add_cons, empty_add_empty,
      EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true]
    constructor
    · ext i; fin_cases i <;> simp
    · constructor <;>
      · ext i; fin_cases i <;> simp [vecHead]

lemma grudka_basic_operation₂ : krausApply (grudka_R₀ 0)
  (pureState e₂) = pureState e₃ := by
    unfold krausApply pureState e₃ e₂
    have : mulᵣ ![(0: Fin 1 → ℝ), 1, 0] ![0, 1, 0]ᵀ =
      !![0,0,0;0,1,0;0,0,0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp
    rw [this]
    have : mulᵣ ![(0: Fin 1 → ℝ), 0, 1] ![0, 0, 1]ᵀ =
      !![0,0,0;0,0,0;0,0,1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp
    rw [this]
    unfold grudka_R₀
    simp only [Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
      conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, empty_vecMul, add_zero, one_smul,
      empty_mul, Equiv.symm_apply_apply, cons_transpose, zero_vecMul, cons_vecMul, cons_val_one,
      neg_smul, neg_cons, neg_zero, neg_empty, zero_add, of_add_of, add_cons, empty_add_empty,
      EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, and_self_left]
    constructor
    · ext i
      fin_cases i <;> simp
    · ext i
      fin_cases i <;> simp [vecHead,vecTail,vecHead,vecTail]


-- This is not hard to finish now:
-- example : krausApplyWord ![0,1] grudka_R₀ (pureState e₁) =
--   pureState e₁ := by
--   unfold krausApplyWord
--   have : Fin.init ![(0:Fin 2),1] = ![0] := by
--     ext i
--     rw [Fin.fin_one_eq_zero i]
--     rfl
--   rw [this]
--   simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
--   unfold krausApplyWord
--   have : Fin.init ![(0 : Fin 2)] = ![] := by
--     ext i
--     have := i.2
--     simp at this
--   rw [this]
--   unfold krausApplyWord
--   simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
--     cons_val_fin_one]
--   have : ![(0:Fin 2),1] ⟨1, (by simp : 1 < 1 + 1)⟩ = 1 := by simp
--   rw [this]
--   rw [grudka_basic_operation]
--   have := @grudka_basic_operation₂
--   unfold krausApply
--   unfold grudka_R₀

--   simp

--   sorry
