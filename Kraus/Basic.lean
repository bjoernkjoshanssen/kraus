import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions


import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
/-!

# Kraus operator automata and projection-valued measures

We define the language accepted by a measure-once Kraus operator automaton,
and a family of examples due to Grudka et al.

References:

 * J. Lakshmanan, doctoral dissertation, University of Hawaii at Manoa, 2026

 * `Quantum Synchronizing Words: Resetting and Preparing Qutrit States`,
   Grudka et al., 2025

 * `Unbounded length minimal synchronizing words for quantum channels over qutrits`,
   B. Kjos-Hanssen and J. Lakshmanan, preprint 2026.

 * Li, Lvzhou and Qiu, Daowen and Zou, Xiangfu and Li, Lvjun and
              Wu, Lihua and Mateus, Paulo,
     `Characterizations of one-way general quantum finite automata`, 2012

 * Yakary{\i}lmaz, Abuzer and Say, A. C. Cem,
    `Unbounded-error quantum computation with small space bounds`,
    2011
-/

open Matrix MatrixOrder

/-- Completely positive map given by a (not necessarily minimal) Kraus family. -/
def krausApply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
  {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
  (K : r → Matrix q q R)
  (ρ : Matrix q q R) : Matrix q q R :=
  ∑ i : r, K i * ρ * (K i)ᴴ



/-- Kraus operator preserves PSD property. -/
lemma krausApply_psd {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
[AddLeftMono R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (ρ : Matrix (Fin q) (Fin q) R) (hρ : ρ.PosSemidef) :
  (krausApply K ρ).PosSemidef := by
  unfold krausApply
  refine posSemidef_sum Finset.univ ?_
  intro i _
  have := @Matrix.PosSemidef.mul_mul_conjTranspose_same (Fin q) (Fin q) R
    _ _ _ _ _ ρ hρ (K i)
  convert this

def quantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R) : Prop :=
    ∑ i : Fin r, (K i)ᴴ * K i = 1

open MatrixOrder

def quantumOperation {R : Type*} [RCLike R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R) : Prop :=
    ∑ i : Fin r, (K i)ᴴ * K i ≤ 1

def densityMatrix
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (q : ℕ) :=
{ρ : Matrix (Fin q) (Fin q) R // ρ.PosSemidef ∧ ρ.trace = 1}

def subNormalizedDensityMatrix
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (q : ℕ) :=
{ρ : Matrix (Fin q) (Fin q) R // ρ.PosSemidef ∧ ρ.trace ≤ 1}


def quantum_channel
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (q r : ℕ) :=
  {K : Fin r → Matrix (Fin q) (Fin q) R // ∑ i : Fin r, (K i)ᴴ * K i = 1 }

lemma quantumChannel_preserves_trace
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (hq : quantumChannel K)
  (ρ : Matrix (Fin q) (Fin q) R) :
  (krausApply K ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  rw [hq]
  simp

instance {R : Type*} [RCLike R] : PartialOrder R := RCLike.toPartialOrder


lemma quantum_channel_preserves_trace
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
  {q r : ℕ}
  (K : quantum_channel q r)
  (ρ : Matrix (Fin q) (Fin q) R) :
  (krausApply K.1 ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K.1 i)ᴴ) (B := ρ) (A := K.1 i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  rw [K.2]
  simp


lemma quantumChannel_preserves_trace_one
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (hq : quantumChannel K)
  (ρ : Matrix (Fin q) (Fin q) R) (hρ : ρ.trace = 1) :
  (krausApply K ρ).trace = 1 := by
  rw [@quantumChannel_preserves_trace R _ _ _ q r K hq ρ]
  exact hρ

/-- Realizing a quantumChannel as a map on densityMatrices. -/
def krausApply_densityMatrix
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [AddLeftMono R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (hq : quantumChannel K)
  (ρ : densityMatrix q (R := R)) : densityMatrix q (R := R) :=
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

/-- As long as we have a quantum channel,
we can iterate over a word and stay within the density matrices. -/
theorem krausApplyWord_densityMatrix {α : Type*}
 {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
{n q r : ℕ} (word : Fin n → α)
  {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R}
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
{R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
  (hq : ∀ a, quantumChannel (𝓚 a))
  (ρ : densityMatrix q (R := R)) : densityMatrix q (R := R) :=
  ⟨krausApplyWord word 𝓚 ρ.1, krausApplyWord_densityMatrix _ hq _⟩


def krausApplyWord_channel {α : Type*}
    {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
    {n q r : ℕ} (word : Fin n → α)
    (𝓚 : α → quantum_channel q r (R := R))
    (ρ : densityMatrix q (R := R)) : densityMatrix q (R := R) :=
  krausApplyWord_map word (fun a => (𝓚 a).1)
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

def grudka_R₀ {R : Type*} [RCLike R] : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) R := ![
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
open Real in
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

noncomputable def grudka_C (θ : ℂ) : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℂ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![Complex.cos θ, -Complex.sin θ, 0;
       Complex.sin θ, Complex.cos θ,  0;
       0,     0,      1],
    0
  ] -- B
]

example (θ : ℝ) : (grudka_R θ 0 0).trace = 0 := by simp [grudka_R]
example (θ : ℂ) : (grudka_C θ 0 0).trace = 0 := by simp [grudka_C]

open Matrix

open Real in
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


-- example (θ : ℂ) {ρ : Matrix (Fin 3) (Fin 3) ℂ}
--     (hρ : ρ.trace = 1) :
--     (krausApply (grudka_C θ 1) ρ).trace = 1 := by
--   rw [krausApply, trace]
--   unfold grudka_C
--   simp only [diag, sum_apply, mul_apply, conjTranspose_apply]
--   simp [Fin.sum_univ_succ]
--   rw [trace] at hρ
--   simp [Fin.sum_univ_succ] at hρ
--   ring_nf
--   have := Complex.cos_sq_add_sin_sq θ
--   have := Complex.sin_sq_add_cos_sq θ
--   generalize Complex.cos θ  = c at *
--   generalize Complex.sin θ  = s at *
--   have : c ^ 2 = 1 - s ^ 2 := by exact eq_sub_of_add_eq' this
--   generalize (starRingEnd ℂ) s = s' at *
--   generalize (starRingEnd ℂ) c = c' at *
--   generalize ρ 0 0 = ρ₀₀ at *
--   generalize ρ 0 1 = ρ₀₁ at *
--   generalize ρ 1 0 = ρ₁₀ at *
--   generalize ρ 1 1 = ρ₁₁ at *
--   generalize ρ 2 2 = ρ₂₂ at *
--   ring_nf
--   have : ρ₀₀ = 1 - (ρ₁₁ + ρ₂₂) := by exact eq_sub_of_add_eq hρ
--   subst this
--   clear hρ
--   have : c * c' + s * s' = 1 := by sorry

--   suffices c * (1 - (ρ₂₂)) * c' + (c * ρ₁₀ * s' - c * s' * ρ₀₁) +
--           ((1 - (ρ₂₂)) * s' * s - c' * ρ₁₀ * s) +
--         c' * ρ₀₁ * s +
--     ρ₂₂ =
--     1 by sorry
--   suffices c * (1 - (ρ₂₂)) * c' + (c * ρ₁₀ * s' - c * s' * ρ₀₁) +
--           ((1 - (ρ₂₂)) * s' * s - c' * ρ₁₀ * s) +
--         c' * ρ₀₁ * s +
--     ρ₂₂ =
--     1 by sorry
--   sorry

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

example : quantumChannel (grudka_R₀ 1 (R := ℝ)) := by
  unfold quantumChannel grudka_R₀
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ]

open Real in
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
  densityMatrix 3 (R := ℝ) → densityMatrix 3 (R := ℝ) :=
  krausApplyWord_map word _ fun i ↦ grudka_quantumChannel θ i





def e₁ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![1, 0, 0]
def e₂ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![0, 1, 0]
def e₃ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![0, 0, 1]
def e {R : Type*} [One R] [Zero R] {k : ℕ} : Fin k → Matrix (Fin k) (Fin 1) R :=
  fun i => single i 0 1
def pureState {R : Type*} [Mul R] [Add R] [Zero R] {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :=
    mulᵣ e e.transpose

def pureState_C {R : Type*} [Mul R] [Add R] [Zero R] [Star R]
    {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :=
  mulᵣ e eᴴ

lemma pureState_selfAdjoint_C {R : Type*} [Ring R] [StarRing R]
        {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :
  Matrix.IsHermitian (pureState_C e) := by
    unfold pureState_C
    simp +decide [ Matrix.IsHermitian]

lemma pureState_selfAdjoint {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) :
  Matrix.IsHermitian (pureState e) := by
    unfold pureState
    norm_num [ Matrix.PosSemidef ] at *;
    simp +decide [ Matrix.IsHermitian, Matrix.transpose_mul ];

open Real in
def pureState_projection'_C {R : Type*} [RCLike R]
    {k : ℕ} (e : EuclideanSpace R (Fin k)) (he : ‖e‖ = 1) :
    IsStarProjection (pureState_C (fun (i : Fin k) (_ : Fin 1) => e i)) := {
      isIdempotentElem := by
        unfold pureState_C
        simp +decide only [IsIdempotentElem, mulᵣ_eq];
        simp +decide only [ ← Matrix.ext_iff, Matrix.mul_apply ];
        simp +decide only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
          conjTranspose_apply, RCLike.star_def, Finset.sum_const, Finset.card_singleton, one_smul,
          ← mul_assoc, ← Finset.sum_mul, mul_eq_mul_right_iff, map_eq_zero];
        simp +decide only [EuclideanSpace.norm_eq, sqrt_eq_one, mul_assoc,
          ← Finset.mul_sum _ _ _] at he ⊢;
        intro i j
        left
        suffices  ∑ i, (starRingEnd R) (e.ofLp i) * e.ofLp i = 1 by
            rw [this]
            simp
        have (i : Fin k) : (starRingEnd R) (e.ofLp i) * e.ofLp i
            = ‖e.ofLp i‖ ^ 2 := by exact RCLike.conj_mul (e.ofLp i)
        simp_rw [this]
        generalize e.ofLp = α at *
        suffices RCLike.ofReal (∑ x, ‖α x‖ ^ 2) = (1 : R) by
            rw [← this]
            norm_num
        rw [he]
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint_C
  }

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
  IsStarProjection (pureState (e i) (R := ℝ)) := {
      isIdempotentElem := by
        unfold IsIdempotentElem pureState e
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint
  }

lemma pureState_projection_C {R : Type*} [Ring R] [StarRing R] {k : ℕ} (i : Fin k) :
  IsStarProjection (pureState_C (e i) (R := R)) := {
      isIdempotentElem := by
        unfold IsIdempotentElem pureState_C e
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint_C
  }

/-- Projection onto span ⟨e₁, e₂⟩ is indeed a star-projection.
So we could form a PMF with two outcomes (e₁,e₂) vs. e₃.
-/
lemma pureState_projection'' :
  IsStarProjection (pureState (e (0:Fin 3) (R := ℝ))
    + pureState (e (1 : Fin 3))) := {
      isIdempotentElem := by
        unfold IsIdempotentElem
        rw [mul_add]
        repeat rw [add_mul]
        have : pureState (e (0:Fin 3)) * pureState (e 0) (R := ℝ) =
          pureState (e 0) := by
          have := @pureState_projection 3 0
          exact this.isIdempotentElem
        rw [this]
        have : pureState (e (1:Fin 3)) * pureState (e 1) (R := ℝ) =
          pureState (e 1) := by
          have := @pureState_projection 3 1
          exact this.isIdempotentElem
        rw [this]
        have : pureState (e (1:Fin 3)) * pureState (e 0) (R := ℝ) =
          0 := by
          unfold pureState e
          simp
        rw [this]
        have : pureState (e (0:Fin 3)) * pureState (e 1) (R := ℝ) =
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

lemma pureState_projection''_C {R : Type*} [RCLike R] :
  IsStarProjection (pureState_C (e (0:Fin 3) (R := R))
    + pureState_C (e (1 : Fin 3))) := {
      isIdempotentElem := by
        unfold IsIdempotentElem
        rw [mul_add]
        repeat rw [add_mul]
        have : pureState_C (e (0:Fin 3)) * pureState_C (e 0) (R := R) =
          pureState_C (e 0) := by
          have := @pureState_projection_C R _ _ 3 0
          exact this.isIdempotentElem
        rw [this]
        have : pureState_C (e (1:Fin 3)) * pureState_C (e 1) (R := R) =
          pureState_C (e 1) := by
          have := @pureState_projection_C R _ _ 3 1
          exact this.isIdempotentElem
        rw [this]
        have : pureState_C (e (1:Fin 3)) * pureState_C (e 0) (R := R) =
          0 := by
          unfold pureState_C e
          simp
        rw [this]
        have : pureState_C (e (0:Fin 3)) * pureState_C (e 1) (R := R) =
          0 := by
          unfold pureState_C e
          simp
        rw [this]
        simp
      isSelfAdjoint := by
        refine IsSelfAdjoint.add ?_ ?_
        · apply (@pureState_projection_C R _ _ 3 0).isSelfAdjoint
        · apply (@pureState_projection_C R _ _ 3 1).isSelfAdjoint
  }


theorem psd_versions_general {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    {k : ℕ} (e : Matrix (Fin k) (Fin k) R) (x : Fin k →₀ R)
  (this : 0 ≤ star ⇑x ⬝ᵥ e *ᵥ ⇑x) :
  0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * e i j * xj := by
      convert this
      rw [Finsupp.sum]
      have : (∑ a ∈ x.support, x.sum fun j xj ↦ star (x a) * e a j * xj)
           = (∑ a ∈ x.support, star (x a) * x.sum fun j xj ↦ e a j * xj)  := by
        congr
        ext j
        simp_rw [mul_assoc]
        exact Eq.symm (Finsupp.mul_sum _ x)
      simp_rw [this]
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · rw [dotProduct]
        congr
        ext i
        rw [mulVec, dotProduct]
        simp only [Pi.star_apply]
        congr
        refine Finsupp.sum_fintype x (fun j xj ↦ e i j * xj) ?_
        simp
      · intro i _ hi
        simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
        rw [hi]
        simp

theorem psd_versions {k : ℕ} (e : Matrix (Fin k) (Fin k) ℝ) (x : Fin k →₀ ℝ)
  (this : 0 ≤ ⇑x ⬝ᵥ e *ᵥ ⇑x) :
  0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * e i j * xj := by
      apply psd_versions_general
      convert this

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

-- {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

theorem matrix_identity_general {R : Type*} [RCLike R]
    (k : ℕ) (e : Matrix (Fin k) (Fin 1) R) (α : Fin k → R) :
  star α ⬝ᵥ (e * eᴴ) *ᵥ α = (star α ᵥ* e * eᴴ *ᵥ α) 0 := by
  simp only [Pi.mul_apply, vecMul, dotProduct, Pi.star_apply,
    RCLike.star_def, mulVec, mul_comm, Finset.mul_sum, mul_assoc];
  congr; ext u; congr; ext v
  simp [ Matrix.mul_apply, mul_comm, mul_left_comm ]



lemma pureState_psd_C {R : Type*} [RCLike R] [PartialOrder R]
    [StarOrderedRing R]
    {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :
  Matrix.PosSemidef (pureState_C e) := by
  constructor
  · exact pureState_selfAdjoint_C _
  · intro x
    suffices 0 ≤ star x ⬝ᵥ (pureState_C e).mulVec x by
      apply psd_versions_general
      convert this
    unfold pureState_C
    generalize ⇑x = α at *
    rw [mulᵣ_eq]
    rw [matrix_identity_general]
    change 0 ≤ (star α ᵥ* e) 0 * (eᴴ *ᵥ α) 0
    have : star ((eᴴ *ᵥ α) 0) = (star α ᵥ* e) 0 := by
        rw [vecMul, mulVec, dotProduct, dotProduct]
        simp only [conjTranspose_apply, RCLike.star_def, star_sum, star_mul',
          RingHomCompTriple.comp_apply, RingHom.id_apply, Pi.star_apply]
        congr
        ext i
        rw [mul_comm]
    rw [← this]
    refine star_mul_self_nonneg ((eᴴ *ᵥ α) 0)


example : pureState e₁ = !![1,0,0;0,0,0;0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureState, e₁, pureState, mulᵣ]

-- Trace exercise: probability of being in the state e₁.
open Real in
example : (pureState e₁ * (grudka_R θ 1 0)).trace = cos θ := by
  unfold e₁ grudka_R pureState
  simp only [mulᵣ_eq, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

open Real in
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
  rw [← hρ, Fin.sum_univ_three]

lemma pureState_probability_one_C {R : Type*} [RCLike R] {ρ : Matrix (Fin 3) (Fin 3) R}
    (hρ : ρ.trace = 1) :
      (pureState_C e₁ * ρ).trace
    + (pureState_C e₂ * ρ).trace
    + (pureState_C e₃ * ρ).trace = 1 := by
  unfold pureState_C e₁ e₂ e₃
  unfold conjTranspose
  simp only [transpose, cons_val', Pi.one_apply, Pi.zero_apply, cons_val_fin_one, mulᵣ_eq]
  repeat rw [trace]
  simp only [diag, mul_apply] at hρ ⊢
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, cons_val', Pi.one_apply,
    Pi.zero_apply, cons_val_fin_one, Finset.sum_const, Finset.card_singleton, one_smul,
    Fin.sum_univ_succ, cons_val_zero, cons_val_succ, Fin.succ_zero_eq_one,
    zero_mul, add_zero, one_mul, zero_add, Finset.sum_singleton,
    Fin.succ_one_eq_two] at hρ ⊢
  rw [trace] at hρ
  simp only [diag_apply] at hρ
  simp only [RCLike.star_def, Fin.isValue, map_apply, of_apply, cons_val_zero, map_one, one_mul,
    cons_val_one, map_zero, zero_mul, cons_val, add_zero, zero_add]
  rw [← hρ, Fin.sum_univ_three]


lemma pure_state_eq {k : ℕ} (i : Fin k) :
    (single i (0 : Fin 1) (1 : ℝ)).mulᵣ (single i 0 1)ᵀ
    = Matrix.single i i 1 := by
  have : (single i (0:Fin 1) (1:ℝ))ᵀ = single 0 i 1 := by
    simp
  rw [this]
  simp

lemma pure_state_eq_C {R : Type*} [RCLike R] {k : ℕ} (i : Fin k) :
    (single i (0 : Fin 1) (1 : R)).mulᵣ (single i 0 1)ᴴ
    = Matrix.single i i 1 := by
  have : (single i (0:Fin 1) (1:R))ᴴ = single 0 i 1 := by
    simp
  rw [this]
  simp

open MatrixOrder
-- instance {n : ℕ} :   StarRing (Matrix (Fin n) (Fin n) ℝ) := by apply?

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

theorem matrix_posSemidef_eq_star_mul_self'_C {R : Type*} [RCLike R] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) R)
(hP : 0 ≤ P) : ∃ B, P = star B * B := by
  use CFC.sqrt P
  have h₀ : (CFC.sqrt P)ᴴ = CFC.sqrt P := by
    have := hP.1
    simp only [sub_zero] at this ⊢
    nth_rw 2 [← this]
    symm
    rw [@CFC.sqrt_eq_iff]
    · rw [← conjTranspose_mul]
      congr
      apply @CFC.sqrt_mul_sqrt_self (a := P)
      · exact topologicalRing
      · exact instT2SpaceMatrix
      · exact hP
    · exact star_nonneg_iff.mpr hP
    · exact star_nonneg_iff.mpr <| CFC.sqrt_nonneg P
  have : star (CFC.sqrt P) = CFC.sqrt P := by
    have := hP.1
    simp only [sub_zero] at this ⊢
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


instance {R : Type*} [RCLike R] : PartialOrder R := RCLike.toPartialOrder

instance {R : Type*} [RCLike R] : StarOrderedRing R := RCLike.toStarOrderedRing

theorem trace_mul_posSemidef_nonneg_general {R : Type*} [RCLike R]
    {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) R}
    (hρ : ρ ≥ 0) (hP : P ≥ 0) : 0 ≤ (P * ρ).trace := by
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) R, P = star B * B :=
        @matrix_posSemidef_eq_star_mul_self'_C R _ n P hP
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) R, P = Bᴴ * B := by
        use B
        rw [hB]
        congr
      have h_trace_cyclic : Matrix.trace (P * ρ) = Matrix.trace (B * ρ * Bᴴ) := by
        simp +decide only [hB, Matrix.mul_assoc, Matrix.trace_mul_comm B];
        exact trace_mul_cycle' Bᴴ B ρ;
      have h_pos_semidef : 0 ≤ (B * ρ * Bᴴ) := by
        constructor
        · unfold IsHermitian
          simp only [sub_zero, conjTranspose_mul, conjTranspose_conjTranspose]
          rw [mul_assoc]
          congr
          refine IsHermitian.eq ?_
          refine isHermitian_iff_isSelfAdjoint.mpr ?_
          exact LE.le.isSelfAdjoint hρ
        · intro x
          have := @psd_versions_general R _ _ RCLike.toPartialOrder
            n (B * ρ * Bᴴ) x (by
                change @LE.le R RCLike.toPartialOrder.toLE 0 (star ⇑x ⬝ᵥ (B * ρ * Bᴴ) *ᵥ ⇑x)
                have := Bᴴ *ᵥ ⇑x
                have := ρ *ᵥ this
                have := ((B * ρ) *ᵥ (Bᴴ *ᵥ ⇑x))
                suffices @LE.le R RCLike.toPartialOrder.toLE 0
                    (star ⇑x ⬝ᵥ ((B * ρ) *ᵥ (Bᴴ *ᵥ ⇑x))) by
                    convert this using 1
                    simp
                suffices @LE.le R RCLike.toPartialOrder.toLE 0
                    (star ⇑x ⬝ᵥ (B *ᵥ ρ *ᵥ (Bᴴ *ᵥ ⇑x))) by
                    convert this using 1
                    simp
                    grind only
                rw [Matrix.dotProduct_mulVec]
                rw [Matrix.dotProduct_mulVec]
                have : star ⇑x ᵥ* B = star (Bᴴ *ᵥ ⇑x) := by
                    rw [star_mulVec]
                    congr
                    exact Eq.symm (conjTranspose_conjTranspose B)
                rw [this]
                generalize (Bᴴ *ᵥ ⇑x) = b
                rw [← Matrix.dotProduct_mulVec]
                have := @PosSemidef.dotProduct_mulVec_nonneg (Fin n)
                    R _ RCLike.toPartialOrder _ _ ρ (LE.le.posSemidef hρ) b
                    -- notice this trick ^^
                convert this)
          simp only [RCLike.star_def, sub_apply, zero_apply, sub_zero, ge_iff_le]
          exact this
      rw [h_trace_cyclic]
      exact @PosSemidef.trace_nonneg (Fin n) R _ _ _ _
        _ (B * ρ * Bᴴ) (by apply LE.le.posSemidef;tauto)

/-- Feb 1, 2026 -/
lemma quantumOperation_reduces_trace
    {R : Type*} [RCLike R]
    {q r : ℕ}
    (K : Fin r → Matrix (Fin q) (Fin q) R)
    (hq : quantumOperation K)
    (ρ : Matrix (Fin q) (Fin q) R)
    (hρ : 0 ≤ ρ) :
    (krausApply K ρ).trace ≤ ρ.trace := by
  unfold quantumOperation at hq
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  generalize  ∑ i, (K i)ᴴ * K i = α at *
  suffices 0 ≤ ((1 - α) * ρ).trace by
    have : 0 ≤ (ρ - α * ρ).trace := by
        convert this using 1
        congr
        have : ρ = 1 * ρ := by simp
        nth_rw 1 [this]
        exact Eq.symm (Matrix.sub_mul 1 α ρ)
    have :  0 ≤ ρ.trace - (α * ρ).trace := by
        rw [← trace_sub]
        exact this
    exact sub_nonneg.mp this
  have : 0 ≤ 1 - α := by exact nonneg_iff_posSemidef.mpr hq
  exact @trace_mul_posSemidef_nonneg_general R _ q ρ (1 - α) hρ this

lemma quantumOperation_preserves_trace_le_one
    {R : Type*} [RCLike R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (hq : quantumOperation K)
  (ρ : Matrix (Fin q) (Fin q) R)
  (hρ : 0 ≤ ρ)
  (hρ₁ : ρ.trace ≤ 1) :
  (krausApply K ρ).trace ≤ 1 := by
  have := @quantumOperation_reduces_trace R _ q r K hq ρ hρ
  exact Std.IsPreorder.le_trans (krausApply K ρ).trace ρ.trace 1 this hρ₁

/--
Feb 1, 2026
Realizing a quantumChannel as a map on densityMatrices. -/
def krausApply_subNormalizedDensityMatrix
    {R : Type*} [RCLike R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (hq : quantumOperation K)
  (ρ : subNormalizedDensityMatrix q (R := R)) : subNormalizedDensityMatrix q (R := R) :=
  ⟨krausApply K ρ.1, ⟨krausApply_psd K ρ.1 ρ.2.1,
    quantumOperation_preserves_trace_le_one K hq ρ.1 (by
        have := ρ.2
        rw [← Matrix.nonneg_iff_posSemidef] at this
        exact this.1) ρ.2.2
   ⟩⟩

theorem krausApplyWord_subNormalizedDensityMatrix {α : Type*}
 {R : Type*} [RCLike R]
{n q r : ℕ} (word : Fin n → α)
  {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R}
  (hq : ∀ (a : α), quantumOperation (𝓚 a)) (ρ : subNormalizedDensityMatrix q) :
  (krausApplyWord word 𝓚 ρ.1).PosSemidef ∧ (krausApplyWord word 𝓚 ρ.1).trace ≤ 1 := by
    induction n with
    | zero => exact ρ.2
    | succ n ih =>
        exact (krausApply_subNormalizedDensityMatrix (𝓚 (word (Fin.last n))) (hq _)
          ⟨krausApplyWord (Fin.init word) 𝓚 ρ.1, ih (Fin.init word)⟩).2

/-- If each letter is a quantum channel
then the whole word maps density matrices to density matrices. -/
def krausApplyWord_map_sub {α : Type*}
  {R : Type*} [RCLike R]
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
  (hq : ∀ a, quantumOperation (𝓚 a))
  (ρ : subNormalizedDensityMatrix q (R := R)) : subNormalizedDensityMatrix q (R := R) :=
    ⟨
    krausApplyWord word 𝓚 ρ.1,
    @krausApplyWord_subNormalizedDensityMatrix α R _ n q r word
    𝓚 hq ρ⟩



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

theorem posSemidef_of_isStarProjection_C {R : Type*} [RCLike R] {n : ℕ}
  (P : Matrix (Fin n) (Fin n) R) (hP : IsStarProjection P) : P.PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact IsStarProjection.nonneg hP


lemma trace_mul_nonneg {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg hρ'
  apply posSemidef_of_isStarProjection
  exact hP

lemma trace_mul_nonneg_C {R : Type*} [RCLike R] {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) R}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg_general (nonneg_iff_posSemidef.mpr hρ')
  suffices P.PosSemidef by exact nonneg_iff_posSemidef.mpr this
  apply posSemidef_of_isStarProjection_C
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

lemma nonneg_trace'_C {R : Type*} [RCLike R] {n : ℕ}
    {ρ : Matrix (Fin n) (Fin n) R} (hρ' : ρ.PosSemidef)
    (e : Matrix (Fin n) (Fin 1) R)
    (he : ‖WithLp.toLp 2 fun i ↦ e i 0‖ = 1) -- not really necessary
  : 0 ≤ (pureState_C e * ρ).trace := by
      apply trace_mul_nonneg_C hρ'
      have := @pureState_projection'_C _ _ n {ofLp := fun i => e i 0} he
      convert this

lemma nonneg_trace_of_posSemidef {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef) (i : Fin n) :
    0 ≤ (pureState (e i) * ρ).trace := by
  apply nonneg_trace' hρ'
  simp [e, single, PiLp.instNorm]

open Real in
lemma nonneg_trace_of_posSemidef_C {R : Type*} [RCLike R] {n : ℕ} {ρ : Matrix (Fin n) (Fin n) R}
    (hρ' : ρ.PosSemidef) (i : Fin n) :
    0 ≤ (pureState_C (e i) * ρ).trace := by
  apply nonneg_trace'_C hρ'
  simp only [PiLp.instNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, rpow_ofNat, one_div, e, single, Fin.isValue, of_apply, and_true]
  suffices (∑ x, ‖if i = x then (1:R) else 0‖ ^ 2) = 1 by rw [this];simp
  have : (fun (x : Fin n) => ‖if i = x then  (1:R)  else 0‖ ^ 2) =
         (fun x =>            if i = x then ‖(1:R)‖ else ‖(0:R)‖) := by
        ext j
        split_ifs <;> simp
  simp_rw [this]
  simp


lemma sum_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, of (Function.update 0 x (ρ.row x)) = ρ := by
      ext i j
      rw [Finset.sum_apply]
      simp only [row, Finset.sum_apply, of_apply, Function.update,
        eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      rw [← congrFun (Fintype.sum_ite_eq i fun j ↦ ρ i) j]
      aesop

lemma sum_rows_C {R : Type*} [RCLike R] {k : ℕ} (ρ : Matrix (Fin k) (Fin k) R) :
  ∑ x, of (Function.update 0 x (ρ.row x)) = ρ := by
      ext i j
      rw [Finset.sum_apply]
      simp only [row, Finset.sum_apply, of_apply, Function.update,
        eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      rw [← congrFun (Fintype.sum_ite_eq i fun j ↦ ρ i) j]
      aesop


lemma single_row {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R} (x : Fin k) :
  single x x 1 * ρ = of (Function.update 0 x (ρ.row x)) := by
        rw [@Matrix.single_mul_eq_updateRow_zero]
        unfold updateRow
        simp

lemma combined_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, single x x 1 * ρ = ρ := by
      have := @sum_rows k ρ
      nth_rw 2 [← this]
      have := @single_row ℝ _ k ρ
      simp_rw [this]


theorem POVM_PMF.aux₀ {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
  (hρ : ρ.trace = 1) (hρ' : ρ.PosSemidef) :
  (∑ a, ⟨
    (pureState (e a) * ρ).trace,
    nonneg_trace_of_posSemidef hρ' a⟩) = ENNReal.toNNReal 1 := by
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
  ∑ a, ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩ = 1 := by
    exact
      (toNNReal_eq_one_iff _).mp
      <| ENNReal.toNNReal_one ▸ POVM_PMF.aux₀ hUT hPS
       ▸ toNNReal_sum (by simp)

/-- Unlike `standard_basis_probability_one` this one does not require PSD. -/
lemma standard_basis_probability_one_C {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} (hUT : ρ.trace = 1) :
  ∑ a, (pureState_C (e a) * ρ).trace = 1 := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    rw [← sum_rows_C ρ] at hUT
    rw [← trace_sum]
    exact hUT

lemma standard_basis_probability_general {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} :
  ∑ a, (pureState_C (e a) * ρ).trace = ρ.trace := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    nth_rw 2 [← sum_rows_C ρ]
    rw [← trace_sum]



def subPMF (α : Type*) :=
  { f : α → ℝ≥0∞ // ∃ p ≤ 1, HasSum f p }

def subPMF.ofFinset (α : Type*)
    (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a ≤ 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : subPMF α :=
  ⟨f, by
    have := @hasSum_sum_of_ne_finset_zero (α := ENNReal) (β := α) _ _
        (by exact SummationFilter.unconditional α) f s h'
            (SummationFilter.instLeAtTopUnconditional α)
    use ∑ a ∈ s, f a
    ⟩

def subPMF.ofFintype (α : Type*) [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a ≤ 1) : subPMF α := by
    apply subPMF.ofFinset (s := Finset.univ)
    · exact h
    intro a ha
    simp at ha


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
noncomputable def POVM_PMF {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : 0 ≤ ρ) : PMF (Fin k) := by
    apply PMF.ofFintype (
        fun i => ofNNReal ⟨RCLike.re (pureState_C (e i) * ρ).trace, by
            let t := (pureState_C (e i) * ρ).trace
            have : 0 ≤ t := by
                have := nonneg_trace_of_posSemidef_C hPS i
                convert this
                simp
            refine (RCLike.re_nonneg_of_nonneg ?_).mpr this
            exact LE.le.isSelfAdjoint this⟩)
    refine Eq.symm ((fun {x y} hx hy ↦ (toReal_eq_toReal_iff' hx hy).mp) ?_ ?_ ?_)
    · simp
    · simp
    simp only [toReal_one]
    symm
    have := @standard_basis_probability_one_C R _ k ρ hUT
    have := congrArg (RCLike.re) this
    simp only [map_sum, RCLike.one_re] at this ⊢
    rw [← this]
    refine toReal_sum ?_
    simp

/-- Feb 1, 2026 -/
noncomputable def POVM_subPMF {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) : subPMF (Fin k) := by
    apply subPMF.ofFintype _ (
        fun i => ofNNReal ⟨RCLike.re (pureState_C (e i) * ρ).trace, by
            let t := (pureState_C (e i) * ρ).trace
            have : 0 ≤ t := by
                have := nonneg_trace_of_posSemidef_C hPS i
                convert this
                simp
            refine (RCLike.re_nonneg_of_nonneg ?_).mpr this
            exact LE.le.isSelfAdjoint this⟩)
    show ∑ a, ofNNReal ⟨RCLike.re (pureState_C (e a) * ρ).trace, _⟩ ≤ 1
    apply le_of_eq_of_le (α := ENNReal) --(b := ofNNReal ⟨RCLike.re ρ.trace, sorry⟩)
    · have := @toReal_eq_toReal_iff' (∑ a, ofNNReal
        ⟨RCLike.re (pureState_C (e a) * ρ).trace, by
            have := @nonneg_trace_of_posSemidef_C R _ k ρ (LE.le.posSemidef hPS)
                a
            have := (@RCLike.le_iff_re_im R _ 0 (w := (pureState_C (e a) * ρ).trace)).mp (by
                tauto)
            simp at this
            tauto⟩)
        (ofNNReal ⟨RCLike.re ρ.trace, by
            have : 0 ≤ ρ.trace := by
                refine PosSemidef.trace_nonneg ?_
                exact LE.le.posSemidef hPS
            have := (@RCLike.le_iff_re_im R _ 0 (w := ρ.trace)).mp this
            simp at this
            tauto⟩) (by simp) (by simp)
      rw [← this]
      simp only [coe_toReal, NNReal.coe_mk]
      have := @standard_basis_probability_general R _ k ρ
      have := congrArg (RCLike.re) this
      simp only [map_sum] at this ⊢
      simp_rw [← this]
      refine toReal_sum ?_
      simp
    · have := (@RCLike.le_iff_re_im R _ (z := ρ.trace) (w := 1)).mp hUT
      simp at this
      tauto






noncomputable def POVM_PMF' {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : ρ.PosSemidef) : PMF (Fin k) := by
    apply POVM_PMF (R := R) hUT (by exact nonneg_iff_posSemidef.mpr hPS)

noncomputable def POVM_subPMF' {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : ρ.PosSemidef) : subPMF (Fin k) := by
    apply POVM_subPMF (R := R) hUT (by exact nonneg_iff_posSemidef.mpr hPS)


lemma PMF₂₃help {R : Type*} [RCLike R] {ρ : Matrix (Fin 3) (Fin 3) R}
  (hPS : ρ.PosSemidef) :
  0 ≤ ((pureState_C (e 0) + pureState_C (e 1)) * ρ).trace := by
        refine trace_mul_posSemidef_nonneg_general (by exact nonneg_iff_posSemidef.mpr hPS) ?_
        have := (@nonneg_iff_posSemidef R (Fin 3) _ (pureState_C (e 0) + pureState_C (e 1))).mpr
        apply this
        refine PosSemidef.add (pureState_psd_C _) (pureState_psd_C _)

/-- A probability measure that gives the probability
of being in the xy-plane, or the z-axis,
for a given PSD trace-one matrix `ρ`.
See `myPVM₂₃` below.
-/
def PVM_PMF₂₃ {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((pureState (e 0) + pureState (e 1)) * ρ).trace, PMF₂₃help hPS⟩
      ⟨(                   pureState (e 2)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩)
  rw [← standard_basis_probability_one hUT hPS]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp_rw [add_mul, trace_add]
  simp
  rfl

-- noncomputable def PVM_PMF₂₃_C {ρ : Matrix (Fin 3) (Fin 3) ℂ}
--     (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
--   apply PMF.ofFintype (fun i => ofNNReal <| by
--     by_cases H : i = 0
--     · let p := ((pureState_C (e 0) + pureState_C (e 1)) * ρ).trace.re
--       exact ⟨p, (@PMF₂₃help_C ρ hPS).1⟩
--     · let p : NNReal := ⟨(pureState_C (e 2)  * ρ).trace.re, by
--             have := (nonneg_trace_of_posSemidef_C hPS 2).1
--             simp only [Complex.zero_re] at this
--             exact this
--             ⟩
--       exact ⟨p, by
--         unfold p
--         have := (@nonneg_trace_of_posSemidef_C 3 ρ hPS 2).1
--         simp only [Complex.zero_re] at this
--         exact this⟩)
--   simp
--   have := @standard_basis_probability_one_C 3 ρ hUT
--   rw [Fin.sum_univ_three] at this
--   simp_rw [add_mul, trace_add]
--   simp

--   have := @Complex.add_re (pureState_C (e 0) * ρ).trace
--     (pureState_C (e 1) * ρ).trace
--   simp_rw [← this]
--   sorry

lemma one_eq_sum_pureState {R : Type*} [RCLike R] {k : ℕ} :
    1 = ∑ i : Fin k, pureState_C (e i) (R := R) := by
  unfold pureState_C e
  ext i j
  simp only [Fin.isValue, conjTranspose_single, star_one, mulᵣ_eq, single_mul_single_same, mul_one]
  by_cases H : i = j
  · subst H
    simp only [one_apply_eq, single]
    rw [Finset.sum_apply] -- !
    simp
  · simp only [single]
    rw [Finset.sum_apply] -- !
    symm
    have : (1 : Matrix (Fin k) (Fin k) R) i j = 0 := by
        exact one_apply_ne' fun a ↦ H (id (Eq.symm a))
    rw [this]
    simp only [Finset.sum_apply, of_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, forall_const, forall_eq, ne_eq]
    exact H

lemma one_eq_sum_pureState_R {k : ℕ} :
    1 = ∑ i : Fin k, pureState (e i) (R := ℝ) := by
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

lemma sum_one_sub₀ {R : Type*} [Ring R]
{k : ℕ}
(acc : Fin k)
(f : Fin k → Matrix (Fin k) (Fin k) R)
: ∑ i, f i - f acc = ∑ i, if i = acc then 0 else f i := by
    suffices  ∑ i, f i = (∑ i, if i = acc then 0 else f i) + f acc
        by rw [this];simp
    rw [← Finset.sum_add_sum_compl (s := {i | i ≠ acc})]
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not]
    have : ∑ i with i = acc, f i =
        f acc := by
        have :  ∑ i with i = acc, f i
            =  ∑ i ∈ {acc}, f i := by
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

lemma trace_one_sub_C {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
  (hPS : ρ.PosSemidef) : 0 ≤ ((1 - pureState_C (e acc)) * ρ).trace := by
        rw [one_eq_sum_pureState]
        rw [sum_one_sub₀]
        refine trace_mul_posSemidef_nonneg_general (by exact nonneg_iff_posSemidef.mpr hPS) ?_
        suffices (∑ i, if i = acc then
            (0 : Matrix (Fin k) (Fin k) R) else pureState_C (e i)).PosSemidef by
            exact nonneg_iff_posSemidef.mpr this
        refine posSemidef_sum Finset.univ ?_
        intro i _
        by_cases H : i = acc
        · subst H
          simp only [↓reduceIte]
          exact PosSemidef.zero
        · rw [if_neg H]
          refine posSemidef_of_isStarProjection_C (pureState_C (e i)) ?_
          exact pureState_projection_C i

lemma trace_one_sub {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
  (hPS : ρ.PosSemidef) : 0 ≤ ((1 - pureState (e acc)) * ρ).trace := by
        rw [one_eq_sum_pureState_R]
        rw [sum_one_sub₀]
        refine trace_mul_posSemidef_nonneg hPS ?_
        refine posSemidef_sum Finset.univ ?_
        intro i _
        by_cases H : i = acc
        · subst H
          simp only [↓reduceIte]
          exact PosSemidef.zero
        · rw [if_neg H]
          refine posSemidef_of_isStarProjection (pureState (e i)) ?_
          exact pureState_projection i

lemma PMF_of_state.sum_one {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ} (hUT : ρ.trace = 1)
  (hPS : ρ.PosSemidef) :
  ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨((1 - pureState (e acc)) * ρ).trace, trace_one_sub _ hPS⟩
      ⟨(     pureState (e acc)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩) = 1 := by
  rw [← standard_basis_probability_one hUT hPS, Fin.sum_univ_two]
  simp_rw [one_eq_sum_pureState_R]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero]
  simp_rw [sub_mul, trace_sub]
  refine (toReal_eq_toReal_iff' (by simp) (by simp)).mp ?_
  have h₀ : ((∑ i, pureState (e i) - pureState (e acc)) * ρ).trace
                                   + (pureState (e acc) * ρ).trace =
                                  ∑ a, (pureState (e a) * ρ).trace := by
    rw [sub_mul, trace_sub, sub_add_cancel, ← trace_sum]
    congr
    apply Matrix.sum_mul
  have h₁ : (∑ a, ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace_of_posSemidef hPS a⟩ ).toReal
           = ∑ a,           (pureState (e a) * ρ).trace := toReal_sum (by simp)
  rw [h₁, ← h₀, toReal_add (by simp) (by simp)]
  have (x : ℝ) (hx : x ≥ 0) : (ofNNReal ⟨x,hx⟩).toReal = x := by rfl
  have h₁ :=
    this (pureState (e acc) * ρ).trace (nonneg_trace_of_posSemidef hPS acc)
  rw [h₁]
  rw [_root_.add_left_inj]
  simp_rw [sub_mul, trace_sub]
  congr

lemma ofReal_inj_aux {k : ℕ} (J : Fin k → ℝ) (hnn : ∀ a, J a ≥ 0) : ∑ a, (⟨J a, hnn a⟩ : NNReal) =
        ⟨∑ a, J a, Fintype.sum_nonneg hnn⟩ := by
            refine Eq.symm (Subtype.ext ?_)
            simp only [NNReal.val_eq_coe]
            rw [← @RCLike.ofReal_inj ℝ _ _ (∑ a, ⟨J a, hnn a⟩ : NNReal)]
            simp

/-- Had to make this lemma as it seems missing in Mathlib. -/
theorem RCLike.re_sum {R : Type*} [RCLike R] {α : Type*} (s : Finset α) (f : α → R) :
RCLike.re (∑ i ∈ s, f i) = ∑ i ∈ s, RCLike.re (f i) := by
    exact map_sum RCLike.re f s

/-- Had to make this lemma as it seems missing in Mathlib. -/
theorem RCLike.sub_re {R : Type*} [RCLike R] (z w : R) :
    RCLike.re (z - w) = RCLike.re z - RCLike.re w := by
    exact AddMonoidHom.map_sub re z w


lemma PMF_of_state.sum_one_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1)
  (hPS : ρ.PosSemidef) :
  ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace,
        by
        have := @trace_one_sub_C R _ k acc ρ hPS
        have := @RCLike.le_iff_re_im R _ 0 ((1 - pureState_C (e acc)) * ρ).trace
        simp at this
        tauto
        ⟩
      ⟨RCLike.re (     pureState_C (e acc)  * ρ).trace, by
        have := (nonneg_trace_of_posSemidef_C hPS acc)
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
        simp at this
        tauto
      ⟩) = 1 := by
  have := @standard_basis_probability_one_C R _ k ρ hUT
  rw [← toReal_eq_toReal_iff']
  · simp only [Fin.isValue, Fin.sum_univ_two, ↓reduceIte, one_ne_zero, toReal_one]
    have : RCLike.re (∑ a, (pureState_C (e a) * ρ).trace) = 1 := by
      rw [this]
      simp
    rw [← this]
    simp_rw [one_eq_sum_pureState]
    have (j : Fin k) : pureState_C (e j) = (pureState_C ∘ e (R := R)) j := by
        simp
    simp_rw [this] at *
    have hnn (a : Fin k) :  0 ≤ RCLike.re ((pureState_C ∘ e (R := R)) a * ρ).trace := by
        have := (@nonneg_trace_of_posSemidef_C R _ k ρ hPS a)
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e a)) * ρ).trace
        simp at this
        tauto
    generalize (pureState_C ∘ e (R := R)) = f at *
    have := @RCLike.re_sum R _ (f := fun i : Fin k => (f i * ρ).trace)
        (s := Finset.univ)
    rw [this]
    simp_rw [sub_mul, trace_sub]
    have h₁ : (∑ a, ofNNReal ⟨RCLike.re (f a * ρ).trace,
      hnn _⟩ ).toReal
           = ∑ a,          RCLike.re (f a * ρ).trace := by
        rw [toReal_sum]
        · simp
        · simp
    rw [← h₁]
    have h₀ : ((∑ i, f i - f acc) * ρ).trace
                                   + (f acc * ρ).trace =
                                  ∑ a, (f a * ρ).trace := by
      rw [sub_mul, trace_sub, sub_add_cancel, ← trace_sum]
      congr
      apply Matrix.sum_mul
    congr
    rw [← coe_finset_sum]
    ring_nf
    set c := acc
    have := @Matrix.sum_mul (M := ρ) (f := f) (s := Finset.univ)
    simp_rw [this]
    simp_rw [RCLike.sub_re, trace_sum, RCLike.re_sum]
    let J : Fin k → ℝ := fun a => RCLike.re (f a * ρ).trace
    conv => left; left; right; left; right; change J c
    conv => left; right; right; change ⟨J c, _⟩
    conv => right; right; change ∑ a, ⟨J a, _⟩
    conv => left; left; right; left; left; change ∑ i, J i
    have : ∑ i, J i - J c = ∑ i with i ≠ c, J i := by
        suffices ∑ i, J i = ∑ i with i ≠ c, J i + J c by linarith
        rw [← Finset.sum_erase_add (a := c)]
        · congr
          ext
          simp
        · simp
    simp_rw [this]
    have (u v : NNReal) : ofNNReal u + ofNNReal v = ofNNReal (u + v) := by
        exact Eq.symm (coe_add u v)
    rw [this]
    congr
    have (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) :
        (⟨a,ha⟩ : NNReal) + (⟨b,hb⟩ : NNReal) =
        (⟨a+b, by linarith⟩) := Nonneg.mk_add_mk ha hb
    rw [this]
    have (J : Fin k → ℝ) (hnn : ∀ a, J a ≥ 0) : ∑ a, (⟨J a, hnn a⟩ : NNReal) =
        ⟨∑ a, J a, Fintype.sum_nonneg hnn⟩ := by
            apply ofReal_inj_aux
    rw [this]
    congr
    apply add_eq_of_eq_sub
    tauto
  · simp
  · simp

theorem pure_trace_one_sub_re {R : Type*} [RCLike R] {k : ℕ} (acc : Fin k)
  {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) :
    0 ≤ RCLike.re ((1 - pureState_C (e acc)) * ρ).trace := by
        have := @trace_one_sub_C R _ k acc ρ hPS
        have := @RCLike.le_iff_re_im R _ 0 ((1 - pureState_C (e acc)) * ρ).trace
        simp at this
        tauto

theorem pure_trace_nonneg_re {R : Type*} [RCLike R] {k : ℕ} (acc : Fin k)
  {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) :
  0 ≤ RCLike.re (pureState_C (e acc) * ρ).trace := by
        have := (nonneg_trace_of_posSemidef_C hPS acc)
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
        simp at this
        tauto

theorem trace_nonneg_re {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) : 0 ≤ RCLike.re ρ.trace := by
        have := (RCLike.le_iff_re_im).mp (PosSemidef.trace_nonneg hPS)
        rw [map_zero] at this
        exact this.1
open RCLike
 -- don't really need `subPMF` even with `subNormalizedDensityMatrix`
 --    For some reason we don't need `ρ.trace ≤ 1`.
lemma PMF_of_state.sum_one_general_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hPS : ρ.PosSemidef) :
    ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace, pure_trace_one_sub_re acc hPS⟩
      ⟨RCLike.re (     pureState_C (e acc)  * ρ).trace, pure_trace_nonneg_re acc hPS⟩)
                         = ofNNReal ⟨RCLike.re ρ.trace, trace_nonneg_re hPS⟩ := by
  have := @standard_basis_probability_general R _ k ρ
  simp only [Fin.isValue, Fin.sum_univ_two, ↓reduceIte, one_ne_zero]
  refine (toReal_eq_toReal_iff' (by simp) (by simp)).mp ?_
  have (x y : ENNReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (x + y).toReal = x.toReal + y.toReal := by
        exact toReal_add hx hy
  rw [this _ _ (by simp) (by simp)]
  simp only [coe_toReal, NNReal.coe_mk]
  rw [sub_mul]
  rw [trace_sub]
  simp
/-- Defining a Bernoulli probability measure by declaring that e_{acc} is the accepted subspace. -/
def PMF_of_state {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((1 - pureState (e acc)) * ρ).trace, trace_one_sub _ hPS⟩
      ⟨(     pureState (e acc)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩)
  exact PMF_of_state.sum_one _ hUT hPS

noncomputable def PMF_of_state_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace, by
        have h₀ := @trace_one_sub_C R _ k acc ρ hPS
        have := @RCLike.le_iff_re_im R _ 0 ((1 - pureState_C (e acc)) * ρ).trace
        simp at this
        tauto
      ⟩
      ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace, by
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
        simp at this
        have := @nonneg_trace_of_posSemidef_C R _ k ρ hPS acc
        tauto
      ⟩)
  exact @PMF_of_state.sum_one_general R _ k acc ρ hUT hPS

/-- To use conditional computability here we would need to know the state
had positive trace. -/
noncomputable def subPMF_of_state_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : subPMF (Fin 2) := by
  apply subPMF.ofFintype _ (fun i => ofNNReal <| ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace, by
        have h₀ := @trace_one_sub_C R _ k acc ρ hPS
        have := @RCLike.le_iff_re_im R _ 0 ((1 - pureState_C (e acc)) * ρ).trace
        simp at this
        tauto
      ⟩
      ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace, by
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
        simp at this
        have := @nonneg_trace_of_posSemidef_C R _ k ρ hPS acc
        tauto
      ⟩)
  have := @PMF_of_state.sum_one_general_general R _ k acc ρ hPS
  rw [this]
  have := (@RCLike.le_iff_re_im R _ (w := 1) (z := ρ.trace)).mp hUT
  simp only [one_re, one_im, coe_le_one_iff, ge_iff_le] at this ⊢
  exact this.1


/-- Feb 1, 2026: nonincreasing trace operators and a PMF. -/
noncomputable def PMF_of_state_bern {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : PMF (Bool) := by
  apply PMF.bernoulli (p := ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace, by
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
        simp at this
        have := @nonneg_trace_of_posSemidef_C R _ k ρ hPS acc
        tauto
      ⟩)
  have := (@RCLike.le_iff_re_im R _ (w := 1) (z := ρ.trace)).mp hUT
  simp only [one_re, one_im, ge_iff_le] at this ⊢
  suffices re (pureState_C (e acc) * ρ).trace ≤ 1 by
    exact NNReal.coe_le_one.mp this
  apply le_trans (b := re ρ.trace)
  · suffices (pureState_C (e acc) * ρ).trace ≤ ρ.trace by
      have := @RCLike.le_iff_re_im R _ (w := ρ.trace)
        (z := (pureState_C (e acc) * ρ).trace)
      simp at this
      tauto
    apply sub_nonneg.mp
    suffices 0 ≤ (1 * ρ).trace - (pureState_C (e acc) * ρ).trace by
      convert this
      simp
    rw [← trace_sub]
    suffices 0 ≤ ((1 - pureState_C (e acc)) * ρ).trace by
      convert this using 1
      congr
      exact Eq.symm (Matrix.sub_mul 1 (pureState_C (e acc)) ρ)
    set M := (1 : Matrix (Fin k) (Fin k) R) - pureState_C (e acc)
    have : M.PosSemidef := by
      unfold M
      refine posSemidef_of_isStarProjection_C (1 - pureState_C (e acc)) ?_
      refine IsStarProjection.one_sub ?_
      exact pureState_projection_C acc
    exact trace_one_sub_C acc hPS
  · exact this.1


open ENNReal

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

structure PVM_C {R : Type*} [RCLike R] where
  k : ℕ -- the dimension
  ρ : Matrix (Fin k) (Fin k) R          -- the state we're in
  hρ : ρ.PosSemidef
  t : ℕ -- the number of projections (states)
  op : Fin t → Matrix (Fin k) (Fin k) R -- the projections

  pf : ∀ i, IsStarProjection (op i)     -- ... are projections

  p : PMF (Fin t)                                       -- the measure
  pf' : ∀ i, p i = ofNNReal ⟨RCLike.re (op i * ρ).trace, by
    have h₀ := (trace_mul_nonneg_C hρ (pf i))
    have := @RCLike.le_iff_re_im R _ 0 ((op i * ρ).trace)
    simp at this
    tauto
    ⟩

open scoped ComplexOrder in
theorem trace_real_of_projection_and_pos_semidef {R : Type*} [RCLike R]
  {k : ℕ}
  (ρ O : Matrix (Fin k) (Fin k) R)
  (g₀ : ρ.IsHermitian) (g₁ : O.IsHermitian) :
  (O * ρ).trace = star (O * ρ).trace := by
    suffices h_trace : Matrix.trace ((O * ρ).conjTranspose) = Matrix.trace (O * ρ) by
      convert h_trace.symm using 1 ; simp +decide [ Matrix.trace ];
      simp +decide [ Matrix.mul_apply, mul_comm ];
    simp_all +decide only [IsHermitian, conjTranspose_mul];
    rw [ Matrix.trace_mul_comm ]

/-- The probability is given as a real part of a complex number.
Fortunately, the imaginary part is zero. -/
lemma im_zero_PVM {R : Type*} [RCLike R] (M : PVM_C (R := R)) :
    ∀ i, RCLike.im (M.op i * M.ρ).trace = 0 := by
    intro i
    have h₀ := M.hρ
    have h₁ := M.pf i
    generalize M.ρ = ρ at *
    generalize M.op i = O at *
    generalize M.t = n at *
    generalize M.k = k at *
    clear M
    have g₀ : ρ.IsHermitian := PosSemidef.isHermitian h₀
    have g₁ : O.IsHermitian := by
        refine isHermitian_iff_isSelfAdjoint.mpr ?_
        exact h₁.isSelfAdjoint
    suffices (O * ρ).trace = star (O * ρ).trace by
        exact RCLike.conj_eq_iff_im.mp (id (Eq.symm this))
    exact @trace_real_of_projection_and_pos_semidef R _ k ρ O g₀ g₁


noncomputable def myPVM {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := k
  t := k
  p := POVM_PMF hUT (nonneg_iff_posSemidef.mpr hPS)
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState (e i)
  pf := by exact fun i ↦ pureState_projection i
  pf' := by intro i; rfl
}

noncomputable def myPVM_C {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM_C (R := R) := {
  k := k
  t := k
  p := POVM_PMF' hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState_C (e i)
  pf := by exact fun i ↦ pureState_projection_C i
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

noncomputable def PVM_of_state_C {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM_C (R := R) := {
  k := k
  t := 2
  p := PMF_of_state_general acc hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (1 - pureState_C (e acc)) <| pureState_C (e acc)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte];
      refine IsStarProjection.one_sub ?_
      exact pureState_projection_C _
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte];
      exact pureState_projection_C acc
  pf' := by
    intro i
    fin_cases i
    · unfold PMF_of_state_general
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

def languageAcceptedBy_C {R : Type*} [RCLike R] {α : Type*}
  {q r : ℕ} (acceptStateIndex : Fin q.succ)
  (𝓚 : α → Fin r → Matrix (Fin q.succ) (Fin q.succ) R) :=
  {word : Σ n : ℕ, (Fin n → α) |
    krausApplyWord word.2 𝓚 (pureState_C (e 0)) = pureState_C (e acceptStateIndex)}


lemma grudka_helper : mulᵣ ![(1: Fin 1 → ℝ), 0, 0] ![1, 0, 0]ᵀ =
      !![1,0,0;0,0,0;0,0,0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp

theorem basisState_trace_one {k : ℕ} {i : Fin k.succ} :
    (pureState (e (i : Fin k.succ)) (R := ℝ)).trace = 1 := by
    unfold pureState e
    have : ((single (i:Fin k.succ) (0:Fin 1) (1:ℝ)).mulᵣ
            (single (i:Fin k.succ) (0:Fin 1) 1)ᵀ)
        = Matrix.of (fun a b => ite (a = i) (ite (b = i) 1 0) 0
        ) := by
        ext i j
        unfold mulᵣ dotProductᵣ single
        simp
        split_ifs
        all_goals tauto
    simp_rw [this, trace]
    simp

theorem basisState_trace_one_C {R : Type*} [RCLike R] {k : ℕ} {i : Fin k.succ} :
    (pureState_C (e (i : Fin k.succ)) (R := R)).trace = 1 := by
    unfold pureState_C e
    have : ((single (i:Fin k.succ) (0:Fin 1) (1:R)).mulᵣ
            (single (i:Fin k.succ) (0:Fin 1) 1)ᴴ)
        = Matrix.of (fun a b => ite (a = i) (ite (b = i) 1 0) 0
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
def PVM_of_word_of_channel {α : Type*} {r k : ℕ} (acc : Fin k.succ)
(𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ)
(h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM := by
have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
    (ρ := ⟨pureState (e 0),⟨pureState_psd _, basisState_trace_one⟩⟩) (hq := h𝓚)
exact @PVM_of_state k.succ acc
    (@krausApplyWord α ℝ _ _ _ word.1 k.succ r word.2 𝓚 (pureState (e 0)))
    this.2 this.1

noncomputable def PVM_of_word_of_channel_C
    {R : Type*} [RCLike R]
    {α : Type*} {r k : ℕ} (acc : Fin k.succ)
(𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R)
(h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM_C (R := R) := by
have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
    (ρ := ⟨pureState_C (e 0),⟨pureState_psd_C _, basisState_trace_one_C⟩⟩) (hq := h𝓚)
exact @PVM_of_state_C R _ k.succ acc
    (@krausApplyWord α R _ _ _ word.1 k.succ r word.2 𝓚 (pureState_C (e 0)))
    this.2 this.1

def getPVM₃ {α : Type*} {r : ℕ}
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

def MOlanguageAcceptedBy_C {R : Type*} [RCLike R] {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    (𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (PVM_of_word_of_channel_C acc 𝓚 (h𝓚) word).p
    (by simp only [PVM_of_word_of_channel_C, PVM_of_state_C]; exact 1) > 1/2}


/-- If the start and accept states are the same then
the empty string is accepted in the measure-once setting. -/
lemma MO_language_nonempty {α : Type*} {r k : ℕ}
    (𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) :
  MOlanguageAcceptedBy 0 𝓚
    h𝓚 ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty'.mp ?_
  refine nonempty_subtype.mpr ?_
  use ⟨0,![]⟩
  unfold MOlanguageAcceptedBy PVM_of_word_of_channel
  unfold PVM_of_state PMF_of_state
  simp only [Nat.succ_eq_add_one, Fin.isValue, Lean.Elab.WF.paramLet, id_eq, PMF.ofFintype_apply,
    one_ne_zero, ↓reduceIte, one_div, gt_iff_lt, Set.mem_setOf_eq]
  unfold krausApplyWord
  have : pureState (e (0 : Fin k.succ)) * pureState (e 0) (R := ℝ) = pureState (e 0) := by
    suffices IsStarProjection (pureState (e (0 : Fin k.succ))) by exact this.1
    exact pureState_projection 0
  simp only [gt_iff_lt]
  simp_rw [this]
  simp_rw [basisState_trace_one]
  simp

/-- For the Grudka channel with start state 0,
the probability of accepting the empty word is 1 > 1/2
hence ![] is in the corresponding measure-once language.
This can be generalized to any quantum channel.
-/
lemma MO_grudka0_language_nonempty :
  MOlanguageAcceptedBy 0 (grudka_R (θ := 0))
    (fun a ↦ grudka_quantumChannel 0 a) ≠ ∅ := by
  apply MO_language_nonempty


/-- Measure-Once language accepted by 𝓚 is
{word | Probability that we are in state e₃, and not in the span of e₁,e₂, > 1/2}.
`q = 2` because we haven't generalized myPVM₂₃ yet
-/
def MOlanguageAcceptedBy₃ {α : Type*} {r : ℕ}
    (𝓚 : α → Fin r → Matrix (Fin 3) (Fin 3) ℝ)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
    @MOlanguageAcceptedBy α r 2 1 𝓚 h𝓚



def MOlanguageAcceptedBy' {α : Type*} {r : ℕ}
    (𝓚 : α → quantum_channel 3 r (R := ℝ)) : Set ((n : ℕ) × (Fin n → α)) :=
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


lemma grudka₀_basic_operation : krausApply (grudka_R₀ 0 (R := ℝ))
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

lemma grudka_basic_operation : krausApply (grudka_R 0 0)
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
    unfold grudka_R
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

lemma grudka_basic_operation₂ : krausApply (grudka_R₀ 0 (R := ℝ))
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

/- If now the 2nd basis state is the accept state, we should still be able
to accept something... -/
lemma MO_grudka1_language_nonempty :
  MOlanguageAcceptedBy 1 (grudka_R (θ := 0))
    (fun a ↦ grudka_quantumChannel 0 a) ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty'.mp <| nonempty_subtype.mpr ?_
  use ⟨1,![0]⟩
  simp only [
    MOlanguageAcceptedBy, PVM_of_word_of_channel, PVM_of_state, PMF_of_state,
    Set.mem_setOf_eq, krausApplyWord, krausApply, cons_val_fin_one,
    conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two]
  have g₀: (
    grudka_R (0:ℝ) (0:Fin 2) (0:Fin 2) * pureState (single 0 0 1) * (grudka_R 0 0 0)ᵀ
    +
    grudka_R 0 0 1 * pureState (single 0 0 1) (R := ℝ) * (grudka_R 0 0 1)ᵀ
    ) =  pureState ![0, 1, 0] := by
    have h₅ := @grudka_basic_operation
    unfold e₁ e₂ krausApply at h₅
    rw [← h₅, Fin.sum_univ_two]
    congr
    all_goals exact ext_iff_trace_mul_left.mpr (congrFun rfl)
  have g₁: (single (1:Fin 3) (0:Fin 1) (1:ℝ)) = ![0,1,0] := by
    ext i j; fin_cases i <;> (fin_cases j; simp)
  have g₂ : pureState ![(0 : Fin 1 → ℝ), 1, 0] (R := ℝ) * pureState ![0, 1, 0]
   = pureState ![0, 1, 0] := (pureState_projection 1).1
  have g₃ : (pureState ![0, 1, 0] (R := ℝ)).trace = 1 := g₁ ▸ @basisState_trace_one 2 (1 : Fin 3)
  simp_rw [e, g₀, g₁, g₂, g₃]
  simp

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
