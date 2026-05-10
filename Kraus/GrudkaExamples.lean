import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Kraus.Basic
import Kraus.Real
import Kraus.DimensionThree
/-!

# Kraus operator automata and projection-valued measures: examples from Grudka et al.


References:

 * `Quantum Synchronizing Words: Resetting and Preparing Qutrit States`,
   Grudka et al., 2025

-/

open Matrix MatrixOrder ComplexOrder

noncomputable section

/-- The example Kraus operators from QCNC 2026. -/
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

open Real in
example (θ : ℝ) {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
    (krausApply (grudka_R θ 1) ρ).trace = 1 := by
  -- follows from it being a quantum channel, and ...
  rw [krausApply, trace]
  unfold grudka_R
  simp only [diag, sum_apply, mul_apply, conjTranspose_apply]
  simp [Fin.sum_univ_succ]
  rw [trace] at hρ
  simp [Fin.sum_univ_succ] at hρ
  ring_nf
  rw [cos_sq' θ]
  linarith


/-- Grudka et al. map does indeed map density matrices to density matrices. -/
noncomputable def grudka_map (θ : ℝ) {n : ℕ} (word : Fin n → Fin 2) :
  densityMatrix (Fin 3) (R := ℝ) → densityMatrix (Fin 3) (R := ℝ) :=
  krausApplyWord_map word _ fun i ↦ grudka_quantumChannel θ i


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
example (θ : ℝ) : (pureState e₂ * (grudka_R θ 1 0)).trace = cos θ := by
  unfold e₂ grudka_R pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example (θ : ℝ) : (pureState e₃ * (grudka_R θ 1 0)).trace = 1 := by
  unfold e₃ grudka_R pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]



instance : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedRing

instance :  NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedAlgebra




open ENNReal



open RCLike




lemma grudka_helper : mulᵣ ![(1: Fin 1 → ℝ), 0, 0] ![1, 0, 0]ᵀ =
      !![1,0,0;0,0,0;0,0,0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Fin.isValue, mulᵣ_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one]
        all_goals
          rw [← mulᵣ_eq]
          unfold mulᵣ
          simp


/-- For the Grudka channel with start state 0,
the probability of accepting the empty word is 1 > 1/2
hence ![] is in the corresponding measure-once language.
This can be generalized to any quantum channel.
-/
lemma MO_grudka0_language_nonempty :
  MOlanguageAcceptedBy 0
    (fun a ↦ grudka_quantumChannel 0 a) ≠ ∅ := by
  apply MO_language_nonempty



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
  MOlanguageAcceptedBy 1
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
