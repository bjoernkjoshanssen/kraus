import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Kraus.Basic
import Kraus.Real
/-!

# Dimension 3

e₁ etc.
-/

open Matrix MatrixOrder ComplexOrder



noncomputable section

-- Move e₁ to DimensionThree.lean
def e₁ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![1, 0, 0]
def e₂ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![0, 1, 0]
def e₃ {R : Type*} [One R] [Zero R] : Matrix (Fin 3) (Fin 1) R := ![0, 0, 1]


example : pureState e₁ = !![1,0,0;0,0,0;0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureState, e₁, pureState, mulᵣ]


/-- The positive operator `pureState e₁` is chosen
with probability `(pureState e₁ * ρ).trace`. -/
lemma pureState_probability_one {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
    (pureState e₁ * ρ).trace +
    (pureState e₂ * ρ).trace +
    (pureState e₃ * ρ).trace = 1 := by
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
