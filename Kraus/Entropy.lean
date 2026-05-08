import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Kraus.Basic

/-!

# Trace distance and von Neumann entropy

To prove more results here we should probably work with the characteristic polynomial
of a density matrix.

-/

open Matrix MatrixOrder ComplexOrder


noncomputable section

/-- The trace distance between two density matrices. -/
def traceDistance {R : Type*} [RCLike R]
    {q : ℕ} (ρ σ : densityMatrix (Fin q) (R := R)) : ℝ :=
  (1 / 2) * ∑ i : Fin q, |(ρ.2.1.1.sub σ.2.1.1).eigenvalues i|

/-- The von Neumann entropy of a density matrix. -/
def vonNeumannEntropy {R : Type*} [RCLike R]
    {q : ℕ} (ρ : densityMatrix (Fin q) (R := R)) : ℝ :=
  let Λ := (ρ.2.1.1).eigenvalues; - ∑ i, Λ i * Real.log (Λ i)

/-- A 1x1 density matrix has 1 as its single entry. -/
lemma densityMatrix_one {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (ρ : densityMatrix (Fin 1) (R := R)) : ρ.1 = !![1] := by
  have h₁ : ρ.1 = !![ρ.1 0 0] := by
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp
  have h₀ := ρ.2.2
  rw [h₁, trace_fin_one_of] at h₀
  rw [h₁, h₀]

/-- The trace distance satisfies the axiom d(x,x)=0 of a metric.
-/
lemma traceDistance_zero {R : Type*} [RCLike R]
    {q : ℕ} (ρ : densityMatrix (Fin q) (R := R)) :
    traceDistance ρ ρ = 0 := by
  change _ * ∑ i ∈ _, |(ρ.2.1.1.sub ρ.2.1.1).eigenvalues _| = _
  simp_rw [IsHermitian.eigenvalues_eq]
  simp
