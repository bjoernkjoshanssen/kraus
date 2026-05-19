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


/-
A "fun" "game": Unitary exercises
-/
example (z : ℂ) : star z * z = 1 ↔ !![z] ∈ unitary _ := by
  constructor
  · intro hz
    have : star !![z] * !![z] = 1 := by
      ext i j
      fin_cases i; fin_cases j
      convert hz
      simp [mul_apply]
    constructor
    · exact this
    · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp this
  · intro h
    convert congrFun (congrFun h.1 0) 0
    simp [mul_apply]

example (a b c d : ℂ) :
  star a * a + star c * c = 1 ∧
  star b * b + star d * d = 1 ∧
  star a * b + star c * d = 0 ↔
  !![a,b;c,d] ∈ unitary _ := by
  constructor
  intro ⟨hac,hbd,h⟩
  have :  star !![a, b; c, d] * !![a, b; c, d] = 1 := by
    ext i j
    rw [mul_apply]
    fin_cases i
    · fin_cases j
      · convert hac
        simp
      · convert h
        simp
    fin_cases j
    · apply star_injective
      simp only [Fin.mk_one, Fin.isValue, star_apply, of_apply, cons_val', cons_val_one,
        cons_val_fin_one, RCLike.star_def, Fin.zero_eta, cons_val_zero, Fin.sum_univ_two, star_add,
        star_mul', RingHomCompTriple.comp_apply, RingHom.id_apply, ne_eq, one_ne_zero,
        not_false_eq_true, one_apply_ne, star_zero]
      rw [← h]
      simp only [RCLike.star_def]
      ring_nf
    · convert hbd
      simp
  constructor
  · exact this
  · exact (mul_eq_one_comm_of_card_eq (Fin 2) (Fin 2) ℂ rfl).mp this
  · intro ⟨h₀,h₁⟩

    have := congrFun (congrFun h₀ 0) 0
    simp [mul_apply] at this
    constructor
    · exact this
    · constructor
      · have := congrFun (congrFun h₀ 1) 1
        simp [mul_apply] at this
        exact this
      · have := congrFun (congrFun h₀ 0) 1
        simp [mul_apply] at this
        exact this
