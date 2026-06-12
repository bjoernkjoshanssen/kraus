import Mathlib.Data.Matrix.PEquiv
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Quantum harmonic oscillator tutorial
-/

noncomputable section

/-- Annihilation operator. -/
def a (x : ℕ → ℂ) : ℕ → ℂ := fun n => √(n + 1) * x (n + 1)

def aLin : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := {
  toFun := a
  map_add' := by
    sorry
  map_smul' := by
    sorry
}

/-- Creation operator. -/
def a_dag (x : ℕ → ℂ) : ℕ → ℂ := fun n => ite (n = 0) 0 (√n * x (n - 1))

def a_dagLin : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := {
  toFun := a_dag
  map_add' := by
    sorry
  map_smul' := by
    sorry
}

def ε (n : ℕ) (c : ℂ) : ℕ → ℂ := fun i => ite (i = n) c 0

/-- Verify that a_dag really is the transpose of a. -/
lemma a_dag_eq (i j : ℕ) : a_dag (ε i 1) j = star (a (ε j 1) i) := by
    sorry

/-- Verify that a |n + 1⟩ = √(n + 1) |n ⟩ -/
lemma verify_a (n : ℕ) :
    a (ε (n + 1) 1) =
       ε n (√(n + 1))  := by
  sorry

/-- Verify that a† ∣n⟩ = √(n+1) ∣n+1⟩. -/
lemma verify_a_dag (n : ℕ) :
    a_dag (ε n 1) = ε (n + 1) (√(n + 1))  := by
  sorry

lemma verify_a_dag_a (n : ℕ) (x : ℕ → ℂ) :
    a_dag (a x) n = n * x n  := by
  sorry

lemma verify_a_a_dag (n : ℕ) (x : ℕ → ℂ) :
    a (a_dag x) n = (n + 1) * x n  := by
  sorry

lemma commutation_relation :
    a ∘ a_dag - a_dag ∘ a = id := by
  sorry

def coherentState (α : ℂ) : ℕ → ℂ :=
    fun n : ℕ => Real.exp (-‖α‖^2 / 2) * α ^ n / √(n.factorial)

def probabilityOf (n : ℕ) (α : ℂ) : NNReal :=
    ⟨‖coherentState α n‖^2, by simp⟩

/-- Coherent state has a Poisson distribution. -/
lemma probabilityOf_eq_poisson_C (n : ℕ) (α : ℂ) :
    let Λ := ⟨‖α‖ ^ 2, sq_nonneg ‖α‖⟩
    probabilityOf n α =
    ProbabilityTheory.poissonMeasure Λ {n} := by
  sorry


/-- June 11, 2026. The only eigenvectors of `a` are the coherent states. -/
lemma coherentState_only_eigenvector (α : ℂ) (v : ℕ → ℂ) :
  a v = α • v ↔
  v = (Complex.exp (↑‖α‖ ^ 2 / 2) * v 0) • coherentState α := by
    sorry

lemma eigenvector_coherentState (α : ℂ) :
    a (coherentState α) = α • coherentState α := by
  sorry

/-- None of the `coherentState` eigenvectors are proportional. -/
lemma distinct_eigenvectors_a (α β c : ℂ)
 (hc : coherentState α = c • coherentState β) : α = β := by
  sorry

/-- Formal eigenvectors for `a_dag` (not in `ℓ²(ℂ)`)
(fails at n=0) . -/
lemma a_dagalmost_eigenvector {α : ℂ} (hα : α ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    a_dag (fun n => √(n.factorial) / α^n) n =
      α • (fun n => √(n.factorial) / α^n) n := by
  sorry

lemma a_dag_nullspace
    {v : ℕ → ℂ} (hv : a_dag v = 0) : v = 0 := by
  sorry

lemma no_a_dag_eigenvector {α : ℂ}
    {v : ℕ → ℂ} : a_dag v = α • v ↔ v = 0 := by
  sorry

lemma commutationRelation : ⁅aLin, a_dagLin⁆ = 1 := by
    sorry
