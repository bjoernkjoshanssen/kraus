import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Stinespring dilation
-/

open Matrix RCLike

noncomputable def partialTraceRight {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ k : Fin n, ρ (i, k) (j, k)

noncomputable def V {R : Type*} [Ring R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) : Matrix (Fin m × Fin r) (Fin m) R :=
  let V₀ : Matrix ((Fin m) × (Fin r)) ((Fin m) × (Fin 1)) R :=
    ∑ i, Matrix.kronecker (K i) (single i 0 1)
  fun x y => V₀ x (y,0)

noncomputable def stinespringDilation {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :=
  (V K) * ρ * (V K)ᴴ

/-- A version of the Stinespring Dilation Theorem. -/
lemma stinespringForm_eq {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    partialTraceRight (stinespringDilation K ρ) = ∑ i, K i * ρ * (K i)ᴴ := by
  ext u v
  repeat rw [Finset.sum_apply]
  simp only [partialTraceRight, stinespringDilation, V, kronecker, Fin.isValue]
  congr
  ext w
  simp only [kroneckerMap, single, Fin.isValue, of_apply,
    mul_ite, mul_one, mul_zero]
  repeat rw [Matrix.mul_apply]
  congr
  ext j
  repeat rw [Matrix.mul_apply]
  simp only [Fin.isValue, conjTranspose_apply, star_def]
  repeat rw [Finset.sum_apply]
  simp
