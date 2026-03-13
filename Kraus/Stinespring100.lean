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
  simp only [partialTraceRight, stinespringDilation, V, kronecker, Fin.isValue]
  have :  (∑ i, K i * ρ * (K i)ᴴ) u v =  ∑ i, (K i * ρ * (K i)ᴴ) u v := by
    exact sum_apply u v Finset.univ fun c ↦ K c * ρ * (K c)ᴴ
  rw [this]
  congr
  ext w
  simp only [kroneckerMap, single, Fin.isValue, of_apply,
    mul_ite, mul_one, mul_zero]
  repeat rw [Matrix.mul_apply]
  congr
  ext j
  repeat rw [Matrix.mul_apply]
  simp only [Fin.isValue, conjTranspose_apply, star_def]
  rw [Matrix.sum_apply]
  have (x : Fin r) :
      (fun i j ↦ if x = i.2 ∧ 0 = j.2 then K x i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ)
    = (fun i j ↦ if x = i.2 then K i.2 i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ) := by
        ext i j
        split_ifs with g₀ g₁ g₂
        · rw [g₁]
        · tauto
        · omega
        rfl
  simp_rw [this]
  simp only [Fin.isValue, of_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    mul_eq_mul_right_iff, map_eq_zero]
  left
  congr
  ext a
  congr
  rw [of]
  suffices (of (∑ x, fun i (j : Fin m × Fin 1) ↦ if x = i.2 then K i.2 i.1 j.1 else 0))
    (u, w) (a, 0) =
      K w u a by
    rw [← this]
    let G (x : Fin r) := (fun (i : Fin m × Fin r) (j : Fin m × Fin 1) ↦
        if x = i.2 then K i.2 i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ)
    change (∑ x, of G x) (u, w) (a, 0) = Matrix.of (∑ x : Fin r, G x) (u, w) (a, 0)
    simp
  simp
