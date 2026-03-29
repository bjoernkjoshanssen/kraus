import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Kraus.Basic
import Kraus.Stinespring

/-!
# Stinespring dilation
-/

open Matrix RCLike



/-- A version of the Stinespring Dilation Theorem. -/
theorem stinespringForm_eq {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R)
    (ρ : Matrix (Fin m) (Fin m) R) :
    partialTraceRight (stinespringDilation K ρ) = krausApply K ρ := by
  unfold krausApply
  ext u v
  repeat rw [Finset.sum_apply]
  simp only [partialTraceRight, stinespringDilation, stinespringOp, Fin.isValue]
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
open Matrix MatrixOrder ComplexOrder RCLike

open TensorProduct



theorem heisenberg_schrõdinger_picture {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
  -- let K' := fun i x y => star <| K i y x
  -- let U := stinespringOp K'
  -- let V := stinespringOp K
  -- Uᴴ * (ρ ⊗ₖ 1) * U = partialTraceRight (V * ρ * Vᴴ)
    0 = 0 := by

    have h₀ := @tracefree_version ℂ _ (Fin m) (Fin r.succ) _ _ _ _ _ K ρ
    have h₁ := @stinespringForm_eq _ _ m r.succ K ρ
    have := h₀.trans h₁
    simp at this

    sorry



lemma partialTraceRight_one_of_unital {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (hu : unital K) :
    partialTraceRight ((stinespringOp K) * (stinespringOp K)ᴴ) = 1 := by
      have := @stinespringForm_eq _ _ m r K 1
      simp only [stinespringDilation, krausApply, Matrix.mul_one] at this
      rw [this]
      convert hu


  -- PROOF THAT WORKS IN 4.29.0-rc6 TOO:
  -- ext u v
  -- simp only [partialTraceRight, stinespringDilation, V, kronecker, Fin.isValue, krausApply]
  -- have :  (∑ i, K i * ρ * (K i)ᴴ) u v =  ∑ i, (K i * ρ * (K i)ᴴ) u v := by
  --   exact sum_apply u v Finset.univ fun c ↦ K c * ρ * (K c)ᴴ
  -- rw [this]
  -- congr
  -- ext w
  -- simp only [kroneckerMap, single, Fin.isValue, of_apply,
  --   mul_ite, mul_one, mul_zero]
  -- repeat rw [Matrix.mul_apply]
  -- congr
  -- ext j
  -- repeat rw [Matrix.mul_apply]
  -- simp only [Fin.isValue, conjTranspose_apply, star_def]
  -- rw [Matrix.sum_apply]
  -- have (x : Fin r) :
  --     (fun i j ↦ if x = i.2 ∧ 0 = j.2 then
  --      K x i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ)
  --   = (fun i j ↦ if x = i.2 then K i.2 i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ) := by
  --       ext i j
  --       split_ifs with g₀ g₁ g₂
  --       · rw [g₁]
  --       · tauto
  --       · omega
  --       rfl
  -- simp_rw [this]
  -- simp only [Fin.isValue, of_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
  --   mul_eq_mul_right_iff, map_eq_zero]
  -- left
  -- congr
  -- ext a
  -- congr
  -- rw [of]
  -- suffices (of (∑ x, fun i (j : Fin m × Fin 1) ↦ if x = i.2 then K i.2 i.1 j.1 else 0))
  --   (u, w) (a, 0) =
  --     K w u a by
  --   rw [← this]
  --   let G (x : Fin r) := (fun (i : Fin m × Fin r) (j : Fin m × Fin 1) ↦
  --       if x = i.2 then K i.2 i.1 j.1 else 0 : Fin m × Fin r → Fin m × Fin 1 → ℂ)
  --   change (∑ x, of G x) (u, w) (a, 0) = Matrix.of (∑ x : Fin r, G x) (u, w) (a, 0)
  --   simp
  -- simp
