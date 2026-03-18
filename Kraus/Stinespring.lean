import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace
import Kraus.Basic

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Stinespring dilation

-/

open Matrix MatrixOrder ComplexOrder RCLike

noncomputable def partialTraceRight {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ k : Fin n, ρ (i, k) (j, k)

/-- `stinespringOp` is often written as `V`. -/
noncomputable def stinespringOp {R : Type*} [Ring R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) : Matrix (Fin m × Fin r) (Fin m) R :=
  let V₀ : Matrix (Fin m × Fin r) (Fin m × Fin 1) R :=
    ∑ i, Matrix.kronecker (K i) (single i 0 1)
  fun x y => V₀ x (y,0)

noncomputable def stinespringDilation {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :=
  (stinespringOp K) * ρ * (stinespringOp K)ᴴ

noncomputable def stinespringForm {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ) :=
  fun ρ => partialTraceRight (stinespringDilation K ρ)





/-- The "orthogonal" CPTP completion of a CPTNI map.
`Vtilde` is an alternative name for `krausCompletion`.
-/
noncomputable def krausCompletion {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) :
  Matrix (Fin m × Fin (r+1)) (Fin m) R := fun x => dite (x.2 < r)
  (fun H => stinespringOp K ⟨x.1, ⟨x.2, H⟩⟩)
   fun _ => (CFC.sqrt (1 - (stinespringOp K)ᴴ * (stinespringOp K)) : Matrix _ _ _) x.1

lemma stinespringOp_adjoint_mul_self {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) :
    ∑ i, star K i * K i = (stinespringOp K)ᴴ * stinespringOp K := by
  ext i j
  simp only [stinespringOp]
  repeat rw [Finset.sum_fn]
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [single, Finset.sum_apply, kronecker, kroneckerMap_apply, of_apply,
    and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  congr

lemma stinespringForm_CPTNI_reason {m r : ℕ} (K : Fin r → Matrix (Fin m) (Fin m) ℂ) :
    (stinespringOp K)ᴴ * stinespringOp K = ∑ i, (K i)ᴴ * K i := by
  rw [← stinespringOp_adjoint_mul_self]
  congr

lemma stinespringForm_CPTNI {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) ≤ 1 := by
  convert hK
  apply stinespringForm_CPTNI_reason

lemma stinespringForm_CPTP_isometry {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) = 1 := by
  rw [← hK]
  have := @stinespringOp_adjoint_mul_self ℂ _ m r K
  rw [← this]
  congr

lemma hz (z : ℂ) : star z * z = ‖z‖^2 := by
  rw [← Complex.ofReal_pow]
  rw [norm_sq_eq_def]
  have : z = z.re + z.im * Complex.I := by exact Eq.symm (Complex.re_add_im z)
  nth_rw 1 [this]
  nth_rw 3 [this]
  have : star (↑z.re + ↑z.im * Complex.I)
    =  (↑z.re - ↑z.im * Complex.I) := by
      refine Eq.symm ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
      constructor <;> simp
  rw [this]
  ring_nf
  simp

/--
Mar 16, 2026

Proving the columns of `V = stinespringOp K` are independent is a step
on the way to constructing the unitary dilation. -/
lemma stinespringOrtho {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal (𝕜 := ℂ)
      fun j : Fin m => WithLp.toLp 2 fun i : Fin m × Fin r => stinespringOp K i j := by
    have h₀ := @stinespringForm_CPTP_isometry m r K hK
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    have h₁ : (((stinespringOp K)ᴴ * stinespringOp K) i j)
      = ((1 : Matrix (Fin m) (Fin m) ℂ) i j) := by
      rw [h₀]
    rw [mul_apply] at h₁
    split_ifs with g₀
    · subst i
      simp only [conjTranspose_apply, star_def, one_apply_eq] at h₁
      rw [← h₁]
      simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap]
      generalize stinespringOp K = α
      set β := (fun i => α i j)
      have hz := hz
      simp only [star_def] at hz
      simp_rw [hz]
      rw [← Complex.ofReal_pow]
      simp_rw [← Complex.ofReal_pow]
      rw [← Complex.ofReal_sum]
      congr
      exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 β)
    · have : (1 : Matrix (Fin m) (Fin m) ℂ) i j = 0 := by
        exact one_apply_ne' fun a ↦ g₀ (id (Eq.symm a))
      rw [this] at h₁
      rw [← h₁]
      -- same as before:
      generalize stinespringOp K = α
      set β := (fun x => α x i)
      set γ := (fun x => α x j)
      have hz := hz
      simp only [star_def] at hz
      change _ = ∑ x, ((star β) x) * γ x
      rw [PiLp.inner_apply] -- !!
      simp only [inner_apply, Pi.star_apply, star_def]
      congr
      ext x
      ring_nf

/-- `m` will of course be finite and bounded by `n` here,
but no need to assume or prove that.
-/
lemma basisCard {n m : Type*} [Fintype n] {s : Matrix n m ℂ}
    (hh : Orthonormal ℂ fun j ↦ WithLp.toLp 2 fun i ↦ s i j) :
    Fintype.card n =
    hh.toSubtypeRange.exists_orthonormalBasis_extension.choose.card := by
  set α := hh.toSubtypeRange.exists_orthonormalBasis_extension
  let h₀ := rank_eq_card_basis α.choose_spec.choose.toBasis
  have h := (rank_eq_card_basis <| PiLp.basisFun _ _ _).symm.trans h₀
  rw [← Fintype.card_coe]
  rw [Nat.cast_inj] at h
  exact h

lemma stinespringCard {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Fintype.card (Fin m × Fin r) =
    (stinespringOrtho
    hK).toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  basisCard <| stinespringOrtho hK

open Finset in
/-- Mar 16, 2026
Not very constructive but works.
Extend to a unitary (m×r) × (m×r) matrix.
-/
noncomputable def unitary_dilation {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ :=
  fun x => (stinespringOrtho
  hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose
  (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)

open Finset in
theorem unitary_dilation_orthonormal {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) : Orthonormal ℂ fun i ↦ WithLp.toLp 2 (unitary_dilation hK i) := by
    unfold unitary_dilation
    have hα : Orthonormal ℂ
      (stinespringOrtho hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose
      := (stinespringOrtho
  hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose.orthonormal
    let α := (stinespringOrtho
      hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose
    change Orthonormal ℂ α at hα
    let f (x : Fin m × Fin r) := ⇑α (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
    change Orthonormal ℂ f
    let u := (stinespringOrtho
  hK).toSubtypeRange.exists_orthonormalBasis_extension.choose
    -- let g : u → WithLp 2 (Fin m × Fin r → ℂ) := DFunLike.coe α
    -- have : ∀ v, g v = v := by
    --   intro v
    --   unfold g α
    --   simp
    --   have := α.repr.2
    --   have := α.repr.1
    --   let β := (stinespringOrtho
    --   hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose_spec.2
    --   simp at β
    --   rw [β]
    -- should maybe prove that `u` literally is Finset.univ
    have := @Orthonormal.comp (v := α) ℂ _ _ _ _
      (f := fun x => equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
    specialize this hα (by
      show Function.Injective fun x => (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
      have := (equivOfCardEq (stinespringCard hK)).3
      refine Function.HasLeftInverse.injective ?_
      unfold Function.HasLeftInverse
      use fun x => (equivOfCardEq (stinespringCard hK)).2 x
      intro
      simp)
    exact this

open Finset in
lemma unitary_dilation_unitary {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    unitary_dilation hK ∈ unitary _ := by
  have h₁ (a b : ℂ) (h : star a = star b) : a = b := by
    rw [Complex.ext_iff] at h
    simp only [star_def, Complex.conj_re, Complex.conj_im, neg_inj] at h
    exact Complex.ext_iff.mpr h
  have h₀ : Orthonormal ℂ (fun i => WithLp.toLp 2 <| unitary_dilation hK i) := by
    apply unitary_dilation_orthonormal
  have H₀ : unitary_dilation hK * star (unitary_dilation hK) = 1 := by
    ext i j
    unfold Orthonormal at h₀
    by_cases H : i = j
    · subst i
      have := h₀.1 j
      simp only at this
      generalize unitary_dilation hK = α at *
      rw [mul_apply]
      apply h₁
      simp only [star_apply, star_def, star_sum, star_mul', RingHomCompTriple.comp_apply,
        RingHom.id_apply, one_apply_eq, star_one]
      generalize α j = β at *
      refine Eq.symm ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
      constructor
      · simp only [Complex.one_re, Complex.re_sum, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, neg_mul, sub_neg_eq_add]
        have h₂ : (1 : ℝ) = 1^2 := by simp
        rw [h₂]
        rw [← this]
        have (x : Fin m × Fin r) :
            ((β x).re * (β x).re + ((β x).im * (β x).im)) =
                ‖β x‖^2
                 := by
            ring_nf
            generalize β x = γ
            symm
            refine Eq.symm ((fun {x y} hx hy ↦ (Real.sqrt_eq_iff_eq_sq hx hy).mp) ?_ ?_ ?_)
            · positivity
            · positivity
            · exact Eq.symm (Complex.norm_eq_sqrt_sq_add_sq γ)
        simp_rw [this]
        exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 β)
      · simp only [Complex.one_im, Complex.im_sum, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, neg_mul]
        have (x : Fin m × Fin r) :
            ((β x).re * (β x).im + -((β x).im * (β x).re)) = 0 := by
            ring_nf
        simp_rw [this]
        simp
    · have : (1 : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) i j = 0 := by
        apply one_apply_ne'
        contrapose! H
        rw [H]
      rw [this]
      have := h₀.2
      rw [mul_apply]
      apply h₁
      specialize this H
      convert this
      · simp only [star_apply, star_def, star_sum, star_mul', RingHomCompTriple.comp_apply,
        RingHom.id_apply, inner]
        congr
        ext l
        nth_rw 1 [mul_comm]
      simp
  constructor
  · generalize unitary_dilation hK = α at *
    exact (mul_eq_one_comm_of_card_eq (Fin m × Fin r) (Fin m × Fin r) ℂ rfl).mp H₀
  · exact H₀

/-- Mar 14, 2026 -/
lemma krausCompletion_isometry_of_TNI {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R)
    (h_tni : ∑ i, star K i * K i ≤ 1) :
    (krausCompletion K)ᴴ * krausCompletion K = 1 := by
  have : (krausCompletion K)ᴴ * krausCompletion K =
    fun i j => ∑ k, (krausCompletion K)ᴴ i k  * krausCompletion K k j := by
    ext i j
    apply mul_apply
  rw [this]
  simp_rw [Finset.sum_finset_product (r := Finset.univ) (s := Finset.univ)
    (t := fun _ => Finset.univ) (by simp)]
  simp_rw [Fin.sum_univ_castSucc] -- !!
  simp only [krausCompletion, conjTranspose_apply, Fin.val_castSucc, Fin.is_lt,
    ↓reduceDIte, Fin.eta, star_def, Fin.val_last, lt_self_iff_false]
  suffices (stinespringOp K)ᴴ * stinespringOp K + (1 - (stinespringOp K)ᴴ * stinespringOp K) = 1 by
    simp_rw [Finset.sum_add_distrib]
    have h₀ (f g : Fin m → Fin m → R) : (fun i j => f i j + g i j)
      = (fun i j => f i j) + (fun i j => g i j) :=
        (Pi.add_def (ι := Fin m) (M := fun _ => Fin m → R) f g).symm
    rw [h₀]
    convert this
    · unfold conjTranspose
      repeat rw [mul_apply]
      simp_rw [Finset.sum_finset_product (r := Finset.univ) (s := Finset.univ)
      (t := fun _ => Finset.univ) (by simp)]
      simp
    · expose_names
      have : 1 - (stinespringOp K)ᴴ * stinespringOp K ≥ 0 := by
        rw [← stinespringOp_adjoint_mul_self]
        simp only [Pi.star_apply, ge_iff_le, sub_nonneg]
        exact h_tni
      generalize 1 - (stinespringOp K)ᴴ * stinespringOp K = α at *
      have (x_2 : Fin m) : (starRingEnd R) ((CFC.sqrt α) x_2 x)
                                    = (star (CFC.sqrt α)) x x_2
        := by simp
      simp_rw [this]
      have :  ∑ x_2, star (CFC.sqrt α) x x_2 * CFC.sqrt α x_2 x_1
        = ((star (CFC.sqrt α)) * CFC.sqrt α) x x_1 := by
          rw [mul_apply]
      rw [this]
      repeat apply congrFun
      rw [LE.le.isSelfAdjoint <| CFC.sqrt_nonneg (a := α)]
      apply CFC.sqrt_mul_sqrt_self α
  simp

def unital {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) := ∑ i, K i * star (K i) = 1

def subunital {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) := ∑ i, K i * star (K i) ≤ 1


lemma Matrix.mul_comm_one (A B : Matrix (Fin 1) (Fin 1) ℂ) :
  A * B = B * A := by
    ext i j
    rw [Fin.fin_one_eq_zero i]
    rw [Fin.fin_one_eq_zero j]
    repeat rw [mul_apply]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton]
    rw [mul_comm]


-- For 1x1 matrices, unitality implies TNI and hence isometry.
lemma krausCompletion_I₂ₘNEWPROOF {r : ℕ}
  (K : Fin r → Matrix (Fin 1) (Fin 1) ℂ)
  (h_unital : subunital K) :
  (krausCompletion K)ᴴ * krausCompletion K = 1 := by
  apply krausCompletion_isometry_of_TNI
  unfold subunital at h_unital
  have h₀ (u : Fin r) : star (K u) * K u = K u * star (K u) := mul_comm_one _ _
  simp only [Pi.star_apply, ge_iff_le] at h_unital ⊢
  simp_rw [← h₀] at h_unital
  exact h_unital

/-- krausCompletion is an isometry when `r=0` -/
lemma krausCompletion_isometry_of_zero {m : ℕ}
  (K : Fin 0 → Matrix (Fin m) (Fin m) ℂ) :
  (krausCompletion K)ᴴ * krausCompletion K = 1 := by
  apply krausCompletion_isometry_of_TNI
  simp

/-- krausCompletion is an isometry when `m=0` -/
lemma krausCompletion_Iᵣ₀ {r : ℕ}
  (K : Fin r → Matrix (Fin 0) (Fin 0) ℂ) :
  (krausCompletion K)ᴴ * krausCompletion K = 1 := by
  apply krausCompletion_isometry_of_TNI
  simp



/-- Tr_B (A ⨂ B) = Tr(B) · A -/
lemma partialTrace_tensor {m n : ℕ}
  (A : Matrix (Fin m) (Fin m) ℂ)
  (B : Matrix (Fin n) (Fin n) ℂ) :
    partialTraceRight (Matrix.kronecker A B) =
    (trace B) • A  := by
    unfold partialTraceRight kronecker trace kroneckerMap
    simp only [of_apply, diag_apply]
    ext i j
    simp only [smul_apply, smul_eq_mul]
    have := @Finset.sum_mul (a := A i j) (ι := Fin n)
      (s := Finset.univ) (f := fun k => B k k) _ _
    rw [this]
    simp_rw [mul_comm]

lemma trace_partialTraceRight {m n : ℕ}
  (ρ : Matrix ((Fin m) × (Fin n))
              ((Fin m) × (Fin n)) ℂ) :
    trace ρ = trace (partialTraceRight ρ) := Fintype.sum_prod_type fun x ↦ ρ x x

/-- Feb 2, 2026 The "not orthogonal" CPTP completion of a CPTNI map. -/
lemma CPTP_of_CPTNI {R : Type*} [RCLike R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hq : quantumOperation K) :
    ∃ K' : Fin (r+1) → Matrix (Fin q) (Fin q) R,
    quantumChannel K' ∧
    ∀ i, ∀ H : i ≠ Fin.last r, K' i = K ⟨i.1, Fin.val_lt_last H⟩ := by
  use (fun i x => @krausCompletion R _ q r K (x, i))
  constructor
  · unfold quantumChannel
    unfold quantumOperation at hq
    have := @krausCompletion_isometry_of_TNI R _ q r K hq
    rw [← this]
    ext x y
    rw [mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [sum_apply]
    congr
  · unfold krausCompletion stinespringOp
    simp only [ne_eq, kronecker, Fin.isValue]
    intro i H
    split_ifs with g₀
    · unfold kroneckerMap single
      simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
      have (j : Fin q × Fin 1) : (0 = j.2) = True := by
        have := j.2.2
        simp
        omega
      simp_rw [this]
      rw [Finset.sum_fn]
      simp
    · exfalso
      apply H
      exact Fin.eq_last_of_not_lt g₀


noncomputable def partialTraceLeft {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
fun i j => ∑ k : Fin m, ρ (k, i) (k, j)
