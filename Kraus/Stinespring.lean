import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions


import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace


import Kraus.Basic
/-!

# Stinespring dilation

-/

open Matrix MatrixOrder



/-- Feb 2, 2026 The "not orthogonal" CPTP completion of a CPTNI map. -/
lemma CPTP_of_CPTNI {R : Type*} [RCLike R]
  {q r : ℕ} (hr : r = 1)
  {K : Fin r → Matrix (Fin q) (Fin q) R}
  (hq : quantumOperation K) :
  ∃ K' : Fin (r+1) → Matrix (Fin q) (Fin q) R,
  quantumChannel K' ∧
  ∀ i, ∀ H : i ≠ Fin.last r, K' i = K ⟨i.1, Fin.val_lt_last H⟩ := by
  use (by
    intro i
    by_cases H : i = Fin.last r
    · exact CFC.sqrt (1 - ∑ j, (K j)ᴴ * K j)
    · exact K ⟨i.1, Fin.val_lt_last H⟩)
  unfold quantumChannel
  subst hr
  constructor
  · simp only [Nat.reduceAdd, Fin.reduceLast, Fin.isValue, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, mul_dite, Fin.sum_univ_two, zero_ne_one, ↓reduceDIte,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta]
    have h₂ (U : Matrix (Fin q) (Fin q) R)
    (hU : U ≥ 0) :
      (CFC.sqrt U) * CFC.sqrt U = U := by
      apply @CFC.sqrt_mul_sqrt_self
      simp
      tauto
    have h₀ (U : Matrix (Fin q) (Fin q) R)
    (hU : U ≥ 0) :
      (CFC.sqrt U)ᴴ = CFC.sqrt U := by
      have : CFC.sqrt U ≥ 0 := by exact CFC.sqrt_nonneg U
      refine IsHermitian.eq ?_
      have := this.1
      simp at this
      tauto
    have h₁ : (1 - (K 0)ᴴ * K 0) ≥ 0 := by
      unfold quantumOperation at hq
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton] at hq
      exact nonneg_iff_posSemidef.mpr hq
    rw [h₀ _ h₁]
    rw [h₂ _ h₁]
    simp
  · intro i H
    simp only [Nat.reduceAdd, Fin.reduceLast, ne_eq, Fin.isValue, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton] at H ⊢
    rw [dif_neg H]


noncomputable def partialTraceRight {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ k : Fin n, ρ (i, k) (j, k)

noncomputable def partialTraceLeft {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
fun i j => ∑ k : Fin m, ρ (k, i) (k, j)


lemma trace_partialTraceRight {m n : ℕ}
  (ρ : Matrix ((Fin m) × (Fin n))
              ((Fin m) × (Fin n)) ℂ) :
    trace ρ = trace (partialTraceRight ρ) := by
  unfold partialTraceRight trace
  exact Fintype.sum_prod_type fun x ↦ ρ x x

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


noncomputable def V {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m × Fin r) (Fin m) ℂ := by
  let V₀ : Matrix ((Fin m) × (Fin r)) ((Fin m) × (Fin 1)) ℂ :=
    Finset.sum (s := Finset.univ) fun i =>
    Matrix.kronecker (K i) <| single i 0 1
  let V : Matrix (Fin m × Fin r) (Fin m) ℂ := fun x y => V₀ x (y,0)
  exact V

/-- The "orthogonal" CPTP completion of a CPTNI map. -/
noncomputable def Vtilde {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) :
  Matrix (Fin m × Fin (r+1)) (Fin m) ℂ := fun x => dite (x.2 < r)
  (fun H => V K ⟨x.1, ⟨x.2, H⟩⟩)
   fun _ => (CFC.sqrt (1 - (V K)ᴴ * (V K)) : Matrix _ _ _) x.1


/-- Vtilde is an isometry when `m=0` -/
lemma Vtilde_Iᵣ₀ {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hm : m = 0) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  subst hm
  ext a
  exact False.elim <| not_lt_zero a.2

open RCLike

/-- Vtilde is an isometry when `r=0` -/
lemma Vtilde_I₀ₘ {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hr : r = 0) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  unfold Vtilde
  subst hr
  have : (fun (x : Fin m × Fin 1) => ((1 : Matrix _ _ _) x.1 : Fin m → ℂ)) =
          fun x                   => if H : x.2.1 < 0 then V K (x.1, ⟨x.2.1, H⟩) else
                                     ((CFC.sqrt (1 - (V K)ᴴ * (V K)) : Matrix _ _ _) x.1) := by
    unfold V
    simp only [Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Finset.univ_eq_empty,
      kronecker, Fin.isValue, Finset.sum_empty, zero_apply]
    have : (fun x y ↦ 0 : Fin m × Fin 0 → Fin m → ℂ) = 0 := by rfl
    rw [this]
    simp
  rw [← this]
  ext a b
  · rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      conjTranspose_apply, star_def, Finset.sum_singleton]
    have h₁ (x : Fin m) : (1 : Matrix (Fin m) (Fin m) ℂ) x a = 0 ∨
    (1 : Matrix (Fin m) (Fin m) ℂ) x a = 1 := by
        by_cases H : x = a
        · subst H
          simp
        · left
          exact one_apply_ne' fun a_1 ↦ H (id (Eq.symm a_1))
    have := @conjTranspose_one (α := ℂ) (n := Fin m)
    nth_rw 1 [← this]
    simp only [conjTranspose_apply, star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [← Matrix.mul_apply]
    rw [Matrix.one_mul 1]

-- lemma feb5
-- {K L : Matrix (Fin 1) (Fin 1) ℂ}

--  : K ≤ L → K 0 0 ≤ L 0 0 := by

--  sorry

-- lemma feb (L : Matrix (Fin 1) (Fin 1) ℂ) :
--     L.PosSemidef ↔ 0 ≤ L 0 0 := by
--     unfold PosSemidef
--     sorry

-- lemma feb5'
-- {L : Matrix (Fin 1) (Fin 1) ℂ}
-- (hadhoc : Lᴴ * L ≤ 1)
--  : (1 - !![(starRingEnd ℂ) (L 0 0) * L 0 0]).PosSemidef := by
--  sorry

-- lemma feb5''
-- {A : Matrix (Fin 1) (Fin 1) ℂ}
-- (hA : A.PosSemidef) : (starRingEnd ℂ) (CFC.sqrt A 0 0) = CFC.sqrt A 0 0 := by
--     sorry

lemma Vtilde_I''
  (K : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ)
  (h : (K 0)ᴴ * K 0 ≤ 1) : star (K 0 0 0) * (K 0 0 0) ≤ 1 := by
    sorry

lemma Vtilde_I
  (K : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ)
  (h₀ : (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]).PosSemidef)
  (h₁ : (starRingEnd ℂ) (CFC.sqrt (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]) 0 0) =
                         CFC.sqrt (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]) 0 0)
  :
  (Vtilde K)ᴴ * Vtilde K = 1 := by

  unfold Vtilde V
  ext a b
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  rw [Fin.fin_one_eq_zero a]
  rw [Fin.fin_one_eq_zero b]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd, Nat.lt_one_iff,
    Fin.val_eq_zero_iff, kronecker, Finset.sum_singleton, kroneckerMap_apply, conjTranspose_apply,
    star_def, Fin.sum_univ_two, ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
    single_apply_same, mul_one, one_ne_zero, one_apply_eq]
  generalize K 0 = L at *
  have (x y : Fin 1) : L x y = L 0 0 := by
    have : x = 0 := by exact Fin.fin_one_eq_zero x
    subst this
    have : y = 0 := by exact Fin.fin_one_eq_zero _
    subst this
    rfl
  simp_rw [this]
--   generalize L 0 0 = l at *
  have (l : ℂ) : (fun (x : Fin 1 × Fin 1) (y : Fin 1) ↦ (l * single (0:Fin 1) (0:Fin 1) (1:ℂ) x.2
    (0:Fin 1) : ℂ))
       = (fun x y ↦                             (l * single 0 0 1 0 0 : ℂ)) := by
        ext x y
        unfold single
        simp only [Fin.isValue, of_apply, and_true, mul_ite, mul_one, mul_zero, and_self,
          ↓reduceIte, ite_eq_left_iff]
        intro h
        exfalso
        apply h
        exact Eq.symm (Fin.fin_one_eq_zero x.2)
  have (l : ℂ): (fun (x : Fin 1 × Fin 1) (y : Fin 1) ↦ (l * single (0:Fin 1) (0:Fin 1) (1:ℂ) x.2
    (0:Fin 1) : ℂ))
       = (fun x y ↦                             (l  : ℂ)) := by
        ext x y
        unfold single
        simp only [Fin.isValue, of_apply, and_true, mul_ite, mul_one, mul_zero, ite_eq_left_iff]
        intro h
        exfalso
        apply h
        exact Eq.symm (Fin.fin_one_eq_zero x.2)
  simp_rw [this]
  have (l : ℂ) : (@HMul.hMul (Matrix (Fin 1) (Fin 1 × Fin 1) ℂ) (Matrix (Fin 1 × Fin 1) (Fin 1) ℂ)
    (Matrix (Fin 1) (Fin 1) ℂ)
  instHMulOfFintypeOfMulOfAddCommMonoid (fun x y ↦ l)ᴴ fun x y ↦ l : Matrix (Fin 1) (Fin 1) ℂ)
     = !![(starRingEnd ℂ) l * l] := by
        ext i j
        rw [Fin.fin_one_eq_zero i]
        rw [Fin.fin_one_eq_zero j]
        rw [Matrix.mul_apply]
        simp
  rw [this]
  have (a b : ℂ) : a + b = 1 ↔ b = 1 - a := by
    exact Iff.symm eq_sub_iff_add_eq'
  rw [this]
  rw [h₁]

  have (A : (Matrix (Fin 1) (Fin 1) ℂ)) (hA : A.PosSemidef) :
    (CFC.sqrt A) * (CFC.sqrt A) = A  := PosSemidef.sqrt_mul_self hA

  have (A : (Matrix (Fin 1) (Fin 1) ℂ)) ( i j : Fin 1)
    (hA : A.PosSemidef) :
    (CFC.sqrt A i j) * (CFC.sqrt A i j)
     = A i j := by
        rw [Fin.fin_one_eq_zero i]
        rw [Fin.fin_one_eq_zero j]
        nth_rw 3 [← this (A := A)]
        · rw [Matrix.mul_apply]
          simp
        · tauto
  rw [this (hA := h₀)]
  simp

theorem Complex.sqrt_nonneg (α : ℂ) (h : 0 ≤ α) : 0 ≤ α.sqrt := by
  unfold Complex.sqrt;
  rw [ Complex.le_def ] at *;
  norm_num [ Complex.cpow_def ] at *;
  split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
  norm_num [ Complex.arg ];
  norm_num [ h.1, h.2.symm ];
  positivity


open scoped ComplexOrder

/-
Defining Complex.sqrt as z^(1/2).
-/
noncomputable def Complex.sqrt' (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

open scoped ComplexOrder MatrixOrder

lemma matrix_1x1_nonneg_iff (x : ℂ) : 0 ≤ !![x] ↔ 0 ≤ x := by
  constructor
  · rintro ⟨ y, hy ⟩;
    specialize hy {
      toFun := by intro _; exact 1
      support := by exact Finset.univ
      mem_support_toFun := by intro z; simp only [Finset.univ_unique, Fin.default_eq_zero,
        Fin.isValue, Finset.mem_singleton, ne_eq, one_ne_zero, not_false_eq_true, iff_true]; exact Fin.fin_one_eq_zero z
    }
    simp at hy
    convert hy using 1
    unfold Finsupp.sum
    norm_num [ Matrix.mulVec, dotProduct ];

  · intro hx
    have h_pos : ∀ v : Fin 1 → ℂ, 0 ≤ (star v 0 * x * v 0).re := by
      simp_all +decide [ Complex.le_def ];
      intro v; rw [ ← hx.2 ] ; ring_nf; nlinarith [ sq_nonneg ( ( v 0 |> Complex.re ) - ( v 0 |> Complex.im ) ), sq_nonneg ( ( v 0 |> Complex.re ) + ( v 0 |> Complex.im ) ) ] ;
    constructor <;> norm_num;
    · ext i j ; fin_cases i ; fin_cases j ; simp +decide [ Complex.ext_iff ];
      simp_all +decide [ Complex.le_def ];
      linarith;
    · intro v; specialize h_pos v; simp_all +decide;
      simp_all +decide [ Complex.le_def ];
      rw [← hx.2]
      unfold Finsupp.sum Finsupp.support
      have h₀ : v.1 = ∅ ∨ v.1 = Finset.univ := by
        by_cases H : 0 ∈ v.1
        · right
          simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue]
          ext i
          have : i = 0 := by exact Fin.fin_one_eq_zero i
          subst this
          simp
          unfold Finsupp.support at H
          simp at H
          exact H
        · left
          ext i
          have : i = 0 := by exact Fin.fin_one_eq_zero i
          subst this
          simp only [Finset.notMem_empty]
          tauto
      constructor
      · simp
        cases h₀ with
        | inl h =>
          simp_rw [h]
          simp
        | inr h =>
          simp_rw [h]
          simp
          linarith
      · simp
        cases h₀ with
        | inl h =>
          simp_rw [h]
          simp
        | inr h =>
          simp_rw [h]
          simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
          rw [← hx.2]
          simp
          linarith

open scoped ComplexOrder

lemma complex_sq_sqrt {x : ℂ} : (Complex.sqrt x) ^ 2 = x := by
  -- Since the square root function is defined as the principal square root, we can apply the
  -- property (x^(1/2))^2 = x directly.
  have h_sqrt_sq : (x ^ (2⁻¹ : ℂ)) ^ 2 = x := by
    rw [ ← Complex.cpow_nat_mul ] ; norm_num;
  exact h_sqrt_sq

open scoped ComplexOrder

lemma complex_sqrt_nonneg {x : ℂ} (hx : 0 ≤ x) : 0 ≤ Complex.sqrt x := by
  -- Let $x = a + bi$ with $a, b \in \mathbb{R}$.
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℝ, x = a + b * Complex.I := by
    exact ⟨ x.re, x.im, by simp ⟩;
  simp_all +decide [ Complex.le_def ];
  cases le_total a 0 <;> simp +decide [ *, Complex.sqrt ];
  · norm_num [ show a = 0 by linarith, show b = 0 by linarith ];
  · norm_num [ ← hx.2, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ];
    split_ifs <;> simp +decide [ *, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
    norm_num [ ← hx.2, Complex.arg_ofReal_of_nonneg hx.1 ];
    positivity

open scoped ComplexOrder MatrixOrder

lemma matrix_1x1_sqrt (α : ℂ) (h₀ : 0 ≤ α) : CFC.sqrt !![α] = !![Complex.sqrt α] := by
  have := @CFC.sqrt_eq_iff ( Matrix ( Fin 1 ) ( Fin 1 ) ℂ ) _ _ _ _;
  convert this _ _ ?_ ?_ using 1;
  convert Iff.rfl;
  rotate_left;
  · exact !![α];
  · exact !![ Complex.sqrt α ];
  · exact (matrix_1x1_nonneg_iff α).mpr h₀;
  · convert matrix_1x1_nonneg_iff _ |>.2 ( complex_sqrt_nonneg h₀ ) using 1;
  · simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_one ];
    rw [ ← sq, complex_sq_sqrt ] ; norm_num

open scoped ComplexOrder MatrixOrder

theorem matrix_sqrt_eq_complex_sqrt (α : ℂ) (h₀ : 0 ≤ α) :
  CFC.sqrt !![α] 0 0 = Complex.sqrt α := by
    rw [ matrix_1x1_sqrt ]
    · aesop
    · assumption

/-- Feb 5, 2026
The Stinespring dilation as an isometry, in the case where 𝓚 is a single complex number.
-/
lemma Vtilde_I' (z : ℂ) (hz : star z * z ≤ 1) :
  let K : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => !![z]
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  unfold Vtilde V
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd, Nat.lt_one_iff,
    Fin.val_eq_zero_iff, kronecker, Finset.sum_singleton, kroneckerMap_apply, conjTranspose_apply,
    star_def, Fin.sum_univ_two, ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
    single_apply_same, mul_one, one_ne_zero, one_apply_eq]
  rw [Iff.symm eq_sub_iff_add_eq']
  have (A : (Matrix (Fin 1) (Fin 1) ℂ)) (hA : A.PosSemidef) :
    (CFC.sqrt A) * (CFC.sqrt A) = A  := PosSemidef.sqrt_mul_self hA
  simp only [of_apply, cons_val', cons_val_fin_one, Fin.isValue]
  have : (fun (x : Fin 1 × Fin 1) (y : Fin 1) => z * single (0:Fin 1) (0:Fin 1) 1 x.2 0)
        = fun  x                   y          => z := by
    ext x y
    rw [Fin.fin_one_eq_zero x.2]
    simp
  rw [this]
  have : (@HMul.hMul (Matrix (Fin 1) (Fin 1 × Fin 1) ℂ)
    (Matrix (Fin 1 × Fin 1) (Fin 1) ℂ) (Matrix (Fin 1) (Fin 1) ℂ)
  instHMulOfFintypeOfMulOfAddCommMonoid (fun x y ↦ z)ᴴ fun x y ↦ z : Matrix (Fin 1) (Fin 1) ℂ)
    = !![star z * z] := by
    ext i j
    have : i = 0 := by exact Fin.fin_one_eq_zero i
    rw [this]
    have : j = 0 := by exact Fin.fin_one_eq_zero j
    rw [this]
    rw [Matrix.mul_apply]
    simp
  rw [this]
  simp only [star_def, Fin.isValue]
  have : 1 - !![(starRingEnd ℂ) z * z]
    = !![1 -    (starRingEnd ℂ) z * z] := by
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp
  rw [this]
  have : (CFC.sqrt !![1 - (starRingEnd ℂ) z * z] 0 0)
                   = (1 - (starRingEnd ℂ) z * z).sqrt := by
        have h₀ : 1 - (starRingEnd ℂ) z * z ≥ 0 := sub_nonneg_of_le hz
        generalize 1 - (starRingEnd ℂ) z * z = α at *
        simp_all only [star_def, Fin.isValue, ge_iff_le]
        apply matrix_sqrt_eq_complex_sqrt _ h₀
  rw [this]
  have : (starRingEnd ℂ) ((starRingEnd ℂ) z * z)
                        = (starRingEnd ℂ) z * z := by
        simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
        exact CommMonoid.mul_comm z ((starRingEnd ℂ) z)
  have he (z : ℂ) : star z = (starRingEnd ℂ) z := Complex.ext rfl rfl
  have g₀ : (starRingEnd ℂ) (1 - (starRingEnd ℂ) z * z) =
    (1 - (starRingEnd ℂ) z * z) := by
    rw [← he]
    rw [star_sub]
    simp only [star_one, star_mul', star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
      _root_.sub_right_inj]
    exact CommMonoid.mul_comm z ((starRingEnd ℂ) z)
  have : (starRingEnd ℂ) (1 - (starRingEnd ℂ) z * z).sqrt =
    (1 - (starRingEnd ℂ) z * z).sqrt := by
    have g₁ : (1 - (starRingEnd ℂ) z * z) ≥ 0 := by
        simp only [ge_iff_le, sub_nonneg]
        convert hz
    generalize (1 - (starRingEnd ℂ) z * z) = α at *
    refine Complex.conj_eq_iff_im.mpr ?_
    have g₂ : α.sqrt ≥ 0 := Complex.sqrt_nonneg _ g₁
    rw [← g₂.2]
    simp
  rw [this]
  have (a b c : ℂ) (h : a ≠ 0) : a ^b * a^c = a^(b+c) := by
    refine Eq.symm (Complex.cpow_add b c ?_)
    exact h
  by_cases H : 1 - (starRingEnd ℂ) z * z = 0
  · rw [H]
    simp
  have (w : ℂ) (hw : w ≠ 0) : w.sqrt * w.sqrt = w := by
    unfold Complex.sqrt
    rw [this]
    · have : ((2⁻¹ : ℂ) + 2⁻¹) = 1 := by norm_num
      rw [this]
      simp
    · exact hw
  rw [this]
  exact H

noncomputable def stinespringDilation {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (ρ : Matrix (Fin m) (Fin m) ℂ) :  Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ := by
  exact (V K) * ρ * (V K)ᴴ

noncomputable def stinespringForm {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (ρ : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := by
  let V₀ : Matrix ((Fin m) × (Fin r)) ((Fin m) × (Fin 1)) ℂ :=
    Finset.sum (s := Finset.univ) fun i =>
    Matrix.kronecker (K i) <| single i 0 1
  let V : Matrix (Fin m × Fin r) (Fin m) ℂ := fun x y => V₀ x (y,0)
  exact partialTraceRight (stinespringDilation K ρ)

lemma stinespringForm_CPTP {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) (hr : r = 1)
  :
  (V K)ᴴ * (V K) ≤ 1 := by
  subst hr
  convert hK
  unfold V
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, kronecker, Finset.sum_singleton,
    kroneckerMap_apply]
  unfold single
  simp only [Fin.isValue, of_apply, and_true, mul_ite, mul_one, mul_zero]
  ext i j
  rw [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  simp only [Fin.isValue, conjTranspose_apply, star_def, mul_ite, mul_zero]
  rw [Finset.sum_finset_product (r := Finset.univ) (s := Finset.univ)
    (t := fun _ => Finset.univ)
    ]
  · simp
  · simp


/-- stinespringForm works
when there are *no operators* -/
lemma stinespringForm_eq₀ {m r : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ)
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hr : r = 0) :
  stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  subst hr
  simp only [Finset.univ_eq_empty, Finset.sum_empty, stinespringForm]
  ext a b
  simp [partialTraceRight]

/-- stinespringForm works for *0x0 matrices* -/
lemma stinespringForm_eqm₀ {m r : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ)
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hm : m = 0) :
  stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  subst hm
  ext a b
  have := a.2
  simp at this

/-- stinespringForm works for *1x1 matrices and 2 operators* -/
lemma stinespringForm_eqm₁ {m r : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ)
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hm : m = 1) (hr : r = 2) :
  stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  unfold stinespringForm stinespringDilation V
  simp only [kronecker, Fin.isValue]
  unfold partialTraceRight kroneckerMap single
  simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
  have h₀ (f : Fin m → Fin m → Fin r → ℂ) :
    (fun (i j : Fin m) => ∑ k : Fin r, f i j k) =
    ∑ k : Fin r, (fun (i j : Fin m) => f i j k) := by
    symm
    ext u v
    simp only [Finset.sum_apply]
  rw [h₀]
  congr
  ext i a b
  repeat rw [← mulᵣ_eq]
  unfold Matrix.mulᵣ
  simp only [Fin.isValue, dotProductᵣ_eq, FinVec.map_eq, of_apply, Function.comp_apply]
  unfold dotProduct
  subst hm
  simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, of_apply,
    Function.comp_apply, transpose_apply, conjTranspose_apply, star_def]
  · subst hr
    rw [Matrix.mul_apply]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.sum_univ_two, add_apply,
      of_apply, conjTranspose_apply, star_add, star_def, Finset.sum_singleton]
    rw [Matrix.mul_apply]
    fin_cases i <;> simp

/-- stinespringForm works for *1 operator* -/
lemma stinespringForm_eq₁ {m : ℕ} (K : Fin 1 → Matrix (Fin m) (Fin m) ℂ)
  (ρ : Matrix (Fin m) (Fin m) ℂ) :
  stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  have h₀ (f : Fin m → Fin m → Fin 1 → ℂ) :
    (fun (i j : Fin m) => ∑ k : Fin 1, f i j k) =
    ∑ k : Fin 1, (fun (i j : Fin m) => f i j k) := by
    symm
    ext u v
    simp
  unfold stinespringForm partialTraceRight stinespringDilation V
  rw [h₀]
  congr
  ext u v w
  simp only [kronecker, kroneckerMap, single, Fin.isValue, of_apply,
    mul_ite, mul_one, mul_zero]
  have : ∑ x : Fin 1, of (fun (i : Fin m × Fin 1) (j : Fin m × Fin 1)
      ↦ if x = i.2 ∧ 0 = j.2 then K x i.1 j.1 else (0:ℂ))
    = ∑ x : Fin 1, of (fun (i : Fin m × Fin 1) (j : Fin m × Fin 1)
      ↦ if x = i.2 then K x i.1 j.1 else (0:ℂ)) := by
      congr
      ext x i j
      simp only [Fin.isValue, of_apply]
      split_ifs with g₀ g₁ g₂
      · rfl
      · tauto
      · exfalso
        have := j.2.2
        push_neg at g₀
        specialize g₀ g₂
        apply g₀
        clear g₀
        omega
      rfl
  rw [this]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    of_apply]
  have : u = 0 := by exact Fin.fin_one_eq_zero u
  subst this
  rfl

lemma stinespringForm_eq₂ {m r : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ)
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hr : r = 1) :
  stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  have h₀ (f : Fin m → Fin m → Fin r → ℂ) :
    (fun (i j : Fin m) => ∑ k : Fin r, f i j k) =
    ∑ k : Fin r, (fun (i j : Fin m) => f i j k) := by
    symm
    ext u v
    simp
  unfold stinespringForm partialTraceRight stinespringDilation V
  rw [h₀]
  congr
  ext u v w
  simp only [kronecker, kroneckerMap, single, Fin.isValue, of_apply,
    mul_ite, mul_one, mul_zero]
  have : ∑ x : Fin r, of (fun (i : Fin m × Fin r) (j : Fin m × Fin 1)
      ↦ if x = i.2 ∧ 0 = j.2 then K x i.1 j.1 else (0:ℂ))
    = ∑ x : Fin r, of (fun (i : Fin m × Fin r) (j : Fin m × Fin 1)
      ↦ if x = i.2 then K x i.1 j.1 else (0:ℂ)) := by
      congr
      ext x i j
      simp only [Fin.isValue, of_apply]
      split_ifs with g₀ g₁ g₂
      · rfl
      · tauto
      · exfalso
        have := j.2.2
        push_neg at g₀
        specialize g₀ g₂
        apply g₀
        clear g₀
        omega
      rfl
  rw [this]
  subst hr
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    of_apply]
  have : u = 0 := by exact Fin.fin_one_eq_zero u
  subst this
  -- have (x : (Fin m) × (Fin 1)) (y : Fin m) :
  --   (if 0 = x.2 then K 0 x.1 y else 0)
  --   = K 0 x.1 y := by
  --     simp only [Fin.isValue, ite_eq_left_iff];intro h;exfalso;have := x.2.2;omega
  rfl
