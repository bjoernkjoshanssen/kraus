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

open Matrix MatrixOrder ComplexOrder RCLike

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

noncomputable def stinespringForm {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ) :=
  fun ρ => partialTraceRight (stinespringDilation K ρ)

/-- A version of the Stinespring Dilation Theorem. -/
lemma stinespringForm_eq {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    stinespringForm K ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  ext u v
  repeat rw [Finset.sum_apply]
  simp only [stinespringForm, partialTraceRight, stinespringDilation, V, kronecker, Fin.isValue]
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

#min_imports
lemma stinespringForm_CPTNI_reason {m : ℕ} (K : Fin 1 → Matrix (Fin m) (Fin m) ℂ) :
    (V K)ᴴ * V K = ∑ i, (K i)ᴴ * K i := by
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

lemma stinespringForm_CPTNI {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) (hr : r = 1) :
  (V K)ᴴ * (V K) ≤ 1 := by
  subst hr
  convert hK
  apply stinespringForm_CPTNI_reason


/-- The "orthogonal" CPTP completion of a CPTNI map. -/
noncomputable def Vtilde {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) :
  Matrix (Fin m × Fin (r+1)) (Fin m) R := fun x => dite (x.2 < r)
  (fun H => V K ⟨x.1, ⟨x.2, H⟩⟩)
   fun _ => (CFC.sqrt (1 - (V K)ᴴ * (V K)) : Matrix _ _ _) x.1

/-- Mar 14, 2026 -/
lemma Vtilde_isometry_of_TNI {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
       (h_tni : ∑ i, star K i * K i ≤ 1) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  have (i j : Fin m) :  ((Vtilde K)ᴴ * Vtilde K) i j =
    ∑ k,  (Vtilde K)ᴴ i k  * Vtilde K k j := by
      exact mul_apply
  have :  ((Vtilde K)ᴴ * Vtilde K) = fun (i j : Fin m) =>
        ∑ k,  (Vtilde K)ᴴ i k  * Vtilde K k j := by
      ext i j
      apply mul_apply
  rw [this]
  simp_rw [Finset.sum_finset_product (r := Finset.univ) (s := Finset.univ)
    (t := fun _ => Finset.univ) (by simp)]
  simp_rw [Fin.sum_univ_castSucc] -- !!
  clear this
  clear this
  unfold Vtilde
  simp
  suffices (V K)ᴴ * V K + (1 - (V K)ᴴ * V K) = 1 by
    simp_rw [Finset.sum_add_distrib]
    have h₀ (f g : Fin m → Fin m → ℂ) : (fun i j => f i j + g i j)
      = (fun i j => f i j) + (fun i j => g i j) := by
        exact
        Eq.symm (Pi.add_def (fun i j ↦ f i j) fun i j ↦ g i j)
    rw [h₀]
    convert this
    · expose_names
      unfold conjTranspose
      simp
      unfold Matrix.map
      simp
      repeat rw [mul_apply]
      simp
      simp_rw [Finset.sum_finset_product (r := Finset.univ) (s := Finset.univ)
      (t := fun _ => Finset.univ) (by simp)]

    · expose_names
      have : 1 - (V K)ᴴ * V K ≥ 0 := by
        unfold V
        simp only
        simp only [conjTranspose, Matrix.map, transpose, kronecker, kroneckerMap, single,
          Fin.isValue, of_apply, mul_ite, mul_one, mul_zero, star_def, ge_iff_le]
        have (j : Fin m × Fin 1) : (0 = j.2) = True := by have := j.2.2;simp at this ⊢;omega
        simp_rw [this]
        simp only [and_true, Fin.isValue, ge_iff_le]
        have : (@Finset.sum (Fin r) (Matrix (Fin m × Fin r) (Fin m × Fin 1) ℂ)
            addCommMonoid Finset.univ fun x ↦
              of fun i j ↦ if x = i.2 then K x i.1 j.1 else 0 : Matrix (Fin m × Fin r) (Fin m × Fin 1) ℂ)
              =  fun i j ↦ K i.2 i.1 j.1 := by
          ext i j
          have {m : ℕ} (f : Fin m → Fin m → ℂ) : ∑ x : Fin m, (fun (i : Fin m) => f i x)
           = fun (i : Fin m) => ∑ x : Fin m, f i x := by
            exact Finset.sum_fn Finset.univ fun c i ↦ f i c
          have {m : ℕ} (f : Fin m → Fin m → Fin m → ℂ) : ∑ x : Fin m, (fun (i j : Fin m) => f i j x)
           = fun (i j : Fin m) => ∑ x : Fin m, f i j x := by
            repeat rw [Finset.sum_fn]
            ext i j
            simp
          have {m : ℕ} (f : Fin m → Fin m → Fin m → ℂ) : ∑ x : Fin m, Matrix.of (fun (i j : Fin m) => f i j x)
           = fun (i j : Fin m) => ∑ x : Fin m, f i j x := by
            repeat rw [Finset.sum_fn]
            ext i j
            simp
          have fact {t₀ t₁ t₂ : Type} [Fintype t₀] [Fintype t₁]
            [Fintype t₂]
            (f : t₀ → t₁ → t₂ → ℂ) : ∑ x : t₂, Matrix.of (fun (i : t₀) (j : t₁) => f i j x)
           = fun (i : t₀) (j : t₁) => ∑ x, f i j x := by
            repeat rw [Finset.sum_fn]
            ext i j
            simp
          rw [@fact ((Fin m) × (Fin r))]
          simp
        rw [this]
        simp only [ge_iff_le]
        simp
        convert h_tni
        ext i j
        rw [mul_apply]
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp
        rw [sum_apply]
        congr
      generalize 1 - (V K)ᴴ * V K = α at *
      -- have := @Matrix.transpose_inj
      have (x_2 : Fin m) :
        (starRingEnd ℂ) ((CFC.sqrt α) x_2 x)
        =
        (star (CFC.sqrt α)) x x_2
        := by simp
      simp_rw [this]
      have :  ∑ x_2, star (CFC.sqrt α) x x_2 * CFC.sqrt α x_2 x_1
        = ((star (CFC.sqrt α)) * CFC.sqrt α) x x_1 := by
          rw [mul_apply]
      rw [this]
      repeat apply congrFun
      clear this
      clear this
      have : star α = α := LE.le.star_eq this
      have : IsSelfAdjoint α := by exact isHermitian_iff_isSelfAdjoint.mp this
      have : IsSelfAdjoint (CFC.sqrt α) := by
        refine isHermitian_iff_isSelfAdjoint.mp ?_
        refine PosSemidef.isHermitian ?_
        exact PosSemidef.posSemidef_sqrt
      have : star (CFC.sqrt α) = CFC.sqrt α := by
        exact Matrix.ext fun i ↦ congrFun (congrFun this i)
      rw [this]
      (expose_names; refine CFC.sqrt_mul_sqrt_self α this_2)
  simp

def unital {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) := ∑ i, K i * star (K i) = 1



-- For 1x1 matrices, unitality implies TNI and hence isometry.
lemma Vtilde_I₂ₘNEWPROOF {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
    (hm : m = 1) (h_unital : unital K) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  apply Vtilde_isometry_of_TNI
  unfold unital at h_unital
  subst hm
  have h₀ (u : Fin r) : star (K u) * K u = K u * star (K u) := by
    ext i j
    rw [Fin.fin_one_eq_zero i]
    rw [Fin.fin_one_eq_zero j]
    repeat rw [mul_apply]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, star_apply,
      Finset.sum_singleton]
    rw [mul_comm]
  simp at h_unital ⊢
  simp_rw [← h₀] at h_unital
  rw [h_unital]


/-- Vtilde is an isometry when `r=0` -/
lemma Vtilde_I₀ₘ {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hr : r = 0) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  apply Vtilde_isometry_of_TNI
  subst hr
  simp

/-- Vtilde is an isometry when `m=0` -/
lemma Vtilde_Iᵣ₀ {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) ℂ) (hm : m = 0) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  apply Vtilde_isometry_of_TNI
  subst hm
  simp



theorem Complex.sqrt_nonneg (α : ℂ) (h : 0 ≤ α) : 0 ≤ α.sqrt := by
  unfold Complex.sqrt;
  rw [ Complex.le_def ] at *;
  norm_num [ Complex.cpow_def ] at *;
  split_ifs
  · simp
  · simp only [one_div, exp_re, mul_re, log_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
    log_im, inv_im, im_ofNat, neg_zero, zero_div, mul_zero, sub_zero, mul_im, zero_add, exp_im,
    zero_eq_mul, Real.exp_ne_zero, false_or];
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
      mem_support_toFun := by
        intro z; simp only [Finset.univ_unique, Fin.default_eq_zero,
          Fin.isValue, Finset.mem_singleton, ne_eq, one_ne_zero, not_false_eq_true, iff_true];
        exact Fin.fin_one_eq_zero z
    }
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, star_def, sub_apply, of_apply,
      cons_val', cons_val_fin_one, zero_apply, sub_zero] at hy
    convert hy using 1
    unfold Finsupp.sum
    norm_num [ Matrix.mulVec, dotProduct ];
  · intro hx
    have h_pos : ∀ v : Fin 1 → ℂ, 0 ≤ (star v 0 * x * v 0).re := by
      simp_all only [Complex.le_def, Complex.zero_re, Complex.zero_im, Fin.isValue, Pi.star_apply,
        star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
        Complex.mul_im];
      intro v; rw [ ← hx.2 ] ;
      ring_nf;
      nlinarith [ sq_nonneg ( ( v 0 |> Complex.re ) - ( v 0 |> Complex.im ) ),
        sq_nonneg ( ( v 0 |> Complex.re ) + ( v 0 |> Complex.im ) ) ] ;
    constructor <;> norm_num;
    · ext i j ; fin_cases i ; fin_cases j ; simp +decide [ Complex.ext_iff ];
      simp_all +decide [ Complex.le_def ];
      linarith;
    · intro v; specialize h_pos v; simp_all +decide only [Fin.isValue, Pi.star_apply, star_def,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.mul_im,
      sub_nonneg];
      simp_all +decide only [Complex.le_def, Complex.zero_re, Complex.zero_im, Fin.isValue];
      rw [← hx.2]
      unfold Finsupp.sum Finsupp.support
      have h₀ : v.1 = ∅ ∨ v.1 = Finset.univ := by
        by_cases H : 0 ∈ v.1
        · right
          simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue]
          ext i
          have : i = 0 := by exact Fin.fin_one_eq_zero i
          subst this
          simp only [Fin.isValue, Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton, iff_true]
          unfold Finsupp.support at H
          simp only [Fin.isValue, Finsupp.mem_support_iff, ne_eq] at H
          exact H
        · left
          ext i
          have : i = 0 := by exact Fin.fin_one_eq_zero i
          subst this
          simp only [Finset.notMem_empty]
          tauto
      constructor
      · simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
        sub_neg_eq_add, Complex.mul_im, Finset.sum_sub_distrib, sub_nonneg]
        cases h₀ with
        | inl h =>
          simp_rw [h]
          simp
        | inr h =>
          simp_rw [h]
          simp
          linarith
      · simp only [Complex.im_sum, Complex.mul_im, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, neg_mul, sub_neg_eq_add]
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
  simp_all only [Complex.le_def, Complex.zero_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.zero_im, Complex.add_im, Complex.mul_im, zero_add];
  cases le_total a 0 <;> simp +decide only [Complex.sqrt];
  · norm_num [ show a = 0 by linarith, show b = 0 by linarith ];
  · norm_num [← hx.2, Complex.exp_re, Complex.exp_im,
      Complex.log_re, Complex.log_im, Complex.cpow_def]
    split_ifs
    · simp
    simp +decide only [one_div, Complex.exp_re, Complex.mul_re, Complex.log_re, Complex.norm_real,
      Real.norm_eq_abs, Real.log_abs, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.log_im, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div,
      mul_zero, sub_zero, Complex.mul_im, zero_add, Complex.exp_im, zero_eq_mul, Real.exp_ne_zero,
      false_or];
    norm_num [ ← hx.2, Complex.arg_ofReal_of_nonneg hx.1 ];
    positivity

open scoped ComplexOrder MatrixOrder

lemma matrix_1x1_sqrt (α : ℂ) (h₀ : 0 ≤ α) : CFC.sqrt !![α] = !![Complex.sqrt α] := by
  have := @CFC.sqrt_eq_iff ( Matrix ( Fin 1 ) ( Fin 1 ) ℂ ) _ _ _ _;
  convert this _ _ ?_ ?_ using 1;
  rotate_left;
  · exact !![α];
  · exact !![ Complex.sqrt α ];
  · exact (matrix_1x1_nonneg_iff α).mpr h₀;
  · convert matrix_1x1_nonneg_iff _ |>.2 ( complex_sqrt_nonneg h₀ ) using 1;
  · simp only [← Matrix.ext_iff, of_apply, cons_val', cons_val_fin_one, Fin.forall_fin_one,
    Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
    smul_eq_mul, smul_empty, tail_cons, empty_vecMul, add_zero, empty_mul, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true];
    rw [ ← sq, complex_sq_sqrt ] ; norm_num


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
  -- apply Vtilde_isometry_of_TNI should work...
  unfold Vtilde V
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd, Nat.lt_one_iff,
    Fin.val_eq_zero_iff, kronecker, Finset.sum_singleton, kroneckerMap_apply, conjTranspose_apply,
    star_def, Fin.sum_univ_two, ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
    single_apply_same, mul_one, one_ne_zero, one_apply_eq]
  rw [Iff.symm eq_sub_iff_add_eq']
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
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, Matrix.mul_apply]
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



lemma Vtilde_I
  (K : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ)
  (h₀ : (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]).PosSemidef)
  (h₁ : (starRingEnd ℂ) (CFC.sqrt (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]) 0 0) =
                         CFC.sqrt (1 - !![(starRingEnd ℂ) (K 0 0 0) * K 0 0 0]) 0 0) :
  (Vtilde K)ᴴ * Vtilde K = 1 := by
  have := @Vtilde_I' (K 0 0 0) (by
    generalize K 0 0 0 = κ at *
    have : 1 - !![(starRingEnd ℂ) κ * κ] ≥ 0 := by sorry
    have : 1 - !![star κ * κ] ≥ 0 := this
    have : !![star κ * κ] ≤ 1 := by sorry
    generalize star κ * κ = μ at *

    have := matrix_1x1_nonneg_iff -- maybe generalize that
    sorry)
  simp only [Nat.reduceAdd, Fin.isValue] at this

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
    (CFC.sqrt A) * (CFC.sqrt A) = A  := by
    have : A ≥ 0 := by exact nonneg_iff_posSemidef.mpr hA
    exact CFC.sqrt_mul_sqrt_self A this -- PosSemidef.sqrt_mul_self hA
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
    trace ρ = trace (partialTraceRight ρ) := by
  unfold partialTraceRight trace
  exact Fintype.sum_prod_type fun x ↦ ρ x x

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

noncomputable def partialTraceLeft {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
fun i j => ∑ k : Fin m, ρ (k, i) (k, j)
