import Kraus.Basic

/-!
# Stinespring dilation
-/

open Matrix MatrixOrder ComplexOrder RCLike

noncomputable def partialTraceRight {R : Type*} [Ring R] {m n m' : Type*} [Fintype n]
    (ρ : Matrix (m × n) (m' × n) R) : Matrix m m' R :=
  fun i j => ∑ k : n, ρ (i, k) (j, k)

/-- `stinespringOp` is often written as `V`. -/
noncomputable def stinespringOp {R : Type*} [Ring R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) : Matrix (Fin m × Fin r) (Fin m) R :=
  let V₀ : Matrix (Fin m × Fin r) (Fin m × Fin 1) R :=
    ∑ i, Matrix.kronecker (K i) (single i 0 1)
  fun x y => V₀ x (y,0)

noncomputable def stinespringDilation {R : Type*} [Ring R] [StarRing R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R)
    (ρ : Matrix (Fin m) (Fin m) R) :=
  let V := stinespringOp K; V * ρ * Vᴴ

noncomputable def stinespringForm {R : Type*} [Ring R] [StarRing R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) :=
  fun ρ => partialTraceRight (stinespringDilation K ρ)

lemma stinespringOp_adjoint_mul_self {R : Type*} [Ring R] [StarRing R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) :
    ∑ i, star K i * K i = (stinespringOp K)ᴴ * stinespringOp K := by
  ext i j
  simp only [stinespringOp]
  repeat rw [Finset.sum_fn]
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [single, Finset.sum_apply, kronecker, kroneckerMap_apply, of_apply,
    and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  congr

lemma stinespringForm_CPTNI {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) ≤ 1 := by
  convert hK
  rw [← stinespringOp_adjoint_mul_self]
  rfl

lemma stinespringForm_CPTP_isometry {R : Type*} [Ring R] [StarRing R] {m r : ℕ}
  {K : Fin r → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) = 1 := by
  rw [← hK]
  rw [← stinespringOp_adjoint_mul_self]
  rfl

lemma hz (z : ℂ) : star z * z = ‖z‖^2 := by
  rw [← Complex.ofReal_pow]
  rw [norm_sq_eq_def]
  nth_rw 1 [← Complex.re_add_im z]
  nth_rw 3 [← Complex.re_add_im z]
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
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    have h₁ : (((stinespringOp K)ᴴ * stinespringOp K) i j)
      = ((1 : Matrix (Fin m) (Fin m) ℂ) i j) := by
      rw [stinespringForm_CPTP_isometry hK]
    rw [mul_apply] at h₁
    by_cases g₀ : i = j
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
    · rw [if_neg g₀]
      have : (1 : Matrix (Fin m) (Fin m) ℂ) i j = 0 := by
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
    (ho : Orthonormal ℂ fun j ↦ WithLp.toLp 2 fun i ↦ s i j) :
    Fintype.card n =
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  Fintype.card_coe _ ▸ (Nat.cast_inj.mp  <|
    (rank_eq_card_basis <| PiLp.basisFun _ _ _).symm.trans <|
     rank_eq_card_basis
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose.toBasis)


lemma stinespringCard {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Fintype.card (Fin m × Fin r) =
    (stinespringOrtho
    hK).toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  basisCard <| stinespringOrtho hK



open Finset in
theorem complCard {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    let 𝓞 := fun j ↦ WithLp.toLp 2 fun i ↦ stinespringOp K i j;
    let theRange := Submodule.span ℂ (Set.range 𝓞);
    let u' := (exists_orthonormalBasis ℂ theRangeᗮ).choose;
      Fintype.card (Fin m × Fin r) = #u' := by
    intro 𝓞 theRange u'
    let u : Finset theRange :=
        (Set.range fun i => (⟨𝓞 i, Submodule.subset_span ⟨i, rfl⟩⟩)).toFinset
    have hind := (stinespringOrtho hK).linearIndependent
    have hinj := hind.injective
    have h₀ : #u = m := by
        simp only [u, Nat.succ_eq_add_one, Set.toFinset_range]
        have : m = #(Finset.univ : Finset (Fin m)) := by simp
        simp_rw [this]
        apply card_image_of_injective
        intro i j h
        apply hinj
        simp only [Nat.succ_eq_add_one, Subtype.mk.injEq, WithLp.toLp.injEq, 𝓞] at h ⊢
        exact h
    have h₁ : m * (r + 1) = #u + #u' := by
        have := Submodule.finrank_add_finrank_orthogonal theRange
        simp only [Nat.succ_eq_add_one, finrank_euclideanSpace, Fintype.card_prod,
          Fintype.card_fin] at this
        rw [← this]
        congr
        all_goals apply Module.finrank_eq_card_finset_basis
        · simp only [theRange, u, Set.toFinset_range, mem_image, mem_univ, true_and]
          apply (Module.Basis.span hind).reindex
          apply Equiv.ofBijective
            fun i => ⟨⟨𝓞 i, Submodule.mem_span_of_mem <| by simp [𝓞]⟩, by use i⟩
          constructor
          · intro i j h
            exact hinj (by aesop)
          · intro x
            have ⟨a,ha⟩ := x.2
            use a
            simp_rw [ha]
        · exact (exists_orthonormalBasis ℂ _).choose_spec.choose.toBasis
    simp
    linarith


noncomputable def onbPart {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r.succ) (hx : ¬x.2 = 0) :
  -- if we make it `r+2` then the `x.2≠0` becomes unused.
  Fin m × Fin r.succ → ℂ := by
    let theRange := Submodule.span ℂ <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    have (z : Fin m × Fin r) :=
        ((exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose
        (Finset.equivOfCardEq (complCard hK) ⟨z, Finset.mem_univ _⟩)).1.1
    apply this
    exact (x.1, ⟨x.2.1 - 1, by omega⟩)


lemma onbPart_inner {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {y : Fin m × Fin r.succ} (hy : ¬y.2 = 0)
    {z : Fin m × Fin r.succ} (hz : ¬z.2 = 0)
    (h : y ≠ z) :
    inner ℂ (WithLp.toLp 2 <| onbPart hK y hy)
            (WithLp.toLp 2 <| onbPart hK z hz) = 0 := by
    let theRange := Submodule.span ℂ <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    have := (exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose.orthonormal.2
    simp [Pairwise] at this
    have h₁ := this (WithLp.toLp 2 <| onbPart hK y hy)
        (by simp [onbPart]) (by
            simp [onbPart]
            rw [(exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose_spec]
            simp)
        (WithLp.toLp 2 <| onbPart hK z hz)
        (by simp [onbPart]) (by
            simp [onbPart]
            rw [(exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose_spec]
            simp) (by
                simp [onbPart]
                rw [(exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose_spec]
                simp
                intro hyz
                contrapose! h
                have : y.2.1 ≠ 0 := Fin.val_ne_zero_iff.mpr hy
                have : z.2.1 ≠ 0 := Fin.val_ne_zero_iff.mpr hz
                have : y.2.1 = z.2.1 := by omega
                have : y.2 = z.2 := by omega
                exact Prod.ext hyz this)
    simp at h₁
    rw [← h₁]
    simp_rw [(exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose_spec]

lemma onbPart_norm {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r.succ) (hx : ¬x.2 = 0) :
  ‖WithLp.toLp 2 <| onbPart hK x hx‖ = 1 := by
    let theRange := Submodule.span ℂ <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    let v := WithLp.toLp 2 <| (fun z =>
        ((exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose
        (Finset.equivOfCardEq (complCard hK) ⟨z, Finset.mem_univ _⟩)).1.1)
        (x.1, ⟨x.2.1 - 1, by omega⟩)
    have hv : ‖v‖ = 1 := by
        have := (exists_orthonormalBasis ℂ theRangeᗮ).choose_spec.choose.orthonormal.1
        apply this
    convert hv



/-- Respects x,y order. -/
noncomputable def unitaryDilation {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x y
  by_cases hy : y.2 = 0
  · exact stinespringOp K x y.1
  · exact onbPart hK y hy x

/-- A general, not necessarily unitary, dilation. -/
noncomputable def dilation {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x y
  by_cases hy : y.2 = 0
  · exact stinespringOp K x y.1
  · exact M x y -- or maybe x y


/-- One version of it. -/
theorem unitaryDilation_orthonormal₁ {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal ℂ fun y ↦
    if hy : y.2 = 0 then WithLp.toLp 2 fun i ↦ stinespringOp K i y.1
    else WithLp.toLp 2 fun i ↦ onbPart hK y hy i := by
    constructor
    · intro i
      simp only
      split_ifs with g₀
      · apply (stinespringOrtho hK).1
      · apply onbPart_norm
    · intro i j h
      simp only
      let theRange := Submodule.span ℂ <| Set.range
            fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
      split_ifs with g₀ g₁ g₂
      · apply (stinespringOrtho hK).2
        contrapose! h
        refine Prod.ext_iff.mpr ?_
        constructor
        · tauto
        · rw [g₀,g₁]
      · -- use that they came from `theRange`, `theRangeᗮ` respectively.
        have h₀ : (WithLp.toLp 2 fun i_1 ↦ stinespringOp K i_1 i.1) ∈ theRange := by
            unfold theRange
            generalize stinespringOp K = α
            apply Submodule.mem_span_of_mem
            simp
        have h₁ : (WithLp.toLp 2 fun i ↦ onbPart hK j g₁ i) ∈ theRangeᗮ := by
            unfold theRange
            simp [onbPart]
        exact h₁ _ h₀
      · have h₀' : (WithLp.toLp 2 fun i_1 ↦ stinespringOp K i_1 j.1) ∈ theRange := by
            unfold theRange
            generalize stinespringOp K = α
            apply Submodule.mem_span_of_mem
            simp
        have h₁ :  (WithLp.toLp 2 fun t ↦ onbPart hK i g₀ t) ∈ theRangeᗮ := by
            unfold theRange
            simp [onbPart]
        have := h₁ _ h₀'
        generalize (WithLp.toLp 2 fun i_1 ↦ onbPart hK i g₀ i_1) = α at *
        generalize (WithLp.toLp 2 fun i ↦ stinespringOp K i j.1) = β at *
        exact inner_eq_zero_symm.mp (h₁ β h₀')
      · exact onbPart_inner hK g₀ g₂ h
theorem unitaryDilation_orthonormal₂ {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Orthonormal ℂ fun y ↦
      WithLp.toLp 2 fun i ↦ if hy : y.2 = 0 then stinespringOp K i y.1 else onbPart hK y hy i := by
    have := unitaryDilation_orthonormal₁ hK
    simp at this ⊢
    constructor
    · intro i
      have := this.1 i
      rw [← this]
      congr
      ext y
      simp
      split_ifs with g₀ <;> simp
    · intro i j hij
      have := this.2 hij
      simp at this ⊢
      rw [← this]
      generalize stinespringOp K = α
      generalize onbPart hK = β
      split_ifs at * with g₀ g₁ <;> rfl


lemma Complex.norm_eq (γ : ℂ) : γ.re * γ.re + γ.im * γ.im = ‖γ‖ ^ 2 := by
    ring_nf
    symm
    refine Eq.symm ((fun {x y} hx hy ↦ (Real.sqrt_eq_iff_eq_sq hx hy).mp) ?_ ?_ ?_)
    · positivity
    · positivity
    · exact Eq.symm (Complex.norm_eq_sqrt_sq_add_sq γ)

lemma smul_self_one_of_norm_one {t : Type*} [Fintype t] {β : t → ℂ} (hj : ‖WithLp.toLp 2 β‖ = 1) :
  ∑ x, (starRingEnd ℂ) (β x) * β x = 1 := by
      refine Eq.symm ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
      constructor
      · simp only [Complex.one_re, Complex.re_sum, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, neg_mul, sub_neg_eq_add]
        rw [← one_pow 2]
        rw [← hj]
        simp_rw [Complex.norm_eq]
        exact EuclideanSpace.norm_sq_eq _
      · simp only [Complex.one_im, Complex.im_sum, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, neg_mul]
        symm
        apply Fintype.sum_eq_zero
        ring_nf
        simp

theorem unitary_of_orthonormal {m r : ℕ}
    (α : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ)
  (h₀ : Orthonormal ℂ fun i ↦ WithLp.toLp 2 (α i)) : α * star α = 1 := by
    ext i j
    rw [mul_apply]
    apply star_injective
    simp only [star_apply, star_def, star_sum, star_mul', RingHomCompTriple.comp_apply,
      RingHom.id_apply]
    by_cases H : i = j
    · subst i
      simp only [one_apply_eq, map_one]
      exact smul_self_one_of_norm_one <| h₀.1 _
    · rw [one_apply_ne' <| H ∘ Eq.symm, map_zero]
      convert h₀.2 H
      simp only [inner]
      congr
      ext l
      nth_rw 1 [mul_comm]


lemma unitaryDilation_unitaryT {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (unitaryDilation hK)ᵀ ∈ unitary _ := by
  have h₁ := unitaryDilation_orthonormal₂ hK
  have H₀ := unitary_of_orthonormal (unitaryDilation hK)ᵀ h₁
  simp [transpose] at H₀ ⊢
  constructor
  · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp H₀
  · exact H₀

/-- Well will you look at that... -/
lemma unitaryDilation_unitary {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (unitaryDilation hK) ∈ unitary _ := by
     have := unitaryDilation_unitaryT hK
     generalize unitaryDilation hK = U at *
     clear hK K
     have :  star U * U = 1 := by
       have := this.2
       have : (Uᵀ * star Uᵀ)ᵀ = 1ᵀ := by exact transpose_inj.mpr this
       simp at this
       have : (star Uᵀ)ᵀ = star U := by
         exact Eq.symm (Matrix.ext fun i ↦ congrFun rfl)
       rw [← this]
       tauto
     constructor
     · exact this
     · exact (mul_eq_one_comm_of_card_eq (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ rfl).mp this


open Kronecker

def Matrix.kronecker_map_right {m n : ℕ} {R : Type*} [RCLike R]
  (A : Matrix (Fin n) (Fin n) R) :
       Matrix (Fin m × Fin n) (Fin m × Fin n) R := 1 ⊗ₖ A

lemma general_kronecker_map_right_apply {m m' n n' o o' : Type*}
    [Fintype m'] [Fintype n'] {R : Type*} [RCLike R]
    (B : Matrix n n' R) (A : Matrix m m' R)
    (e₁ : Matrix m' o R) (e₂ : Matrix n' o' R) :
    (A ⊗ₖ B) * (e₁ ⊗ₖ e₂) = (A * e₁) ⊗ₖ (B * e₂) := by
  exact Eq.symm (mul_kronecker_mul A e₁ B e₂)

open TensorProduct

/-
The projector | e₀ > < e₀ |
-/
def e₀Xe₀ {w : ℕ} : Matrix (Fin w.succ) (Fin w.succ) ℂ :=
    fun x y => if (x,y) = (0,0) then 1 else 0

lemma partialTraceRight_e₀Xe₀ {w m : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ) :
    partialTraceRight (ρ ⊗ₖ (e₀Xe₀ : Matrix (Fin w.succ) (Fin w.succ) ℂ)) =
        ρ := by
        unfold partialTraceRight kroneckerMap e₀Xe₀
        simp


/-- The best version. -/
noncomputable def stinespringUnitaryForm {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) :=
    let U := unitaryDilation hK
    partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

noncomputable def stinespringGeneralForm {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) :=
    let U := dilation K M
    partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)


/-- When we plug in `M = unitaryDilation hK`
into the general `stinespringGeneralForm`,
then we do get
stinespringUnitaryForm hK
-/
theorem unitaryForm_of_general {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringGeneralForm K (unitaryDilation hK) =
    stinespringUnitaryForm hK := by
  unfold
    stinespringUnitaryForm partialTraceRight unitaryDilation
    stinespringGeneralForm dilation partialTraceRight
  ext a b
  congr
  ext c
  repeat rw [mul_apply]
  repeat rw [Fintype.sum_prod_type]
  congr
  ext d
  congr
  ext e
  repeat rw [mul_apply]
  simp only [Nat.succ_eq_add_one, dite_eq_ite, kroneckerMap_apply, ite_mul, dite_mul,
    conjTranspose_apply, star_def]
  repeat rw [Fintype.sum_prod_type]
  congr
  · ext f
    congr
    ext g
    simp only [ite_eq_right_iff, left_eq_dite_iff, mul_eq_mul_right_iff, mul_eq_zero]
    intro hg
    subst g
    intro h
    simp at h ⊢
  · split_ifs with g₀ <;> rfl


/-- Mar 26, 2026
Note we don't need any special properties of M,
and we don't need K to be CPTP.
-/
lemma stinespringGeneralForm_works {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ) :
    stinespringGeneralForm K M = krausApply K := by
    unfold stinespringGeneralForm
        dilation
        krausApply partialTraceRight e₀Xe₀ stinespringOp single
    ext a b
    rw [sum_apply]
    congr
    ext c
    repeat rw [mul_apply]
    rw [Fintype.sum_prod_type]
    congr
    ext d
    rw [mul_apply]
    simp only [Nat.succ_eq_add_one, kronecker, Fin.isValue, dite_eq_ite, Prod.mk.injEq,
      conjTranspose_apply, star_def]
    rw [Finset.sum_fn]
    rw [Fin.sum_univ_succAbove _ 0]
    rw [mul_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fin.isValue, Finset.sum_apply, kroneckerMap_apply, of_apply, and_true, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul,
      add_eq_left]
    rw [Finset.sum_eq_zero]
    simp_rw [mul_apply]
    simp


/--
Mar 25, 2026
Behold...
For good measure should also prove that
`stinespringUnitaryForm`
is actually unitary, but it might be similar to the
proof for
`stinespringUnitaryForm`.
Notice that unitarity is a side property, it is not why
the Stinespring form works.
-/
lemma stinespringUnitaryForm_works {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringUnitaryForm hK = krausApply K := by
  rw [← stinespringGeneralForm_works K (unitaryDilation hK) ]
  rw [unitaryForm_of_general]


/-- The "orthogonal" CPTP completion of a CPTNI map.
`Vtilde` is an alternative name for `krausCompletion`.
-/
noncomputable def krausCompletion {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) :
  Matrix (Fin m × Fin (r+1)) (Fin m) R := fun x => dite (x.2 < r)
  (fun H => stinespringOp K ⟨x.1, ⟨x.2, H⟩⟩)
   fun _ => (CFC.sqrt (1 - (stinespringOp K)ᴴ * (stinespringOp K)) : Matrix _ _ _) x.1

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
