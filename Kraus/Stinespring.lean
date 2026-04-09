import Kraus.Basic

/-!
# Stinespring dilation
-/

open Matrix MatrixOrder ComplexOrder RCLike TensorProduct Kronecker

/-- Also known as `partialTraceRight`. -/
noncomputable def tr₂ {R : Type*} [Ring R] {m n m' : Type*} [Fintype n]
    (ρ : Matrix (m × n) (m' × n) R) : Matrix m m' R :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- `stinespringOp` is often written as `V`. -/
noncomputable def stinespringOp {R : Type*} [Ring R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
  (K : r → Matrix m m R) : Matrix (m × r) m R :=
  let V₀ : Matrix (m × r) (m × Fin 1) R :=
    ∑ i, K i ⊗ₖ single i (0 : Fin 1) (1 : R)
  fun x y => V₀ x (y,0)

noncomputable def stinespringDilation {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R)
    (ρ : Matrix m m R) :=
  let V := stinespringOp K; V * ρ * Vᴴ

noncomputable def stinespringForm {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R) :=
  fun ρ => tr₂ (stinespringDilation K ρ)

lemma stinespringOp_adjoint_mul_self {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R) :
    ∑ i, star K i * K i = (stinespringOp K)ᴴ * stinespringOp K := by
  ext i j
  simp only [stinespringOp]
  repeat rw [Finset.sum_fn]
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [single, Finset.sum_apply, kroneckerMap_apply, of_apply,
    and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  congr

lemma stinespringForm_CPTNI {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) ≤ 1 := by
  convert hK
  rw [← stinespringOp_adjoint_mul_self]
  rfl

lemma stinespringForm_CPTP_isometry {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
  {K : r → Matrix m m R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) = 1 := by
  rw [← hK]
  rw [← stinespringOp_adjoint_mul_self]
  rfl

lemma hzRC {R : Type*} [RCLike R] (z : R) : star z * z = ‖z‖^2 := RCLike.conj_mul z


/--
Mar 16, 2026
(Mar 27: RCLike version)
Proving the columns of `V = stinespringOp K` are independent is a step
on the way to constructing the unitary dilation. -/
lemma stinespringOrtho {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal (𝕜 := R)
      fun j : m => WithLp.toLp 2 fun i : m × r => stinespringOp K i j := by
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    have h₁ : (((stinespringOp K)ᴴ * stinespringOp K) i j)
      = ((1 : Matrix m m R) i j) := by
      rw [stinespringForm_CPTP_isometry hK]
    rw [mul_apply] at h₁
    by_cases g₀ : i = j
    · subst i
      simp only [conjTranspose_apply, star_def, one_apply_eq] at h₁
      rw [← h₁]
      simp only [inner_self_eq_norm_sq_to_K]
      generalize stinespringOp K = α
      have hz := hzRC (R := R)
      simp only [star_def] at hz
      simp only [↓reduceIte]
      simp_rw [RCLike.conj_mul]
      norm_cast -- !!
      exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 fun i ↦ α i j)
    · rw [if_neg g₀]
      have : (1 : Matrix m m R) i j = 0 := by
        exact one_apply_ne' fun a ↦ g₀ (id (Eq.symm a))
      rw [this] at h₁
      rw [← h₁]
      simp only [inner, conjTranspose_apply, star_def]
      congr
      ext x
      ring_nf

/-- `m` will of course be finite and bounded by `n` here,
but no need to assume or prove that.
-/
lemma basisCard {R : Type*} [RCLike R] {n m : Type*} [Fintype n] {s : Matrix n m R}
    (ho : Orthonormal R fun j ↦ WithLp.toLp 2 fun i ↦ s i j) :
    Fintype.card n =
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  Fintype.card_coe _ ▸ (Nat.cast_inj.mp  <|
    (rank_eq_card_basis <| PiLp.basisFun _ _ _).symm.trans <|
     rank_eq_card_basis
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose.toBasis)


lemma stinespringCard {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Fintype.card (m × r) = (stinespringOrtho
    hK).toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  basisCard <| stinespringOrtho hK



open Finset in
/-- We need the 1 matrix, which we don't seem to have for an arbitrary
`[Fintype m]`.
Since we are comparing `Fin r` and `Fin r.succ` we also cannot too
easily use an arbitrary `[Fintype r] [Zero r]`.
-/
theorem complCard {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    let 𝓞 := fun j ↦ WithLp.toLp 2 fun i ↦ stinespringOp K i j;
    let theRange := Submodule.span R (Set.range 𝓞);
    let u' := (exists_orthonormalBasis R theRangeᗮ).choose;
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
        · exact (exists_orthonormalBasis R _).choose_spec.choose.toBasis
    simp
    linarith

/--
See discussion at https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/succAbove.20and.20predAbove.20lemmas/with/584270574
-/
def Fin.predAbove_of_ne {n : ℕ} (k : Fin (n + 1)) (i : Fin (n + 1))
    (h : i ≠ k) : Fin n := by
  by_cases H : i.1 > k.1
  · exact ⟨i.1 - 1, by omega⟩
  · exact ⟨i.1, by omega⟩

lemma Fin.predAbove_of_ne_injective (n : ℕ) (k : Fin (n + 1)) (x y : Fin (n + 1))
    (hx : x ≠ k) (hy : y ≠ k)
    (heq : Fin.predAbove_of_ne k x hx = Fin.predAbove_of_ne k y hy) : x = y := by
  unfold predAbove_of_ne at heq
  split_ifs at heq
  all_goals
  · simp at heq
    omega


/-- The way this is written, `Fin r.succ` and `Fin r` both occur
so it is tricky to go to a general `Fintype`.
If we want to truncate `Fin 5` to remove `2` for example the
columns would be laid out like:
0 => 0
1 => 1
2 => 3
3 => 4
-/
noncomputable def onbPart {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r.succ) (hx : ¬x.2 = 0) :
  -- if we make it `r+2` then the `x.2≠0` becomes unused.
  Fin m × Fin r.succ → R := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    have (z : Fin m × Fin r) :=
        ((exists_orthonormalBasis R theRangeᗮ).choose_spec.choose
        (Finset.equivOfCardEq (complCard hK) ⟨z, Finset.mem_univ _⟩)).1.1
    apply this
    exact (x.1, by
      apply Fin.predAbove_of_ne 0
      exact hx)

/-- The custom in quantum information theory is to use
|e₁>< e₁| as ancillary, as in `onbPart`, but type-theoretically it is more convenient to use
|e (Fin.last)>.
-/
noncomputable def onbPart' {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r) :
  Fin m × Fin r.succ → R := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    have (z : Fin m × Fin r) :=
        ((exists_orthonormalBasis R theRangeᗮ).choose_spec.choose
        (Finset.equivOfCardEq (complCard hK) ⟨z, Finset.mem_univ _⟩)).1.1
    apply this
    exact x


lemma onbPart_inner {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {y : Fin m × Fin r.succ} (hy : ¬y.2 = 0)
    {z : Fin m × Fin r.succ} (hz : ¬z.2 = 0)
    (h : y ≠ z) :
    inner R (WithLp.toLp 2 <| onbPart hK y hy)
            (WithLp.toLp 2 <| onbPart hK z hz) = 0 := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    let α := (exists_orthonormalBasis R theRangeᗮ).choose_spec
    have := α.choose.orthonormal.2
    simp only [Pairwise, Nat.succ_eq_add_one, ne_eq, Submodule.coe_inner, Subtype.forall,
      Subtype.mk.injEq] at this
    have h₁ := this (WithLp.toLp 2 <| onbPart hK y hy)
        (by simp [onbPart]) (by
            simp only [onbPart, Nat.succ_eq_add_one, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp)
        (WithLp.toLp 2 <| onbPart hK z hz)
        (by simp [onbPart]) (by
            simp only [onbPart, Nat.succ_eq_add_one, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp) (by
                simp only [onbPart, Nat.succ_eq_add_one, WithLp.toLp_ofLp, SetLike.coe_eq_coe]
                rw [α.choose_spec]
                simp only [Nat.succ_eq_add_one, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq,
                  Subtype.mk.injEq, Prod.mk.injEq, not_and]
                intro hyz
                contrapose! h
                have : y.2.1 ≠ 0 := Fin.val_ne_zero_iff.mpr hy
                have : z.2.1 ≠ 0 := Fin.val_ne_zero_iff.mpr hz
                have : y.2.1 = z.2.1 := by
                    suffices y.2 = z.2 by rw [this]
                    apply Fin.predAbove_of_ne_injective
                    omega
                have : y.2 = z.2 := by omega
                exact Prod.ext hyz this)
    rw [← h₁]
    simp_rw [α.choose_spec]

lemma onbPart_inner' {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {y : Fin m × Fin r}
    {z : Fin m × Fin r}
    (h : y ≠ z) :
    inner R (WithLp.toLp 2 <| onbPart' hK y)
            (WithLp.toLp 2 <| onbPart' hK z) = 0 := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    let α := (exists_orthonormalBasis R theRangeᗮ).choose_spec
    have := α.choose.orthonormal.2
    simp only [Pairwise, Nat.succ_eq_add_one, ne_eq, Submodule.coe_inner, Subtype.forall,
      Subtype.mk.injEq] at this
    have h₁ := this (WithLp.toLp 2 <| onbPart' hK y)
        (by simp [onbPart']) (by
            simp only [onbPart', Nat.succ_eq_add_one, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp)
        (WithLp.toLp 2 <| onbPart' hK z)
        (by simp [onbPart']) (by
            simp only [onbPart', Nat.succ_eq_add_one, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp) (by
                simp only [onbPart', Nat.succ_eq_add_one, WithLp.toLp_ofLp, SetLike.coe_eq_coe]
                rw [α.choose_spec]
                simp only [Nat.succ_eq_add_one, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq,
                  Subtype.mk.injEq]
                exact h)
    rw [← h₁]
    simp_rw [α.choose_spec]

lemma onbPart_norm' {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r) :
  ‖WithLp.toLp 2 <| onbPart' hK x‖ = 1 :=
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    (exists_orthonormalBasis R theRangeᗮ).choose_spec.choose.orthonormal.1 _


lemma onbPart_norm {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r.succ) (hx : ¬x.2 = 0) :
  ‖WithLp.toLp 2 <| onbPart hK x hx‖ = 1 :=
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    (exists_orthonormalBasis R theRangeᗮ).choose_spec.choose.orthonormal.1 _



/-- Also known as `unitaryDilation`. Respects x,y order. -/
noncomputable def Ud {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) R := by
  intro x y
  by_cases hy : y.2 = 0
  · exact stinespringOp K x y.1
  · exact onbPart hK y hy x

noncomputable def Ud' {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) R := by
  intro x y
  by_cases hy : y.2 = Fin.last _
  · exact stinespringOp K x y.1
  · apply onbPart' hK ⟨y.1, ⟨y.2, Fin.val_lt_last hy⟩⟩ x


/-- A general, not necessarily unitary, dilation. -/
noncomputable def dilation {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m] [Zero r]
    (K : r → Matrix m m R) (M : Matrix (m × r) (m × r) R) :
    Matrix (m × r) (m × r) R := fun x y =>
  ite (y.2 = 0) (stinespringOp K x y.1) (M x y)

noncomputable def dilation' {R : Type*} [RCLike R]
    {m : Type*} {r : ℕ} [Fintype m] [DecidableEq m]
    (K : Fin r.succ → Matrix m m R) (M : Matrix (m × Fin r.succ) (m × Fin r.succ) R) :
    Matrix (m × Fin r.succ) (m × Fin r.succ) R := fun x y =>
  ite (y.2 = Fin.last _) (stinespringOp K x y.1) (M x y)


/-- One version of it. -/
theorem Ud_orthonormal₁ {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal R fun y ↦
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
      let theRange := Submodule.span R <| Set.range
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

theorem Ud_orthonormal₁' {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal R fun y : Fin m × Fin r.succ ↦
    if hy : y.2 = Fin.last _ then WithLp.toLp 2 fun i ↦ stinespringOp K i y.1
    else WithLp.toLp 2 fun i ↦ onbPart' hK ⟨y.1, ⟨y.2, Fin.val_lt_last hy⟩⟩ i := by
    constructor
    · intro i
      simp only
      split_ifs with g₀
      · apply (stinespringOrtho hK).1
      · apply onbPart_norm'
    · intro i j h
      simp only
      let theRange := Submodule.span R <| Set.range
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
        have h₁ : (WithLp.toLp 2 fun i ↦ onbPart' hK
            ⟨j.1, ⟨j.2, Fin.val_lt_last g₁⟩⟩ i) ∈ theRangeᗮ := by
            unfold theRange
            simp [onbPart']
        exact h₁ _ h₀
      · have h₀' : (WithLp.toLp 2 fun i_1 ↦ stinespringOp K i_1 j.1) ∈ theRange := by
            unfold theRange
            generalize stinespringOp K = α
            apply Submodule.mem_span_of_mem
            simp
        have h₁ :  (WithLp.toLp 2 fun t ↦ onbPart' hK
            ⟨i.1, ⟨i.2, Fin.val_lt_last g₀⟩⟩ t) ∈ theRangeᗮ := by
            unfold theRange
            simp [onbPart']
        have := h₁ _ h₀'
        generalize (WithLp.toLp 2 fun i_1 ↦ onbPart' hK
            ⟨i.1, ⟨i.2, Fin.val_lt_last g₀⟩⟩ i_1) = α at *
        generalize (WithLp.toLp 2 fun i ↦ stinespringOp K i j.1) = β at *
        exact inner_eq_zero_symm.mp (h₁ β h₀')
      · apply onbPart_inner' hK  --g₀ g₂ h
        contrapose! h
        simp only [Nat.succ_eq_add_one, Prod.mk.injEq, Fin.mk.injEq] at h
        refine Prod.ext_iff.mpr ⟨h.1, Fin.eq_of_val_eq h.2⟩


theorem Ud_orthonormal₂ {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Orthonormal R fun y ↦
      WithLp.toLp 2 fun i ↦ if hy : y.2 = 0 then stinespringOp K i y.1 else onbPart hK y hy i := by
    have := Ud_orthonormal₁ hK
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
      simp only at this ⊢
      rw [← this]
      generalize stinespringOp K = α
      generalize onbPart hK = β
      split_ifs at * with g₀ g₁ <;> rfl


theorem Ud_orthonormal₂' {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Orthonormal R fun y : Fin m × Fin r.succ ↦
      WithLp.toLp 2 fun i ↦ if hy : y.2 = Fin.last _ then stinespringOp K i y.1
        else onbPart' hK ⟨y.1, ⟨y.2, Fin.val_lt_last hy⟩⟩ i := by
    have := Ud_orthonormal₁' hK
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
      simp only at this ⊢
      rw [← this]
      split_ifs at * with g₀ g₁ <;> rfl


lemma RCLike.norm_eq {R : Type*} [RCLike R] (γ : R) :
    RCLike.re γ * RCLike.re γ + RCLike.im γ * RCLike.im γ = ‖γ‖ ^ 2 := by
    rw [RCLike.norm_sq_eq_def]

lemma smul_self_one_of_norm_one {R : Type*} [RCLike R]
    {t : Type*} [Fintype t] {β : t → R} (hj : ‖WithLp.toLp 2 β‖ = 1) :
  ∑ x, (starRingEnd R) (β x) * β x = 1 := by
      refine Eq.symm ((fun {z w} ↦ RCLike.ext_iff.mpr) ?_)
      constructor
      · simp only [one_re, map_sum, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
        rw [← one_pow 2]
        rw [← hj]
        simp_rw [← RCLike.norm_sq_eq_def]
        exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 β)
      · simp only [one_im, map_sum, mul_im, conj_re, conj_im, neg_mul]
        symm
        apply Fintype.sum_eq_zero
        ring_nf
        simp

theorem unitary_of_orthonormal {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (α : Matrix (m × r) (m × r) R)
  (h₀ : Orthonormal R fun i ↦ WithLp.toLp 2 (α i)) : α * star α = 1 := by
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

lemma Ud_unitaryT {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (Ud hK)ᵀ ∈ unitary _ := by
  have H₀ := unitary_of_orthonormal (Ud hK)ᵀ
    <| Ud_orthonormal₂ hK
  constructor
  · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp H₀
  · exact H₀

lemma Ud_unitaryT' {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (Ud' hK)ᵀ ∈ unitary _ := by
  have H₀ := unitary_of_orthonormal (Ud' hK)ᵀ
    <| Ud_orthonormal₂' hK
  constructor
  · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp H₀
  · exact H₀

/-- Well will you look at that... -/
lemma Ud_unitary {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (Ud hK) ∈ unitary _ := by
     have := Ud_unitaryT hK
     generalize Ud hK = U at *
     clear hK K
     have :  star U * U = 1 := by
       have := this.2
       have : (Uᵀ * star Uᵀ)ᵀ = 1ᵀ := transpose_inj.mpr this
       simp at this
       have : (star Uᵀ)ᵀ = star U := by
         exact Eq.symm (Matrix.ext fun i ↦ congrFun rfl)
       rw [← this]
       tauto
     constructor
     · exact this
     · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp this

lemma Ud_unitary' {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (Ud' hK) ∈ unitary _ := by
     have := Ud_unitaryT' hK
     generalize Ud' hK = U at *
     clear hK K
     have :  star U * U = 1 := by
       have := this.2
       have : (Uᵀ * star Uᵀ)ᵀ = 1ᵀ := transpose_inj.mpr this
       simp at this
       have : (star Uᵀ)ᵀ = star U := by
         exact Eq.symm (Matrix.ext fun i ↦ congrFun rfl)
       rw [← this]
       tauto
     constructor
     · exact this
     · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp this


open Kronecker TensorProduct

/-
The projector | e₀ > < e₀ |
-/
def e₀Xe₀ {R : Type*} [RCLike R] {w : Type*} [Fintype w] [DecidableEq w] [Zero w] :
    Matrix w w R :=
    fun x y => if (x,y) = (0,0) then 1 else 0

/-- Also known as e₀Xe₀' I guess. -/
def eXe {R : Type*} [RCLike R] {w : ℕ} :
    Matrix (Fin w.succ) (Fin w.succ) R :=
    fun x y => if (x,y) = (Fin.last w,Fin.last w) then 1 else 0


example {w : ℕ} : e₀Xe₀ (w := Fin w.succ) (R := ℂ) = single 0 0 1 := by
    unfold e₀Xe₀ single
    simp only [Nat.succ_eq_add_one, Prod.mk.injEq]
    ext x y
    split_ifs
    · simp
      tauto
    simp
    tauto

/-- Does not need (he : e = e₀Xe₀). -/
lemma tr₂_e₀Xe₀ {R : Type*} [RCLike R]
    {m w : Type*} [Fintype w] [Zero w]
    (e : Matrix w w R) (htr : e.trace = 1)
    (ρ : Matrix m m R) :
    tr₂ (ρ ⊗ₖ e) = ρ := by
  unfold tr₂ kroneckerMap
  simp only [of_apply]
  ext i j
  have :  ∑ x, ρ i j * e x x
    = ρ i j * ∑ x,  e x x := by  rw [Finset.mul_sum]
  rw [this]
  unfold trace at htr
  simp only [diag_apply] at htr
  rw [htr]
  simp


/-- The best version. -/
noncomputable def stinespringUnitaryForm {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) R) :
    (Matrix (Fin m) (Fin m) R) :=
    let U := Ud hK
    tr₂ (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

noncomputable def stinespringUnitaryForm' {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) R) :
    (Matrix (Fin m) (Fin m) R) :=
    let U := Ud' hK
    tr₂ (U * (ρ ⊗ₖ eXe) * Uᴴ)

noncomputable def stinespringUnitaryForm_e {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (e : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    --(he : e.trace = 1)
    (ρ : Matrix (Fin m) (Fin m) R) :
    (Matrix (Fin m) (Fin m) R) :=
    let U := Ud hK
    tr₂ (U * (ρ ⊗ₖ e) * Uᴴ)

/-- Unitary dilation, processing a whole word -/
noncomputable def UdWord {α : Type*} {R : Type*} [RCLike R]
  {n q r : ℕ}
  {𝓚 : α → Fin r.succ → Matrix (Fin q) (Fin q) R}
    (hK : ∀ s, ∑ i, (𝓚 s i)ᴴ * 𝓚 s i = (1 : Matrix (Fin q) (Fin q) R))
   (word : Fin n → α)
  (ρ : Matrix (Fin q × Fin r.succ) (Fin q × Fin r.succ) R) :
  Matrix (Fin q × Fin r.succ) (Fin q × Fin r.succ) R := match n with
| 0 => ρ
| Nat.succ m =>
        let U := Ud (hK (word (Fin.last m)))
        U * (UdWord hK (Fin.init word) ρ) * Uᴴ
-- can generalize to arbitrary matrix in place of `Ud`


-- Trace-free version of the Stinespring Dilation Theorem:
-- mirroring https://chatgpt.com/c/69b329a6-8788-8325-9a82-5789b0b7c453:
theorem tracefree_version {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Zero r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (ρ : Matrix m m R) :
    let K' := fun i x y => star <| K i y x; let U := (stinespringOp K');
    Uᴴ * (ρ ⊗ₖ (1 : Matrix r r R)) * U = stinespringForm K ρ := by
    intro K' U
    unfold stinespringForm U stinespringOp tr₂
        stinespringDilation stinespringOp
    simp only [kroneckerMap, single, Fin.isValue, of_apply, mul_ite,
      mul_one, mul_zero]
    ext i j
    rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    congr
    ext k
    rw [mul_apply]
    congr
    ext l
    rw [mul_apply, Fintype.sum_prod_type, mul_apply, Finset.sum_fn]
    simp only [Fin.isValue, Finset.sum_apply, of_apply, and_true, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    conv =>
        left; left; right
        change (fun x ↦ ∑ x_1, (starRingEnd R) (K' x_1 x i) * (ρ x l * (ite (x_1 = k) 1 0)))
    simp only [star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.isValue, K']
    rw [Finset.sum_fn]
    simp


/- A version of the Stinespring Dilation Theorem. See Stinespring100.lean -/
-- theorem stinespringForm_eq {m r : ℕ}
--     (K : Fin r → Matrix (Fin m) (Fin m) ℂ)
--     (ρ : Matrix (Fin m) (Fin m) ℂ) :
--     tr₂ (stinespringDilation K ρ) = krausApply K ρ := by
--   unfold krausApply
--   ext u v
--   repeat rw [Finset.sum_apply]
--   simp only [tr₂, stinespringDilation, stinespringOp, kronecker, Fin.isValue]
--   congr
--   ext w
--   simp only [kroneckerMap, single, Fin.isValue, of_apply,
--     mul_ite, mul_one, mul_zero]
--   repeat rw [Matrix.mul_apply]
--   congr
--   ext j
--   repeat rw [Matrix.mul_apply]
--   simp only [Fin.isValue, conjTranspose_apply, star_def]
--   repeat rw [Finset.sum_apply]
--   simp

theorem heisenberg_schrõdinger {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Zero r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (ρ : Matrix m m R) :
  let K' := fun i x y => star <| K i y x
  let U := (stinespringOp K'); let V := stinespringOp K
  let schrõdinger := tr₂ (V * ρ * Vᴴ); -- evolve the state forward: V = V(t), ρ = ρ(0)
  let heisenberg := Uᴴ * (ρ ⊗ₖ (1 : Matrix r r R)) * U;
  -- ρ ⊗ₖ 1 is an "observable"; evolve it backward
    schrõdinger = heisenberg := by
    intro K' U
    rw [tracefree_version]
    rfl


noncomputable def stinespringGeneralForm {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Zero r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R)
    (M : Matrix (m × r) (m × r) R) :=
    let U := dilation K M
    fun ρ => tr₂ (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

noncomputable def stinespringGeneralForm' {R : Type*} [RCLike R]
    {r : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (K : Fin r.succ → Matrix m m R)
    (M : Matrix (m × Fin r.succ) (m × Fin r.succ) R) :=
    let U := dilation' K M
    fun ρ => tr₂ (U * (ρ ⊗ₖ eXe) * Uᴴ)

noncomputable def stinespringGeneralForm_e {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Zero r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R) (e : Matrix r r R)
    (M : Matrix (m × r) (m × r) R) :=
    let U := dilation K M
    fun ρ => tr₂ (U * (ρ ⊗ₖ e) * Uᴴ)


/-- When we plug in `M = Ud hK`
into the general `stinespringGeneralForm`,
then we do get
stinespringUnitaryForm hK
-/
theorem unitaryForm_of_general {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringGeneralForm K (Ud hK) =
    stinespringUnitaryForm hK := by
  unfold
    stinespringUnitaryForm tr₂ Ud
    stinespringGeneralForm dilation tr₂
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
  simp only [Nat.succ_eq_add_one, kroneckerMap_apply, ite_mul, dite_mul,
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

theorem unitaryForm_of_general' {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringGeneralForm' K (Ud' hK) =
    stinespringUnitaryForm' hK := by
  unfold
    stinespringUnitaryForm' tr₂ Ud'
    stinespringGeneralForm' dilation' tr₂
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
  simp only [Nat.succ_eq_add_one, kroneckerMap_apply, ite_mul, dite_mul,
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

theorem unitaryForm_of_general_e {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (e : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    stinespringGeneralForm_e K e (Ud hK) =
    stinespringUnitaryForm_e hK e := by
  unfold
    stinespringUnitaryForm_e tr₂ Ud
    stinespringGeneralForm_e dilation tr₂
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
  simp only [Nat.succ_eq_add_one, kroneckerMap_apply, ite_mul, dite_mul,
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

Uses `Fin` types because of the use of
`Fin.sum_univ_succAbove` in the proof.
-/
lemma stinespringGeneralForm_works {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) R)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) R) :
    stinespringGeneralForm K M = krausApply K := by
    unfold stinespringGeneralForm dilation
        krausApply tr₂ e₀Xe₀ stinespringOp single
    ext a b
    rw [sum_apply]
    congr
    ext c
    repeat rw [mul_apply]
    rw [Fintype.sum_prod_type]
    congr
    ext d
    rw [mul_apply]
    simp only [Nat.succ_eq_add_one, Fin.isValue, Prod.mk.injEq,
      conjTranspose_apply, star_def]
    rw [Finset.sum_fn, Fin.sum_univ_succAbove _ 0, mul_apply, Fintype.sum_prod_type]
    simp only [Fin.isValue, Finset.sum_apply, kroneckerMap_apply, of_apply, and_true, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul,
      add_eq_left]
    rw [Finset.sum_eq_zero]
    simp_rw [mul_apply]
    simp

/-- April 7: it works to not use e₀Xe₀ but "Fin.last" instead.
`Fin.predAbove` would be the general construction to use an
arbitrary basis vector (from the standard basis)
instead of `0` or `Fin.last n` except that for some reason it
does not permit `Fin.last n`.
-/
lemma stinespringGeneralForm_works' {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r.succ → Matrix (Fin m) (Fin m) R)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) R) :
    stinespringGeneralForm' K M = krausApply K := by
    unfold stinespringGeneralForm' dilation'
        krausApply tr₂ eXe stinespringOp single
    ext a b
    rw [sum_apply]
    congr
    ext c
    repeat rw [mul_apply]
    rw [Fintype.sum_prod_type]
    congr
    ext d
    rw [mul_apply]
    simp only [Nat.succ_eq_add_one, Fin.isValue, Prod.mk.injEq,
      conjTranspose_apply, star_def]
    rw [Finset.sum_fn, Fin.sum_univ_succAbove _ (Fin.last _), mul_apply, Fintype.sum_prod_type]
    simp only [Fin.isValue, Finset.sum_apply, kroneckerMap_apply, of_apply, and_true, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul,
      add_eq_left]
    rw [Finset.sum_eq_zero]
    simp_rw [mul_apply]
    simp

/- To see how much we can replace e₀Xe₀ by a general e,
this comes up.
Maybe instead generalize e₀Xe₀ with 0 replaced by an arbitrary
element.
April 7
But it has to be e₀Xe₀ because K is in the 0th position,
so the UCNC diagram is okay and the following result fails.
 -/
-- lemma stinespringGeneralForm_works_e {R : Type*} [RCLike R] {m r : ℕ}
--     (K : Fin r.succ → Matrix (Fin m) (Fin m) R)
--     (z : Fin (r + 1))
--     (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) R) :
--     stinespringGeneralForm_e K (eXe z) M = krausApply K := by
--     unfold stinespringGeneralForm_e
--     simp
--     unfold dilation
--     unfold eXe
--     simp
--     apply funext
--     intro ρ
--     unfold stinespringOp
--     simp [kroneckerMap]
--     unfold krausApply tr₂ single
--     ext a b
--     rw [sum_apply]
--     congr
--     ext c
--     repeat rw [mul_apply]
--     rw [Fintype.sum_prod_type]
--     congr
--     ext d
--     rw [mul_apply]
--     simp only [Nat.succ_eq_add_one, Fin.isValue, Prod.mk.injEq,
--       conjTranspose_apply, star_def]
--     rw [Finset.sum_fn, Fin.sum_univ_succAbove _ 0, mul_apply, Fintype.sum_prod_type]
--     simp only [Fin.isValue, Finset.sum_apply, kroneckerMap_apply, of_apply, and_true, mul_ite,
--       mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul,
--       add_eq_left]
--     rw [Finset.sum_eq_zero]
--     simp_rw [mul_apply]
--     simp
--     sorry
--     sorry



/--
Mar 25, 2026
Behold...

Notice that unitarity is a side property, it is not why
the Stinespring form works.
-/
lemma stinespringUnitaryForm_works {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringUnitaryForm hK = krausApply K := by
  rw [← stinespringGeneralForm_works K (Ud hK) ]
  rw [unitaryForm_of_general]

lemma stinespringUnitaryForm_works' {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    stinespringUnitaryForm' hK = krausApply K := by
  rw [← stinespringGeneralForm_works' K (Ud' hK) ]
  rw [unitaryForm_of_general']


/- In order to prove `UdWord_eq`, this is the key. -/
-- lemma UdWord_eq₀ {α : Type*} {R : Type*} [RCLike R]
--   {n q r : ℕ} (word : Fin n → α)
--   (𝓚 : α → Fin r.succ → Matrix (Fin q) (Fin q) R)
--     (hK : ∀ s, ∑ i, (𝓚 s i)ᴴ * 𝓚 s i = (1 : Matrix (Fin q) (Fin q) R))
--   (ρ : Matrix (Fin q) (Fin q) R) :
--   tr₂ (UdWord hK (word) (ρ ⊗ₖ e₀Xe₀))
--     = tr₂ ((tr₂ (UdWord hK (word)
--         (ρ ⊗ₖ e₀Xe₀))) ⊗ₖ (e₀Xe₀ : Matrix (Fin (r+1)) (Fin (r+1)) R))
--   := by sorry
--   induction n with
--   | zero =>
--     have : (UdWord hK word (kroneckerMap (fun x1 x2 ↦ x1 * x2) ρ e₀Xe₀)) =
--         ρ ⊗ₖ e₀Xe₀ := rfl
--     rw [this]
--     unfold tr₂ e₀Xe₀
--     simp
--   | succ n ih =>
--     specialize ih (Fin.init word)
--     have : UdWord hK word (ρ ⊗ₖ e₀Xe₀) =
--             let U := Ud (hK (word (Fin.last n)))
--             U * (UdWord hK (Fin.init word) (ρ ⊗ₖ e₀Xe₀)) * Uᴴ
--         := rfl
--     rw [this]
--     simp
--     rw [← ih]
--     generalize tr₂ (UdWord hK (Fin.init word) (kroneckerMap (fun x1 x2 ↦ x1 * x2) ρ e₀Xe₀)) = 𝓐
--     unfold e₀Xe₀
--     simp [kroneckerMap, tr₂]
--     sorry



-- What's happening is that trying to cast it to matrix does not prevent
-- it from staying a function, and then function 1 is the constant function.
example : ((fun _ _ => 1) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j
    simp

example : ((fun _ _ => 1) : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    sorry

example : (!![1,0;0,1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1,2;3,4] = !![1,2;3,4] := by
    ext i j
    simp

example : (1 : Matrix (Fin 2) (Fin 2) ℂ) * !![1,2;3,4] = !![1,2;3,4] := by
    ext i j
    simp



/-
Mar 27, 2026
See https://chatgpt.com/c/69b329a6-8788-8325-9a82-5789b0b7c453 for the math behind this
Doesn't seem quite true.
-/
-- theorem heisenberg_schrõdinger_unitary {m r : ℕ}
--     {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
--     (hK : ∑ i, (K i)ᴴ * K i = 1)
--     (ρ A : Matrix (Fin m) (Fin m) ℂ) : -- A: observable, ρ: state
--   let K' := fun i x y => star <| K i y x
--   let U := Ud hK; let V := Ud hK
--   stinespringUnitaryForm hK ρ = tr₂ ((ρ ⊗ₖ e₀Xe₀) * Uᴴ * (1 ⊗ₖ 1) * U)
--   ∧
--   trace (stinespringUnitaryForm hK ρ * A) =
--   trace (tr₂ ((ρ ⊗ₖ e₀Xe₀) * Uᴴ * (A ⊗ₖ 1) * U))
--   := by
--     unfold stinespringUnitaryForm
--     simp only [Nat.succ_eq_add_one, zero_mul, implies_true,
--  mul_zero, mul_one, kroneckerMap_one_one]
--     constructor
--     · unfold tr₂
--       have : (Ud hK)ᴴ * Ud hK = 1 := by
--         sorry
--       generalize Ud hK = U at *
--       simp_rw [mul_assoc]
--       simp_rw [this]
--       unfold e₀Xe₀
--       simp [kroneckerMap]
--       suffices ((fun i j ↦
--       (U * ((of fun (i j : Fin m × Fin (r+1)) ↦  ρ i.1 j.1) * Uᴴ)) (i, 0) (j, 0)) =
--       fun i j ↦ ρ i j) by
--         rw [← this]

--         congr
--         ext i j
--         simp
--         repeat rw [mul_apply]
--         simp
--         rw [Fintype.sum_prod_type]
--         rw [Finset.sum_comm]
--         congr
--         ext k
--         rw [mul_apply]
--         simp
--         rw [Fintype.sum_prod_type]
--         congr
--         ext l
--         repeat rw [mul_apply]
--         simp
--         rw [Fintype.sum_prod_type]
--         simp
--         rw [Finset.sum_comm]
--         rw [Finset.mul_sum] -- !!
--         congr
--         ext t
--         repeat rw [mul_apply]
--         simp
--         by_cases ht : t = 0
--         · subst t;simp
--           rw [Fintype.sum_prod_type]
--           simp

--           sorry
--         · sorry
--       show _ = ρ
--       have : r = 0 := by sorry
--       subst r
--       have : m = 2 := by sorry
--       subst m
--       simp

--       ext i j
--       repeat rw [mul_apply]
--       rw [Fintype.sum_prod_type]
--       simp
--       rw [mul_apply]
--       simp
--       rw [Fintype.sum_prod_type]
--       simp
--       rw [mul_apply]
--       simp
--       rw [Fintype.sum_prod_type]
--       simp
--       fin_cases i
--       · fin_cases j
--         · sorry
--         · simp
--           generalize U (0, 0) (0, 0) = u₀₀
--           generalize U (0, 0) (1, 0) = u₀₁
--           generalize U (1, 0) (1, 0) = u₁₁
--           generalize U (1, 0) (0, 0) = u₁₀
--           generalize ρ 0 0 = r₀₀
--           generalize ρ 1 0 = r₁₀
--           generalize ρ 0 1 = r₀₁
--           generalize ρ 1 1 = r₁₁
--           ring_nf
--           rw [← star_def]
--           have : ![u₀₀, u₀₁, u₁₀, u₁₁] = ![0,Complex.I,-Complex.I,0] := by sorry
--           simp at this
--           rw [this.1,this.2.1, this.2.2.1, this.2.2.2]
--           simp
--           -- almost true...
--           sorry
--       · fin_cases j
--         · sorry
--         · sorry
--     · unfold e₀Xe₀ tr₂
--       simp [kroneckerMap]
--       repeat rw [trace]
--       simp
--       congr
--       ext i
--       rw [mul_apply]
--       have : r = 0 := by sorry
--       subst r
--       have : m = 2 := sorry
--       subst m
--       simp
--       generalize Ud hK = U at *
--       rw [mul_apply]
--       rw [mul_apply]
--       simp
--       rw [Fintype.sum_prod_type]
--       rw [Fintype.sum_prod_type]
--       simp
--       rw [mul_apply]
--       rw [mul_apply]
--       simp
--       rw [Fintype.sum_prod_type]
--       rw [Fintype.sum_prod_type]
--       simp
--       rw [mul_apply]
--       rw [Fintype.sum_prod_type]
--       simp
--       fin_cases i
--       ·

--         · simp
--           generalize U (0, 0) (0, 0) = u₀₀
--           generalize U (0, 0) (1, 0) = u₀₁
--           generalize U (1, 0) (1, 0) = u₁₁
--           generalize U (1, 0) (0, 0) = u₁₀
--           generalize ρ 0 0 = r₀₀
--           generalize ρ 1 0 = r₁₀
--           generalize ρ 0 1 = r₀₁
--           generalize ρ 1 1 = r₁₁
--           generalize A 0 0 = a₀₀
--           generalize A 0 1 = a₀₁
--           generalize A 1 0 = a₁₀
--           generalize A 1 1 = a₁₁
--           ring_nf
--           rw [← star_def]
--           have : ![u₀₀, u₀₁, u₁₀, u₁₁] = ![0,1,1,0] := by sorry
--           simp at this
--           rw [this.1,this.2.1, this.2.2.1, this.2.2.2]
--           simp
--           rw [mul_apply]
--           simp
--           rw [Fintype.sum_prod_type]
--           simp
--           rw [mul_apply]
--           simp
--           rw [Fintype.sum_prod_type]
--           simp
--           rw [mul_apply]
--           simp
--           rw [Fintype.sum_prod_type]
--           simp
--           generalize ρ 0 0 = r₀₀
--           generalize ρ 1 0 = r₁₀
--           generalize ρ 0 1 = r₀₁
--           generalize ρ 1 1 = r₁₁
--           generalize U (0, 0) (0, 0) = u₀₀
--           generalize U (0, 0) (1, 0) = u₀₁
--           generalize U (1, 0) (1, 0) = u₁₁
--           generalize U (1, 0) (0, 0) = u₁₀
--           have : ![u₀₀, u₀₁, u₁₀, u₁₁] = ![0,1,1,0] := by sorry
--           simp at this
--           rw [this.1,this.2.1, this.2.2.1, this.2.2.2]
--           simp
--           -- almost true...
--           sorry
--       · sorry


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

def unital {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) := ∑ i, K i * star (K i) = 1

def subunital {R : Type*} [RCLike R] {m r : ℕ}
  (K : Fin r → Matrix (Fin m) (Fin m) R) := ∑ i, K i * star (K i) ≤ 1


lemma Matrix.mul_comm_one {R : Type*} [RCLike R] (A B : Matrix (Fin 1) (Fin 1) R) :
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
lemma partialTrace_tensor {R : Type*} [RCLike R] {m n : ℕ}
  (A : Matrix (Fin m) (Fin m) R)
  (B : Matrix (Fin n) (Fin n) R) :
    tr₂ (A ⊗ₖ B) = (trace B) • A  := by
    unfold tr₂ trace kroneckerMap
    simp only [of_apply, diag_apply]
    ext i j
    simp only [smul_apply, smul_eq_mul]
    have := @Finset.sum_mul (a := A i j) (ι := Fin n)
      (s := Finset.univ) (f := fun k => B k k) _ _
    rw [this]
    simp_rw [mul_comm]

/--
April 7, 2026
To explain the diagram in UCNC paper...
or it contradicts the diagram by looking at A^4?
-/
example {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m.succ) (Fin m.succ) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
     (ρ : Matrix (Fin m.succ) (Fin m.succ) R)
     (α : Matrix (Fin m.succ) (Fin m.succ) R)
     (β : Matrix (Fin r.succ) (Fin r.succ) R)
     (hβ : β.trace = 1)
     (h : (Ud hK) * (ρ ⊗ₖ e₀Xe₀) * (Ud hK)ᴴ = α ⊗ₖ β)
    : krausApply K ρ = α := by
    -- check if it generalizes beyond e₀Xe₀?
    rw [← stinespringUnitaryForm_works hK]
    unfold stinespringUnitaryForm
    simp only [Nat.succ_eq_add_one]
    rw [h]
    rw [partialTrace_tensor]
    simp only [Nat.succ_eq_add_one]
    rw [hβ]
    simp

-- #check TensorProduct.map

-- set_option maxHeartbeats 0 in
lemma UdWord_eq {α : Type*} {R : Type*} [RCLike R]
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r.succ → Matrix (Fin q) (Fin q) R)
    (hK : ∀ s, ∑ i, (𝓚 s i)ᴴ * 𝓚 s i = (1 : Matrix (Fin q) (Fin q) R))
  (ρ : Matrix (Fin q) (Fin q) R) :
    krausApplyWord word 𝓚 ρ =
    tr₂ (UdWord hK word (ρ ⊗ₖ e₀Xe₀)) := by
    induction n with
    | zero =>
        have : (UdWord hK word (kroneckerMap (fun x1 x2 ↦ x1 * x2) ρ e₀Xe₀))
            = (kroneckerMap (fun x1 x2 ↦ x1 * x2) ρ e₀Xe₀) := by rfl
        rw [this]
        unfold krausApplyWord tr₂ e₀Xe₀
        simp
    | succ n ih =>
        have : (UdWord hK word (kroneckerMap (fun x1 x2 ↦ x1 * x2) ρ e₀Xe₀)) =
            let U := Ud (hK (word (Fin.last n)))
            U * (UdWord hK (Fin.init word) (ρ ⊗ₖ e₀Xe₀)) * Uᴴ
            := by rfl
        rw [this]
        specialize ih <| Fin.init word

        unfold krausApplyWord  -- tr₂ e₀Xe₀
        have := @stinespringUnitaryForm_works R _ q r (𝓚 (word (Fin.last n)))
            (hK (word (Fin.last n)))
        rw [← this]
        unfold stinespringUnitaryForm
        simp only [Nat.succ_eq_add_one]
        rw [ih]
        set U := Ud (hK (word (Fin.last n)))
        change tr₂ (U * (tr₂ (UdWord hK (Fin.init word) (ρ ⊗ₖ e₀Xe₀))) ⊗ₖ e₀Xe₀ * Uᴴ) =
               tr₂ (U *       UdWord hK (Fin.init word) (ρ ⊗ₖ e₀Xe₀) * Uᴴ)
        set V := UdWord hK (Fin.init word)
        change tr₂ (U * tr₂ (V (ρ ⊗ₖ e₀Xe₀)) ⊗ₖ e₀Xe₀ * Uᴴ) =
               tr₂ (U *       V (ρ ⊗ₖ e₀Xe₀) * Uᴴ)
        set τ :=  V (ρ ⊗ₖ e₀Xe₀)
        set σ := (e₀Xe₀ : Matrix (Fin (r+1)) (Fin (r+1)) R)
        change tr₂ (U * ((tr₂ τ) ⊗ₖ σ) * Uᴴ) =
               tr₂ (U *     τ          * Uᴴ)
        have : tr₂ (U *     τ          * Uᴴ) = tr₂ (Uᴴ * U * τ) := by
            sorry
        -- if (partial) trace_cycle holds it would suffice that
        have : tr₂ ((tr₂ τ) ⊗ₖ (e₀Xe₀ : Matrix (Fin (r+1)) (Fin (r+1)) R)) = (tr₂ τ) := by
            generalize tr₂ τ = α
            unfold tr₂ e₀Xe₀
            simp

        -- have := @partialTrace_tensor
        -- have : tr₂ (τ ⊗ₖ e₀Xe₀) = τ := by
        --     sorry
        -- rw [this]
        simp

        -- nth_rw 1 [UdWord_eq₀]

        sorry



lemma trace_tr₂ {R : Type*} [RCLike R] {m n : ℕ}
  (ρ : Matrix ((Fin m) × (Fin n))
              ((Fin m) × (Fin n)) R) :
    trace ρ = trace (tr₂ ρ) := Fintype.sum_prod_type fun x ↦ ρ x x


example {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) R)
    (hρ : ρ.trace = 1) (i : Fin m)
    (hρ₀ : 0 ≤ ρ)
    : 0 = 0 := by
  let P := @POVM_PMF R _ m ρ hρ hρ₀
  let D := stinespringUnitaryForm hK ρ
  have := RCLike.re (pureState_C (e i) * ρ).trace
  have : RCLike.re (pureState_C (e i) * (stinespringUnitaryForm hK ρ)).trace
    = RCLike.re (pureState_C (e i) * (krausApply K ρ)).trace := by
    rw [stinespringUnitaryForm_works]
  unfold stinespringUnitaryForm at this
--   simp at this
  have h₀ := @trace_tr₂ R _ m r.succ
    (let U := Ud hK
    (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ))
  simp at h₀
--   have := @partialTrace_tensor
  -- need that trace_mul type formula?
  unfold POVM_PMF at P
  sorry



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
    simp only [ne_eq, Fin.isValue]
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


noncomputable def partialTraceLeft {R : Type*} [RCLike R] {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n)
                (Fin m × Fin n) R) : Matrix (Fin n) (Fin n) R :=
fun i j => ∑ k : Fin m, ρ (k, i) (k, j)
