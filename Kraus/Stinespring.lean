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
/-- Mar 16, 2026
Not a "traceable" version.
-/
noncomputable def unitary_dilation {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ := by
    exact fun x => (stinespringOrtho
        hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose
        (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)

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

/-- Mar 22, 2026.
Intended to be a "traceable" version.
-/
noncomputable def unitary_dilation_respecting_bot {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x
  by_cases hx : x.2 = 0
  · intro y
    exact stinespringOp K y x.1
  · exact onbPart hK x hx
 -- should prove this has orthonormal columns and is unitary, too, I suppose

/-- This ANOTHER may be better
in that it respects x,y order. -/
noncomputable def unitary_dilation_respecting_botANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x y
  by_cases hx : y.2 = 0
  · exact stinespringOp K x y.1
  · exact onbPart hK y hx x


/-- Mar 24, 2026 -/
noncomputable def unitary_dilation_respecting_botGENERALIZE {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x
  by_cases hx : x.2 = 0
  · intro y
    exact stinespringOp K y x.1
  · intro y; exact M y x -- or maybe x y

noncomputable def unitary_dilation_respecting_botGENERALIZEANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ := by
  intro x y
  by_cases hy : y.2 = 0
  · exact stinespringOp K x y.1
  · exact M x y -- or maybe x y


-- open Finset in
-- theorem unitary_dilation_respecting_bot_orthonormal {m r : ℕ}
--     {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
--     Orthonormal ℂ fun i ↦ WithLp.toLp 2 (unitary_dilation_respecting_bot hK i) := by
--     unfold unitary_dilation_respecting_bot
--     constructor
--     · intro i
--       by_cases hi : i.2 = 0
--       · simp_rw [hi]
--         simp
--         unfold stinespringOp
--         simp
--         unfold kroneckerMap single
--         simp
--         have (j : Fin m × Fin 1) : (0 = j.2) = True := by
--             simp
--             have := j.2.2
--             omega
--         simp_rw [this]
--         simp

--         sorry
--       · sorry
--     · sorry

open Finset in
theorem unitary_dilation_orthonormal {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
  (hK : ∑ i, (K i)ᴴ * K i = 1) : Orthonormal ℂ fun i ↦ WithLp.toLp 2 (unitary_dilation hK i) := by
    unfold unitary_dilation
    let α := (stinespringOrtho
        hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose
    have hα : Orthonormal ℂ α := (stinespringOrtho
          hK).toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose.orthonormal
    let f (x : Fin m × Fin r) := ⇑α (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
    change Orthonormal ℂ f
    let u := (stinespringOrtho
        hK).toSubtypeRange.exists_orthonormalBasis_extension.choose
    have := @Orthonormal.comp (v := α) ℂ _ _ _ _
      (f := fun x => equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
    exact this hα (by
      show Function.Injective fun x => (equivOfCardEq (stinespringCard hK) ⟨x, mem_univ _⟩)
      have := (equivOfCardEq (stinespringCard hK)).3
      refine Function.HasLeftInverse.injective ?_
      unfold Function.HasLeftInverse
      use fun x => (equivOfCardEq (stinespringCard hK)).2 x
      intro
      simp)

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

open Finset in
/-- This is nice; the next step would be to show
that a suitable trace of `unitary_dilation hK` recovers the original map `K`. -/
lemma unitary_dilation_unitary {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    unitary_dilation hK ∈ unitary _ := by
  have H₀ : unitary_dilation hK * star (unitary_dilation hK) = 1 := by
    have h₀ : Orthonormal ℂ (fun i => WithLp.toLp 2 <| unitary_dilation hK i) :=
      unitary_dilation_orthonormal _
    generalize unitary_dilation hK = α at *
    clear hK K
    -- extract_goal
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
  constructor
  · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp H₀
  · exact H₀

open Kronecker

def Matrix.kronecker_map_right {m n : ℕ} {R : Type*} [RCLike R]
  (A : Matrix (Fin n) (Fin n) R) :
       Matrix (Fin m × Fin n) (Fin m × Fin n) R := 1 ⊗ₖ A

lemma general_kronecker_map_right_apply {m m' n n' o o' : Type*}
    [Fintype m'] [Fintype n'] {R : Type*} [RCLike R]
    (B : Matrix n n' R) (A : Matrix m m' R)
    (e₁ : Matrix m' o R) (e₂ : Matrix n' o' R) :
    (A ⊗ₖ B) * -- derive the distributional curvature; implement PISALE r.a.
   -- think o=o'=1
  -- n = (m×r), n' = Fin m
  (e₁ ⊗ₖ e₂) = (A * e₁) ⊗ₖ (B * e₂) := by
  exact Eq.symm (mul_kronecker_mul A e₁ B e₂)
--   ext a b
--   unfold kroneckerMap
--   simp_rw [of_apply]
--   repeat rw [mul_apply]
--   rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
--   congr; ext
--   simp_rw [of_apply]
--   rw [Finset.sum_mul]
--   congr; ext
--   ring_nf

open TensorProduct


-- ⊗ₖ = Matrix.kronecker
lemma kronecker_map_right_apply {m n : ℕ} {R : Type*} [RCLike R]
  (A : Matrix (Fin n) (Fin n) R) (e₁ : Matrix (Fin m) (Fin 1) R)
                                 (e₂ : Matrix (Fin n) (Fin 1) R) :
  (1 ⊗ₖ A) * (e₁ ⊗ₖ e₂) = e₁ ⊗ₖ (A * e₂) := by
  rw [← mul_kronecker_mul]
  simp


example (m r : ℕ) : (Fin m × Fin r.succ) × Fin m →
    (Fin m × Fin r.succ) × (Fin m × Fin r.succ) := by
    intro x
    -- relate this to tensor products
    exact (x.1, (x.2,0))


example {m r : ℕ} : (Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ)
        ≃ₗ[ℂ]
        (Matrix (Fin m) (Fin m) ℂ)
        ⊗[ℂ]
        (Matrix (Fin r) (Fin r) ℂ) := by
    exact (kroneckerLinearEquiv (Fin m) (Fin m) (Fin r) (Fin r) ℂ).symm

instance :  Module ℂ (Matrix (Fin m) (Fin m) ℂ) := by exact module

noncomputable def lsmul (x : ℂ ⊗[ℂ] ℂ) : ℂ :=
    TensorProduct.lift
        (LinearMap.lsmul ℂ ℂ) x

def spor {m r : ℕ} (A : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :
    (Matrix (Fin m × Fin r) (Fin m) ℂ) ⊗[ℂ] (Matrix (Fin r) (Fin 1) ℂ) :=
  ∑ v, (fun (x,u) y => A (x,u) (y,v)) ⊗ₜ single v 0 1


def f {m r : ℕ} : Matrix (Fin m × Fin r) (Fin m) ℂ →ₙ+ Matrix (Fin r) (Fin 1) ℂ
                            →ₗ[ℂ] Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ := {
            toFun := by
                intro C
                apply IsLinearMap.mk' ?_ ?_
                · exact fun D (x,u) (y,v) => (C (x,u) y) * (D v 0) -- !!
                · refine { map_add := ?_, map_smul := ?_ } <;>
                    (intro X Y;ext i j;simp;ring_nf),
            map_add' := by intro X Y;ext Z p q;simp;ring_nf}

noncomputable def sporInv {m r : ℕ} :
    Matrix (Fin m × Fin r) (Fin m) ℂ ⊗[ℂ] Matrix (Fin r) (Fin 1) ℂ →
    (Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :=
    TensorProduct.lift (by
        apply LinearMap.mk (toAddHom := f)
        intro z C
        rw [RingHom.id_apply]
        simp only [f]
        ext D p q
        simp only [Prod.mk.eta, Fin.isValue, smul_apply,
          smul_eq_mul, IsLinearMap.mk'_apply, LinearMap.smul_apply]
        ring_nf)

lemma sumSingle {r : ℕ} (b : Matrix (Fin r) (Fin 1) ℂ) : b = ∑ i, b i 0 • single i 0 1 := by
        simp only [Fin.isValue, single, smul_of]
        let f (x : Fin r) := fun (i' : Fin r) (j' : Fin 1) ↦
            if x = i' ∧ 0 = j' then 1 else (0:ℂ)
        let g (x : Fin r) := of (b x 0 • f x)
        have : g = fun x => fun u v => ite (x=u) (b u 0) 0 := by
            unfold g f
            ext u v z
            simp only [Fin.isValue, of_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
              mul_zero]
            split_ifs with g₀ g₁
            · tauto
            · tauto
            · exfalso
              apply g₀
              constructor
              · tauto
              · exact Eq.symm (Fin.fin_one_eq_zero z)
            · rfl
        unfold g at this
        unfold f at this
        simp_rw [this]
        repeat rw [Finset.sum_fn]
        ext a z
        simp only [Fin.isValue, Finset.sum_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        congr
        exact Fin.fin_one_eq_zero z

-- example (R : Type u_1) [CommSemiring R] (M : Type u_7) (N : Type u_8)
--     [AddCommMonoid M] [AddCommMonoid N] [Module ℂ M] [Module ℂ N] :
--     (Module.finrank ℂ M) *
--     (Module.finrank ℂ N)
--     =
--     Module.finrank ℂ (M ⊗[ℂ] N)

--     := by
--     -- have := @Module.finrank_tensorProduct (S := ℂ)
--     sorry

/-- Mar 20, 2026
-/
lemma spor_onto {m r : ℕ}
    (B : Matrix (Fin m × Fin r) (Fin m) ℂ ⊗[ℂ] Matrix (Fin r) (Fin 1) ℂ)
    : spor (sporInv B) = B := by
    apply TensorProduct.induction_on (motive := fun B => spor (sporInv B) = B)
    · unfold spor sporInv
      rw [Fintype.sum_eq_zero]
      intro a
      conv => left; left; change 0
      simp
    · intro a b
      change ∑ i, (fun u v ↦ a u v * b i 0) ⊗ₜ[ℂ] single i 0 1 = a ⊗ₜ[ℂ] b
      nth_rw 2 [sumSingle b]
      rw [tmul_sum]
      congr
      ext i
      rw [tmul_smul]
      congr
      ext
      simp
      ring_nf
    · intro a b ha hb
      rw [sporInv, map_add]
      nth_rw 2 [← ha, ← hb]
      simp only [spor, Prod.mk.eta, add_apply, Fin.isValue]
      rw [← Finset.sum_add_distrib]
      congr
      ext
      rw [← Pi.add_apply]
      apply add_tmul



/-- Here we see the `stinespringOp K` subset
on the left, but we have not guaranteed that it is preserved.
But we can:

Recover control of order

This is the key step.

Instead of trying to extend directly as a sequence, do:

(a) split the space

Let

U := Submodule.span 𝕜 (Set.range v)

Then take the orthogonal complement:

Uᗮ
(b) build a basis on the complement
-/
noncomputable def unitary_dilation' {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (Matrix (Fin m × Fin r.succ) (Fin m) ℂ) ⊗[ℂ] (Matrix (Fin r.succ) (Fin 1) ℂ) := by
  have U := unitary_dilation_respecting_bot hK
  exact @spor m r.succ U

/-- Let's convert tensor products of matrices (as in unitary_dilation')
into large partialTraceable matrices. -/
def F₀ {a m r s : Type*} [Fintype a] [Fintype m] [Fintype r] [Fintype s]
    (A : (Matrix a m ℂ) ⊗[ℂ] (Matrix r s ℂ)) :
    Matrix (a × r) (m × s) ℂ :=
  TensorProduct.lift kroneckerBilinear A

noncomputable def unitary_dilation'' {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Matrix ((Fin m × Fin r.succ) × Fin r.succ) (Fin m × Fin 1) ℂ :=
  TensorProduct.lift kroneckerBilinear (unitary_dilation' hK)

/-- This looks neat but there is no guarantee
that it equals Φ(ρ) unless we take care of the bijections.
-/
noncomputable def stinespringUnitaryForm {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) := by
    let U := unitary_dilation hK
    exact partialTraceRight (U * (ρ ⊗ₖ 1) * Uᴴ)


/-
The projector
| e₀ > < e₀ |
-/
def e₀Xe₀ {w : ℕ} : Matrix (Fin w.succ) (Fin w.succ) ℂ := by
    intro x y
    by_cases H : (x,y) = (0,0)
    · exact 1
    · exact 0

lemma partialTraceRight_one {w m : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ) :
    partialTraceRight (ρ ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) =
        w • ρ := by
        unfold partialTraceRight kroneckerMap
        simp only [of_apply, one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ext i j
        have (i j : Fin m) (w : ℕ) : (w : Matrix (Fin m) (Fin m) ℂ) i j = ite (i=j) w 0 :=
            by exact natCast_apply
        rw [mul_apply]
        simp_rw [this]
        simp

lemma partialTraceRight_e₀Xe₀ {w m : ℕ} (ρ : Matrix (Fin m) (Fin m) ℂ) :
    partialTraceRight (ρ ⊗ₖ (e₀Xe₀ : Matrix (Fin w.succ) (Fin w.succ) ℂ)) =
        ρ := by
        unfold partialTraceRight kroneckerMap e₀Xe₀
        simp

-- noncomputable def stinespringUnitaryForm_respecting_bot___BAD
--     {m r : ℕ}
--     {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
--     (hK : ∑ i, (K i)ᴴ * K i = 1)
--     (ρ : Matrix (Fin m) (Fin m) ℂ) :
--     (Matrix (Fin m) (Fin m) ℂ) := by
--     let U := unitary_dilation_respecting_bot hK
--     exact partialTraceRight (U * (ρ ⊗ₖ 1) * Uᴴ)


noncomputable def stinespringUnitaryForm_respecting_bot {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) := by
    let U := unitary_dilation_respecting_bot hK
    exact partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

noncomputable def stinespringUnitaryForm_respecting_botANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) := by
    let U := unitary_dilation_respecting_botANOTHER hK
    exact partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)


noncomputable def stinespringUnitaryForm_respecting_botGENERALIZE {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) := by
    let U := @unitary_dilation_respecting_botGENERALIZE m r K M
    exact partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

noncomputable def stinespringUnitaryForm_respecting_botGENERALIZEANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix (Fin m) (Fin m) ℂ) := by
    let U := @unitary_dilation_respecting_botGENERALIZEANOTHER m r K M
    exact partialTraceRight (U * (ρ ⊗ₖ e₀Xe₀) * Uᴴ)

lemma unitary_dilation_works₀₀ {m : ℕ}
    {K : Fin 2 → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (h_adhoc : unitary_dilation_respecting_bot hK = 1)
    (h_adhoc₂ : K = ![1, 0])
    :
    stinespringUnitaryForm_respecting_bot hK ρ
    = krausApply K ρ := by
    subst K
    unfold stinespringUnitaryForm_respecting_bot
    rw [h_adhoc]
    have := @partialTraceRight_e₀Xe₀
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_mul, conjTranspose_one, mul_one] at this ⊢
    rw [this]
    simp [krausApply]


set_option linter.flexible false in
/-- Mar 24, 2026.
A small piece of evidence that our unitary dilation works.
-/
lemma unitary_dilation_worksGENERALIZE {m : ℕ}
    {K : Fin 2 → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hm : m = 1)
    (hU : M ∈ unitary _)
    (h : (fun x y => M (x, 0) y) = fun x (y, i) => K i x y) :
    @stinespringUnitaryForm_respecting_botGENERALIZE m 1 K M ρ
    = krausApply K ρ := by
    have getK (i : Fin 2) : K i = fun (x y : Fin m) => M (x,0) (y,i) := by
        ext x y
        rw [congrFun (congrFun h x) (y,i)]
    unfold stinespringUnitaryForm_respecting_botGENERALIZE
        krausApply unitary_dilation_respecting_botGENERALIZE
        e₀Xe₀ partialTraceRight stinespringOp single
        kroneckerMap
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, kronecker, Fin.sum_univ_two,
      add_apply, kroneckerMap_apply, of_apply, and_true, mul_ite, mul_one, mul_zero, Prod.mk.injEq,
      dite_eq_ite]
    ext a b
    repeat rw [mul_apply]
    simp only [Fin.isValue, conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, add_zero, star_def, Fin.sum_univ_two,
      add_apply]
    repeat rw [mul_apply]
    rw [Fintype.sum_prod_type]
    repeat rw [getK]
    simp only [Fin.isValue, Fin.sum_univ_two, conjTranspose_apply, star_def]
    subst m
    have : a = 0 := by exact Fin.fin_one_eq_zero a
    subst a
    have : b = 0 := by exact Fin.fin_one_eq_zero b
    subst b
    congr
    · ext c
      repeat rw [mul_apply]
      rw [Fintype.sum_prod_type]
      simp
      have : c = 0 := by exact Fin.fin_one_eq_zero c
      subst c
      simp
    · ext c
      repeat rw [mul_apply]
      rw [Fintype.sum_prod_type]
      have : c = 0 := by exact Fin.fin_one_eq_zero c
      subst c
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, one_ne_zero, ↓reduceIte,
        of_apply, and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        Finset.sum_singleton, and_false, Finset.sum_const_zero, zero_mul, add_zero]

/-- This is actually good: two operators,
arbitrary mxm matrices, works. -/
lemma unitary_dilation_worksGENERALIZEANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hr : r = 1)
    (hU : M ∈ unitary _)
    (h : (fun x y => M x (y, 0)) = fun (x, i) y => K i x y) :
    @stinespringUnitaryForm_respecting_botGENERALIZEANOTHER m r K M ρ
    = krausApply K ρ := by
    unfold stinespringUnitaryForm_respecting_botGENERALIZEANOTHER
        unitary_dilation_respecting_botGENERALIZEANOTHER
        krausApply partialTraceRight e₀Xe₀ stinespringOp single
    ext a b
    rw [sum_apply]
    congr
    ext c
    rw [mul_apply]
    rw [mul_apply]
    simp
    rw [Fintype.sum_prod_type]
    congr
    ext d
    rw [mul_apply]
    simp
    subst r
    simp
    rw [mul_apply]
    fin_cases c
    all_goals
    · simp
      rw [mul_apply]
      rw [Fintype.sum_prod_type]
      simp

lemma unitary_dilation_worksANOTHER {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hr : r = 1)
    (hU : M ∈ unitary _)
    (h : (fun x y => M x (y, 0)) = fun (x, i) y => K i x y) :
    @stinespringUnitaryForm_respecting_botANOTHER m r K hK ρ
    = krausApply K ρ := by
  have := @unitary_dilation_worksGENERALIZEANOTHER m r K hK
    (unitary_dilation_respecting_botANOTHER hK) ρ hr
    (by
    -- can presumably prove...
    sorry) (by
    -- this proof doesn't use hr
    clear hr
    simp [unitary_dilation_respecting_botANOTHER, stinespringOp, single]
    ext x y
    have (j' : Fin 1) : (0 = j') = True := by
        simp only [Fin.isValue, eq_iff_iff, iff_true];exact Eq.symm (Fin.fin_one_eq_zero j')
    simp_rw [this]
    simp [kroneckerMap]
    change (∑ x, fun i j ↦ if x = i.2 then K x i.1 j.1 else 0) x (y, 0) = K x.2 x.1 y
    simp
    )
  -- and now we prove the vindication of the
  -- GENERALIZE approach
  clear hr
  rw [← this]
  unfold
    stinespringUnitaryForm_respecting_botANOTHER
    partialTraceRight
    unitary_dilation_respecting_botANOTHER
    stinespringUnitaryForm_respecting_botGENERALIZEANOTHER
    unitary_dilation_respecting_botGENERALIZEANOTHER
  simp
  unfold partialTraceRight
  ext a b
  congr
  ext c
  rw [mul_apply]
  rw [mul_apply]
  repeat rw [Fintype.sum_prod_type]
  congr
  simp
  ext d
  congr
  repeat rw [Fintype.sum_prod_type]
  congr
  ext e
  rw [mul_apply]
  rw [mul_apply]
  simp
  repeat rw [Fintype.sum_prod_type]
  congr
  simp
  ext f
  congr
  repeat rw [Fintype.sum_prod_type]
  congr
  ext g
  simp
  intro hg
  subst g
  intro h
  simp at h
  ext i
  simp
  tauto


/--
Mar 24, 2026
Best so far:
three operators, arbitrary mxm.
But we still want to prove that `onbPart` is such an `M`.
-/
lemma unitary_dilation_worksGENERALIZEANOTHER₃ {m r : ℕ}
    {K : Fin r.succ → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (Fin m × Fin r.succ) (Fin m × Fin r.succ) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hr : r = 2)
    (hU : M ∈ unitary _)
    (h : (fun x y => M x (y, 0)) = fun (x, i) y => K i x y) :
    @stinespringUnitaryForm_respecting_botGENERALIZEANOTHER m r K M ρ
    = krausApply K ρ := by
    unfold stinespringUnitaryForm_respecting_botGENERALIZEANOTHER
        unitary_dilation_respecting_botGENERALIZEANOTHER
        krausApply partialTraceRight e₀Xe₀ stinespringOp single
    ext a b
    rw [sum_apply]
    congr
    ext c
    rw [mul_apply]
    rw [mul_apply]
    simp
    rw [Fintype.sum_prod_type]
    congr
    ext d
    rw [mul_apply]
    simp
    subst r
    simp
    fin_cases c
    all_goals
    · simp
      rw [Fin.sum_univ_three]
      simp
      rw [mul_apply]
      rw [Fintype.sum_prod_type]
      simp
      rw [Fin.sum_univ_three]
      simp
      rw [mul_apply]
      rw [Fintype.sum_prod_type]
      simp
      rw [mul_apply]
      rw [Fintype.sum_prod_type]
      simp



lemma unitary_dilation_worksGENERALIZE_ormaybe {m : ℕ}
    {K : Fin 2 → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hm : m = 1)
    (hU : M ∈ unitary _)
    (h : (fun x y => M (x, 0) y) = fun x (y, i) => K i y x)
    -- or maybe K i y x
    :
    @stinespringUnitaryForm_respecting_botGENERALIZE m 1 K M ρ
    = krausApply K ρ := by sorry

/-- Interestingly, the *not swapped* version allows us to
prove an assumption needed for the GENERALIZE version,
for
unitary_dilation_worksGENERALIZE_ormaybe
and
unitary_dilation_worksGENERALIZE equally.
-/
lemma unitary_dilation_works_using_GENERALIZE {m : ℕ}
    {K : Fin 2 → Matrix (Fin m) (Fin m) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hm : m = 1)
    :
    @stinespringUnitaryForm_respecting_bot m 1 K hK ρ
    = krausApply K ρ := by
    have := @unitary_dilation_worksGENERALIZE m K hK
        (unitary_dilation_respecting_bot hK) ρ hm
        (by
        -- can prove this, no harder than before
        sorry) (by
        unfold unitary_dilation_respecting_bot stinespringOp
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, ↓reduceDIte, kronecker,
          Fin.sum_univ_two, add_apply, kroneckerMap_apply]
        ext a b
        subst m
        have : a = 0 := by exact Fin.fin_one_eq_zero a
        subst a
        have : b.1 = 0 := by exact Fin.fin_one_eq_zero b.1
        rw [this]
        simp only [Fin.isValue, single, of_apply, and_true, mul_ite, mul_one, mul_zero]
        split_ifs with g₀ g₁ g₂
        · exfalso
          have := g₀.trans g₁.symm
          simp at this
        · rw [← g₀]
          simp
        · rw [← g₂]
          simp
        · fin_cases b <;> simp_all)
    sorry


/-- Works when `m = 0` (any `r`): -/
lemma unitary_dilation_works₀ {r : ℕ}
    {K : Fin r.succ → Matrix (Fin 0) (Fin 0) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (ρ : Matrix (Fin 0) (Fin 0) ℂ) :
    stinespringUnitaryForm_respecting_bot hK ρ
    = krausApply K ρ := by
    ext z₀
    have := z₀.2
    simp at this



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
