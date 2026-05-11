import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.WithTopBot

/-!

# Kraus operator automata and projection-valued measures

We define the language accepted by a measure-once Kraus operator automaton,
and a family of examples due to Grudka et al.

References:

 * S. Lakshmanan, `Finite-State Quantum Computational Complexity`,
  doctoral dissertation, University of Hawaii at Manoa, 2026.

 * `Quantum Synchronizing Words: Resetting and Preparing Qutrit States`,
   Grudka et al., 2025

 * `Unbounded length minimal synchronizing words for quantum channels over qutrits`,
   B. Kjos-Hanssen and J. Lakshmanan, QCNC 2026.

-/

open Matrix MatrixOrder ComplexOrder

/-- Completely positive map given by a (not necessarily minimal) Kraus family. -/
def krausApply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    (K : r → Matrix q q R) (ρ : Matrix q q R) : Matrix q q R :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- Kraus operator preserves PSD property. -/
lemma krausApply.posSemidef {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [AddLeftMono R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    (K : r → Matrix q q R)
    {ρ : Matrix q q R} (hρ : ρ.PosSemidef) :
    (krausApply K ρ).PosSemidef :=
  posSemidef_sum _ fun _ _ => hρ.mul_mul_conjTranspose_same _

def QuantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    (K : r → Matrix q q R) :=
  ∑ i, (K i)ᴴ * K i = 1

def QuantumOperation {R : Type*} [RCLike R]
  {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
  (K : r → Matrix q q R) := ∑ i, (K i)ᴴ * K i ≤ 1

def densityMatrix {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (d : Type*) [Fintype d] :=
  {ρ : Matrix d d R // ρ.PosSemidef ∧ ρ.trace = 1}

def densityMatrix.convex_comb {R : Type*} [RCLike R]
    {d : ℕ} (ρ₀ ρ₁ : densityMatrix (Fin d) (R := R)) {t : R}
    (hp₀ : 0 ≤ t) (hp₁ : 0 ≤ 1 - t) : densityMatrix (Fin d) (R := R) :=
  ⟨t • ρ₀.1 + (1 - t) • ρ₁.1, by
  constructor
  · exact (ρ₀.2.1.smul hp₀).add (ρ₁.2.1.smul hp₁)
  · rw [trace_add, trace_smul, smul_eq_mul, trace_smul, ρ₀.2.2, ρ₁.2.2]
    simp⟩

noncomputable section

def subNormalizedDensityMatrix
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (q : Type*) [Fintype q] :=
  {ρ : Matrix q q R // ρ.PosSemidef ∧ ρ.trace ≤ 1}

lemma QuantumChannel.trace_eq
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : QuantumChannel K)
    (ρ : Matrix (Fin q) (Fin q) R) :
  (krausApply K ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum, ← Matrix.sum_mul, hK]
  simp

lemma QuantumChannel.trace_eq_one
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : QuantumChannel K)
    (ρ : Matrix (Fin q) (Fin q) R) (hρ : ρ.trace = 1) :
    (krausApply K ρ).trace = 1 :=
  QuantumChannel.trace_eq hK ρ ▸ hρ

/-- Realizing a QuantumChannel as a map on densityMatrices. -/
def densityMatrix.applyChannel
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : QuantumChannel K)
    (ρ : densityMatrix (Fin q) (R := R)) : densityMatrix (Fin q) (R := R) :=
  ⟨krausApply K ρ.1, ⟨krausApply.posSemidef K ρ.2.1,
   QuantumChannel.trace_eq_one hK ρ.1 ρ.2.2⟩⟩


/-- Transition function `δ^*` corresponding to a word `word` over an alphabet `α`,
  where each symbol `a:α` is mapped to a completely positive map in Kraus form,
  of rank at most `r`.
-/
def krausApplyWord {α : Type*} {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
  {n q r : ℕ} (word : Fin n → α)
  (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
  (ρ : Matrix (Fin q) (Fin q) R) :
  Matrix (Fin q) (Fin q) R := match n with
| 0 => ρ
| m + 1 => krausApply (𝓚 (word (Fin.last m)))
        (krausApplyWord (Fin.init word) 𝓚 ρ)

/-- Using a family of quantum channels,
we can iterate over a word and stay within the density matrices. -/
theorem krausApplyWord_densityMatrix {α : Type*}
    {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
    {n q r : ℕ} (word : Fin n → α)
    {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R}
    (h𝓚 : ∀ (a : α), QuantumChannel (𝓚 a)) (ρ : densityMatrix (Fin q)) :
    (krausApplyWord word 𝓚 ρ.1).PosSemidef ∧ (krausApplyWord word 𝓚 ρ.1).trace = 1 := by
  induction n with
  | zero => exact ρ.2
  | succ n ih =>
    exact (densityMatrix.applyChannel (h𝓚 _)
      ⟨krausApplyWord (Fin.init word) 𝓚 ρ.1, ih (Fin.init word)⟩).2

/-- Using a family of quantum channels,
we can iterate over a word and stay within the density matrices. -/
def krausApplyWord_map {α : Type*}
    {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
    {n q r : ℕ} (word : Fin n → α)
    (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
    (hq : ∀ a, QuantumChannel (𝓚 a))
    (ρ : densityMatrix (Fin q) (R := R)) : densityMatrix (Fin q) (R := R) :=
  ⟨krausApplyWord word 𝓚 ρ.1, krausApplyWord_densityMatrix _ hq _⟩

def e {R : Type*} [One R] [Zero R] {k : ℕ} : Fin k → Matrix (Fin k) (Fin 1) R :=
  fun i => single i 0 1


def pureState_C {R : Type*} [Mul R] [Add R] [Zero R] [Star R]
    {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :=
  mulᵣ e eᴴ

lemma pureState_selfAdjoint_C {R : Type*} [Ring R] [StarRing R]
    {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :
    (pureState_C e).IsHermitian := by
  simp [Matrix.IsHermitian, pureState_C]



open Real in
def pureState_projection'_C {R : Type*} [RCLike R]
    {k : ℕ} (e : EuclideanSpace R (Fin k)) (he : ‖e‖ = 1) :
    IsStarProjection (pureState_C (fun (i : Fin k) (_ : Fin 1) => e i)) := {
      isIdempotentElem := by
        unfold pureState_C
        simp only [IsIdempotentElem, mulᵣ_eq];
        simp only [ ← Matrix.ext_iff, Matrix.mul_apply ];
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
          conjTranspose_apply, RCLike.star_def, Finset.sum_const, Finset.card_singleton, one_smul,
          ← mul_assoc, ← Finset.sum_mul, mul_eq_mul_right_iff, map_eq_zero];
        simp only [EuclideanSpace.norm_eq, sqrt_eq_one, mul_assoc,
          ← Finset.mul_sum _ _ _] at he ⊢;
        intro i j
        left
        convert mul_one (e.ofLp i)
        have (i : Fin k) : (starRingEnd R) (e.ofLp i) * e.ofLp i
            = ‖e.ofLp i‖ ^ 2 := by exact RCLike.conj_mul (e.ofLp i)
        simp_rw [this]
        generalize e.ofLp = α at *
        suffices RCLike.ofReal (∑ x, ‖α x‖ ^ 2) = (1 : R) by
            rw [← this]
            norm_num
        rw [he]
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint_C
  }


lemma pureState_projection_C {R : Type*} [Ring R] [StarRing R] {k : ℕ} (i : Fin k) :
  IsStarProjection (pureState_C (e i) (R := R)) := {
      isIdempotentElem := by
        unfold IsIdempotentElem pureState_C e
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint_C
  }

lemma pureState_projection''_C {R : Type*} [RCLike R] :
    IsStarProjection (pureState_C (e (0:Fin 3) (R := R))
    + pureState_C (e (1 : Fin 3))) := {
  isIdempotentElem := by
    unfold IsIdempotentElem
    rw [mul_add]
    repeat rw [add_mul]
    rw [(pureState_projection_C 0).isIdempotentElem]
    rw [(pureState_projection_C 1).isIdempotentElem]
    have : pureState_C (e (1:Fin 3)) * pureState_C (e 0) (R := R) = 0 := by
      unfold pureState_C e
      simp
    rw [this]
    have : pureState_C (e (0:Fin 3)) * pureState_C (e 1) (R := R) = 0 := by
      unfold pureState_C e
      simp
    rw [this]
    simp
  isSelfAdjoint :=
    (pureState_projection_C 0).isSelfAdjoint.add (pureState_projection_C 1).isSelfAdjoint
  }


theorem psd_versions_general {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    {k : ℕ} {e : Matrix (Fin k) (Fin k) R} {x : Fin k →₀ R}
    (he : 0 ≤ star ⇑x ⬝ᵥ e *ᵥ ⇑x) :
    0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * e i j * xj := by
  convert he
  rw [Finsupp.sum]
  have : (∑ a ∈ x.support, x.sum fun j xj ↦ star (x a) * e a j * xj)
        = (∑ a ∈ x.support, star (x a) * x.sum fun j xj ↦ e a j * xj)  := by
    congr
    ext j
    simp_rw [mul_assoc]
    rw [← Finsupp.mul_sum]
  simp_rw [this]
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · rw [dotProduct]
    congr
    ext i
    rw [mulVec, dotProduct]
    simp only [Pi.star_apply]
    congr
    apply Finsupp.sum_fintype
    simp
  · intro i _ hi
    simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
    rw [hi]
    simp

theorem psd_versions {k : ℕ} {e : Matrix (Fin k) (Fin k) ℝ} {x : Fin k →₀ ℝ}
    (he : 0 ≤ ⇑x ⬝ᵥ e *ᵥ ⇑x) :
    0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * e i j * xj :=
  psd_versions_general he


theorem matrix_identity_general {R : Type*} [RCLike R]
    (k : ℕ) (e : Matrix (Fin k) (Fin 1) R) (α : Fin k → R) :
  star α ⬝ᵥ (e * eᴴ) *ᵥ α = (star α ᵥ* e * eᴴ *ᵥ α) 0 := by
  simp only [Pi.mul_apply, vecMul, dotProduct, Pi.star_apply,
    RCLike.star_def, mulVec, mul_comm, Finset.mul_sum, mul_assoc];
  congr; ext u; congr; ext v
  simp [ Matrix.mul_apply, mul_comm, mul_left_comm ]


lemma pureState_psd_C {R : Type*} [RCLike R] [PartialOrder R]
    [StarOrderedRing R]
    {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :
    (pureState_C e).PosSemidef := by
  constructor
  · exact pureState_selfAdjoint_C _
  · intro x
    suffices 0 ≤ star x ⬝ᵥ (pureState_C e).mulVec x by
      apply psd_versions_general
      convert this
    unfold pureState_C
    generalize ⇑x = α at *
    rw [mulᵣ_eq]
    rw [matrix_identity_general]
    change 0 ≤ (star α ᵥ* e) 0 * (eᴴ *ᵥ α) 0
    have : star ((eᴴ *ᵥ α) 0) = (star α ᵥ* e) 0 := by
        rw [vecMul, mulVec, dotProduct, dotProduct]
        simp only [conjTranspose_apply, RCLike.star_def, star_sum, star_mul',
          RingHomCompTriple.comp_apply, RingHom.id_apply, Pi.star_apply]
        congr
        ext i
        rw [mul_comm]
    rw [← this]
    refine star_mul_self_nonneg ((eᴴ *ᵥ α) 0)




lemma pure_state_eq {k : ℕ} (i : Fin k) :
    (single i (0 : Fin 1) (1 : ℝ)).mulᵣ (single i 0 1)ᵀ
    = Matrix.single i i 1 := by
  have : (single i (0:Fin 1) (1:ℝ))ᵀ = single 0 i 1 := by
    simp
  rw [this]
  simp

lemma pure_state_eq_C {R : Type*} [RCLike R] {k : ℕ} (i : Fin k) :
    (single i (0 : Fin 1) (1 : R)).mulᵣ (single i 0 1)ᴴ
    = Matrix.single i i 1 := by
  have : (single i (0:Fin 1) (1:R))ᴴ = single 0 i 1 := by
    simp
  rw [this]
  simp

/-- Cautionary example: This does not become a matrix!
A different kind of identity kicks in. -/
lemma matrix_caution : ((fun _ _ => 1) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j
    simp

instance : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedRing

instance :  NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedAlgebra

/-- Jireh recommends this approach. -/
theorem matrix_posSemidef_eq_star_mul_self' {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
(hP : 0 ≤ P) : ∃ B, P = star B * B := by
  use CFC.sqrt P
  have h₀ : (CFC.sqrt P)ᴴ = CFC.sqrt P := by
    have := hP.1
    simp only [IsHermitian, sub_zero, conjTranspose_eq_transpose_of_trivial] at this ⊢
    nth_rw 2 [← this]
    symm
    rw [@CFC.sqrt_eq_iff]
    · rw [← transpose_mul]
      congr
      apply @CFC.sqrt_mul_sqrt_self (a := P)
      · exact topologicalRing
      · exact instT2SpaceMatrix
      · exact hP
    · exact star_nonneg_iff.mp hP
    · exact star_nonneg_iff.mp <| CFC.sqrt_nonneg P
  have : star (CFC.sqrt P) = CFC.sqrt P := by
    have := hP.1
    simp only [IsHermitian, sub_zero, conjTranspose_eq_transpose_of_trivial] at this ⊢
    nth_rw 2 [← h₀]
    congr
  rw [this]
  symm
  rw [← @CFC.sqrt_eq_iff (a := P) (b := CFC.sqrt P)]
  · exact topologicalRing
  · exact instT2SpaceMatrix
  · simp;tauto
  · exact CFC.sqrt_nonneg P

theorem matrix_posSemidef_eq_star_mul_self'_C {R : Type*} [RCLike R] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) R)
(hP : 0 ≤ P) : ∃ B, P = star B * B := by
  use CFC.sqrt P
  have h₀ : (CFC.sqrt P)ᴴ = CFC.sqrt P := by
    have := hP.1
    simp only [sub_zero] at this ⊢
    nth_rw 2 [← this]
    symm
    rw [@CFC.sqrt_eq_iff]
    · rw [← conjTranspose_mul]
      congr
      apply @CFC.sqrt_mul_sqrt_self (a := P)
      · exact topologicalRing
      · exact instT2SpaceMatrix
      · exact hP
    · exact star_nonneg_iff.mpr hP
    · exact star_nonneg_iff.mpr <| CFC.sqrt_nonneg P
  have : star (CFC.sqrt P) = CFC.sqrt P := by
    have := hP.1
    simp only [sub_zero] at this ⊢
    nth_rw 2 [← h₀]
    congr
  rw [this]
  symm
  rw [← @CFC.sqrt_eq_iff (a := P) (b := CFC.sqrt P)]
  · exact topologicalRing
  · exact instT2SpaceMatrix
  · simp;tauto
  · exact CFC.sqrt_nonneg P

theorem trace_mul_posSemidef_nonneg {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ : ρ.PosSemidef) (hP : P.PosSemidef) : 0 ≤ (P * ρ).trace := by
      -- Use `Matrix.posSemidef_iff_eq_transpose_mul_self` to write $P = Bᵀ * B$.
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, P = star B * B := by
        apply matrix_posSemidef_eq_star_mul_self'
        exact nonneg_iff_posSemidef.mpr hP
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, P = B.transpose * B := by
        use B
        rw [hB]
        congr
      have h_trace_cyclic : Matrix.trace (P * ρ) = Matrix.trace (B * ρ * B.transpose) := by
        simp +decide only [hB, Matrix.mul_assoc, Matrix.trace_mul_comm B];
        exact trace_mul_cycle' Bᵀ B ρ;
      have h_pos_semidef : Matrix.PosSemidef (B * ρ * B.transpose) := by
        apply Matrix.PosSemidef.mul_mul_conjTranspose_same hρ
      exact h_trace_cyclic ▸ h_pos_semidef.trace_nonneg


theorem trace_mul_posSemidef_nonneg_general {R : Type*} [RCLike R]
    {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) R}
    (hρ : ρ ≥ 0) (hP : P ≥ 0) : 0 ≤ (P * ρ).trace := by
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) R, P = star B * B :=
        @matrix_posSemidef_eq_star_mul_self'_C R _ n P hP
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) R, P = Bᴴ * B := by
        use B
        rw [hB]
        congr
      have h_trace_cyclic : (P * ρ).trace = (B * ρ * Bᴴ).trace := by
        simp +decide only [hB, Matrix.mul_assoc, Matrix.trace_mul_comm B];
        exact trace_mul_cycle' Bᴴ B ρ;
      have h_pos_semidef : 0 ≤ (B * ρ * Bᴴ) := by
        constructor
        · unfold IsHermitian
          simp only [sub_zero, conjTranspose_mul, conjTranspose_conjTranspose]
          rw [mul_assoc]
          congr
          refine IsHermitian.eq ?_
          refine isHermitian_iff_isSelfAdjoint.mpr ?_
          exact LE.le.isSelfAdjoint hρ
        · intro x
          have := @psd_versions_general R _ _ RCLike.toPartialOrder
            n (B * ρ * Bᴴ) x (by
                change @LE.le R RCLike.toPartialOrder.toLE 0 (star ⇑x ⬝ᵥ (B * ρ * Bᴴ) *ᵥ ⇑x)
                have := Bᴴ *ᵥ ⇑x
                have := ρ *ᵥ this
                have := ((B * ρ) *ᵥ (Bᴴ *ᵥ ⇑x))
                suffices @LE.le R RCLike.toPartialOrder.toLE 0
                    (star ⇑x ⬝ᵥ ((B * ρ) *ᵥ (Bᴴ *ᵥ ⇑x))) by
                    convert this using 1
                    simp
                suffices @LE.le R RCLike.toPartialOrder.toLE 0
                    (star ⇑x ⬝ᵥ (B *ᵥ ρ *ᵥ (Bᴴ *ᵥ ⇑x))) by
                    convert this using 1
                    simp
                    grind only
                rw [Matrix.dotProduct_mulVec]
                rw [Matrix.dotProduct_mulVec]
                have : star ⇑x ᵥ* B = star (Bᴴ *ᵥ ⇑x) := by
                    rw [star_mulVec]
                    congr
                    exact Eq.symm (conjTranspose_conjTranspose B)
                rw [this]
                generalize (Bᴴ *ᵥ ⇑x) = b
                rw [← Matrix.dotProduct_mulVec]
                have := @PosSemidef.dotProduct_mulVec_nonneg (Fin n)
                    R _ RCLike.toPartialOrder _ _ ρ (LE.le.posSemidef hρ) b
                    -- notice this trick ^^
                convert this)
          simp only [RCLike.star_def, sub_apply, zero_apply, sub_zero, ge_iff_le]
          exact this
      rw [h_trace_cyclic]
      exact @PosSemidef.trace_nonneg (Fin n) R _ _ _ _
        _ (B * ρ * Bᴴ) (by apply LE.le.posSemidef;tauto)

/-- Feb 1, 2026.
And almost again May 9, 2026. -/
lemma QuantumOperation.trace_le {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : QuantumOperation K)
    {ρ : Matrix (Fin q) (Fin q) R} (hρ : 0 ≤ ρ) :
    (krausApply K ρ).trace ≤ ρ.trace := by
  unfold QuantumOperation at hK
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum]
  rw [← Matrix.sum_mul]
  generalize  ∑ i, (K i)ᴴ * K i = α at *
  suffices 0 ≤ ((1 - α) * ρ).trace by
    have : 0 ≤ (ρ - α * ρ).trace := by
        convert this using 1
        congr
        have : ρ = 1 * ρ := by simp
        nth_rw 1 [this]
        exact Eq.symm (Matrix.sub_mul 1 α ρ)
    have :  0 ≤ ρ.trace - (α * ρ).trace := by
        rw [← trace_sub]
        exact this
    exact sub_nonneg.mp this
  exact trace_mul_posSemidef_nonneg_general hρ <| nonneg_iff_posSemidef.mpr hK

lemma QuantumOperation_preserves_trace_le_one
    {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : QuantumOperation K)
    {ρ : Matrix (Fin q) (Fin q) R} (hρ : 0 ≤ ρ)
    (hρ₁ : ρ.trace ≤ 1) : (krausApply K ρ).trace ≤ 1 :=
  le_trans (hK.trace_le hρ) hρ₁

/--
Feb 1, 2026
Realizing a QuantumOperation as a map on subnormalized density matrices. -/
def krausApply_subNormalizedDensityMatrix {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : QuantumOperation K)
    (ρ : subNormalizedDensityMatrix (Fin q) (R := R)) :
    subNormalizedDensityMatrix (Fin q) (R := R) :=
  ⟨krausApply K ρ.1, krausApply.posSemidef K ρ.2.1,
    QuantumOperation_preserves_trace_le_one hK
      (Matrix.nonneg_iff_posSemidef.mpr ρ.2.1) ρ.2.2
   ⟩

theorem krausApplyWord_subNormalizedDensityMatrix {α : Type*}
    {R : Type*} [RCLike R] {n q r : ℕ} (word : Fin n → α)
    {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R} (h𝓚 : ∀ (a : α), QuantumOperation (𝓚 a))
    (ρ : subNormalizedDensityMatrix (Fin q)) :
    (krausApplyWord word 𝓚 ρ.1).PosSemidef ∧ (krausApplyWord word 𝓚 ρ.1).trace ≤ 1 := by
  induction n with
  | zero => exact ρ.2
  | succ n ih => exact (krausApply_subNormalizedDensityMatrix (h𝓚 _)
        ⟨krausApplyWord (Fin.init word) 𝓚 ρ.1, ih (Fin.init word)⟩).2

/-- If each letter is a quantum channel
then the whole word maps density matrices to density matrices. -/
def krausApplyWord_map_sub {α : Type*} {R : Type*} [RCLike R]
    {n q r : ℕ} (word : Fin n → α)
    {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R} (h𝓚 : ∀ a, QuantumOperation (𝓚 a))
    (ρ : subNormalizedDensityMatrix (Fin q) (R := R)) :
    subNormalizedDensityMatrix (Fin q) (R := R) :=
  ⟨krausApplyWord word 𝓚 ρ.1,
   krausApplyWord_subNormalizedDensityMatrix word h𝓚 ρ⟩



/-
A real matrix that is a star projection (symmetric and idempotent) is positive semidefinite.
-/
theorem posSemidef_of_isStarProjection {n : ℕ}
  (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsStarProjection P) : P.PosSemidef := by
  revert hP;
  rintro ⟨ h₁, h₂ ⟩;
  refine ⟨ h₂, ?_ ⟩;
  intro x
  have h_pos_semi_def : (P.mulVec x) ⬝ᵥ (P.mulVec x) ≥ 0 := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp_all only [dotProduct_mulVec, vecMul_mulVec, ge_iff_le, star_trivial];
  simp_all only [IsIdempotentElem, dotProduct_comm];
  simp_all only [IsSelfAdjoint];
  simp_all only [star, conjTranspose_eq_transpose_of_trivial]
  apply psd_versions
  convert h_pos_semi_def
  generalize ⇑x = β at *
  clear h_pos_semi_def h₁
  unfold mulVec vecMul
  simp only
  ext i
  unfold dotProduct
  simp only
  congr
  ext j
  rw [mul_comm]
  suffices P i j = P j i by rw [this]
  exact congrFun (congrFun (id (Eq.symm h₂)) i) j

theorem posSemidef_of_isStarProjection_C {R : Type*} [RCLike R] {n : ℕ}
  (P : Matrix (Fin n) (Fin n) R) (hP : IsStarProjection P) : P.PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact IsStarProjection.nonneg hP


lemma trace_mul_nonneg {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg hρ'
  apply posSemidef_of_isStarProjection
  exact hP

lemma trace_mul_nonneg_C {R : Type*} [RCLike R] {n : ℕ} {ρ P : Matrix (Fin n) (Fin n) R}
    (hρ' : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ (P * ρ).trace := by
  apply trace_mul_posSemidef_nonneg_general (nonneg_iff_posSemidef.mpr hρ')
  suffices P.PosSemidef by exact nonneg_iff_posSemidef.mpr this
  apply posSemidef_of_isStarProjection_C
  exact hP



lemma nonneg_trace'_C {R : Type*} [RCLike R] {n : ℕ}
    {ρ : Matrix (Fin n) (Fin n) R} (hρ' : ρ.PosSemidef)
    (e : Matrix (Fin n) (Fin 1) R)
    (he : ‖WithLp.toLp 2 fun i ↦ e i 0‖ = 1) -- not really necessary
  : 0 ≤ (pureState_C e * ρ).trace := by
      apply trace_mul_nonneg_C hρ'
      have := @pureState_projection'_C _ _ n {ofLp := fun i => e i 0} he
      convert this


open Real in
lemma nonneg_trace_of_posSemidef_C {R : Type*} [RCLike R] {n : ℕ} {ρ : Matrix (Fin n) (Fin n) R}
    (hρ' : ρ.PosSemidef) (i : Fin n) :
    0 ≤ (pureState_C (e i) * ρ).trace := by
  apply nonneg_trace'_C hρ'
  simp only [PiLp.instNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, rpow_ofNat, one_div, e, single, Fin.isValue, of_apply, and_true]
  suffices (∑ x, ‖if i = x then (1:R) else 0‖ ^ 2) = 1 by rw [this];simp
  have : (fun (x : Fin n) => ‖if i = x then  (1:R)  else 0‖ ^ 2) =
         (fun x =>            if i = x then ‖(1:R)‖ else ‖(0:R)‖) := by
        ext j
        split_ifs <;> simp
  simp_rw [this]
  simp


lemma sum_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, of (Function.update 0 x (ρ.row x)) = ρ := by
      ext i j
      rw [Finset.sum_apply]
      simp only [row, Finset.sum_apply, of_apply, Function.update,
        eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      rw [← congrFun (Fintype.sum_ite_eq i fun j ↦ ρ i) j]
      aesop

lemma sum_rows_C {R : Type*} [RCLike R] {k : ℕ} (ρ : Matrix (Fin k) (Fin k) R) :
  ∑ x, of (Function.update 0 x (ρ.row x)) = ρ := by
      ext i j
      rw [Finset.sum_apply]
      simp only [row, Finset.sum_apply, of_apply, Function.update,
        eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      rw [← congrFun (Fintype.sum_ite_eq i fun j ↦ ρ i) j]
      aesop


lemma single_row {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R} (x : Fin k) :
  single x x 1 * ρ = of (Function.update 0 x (ρ.row x)) := by
        rw [@Matrix.single_mul_eq_updateRow_zero]
        unfold updateRow
        simp

lemma combined_rows {k : ℕ} (ρ : Matrix (Fin k) (Fin k) ℝ) :
  ∑ x, single x x 1 * ρ = ρ := by
      have := @sum_rows k ρ
      nth_rw 2 [← this]
      have := @single_row ℝ _ k ρ
      simp_rw [this]



open ENNReal


/-- Unlike `standard_basis_probability_one` this one does not require PSD. -/
lemma standard_basis_probability_C {R : Type*} [RCLike R] {k : ℕ}
  (ρ : Matrix (Fin k) (Fin k) R) :
  ∑ a, (pureState_C (e a) * ρ).trace = ρ.trace := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    rw [← sum_rows_C ρ]
    rw [← trace_sum]
    congr
    ext a b c
    simp only [of_apply]
    repeat simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite]
    split_ifs with g
    · subst b
      simp only [row_apply]
      unfold Function.update
      simp only [eq_rec_constant, Pi.zero_apply, dite_eq_ite]
      simp only [sum_apply, of_apply]
      simp only [row]
      suffices ∑ x, (if a = x then ρ x else 0) = ρ a by
        rw [← this]
        simp
      exact Fintype.sum_ite_eq a ρ
    · simp


/-- Unlike `standard_basis_probability_one` this one does not require PSD. -/
lemma standard_basis_probability_one_C {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} (hUT : ρ.trace = 1) :
  ∑ a, (pureState_C (e a) * ρ).trace = 1 := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    rw [← sum_rows_C ρ] at hUT
    rw [← trace_sum]
    exact hUT

/-- Unlike `standard_basis_probability_one` this one does not require PSD. -/
lemma standard_basis_probability_le_one_C {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} (hUT : ρ.trace ≤ 1) :
  ∑ a, (pureState_C (e a) * ρ).trace ≤ 1 := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    rw [← sum_rows_C ρ] at hUT
    rw [← trace_sum]
    exact hUT

lemma standard_basis_probability_general {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} :
  ∑ a, (pureState_C (e a) * ρ).trace = ρ.trace := by
    unfold pureState_C e
    simp_rw [pure_state_eq_C]
    simp_rw [single_row]
    nth_rw 2 [← sum_rows_C ρ]
    rw [← trace_sum]

def subPMF (α : Type*) :=
  { f : α → ℝ≥0∞ // ∃ p ≤ 1, HasSum f p }

def subPMF.ofFinset (α : Type*)
    (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a ≤ 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : subPMF α :=
  ⟨f, by
    have := @hasSum_sum_of_ne_finset_zero (α := ENNReal) (β := α) _ _
        (SummationFilter.unconditional α) f s h'
            (SummationFilter.instLeAtTopUnconditional α)
    use ∑ a ∈ s, f a
    ⟩

def subPMF.ofFintype (α : Type*) [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a ≤ 1) : subPMF α := by
    apply subPMF.ofFinset (s := Finset.univ)
    · exact h
    intro a ha
    simp at ha

lemma one_eq_sum_pureState {R : Type*} [RCLike R] {k : ℕ} :
    ∑ i : Fin k, pureState_C (e i) (R := R) = 1 := by
  unfold pureState_C e
  ext i j
  simp only [Fin.isValue, conjTranspose_single, star_one, mulᵣ_eq, single_mul_single_same, mul_one]
  symm
  by_cases H : i = j
  · subst H
    simp only [one_apply_eq, single]
    rw [Finset.sum_apply] -- !
    simp
  · simp only [single]
    rw [Finset.sum_apply] -- !
    symm
    rw [one_apply_ne' fun a ↦ H ((Eq.symm a))]
    simp only [Finset.sum_apply, of_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, forall_const, forall_eq]
    exact H

lemma sum_one_sub₀ {R : Type*} [Ring R] {k : ℕ} (acc : Fin k)
    (f : Fin k → Matrix (Fin k) (Fin k) R) :
    ∑ i, f i - f acc = ∑ i, if i = acc then 0 else f i := by
  suffices  ∑ i, f i = (∑ i, if i = acc then 0 else f i) + f acc
      by rw [this];simp
  rw [← Finset.sum_add_sum_compl (s := {i | i ≠ acc})]
  simp only [ne_eq, Finset.compl_filter, Decidable.not_not]
  have : ∑ i with i = acc, f i =
      f acc := by
      have :  ∑ i with i = acc, f i
          =  ∑ i ∈ {acc}, f i := by
          congr
          ext;simp
      rw [this]
      rw [@Finset.sum_singleton]
  rw [this]
  simp only [_root_.add_left_inj]
  refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_
  · simp
  · intro i _
    simp
    tauto
  · intro i hi _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [if_neg hi]

lemma trace_one_sub_C {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hPS : ρ.PosSemidef) : 0 ≤ ((1 - pureState_C (e acc)) * ρ).trace := by
  rw [← one_eq_sum_pureState]
  rw [sum_one_sub₀]
  refine trace_mul_posSemidef_nonneg_general (by exact nonneg_iff_posSemidef.mpr hPS) ?_
  suffices (∑ i, if i = acc then
      (0 : Matrix (Fin k) (Fin k) R) else pureState_C (e i)).PosSemidef by
      exact nonneg_iff_posSemidef.mpr this
  refine posSemidef_sum Finset.univ ?_
  intro i _
  by_cases H : i = acc
  · subst H
    simp only [↓reduceIte]
    exact PosSemidef.zero
  · rw [if_neg H]
    refine posSemidef_of_isStarProjection_C (pureState_C (e i)) ?_
    exact pureState_projection_C i

theorem pure_trace_one_sub_re {R : Type*} [RCLike R] {k : ℕ} (acc : Fin k)
    {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) :
    0 ≤ RCLike.re ((1 - pureState_C (e acc)) * ρ).trace := by
  have := @trace_one_sub_C R _ k acc ρ hPS
  have := @RCLike.le_iff_re_im R _ 0 ((1 - pureState_C (e acc)) * ρ).trace
  simp at this
  tauto

theorem pure_trace_nonneg_re {R : Type*} [RCLike R] {k : ℕ} (acc : Fin k)
    {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) :
    0 ≤ RCLike.re (pureState_C (e acc) * ρ).trace := by
  have := (nonneg_trace_of_posSemidef_C hPS acc)
  have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e acc)) * ρ).trace
  simp at this
  tauto

/-- Positive operator (or projection) valued measure
as a probability mass function.
Technically the measure is valued in `Fin k`
although `pureState (e i)` can stand for `i`.
Could be generalized to let `e` be any orthonormal basis.

`pureState_psd` shows that it is a POVM.
`pureState_projection` shows that it is in fact a PVM for the standard
basis.
In fact `pureState_projection'` shows it's a projection
whenever the vectors have length 1.
-/
def POVM_PMF {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : 0 ≤ ρ) : PMF (Fin k) := by
  apply PMF.ofFintype (
    fun i => ofNNReal ⟨RCLike.re (pureState_C (e i) * ρ).trace,
      pure_trace_nonneg_re _ hPS.posSemidef⟩)
  apply ((toReal_eq_toReal_iff' (by simp) (by simp))).mp
  simp only [toReal_one]
  have := congrArg (RCLike.re) <| standard_basis_probability_one_C hUT
  simp only [map_sum, RCLike.one_re] at this ⊢
  rw [← this]
  apply toReal_sum
  simp


open scoped BigOperators

example {α} (s : Finset α) (f : α → NNReal) :
    ENNReal.ofNNReal (∑ x ∈ s, f x)
      = ∑ x ∈ s, ENNReal.ofNNReal (f x) := by
  exact coe_finset_sum

/-- Probability measure with "lost" trace in the last outcome. -/
def p {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hPS : 0 ≤ ρ) (i : Fin (k + 1)) : ℝ≥0∞ := by
    by_cases H : i = Fin.last _
    · exact some (1 - RCLike.re ρ.trace).toNNReal -- the "missing probability" is 1 - the trace
    · let i : Fin k := Fin.castPred i H
      exact ofNNReal ⟨RCLike.re (pureState_C (e i) * ρ).trace,
          pure_trace_nonneg_re _ hPS.posSemidef⟩

lemma p.ne_top
    {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hPS : 0 ≤ ρ) : ∑ a, p hPS a ≠ ⊤ := by
  simp only [p, some_eq_coe, ne_eq, sum_eq_top, Finset.mem_univ, true_and, not_exists]
  intro x
  split_ifs <;> simp

lemma trace_arithmetic {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) :
    (1 : ENNReal) = ↑(1 - RCLike.re ρ.trace).toNNReal + ↑(RCLike.re ρ.trace).toNNReal := by
  norm_cast
  rw [← Real.toNNReal_add]
  · simp
  · have him : RCLike.im ρ.trace = 0 :=
      RCLike.im_eq_zero_iff_isSelfAdjoint.mpr hPS.posSemidef.trace_nonneg.isSelfAdjoint
    generalize ρ.trace = A at *
    rw [← (RCLike.re_add_im_ax A)] at hUT
    rw [him] at hUT
    simp only [map_zero, zero_mul, add_zero] at hUT
    rw [← RCLike.ofReal_le_ofReal (K := R)]
    simp only [map_zero, map_sub, map_one, sub_nonneg]
    exact hUT
  refine (RCLike.re_nonneg_of_nonneg ?_).mpr ?_
  · refine hPS.posSemidef.trace_nonneg.isSelfAdjoint
  · refine hPS.posSemidef.trace_nonneg

/-- May 8, 2026.
Used to construct `POVM_PMF_withTop`.
-/
def POVM_PMF_withTop₀ {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) : PMF (Fin (k+1)) := by
  apply PMF.ofFintype (p hPS)
  apply (toReal_eq_toReal_iff' (p.ne_top _) one_ne_top).mp
  convert toReal_one
  unfold p
  rw [trace_arithmetic hUT hPS, Finset.sum_dite] --!!
  congr
  · rw [Finset.sum_subtype (p := fun x => x.1 = Fin.last k)]
    · rw [← toReal_eq_toReal_iff']
      · simp only [some_eq_coe, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, toReal_mul,
        toReal_natCast, coe_toReal, Real.coe_toNNReal']
        convert one_mul _
        rw [Nat.cast_eq_one]
        refine Fintype.card_eq_one_iff.mpr <| by simp
      · refine sum_ne_top.mpr <| by simp
      · simp
    · simp
  · rw [← standard_basis_probability_C,
        Finset.sum_subtype (p := fun x => x.1 ≠ Fin.last k)]
    · have : ofNNReal (∑ x, RCLike.re (pureState_C (e x) * ρ).trace).toNNReal
           = ∑ x, ofNNReal (RCLike.re (pureState_C (e x) * ρ).trace).toNNReal := by
        rw [← coe_finset_sum]
        congr
        refine Real.toNNReal_sum_of_nonneg fun _ _ => pure_trace_nonneg_re _ hPS.posSemidef
      simp only [ne_eq, map_sum]
      rw [this]
      apply Function.Bijective.finset_sum
        (e := fun ⟨x,hx⟩ => ⟨x.1.1, Fin.val_lt_last hx⟩)
      · constructor
        · intro ⟨x,hx⟩
          simp only [Fin.mk.injEq, Subtype.forall, Subtype.mk.injEq, Finset.mem_filter,
            Finset.mem_univ, true_and, forall_self_imp]
          exact fun _ _ => SetLike.coe_eq_coe.mp ∘ Fin.eq_of_val_eq
        · intro x
          simp only [Subtype.exists, Finset.mem_filter, Finset.mem_univ, true_and, exists_idem]
          use Fin.castSucc x
          simp
      · intro ⟨x,hx⟩
        congr
        rw [max_eq_left (pure_trace_nonneg_re _ hPS.posSemidef)]
        congr
    · simp
    · exact Subtype.fintype _

/-- A PMF where the probability of `none` is the probability lost due
to trace decrease. -/
def POVM_PMF_withTop {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) : PMF (Option (Fin k)) :=
  PMF.map (f := fun (i : Fin (k + 1)) => dite (i = Fin.last k) (fun _ => none)
    fun hi => some <| Fin.castPred i hi)
  <| POVM_PMF_withTop₀ hUT hPS


/-- POVM_PMF_withTop API, part 1:
The lost probability is 1 - the trace. -/
lemma POVM_PMF_withTop_none {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) :
    POVM_PMF_withTop hUT hPS none = (RCLike.re ((1:R) - ρ.trace)).toNNReal := by
  unfold POVM_PMF_withTop POVM_PMF_withTop₀ p
  simp only [some_eq_coe, PMF.map_ofFintype, PMF.ofFintype_apply, dite_eq_left_iff, reduceCtorEq,
    imp_false, Decidable.not_not]
  have : Finset.univ.filter (fun a => a = Fin.last k) = {Fin.last k} := by
    ext
    simp
  rw [this]
  simp

/-- POVM_PMF_withTop API, part 2:
If the trace is one then no probability is lost. -/
lemma POVM_PMF_withTop_none₀ {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : 0 ≤ ρ) :
    POVM_PMF_withTop (ge_of_eq hUT.symm) hPS none = 0 := by
  rw [POVM_PMF_withTop_none, hUT]
  simp

/-- POVM_PMF_withTop API, part 3.
If the trace is zero then all probability is lost.
-/
lemma POVM_PMF_withTop_none₁ {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 0) (hPS : 0 ≤ ρ) :
    POVM_PMF_withTop (by rw [hUT];simp) hPS none = 1 := by
  rw [POVM_PMF_withTop_none, hUT]
  simp



/-- Feb 1, 2026. An analogous construction from May 8, 2026 uses `PMF (Fin (k+1))`. -/
noncomputable def POVM_subPMF {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : 0 ≤ ρ) : subPMF (Fin k) := by
  apply subPMF.ofFintype _ (
      fun i => ofNNReal ⟨RCLike.re (pureState_C (e i) * ρ).trace, by
          let t := (pureState_C (e i) * ρ).trace
          have : 0 ≤ t := by
              have := nonneg_trace_of_posSemidef_C hPS i
              convert this
              simp
          refine (RCLike.re_nonneg_of_nonneg ?_).mpr this
          exact LE.le.isSelfAdjoint this⟩)
  show ∑ a, ofNNReal ⟨RCLike.re (pureState_C (e a) * ρ).trace, _⟩ ≤ 1
  apply le_of_eq_of_le (α := ENNReal) --(b := ofNNReal ⟨RCLike.re ρ.trace, sorry⟩)
  · have := @toReal_eq_toReal_iff' (∑ a, ofNNReal
      ⟨RCLike.re (pureState_C (e a) * ρ).trace, by
          have := @nonneg_trace_of_posSemidef_C R _ k ρ (LE.le.posSemidef hPS)
              a
          have := (@RCLike.le_iff_re_im R _ 0 (w := (pureState_C (e a) * ρ).trace)).mp (by
              tauto)
          simp at this
          tauto⟩)
      (ofNNReal ⟨RCLike.re ρ.trace, by
          have : 0 ≤ ρ.trace := by
              refine PosSemidef.trace_nonneg ?_
              exact LE.le.posSemidef hPS
          have := (@RCLike.le_iff_re_im R _ 0 (w := ρ.trace)).mp this
          simp at this
          tauto⟩) (by simp) (by simp)
    rw [← this]
    simp only [coe_toReal, NNReal.coe_mk]
    have := @standard_basis_probability_general R _ k ρ
    have := congrArg (RCLike.re) this
    simp only [map_sum] at this ⊢
    simp_rw [← this]
    refine toReal_sum ?_
    simp
  · have := (@RCLike.le_iff_re_im R _ (z := ρ.trace) (w := 1)).mp hUT
    simp at this
    tauto

def POVM_PMF' {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : ρ.PosSemidef) : PMF (Fin k) :=
  POVM_PMF (R := R) hUT (nonneg_iff_posSemidef.mpr hPS)

def POVM_subPMF' {R : Type*} [RCLike R]
    {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : ρ.PosSemidef) : subPMF (Fin k) :=
  POVM_subPMF (R := R) hUT (by exact nonneg_iff_posSemidef.mpr hPS)


lemma PMF₂₃help {R : Type*} [RCLike R] {ρ : Matrix (Fin 3) (Fin 3) R}
    (hPS : ρ.PosSemidef) :
    0 ≤ ((pureState_C (e 0) + pureState_C (e 1)) * ρ).trace := by
  apply trace_mul_posSemidef_nonneg_general (nonneg_iff_posSemidef.mpr hPS)
  apply nonneg_iff_posSemidef.mpr <| (pureState_psd_C _).add (pureState_psd_C _)








lemma ofReal_inj_aux {k : ℕ} (J : Fin k → ℝ) (hnn : ∀ a, J a ≥ 0) :
    ∑ a, (⟨J a, hnn a⟩ : NNReal) =
    ⟨∑ a, J a, Fintype.sum_nonneg hnn⟩ := by
  refine Eq.symm (Subtype.ext ?_)
  simp only [NNReal.val_eq_coe]
  rw [← @RCLike.ofReal_inj ℝ _ _ (∑ a, ⟨J a, hnn a⟩ : NNReal)]
  simp

/-- Had to make this lemma as it seems missing in Mathlib. -/
theorem RCLike.re_sum {R : Type*} [RCLike R] {α : Type*}
    (s : Finset α) (f : α → R) :
    RCLike.re (∑ i ∈ s, f i) = ∑ i ∈ s, RCLike.re (f i) :=
  map_sum RCLike.re f s

/-- Had to make this lemma as it seems missing in Mathlib. -/
theorem RCLike.sub_re {R : Type*} [RCLike R] (z w : R) :
    RCLike.re (z - w) = RCLike.re z - RCLike.re w :=
  AddMonoidHom.map_sub re z w

theorem Finset.sum_erase_sub {k : ℕ} (c : Fin k)
       (J : Fin k → ℝ) : ∑ i : Fin k, J i - J c
      = ∑ i : Fin k with i ≠ c, J i := by
    suffices ∑ i, J i = ∑ i with i ≠ c, J i + J c by linarith
    rw [← Finset.sum_erase_add (a := c)]
    · congr
      ext
      simp
    · simp

lemma PMF_of_state.sum_one_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : ρ.PosSemidef) :
    ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace,
        pure_trace_one_sub_re _ hPS⟩
      ⟨RCLike.re (     pureState_C (e acc)  * ρ).trace,
        pure_trace_nonneg_re _ hPS⟩) = 1 := by
  rw [← toReal_eq_toReal_iff']
  · simp only [Fin.isValue, Fin.sum_univ_two, ↓reduceIte, one_ne_zero, toReal_one]
    have : RCLike.re (∑ a, (pureState_C (e a) * ρ).trace) = 1 := by
      rw [standard_basis_probability_one_C hUT]
      simp
    rw [← this]
    simp_rw [← one_eq_sum_pureState]
    have (j : Fin k) : pureState_C (e j) = (pureState_C ∘ e (R := R)) j := by
        simp
    simp_rw [this] at *
    have hnn (a : Fin k) : 0 ≤ RCLike.re ((pureState_C ∘ e (R := R)) a * ρ).trace := by
        have := (@nonneg_trace_of_posSemidef_C R _ k ρ hPS a)
        have := @RCLike.le_iff_re_im R _ 0 ((pureState_C (e a)) * ρ).trace
        simp at this
        tauto
    generalize (pureState_C ∘ e (R := R)) = f at *
    rw [RCLike.re_sum]
    simp_rw [sub_mul, trace_sub]
    have h₁ : (∑ a, ofNNReal ⟨RCLike.re (f a * ρ).trace, hnn _⟩ ).toReal
             = ∑ a,           RCLike.re (f a * ρ).trace := by
        rw [toReal_sum] <;> simp
    rw [← h₁]
    congr
    rw [← coe_finset_sum]
    ring_nf
    simp_rw [Matrix.sum_mul Finset.univ f ρ,
      RCLike.sub_re, trace_sum, RCLike.re_sum,
      Finset.sum_erase_sub acc (fun a => RCLike.re (f a * ρ).trace)]
    rw [← coe_add]
    congr
    rw [Nonneg.mk_add_mk, ofReal_inj_aux]
    congr
    apply add_eq_of_eq_sub
    rw [Finset.sum_erase_sub]
  · simp
  · simp


theorem trace_nonneg_re {R : Type*} [RCLike R] {k : ℕ}
    {ρ : Matrix (Fin k) (Fin k) R} (hPS : ρ.PosSemidef) :
    0 ≤ RCLike.re ρ.trace := by
  have := (RCLike.le_iff_re_im).mp (PosSemidef.trace_nonneg hPS)
  rw [map_zero] at this
  exact this.1

open RCLike
 -- don't really need `subPMF` even with `subNormalizedDensityMatrix`
 --    For some reason we don't need `ρ.trace ≤ 1`.
lemma PMF_of_state.sum_one_general_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hPS : ρ.PosSemidef) :
    ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace, pure_trace_one_sub_re acc hPS⟩
      ⟨RCLike.re (     pureState_C (e acc)  * ρ).trace, pure_trace_nonneg_re acc hPS⟩)
                         = ofNNReal ⟨RCLike.re ρ.trace, trace_nonneg_re hPS⟩ := by
  have := @standard_basis_probability_general R _ k ρ
  simp only [Fin.isValue, Fin.sum_univ_two, ↓reduceIte, one_ne_zero]
  refine (toReal_eq_toReal_iff' (by simp) (by simp)).mp ?_
  have (x y : ENNReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (x + y).toReal = x.toReal + y.toReal := by
        exact toReal_add hx hy
  rw [this _ _ (by simp) (by simp)]
  simp only [coe_toReal, NNReal.coe_mk]
  rw [sub_mul]
  rw [trace_sub]
  simp

noncomputable def PMF_of_state_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace,
        pure_trace_one_sub_re acc hPS⟩
      ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace,
        pure_trace_nonneg_re acc hPS
      ⟩)
  apply PMF_of_state.sum_one_general _ hUT hPS

/-- May 9, 2026 -/
noncomputable def PMF_of_state_CPTNI {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : PMF (Option (Fin 2)) := by
  -- 3 cases: accept, not accept, and `none`
  apply PMF.ofFintype (fun i : Option (Fin 2) => ofNNReal <|
    ite (i = some 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace,
        pure_trace_one_sub_re acc hPS⟩
   (ite (i = some 1)
      ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace,
        pure_trace_nonneg_re acc hPS
      ⟩
   (RCLike.re (1 - ρ.trace)).toNNReal))
  have h₀ := @PMF_of_state.sum_one_general_general R _ k acc ρ hPS
  rw [Fin.sum_univ_two] at h₀
  have (f : Option (Fin 2) → ENNReal) :
    ∑ i, f i = f none + (f (some 0) + f (some 1)) := by
      rw [Fintype.sum_option]
      congr
      exact Fin.sum_univ_two fun i ↦ f (some i)
  rw [this]; clear this
  simp_all only [Fin.isValue, ↓reduceIte, one_ne_zero, reduceCtorEq, map_sub, one_re,
    Option.some.injEq]
  have h₀ :  0 ≤ 1 - re ρ.trace := by
    have h₁ : ρ.trace = RCLike.re ρ.trace + RCLike.im ρ.trace * RCLike.I   := by
      exact Eq.symm (re_add_im_ax ρ.trace)
    rw [conj_eq_iff_im.mp hPS.trace_nonneg.isSelfAdjoint] at h₁
    rw [h₁] at hUT
    simp at hUT ⊢
    norm_cast at hUT ⊢
  rw [Real.toNNReal_of_nonneg h₀]
  norm_cast
  rw [Nonneg.mk_add_mk]
  simp

  -- apply PMF_of_state.sum_one_general _ hUT hPS

/-- To use conditional computability here we would need to know the state
had positive trace. -/
noncomputable def subPMF_of_state_general {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : subPMF (Fin 2) := by
  apply subPMF.ofFintype _ (fun i => ofNNReal <| ite (i = 0)
      ⟨RCLike.re ((1 - pureState_C (e acc)) * ρ).trace,
        pure_trace_one_sub_re acc hPS⟩
      ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace,
        pure_trace_nonneg_re acc hPS⟩)
  rw [PMF_of_state.sum_one_general_general _ hPS]
  convert ((@RCLike.le_iff_re_im R _ (w := 1) (z := ρ.trace)).mp hUT).1
  simp
  rfl


/-- Feb 1, 2026: nonincreasing trace operators and a PMF. -/
noncomputable def PMF_of_state_bern {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : PMF (Bool) := by
  apply PMF.bernoulli (p := ⟨RCLike.re ((pureState_C (e acc)) * ρ).trace, by
        exact pure_trace_nonneg_re acc hPS⟩)
  have := (@RCLike.le_iff_re_im R _ (w := 1) (z := ρ.trace)).mp hUT
  simp only [one_re, one_im, ge_iff_le] at this ⊢
  suffices re (pureState_C (e acc) * ρ).trace ≤ 1 by
    exact NNReal.coe_le_one.mp this
  apply le_trans (b := re ρ.trace)
  · suffices (pureState_C (e acc) * ρ).trace ≤ ρ.trace by
      have := @RCLike.le_iff_re_im R _ (w := ρ.trace)
        (z := (pureState_C (e acc) * ρ).trace)
      simp at this
      tauto
    apply sub_nonneg.mp
    suffices 0 ≤ (1 * ρ).trace - (pureState_C (e acc) * ρ).trace by
      convert this
      simp
    rw [← trace_sub]
    suffices 0 ≤ ((1 - pureState_C (e acc)) * ρ).trace by
      convert this using 1
      congr
      exact Eq.symm (Matrix.sub_mul 1 (pureState_C (e acc)) ρ)
    set M := (1 : Matrix (Fin k) (Fin k) R) - pureState_C (e acc)
    have : M.PosSemidef := by
      unfold M
      refine posSemidef_of_isStarProjection_C (1 - pureState_C (e acc)) ?_
      refine IsStarProjection.one_sub ?_
      exact pureState_projection_C acc
    exact trace_one_sub_C acc hPS
  · exact this.1

/-- Projection-valued measure. -/
structure PVM where
-- The dimension
  k : ℕ
-- The PSD state we're in
  ρ : Matrix (Fin k) (Fin k) ℝ
  hρ : ρ.PosSemidef
-- The projections (states)
  t : ℕ
  op : Fin t → Matrix (Fin k) (Fin k) ℝ
  pf : ∀ i, IsStarProjection (op i)
-- The measure
  p : PMF (Fin t)
  pf' : ∀ i, p i = ofNNReal ⟨(op i * ρ).trace, by
      apply trace_mul_nonneg hρ
      apply pf⟩

/-- Projection-valued measure. In this version we allow non-probability measures. -/
structure PVMeas where
-- The dimension
  k : ℕ
-- The PSD state we're in
  ρ : Matrix (Fin k) (Fin k) ℝ
  hρ : ρ.PosSemidef
-- The projections (states)
  t : ℕ
  op : Fin t → Matrix (Fin k) (Fin k) ℝ
  pf : ∀ i, IsStarProjection (op i)
-- The measure
  p : MeasureTheory.Measure (Fin t)
  pf' : ∀ i, p {i} = ofNNReal ⟨(op i * ρ).trace, by
      apply trace_mul_nonneg hρ
      apply pf⟩

/-- Projection-valued measure. In this version we allow non-probability measures. -/
structure PVMeas_C {R : Type*} [RCLike R] where
-- The dimension
  k : ℕ
-- The PSD state we're in
  ρ : Matrix (Fin k) (Fin k) R
  hρ : ρ.PosSemidef
-- The projections (states)
  t : ℕ
  op : Fin t → Matrix (Fin k) (Fin k) R
  pf : ∀ i, IsStarProjection (op i)
-- The measure
  p : MeasureTheory.Measure (Fin t)
  pf' : ∀ i, p {i} = ofNNReal ⟨RCLike.re (op i * ρ).trace, by
    have h₀ := (trace_mul_nonneg_C hρ (pf i))
    have := @RCLike.le_iff_re_im R _ 0 ((op i * ρ).trace)
    simp at this
    tauto
⟩

structure PVM_C {R : Type*} [RCLike R] where
  k : ℕ -- the dimension
  ρ : Matrix (Fin k) (Fin k) R          -- the state we're in
  hρ : ρ.PosSemidef
  t : ℕ -- the number of projections (states)
  op : Fin t → Matrix (Fin k) (Fin k) R -- the projections

  pf : ∀ i, IsStarProjection (op i)     -- ... are projections

  p : PMF (Fin t)                                       -- the measure
  pf' : ∀ i, p i = ofNNReal ⟨RCLike.re (op i * ρ).trace, by
    have h₀ := (trace_mul_nonneg_C hρ (pf i))
    have := @RCLike.le_iff_re_im R _ 0 ((op i * ρ).trace)
    simp at this
    tauto
    ⟩

/-- May 9, 2026. -/
structure PVM_CPTNI {R : Type*} [RCLike R] where
  k : ℕ -- the dimension
  ρ : Matrix (Fin k) (Fin k) R          -- the state we're in
  hρ : ρ.PosSemidef
  t : ℕ -- the number of projections (states)
  op : (Fin t) → Matrix (Fin k) (Fin k) R -- the projections

  pf : ∀ i, IsStarProjection (op i)     -- ... are projections

  p : PMF (Option (Fin t))                                       -- the measure
  pf' : ∀ i : Fin t, p i = ofNNReal ⟨RCLike.re (op i * ρ).trace, by
    have h₀ := (trace_mul_nonneg_C hρ (pf i))
    have := @RCLike.le_iff_re_im R _ 0 ((op i * ρ).trace)
    simp at this
    tauto
    ⟩

theorem trace_real_of_projection_and_pos_semidef {R : Type*} [RCLike R]
  {k : ℕ}
  {ρ O : Matrix (Fin k) (Fin k) R}
  (g₀ : ρ.IsHermitian) (g₁ : O.IsHermitian) :
  (O * ρ).trace = star (O * ρ).trace := by
    suffices h_trace : Matrix.trace ((O * ρ).conjTranspose) = Matrix.trace (O * ρ) by
      convert h_trace.symm using 1 ; simp [Matrix.trace ];
      simp [Matrix.mul_apply, mul_comm ];
    simp_all only [IsHermitian, conjTranspose_mul];
    rw [ Matrix.trace_mul_comm ]

/-- The probability is given as a real part of a complex number.
Fortunately, the imaginary part is zero. -/
lemma im_zero_PVM {R : Type*} [RCLike R] (M : PVM_C (R := R)) :
    ∀ i, RCLike.im (M.op i * M.ρ).trace = 0 := by
    intro i
    apply RCLike.conj_eq_iff_im.mp
    symm
    apply trace_real_of_projection_and_pos_semidef
      M.hρ.isHermitian <| isHermitian_iff_isSelfAdjoint.mpr
        (M.pf i).isSelfAdjoint



noncomputable def myPVM_C {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM_C (R := R) := {
  k := k
  t := k
  p := POVM_PMF' hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState_C (e i)
  pf := by exact fun i ↦ pureState_projection_C i
  pf' := by intro i; rfl
}

noncomputable def myPVMeas_C_trace_one {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVMeas_C (R := R) := {
  k := k
  t := k
  p := (POVM_PMF' hUT hPS).toMeasure
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState_C (e i)
  pf := by exact fun i ↦ pureState_projection_C i
  pf' := by intro i; simp; rfl
}

-- noncomputable def myPVMeas_C {R : Type*} [RCLike R] {k : ℕ} {ρ : Matrix (Fin k) (Fin k) R}
--     (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : PVMeas_C (R := R) := {
--   k := k
--   t := k
--   p := sorry --(POVM_PMF' hUT hPS).toMeasure
--   ρ := ρ
--   hρ := hPS
--   op := fun i : Fin k => pureState_C (e i)
--   pf := by exact fun i ↦ pureState_projection_C i
--   pf' := by sorry --intro i; simp; rfl
-- }


noncomputable def PVM_of_state_C {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM_C (R := R) := {
  k := k
  t := 2
  p := PMF_of_state_general acc hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (1 - pureState_C (e acc)) <| pureState_C (e acc)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte];
      refine IsStarProjection.one_sub ?_
      exact pureState_projection_C _
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte];
      exact pureState_projection_C acc
  pf' := by
    intro i
    fin_cases i
    · unfold PMF_of_state_general
      simp
    · rfl
}

/-- May 9, 2026. -/
noncomputable def PVM_of_state_CPTNI {R : Type*} [RCLike R]
    {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) R}
    (hUT : ρ.trace ≤ 1) (hPS : Matrix.PosSemidef ρ) : PVM_CPTNI (R := R) := {
      ρ := ρ
      k := k
      hρ := hPS
      t := 2
      p := PMF_of_state_CPTNI (R := R) acc hUT hPS
      op := fun i : Fin 2 => ite (i=0)
        (1 - pureState_C (e acc)) <| pureState_C (e acc)
      pf := fun i ↦ by
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte];
          refine IsStarProjection.one_sub ?_
          exact pureState_projection_C _
        · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte];
          exact pureState_projection_C acc
      pf' := by
        intro i
        fin_cases i
        · unfold PMF_of_state_CPTNI
          simp
        · rfl
    }

def languageAcceptedBy_C {R : Type*} [RCLike R] {α : Type*}
  {q r : ℕ} (acceptStateIndex : Fin q.succ)
  (𝓚 : α → Fin r → Matrix (Fin q.succ) (Fin q.succ) R) :=
  {word : Σ n : ℕ, (Fin n → α) |
    krausApplyWord word.2 𝓚 (pureState_C (e 0)) = pureState_C (e acceptStateIndex)}


theorem basisState_trace_one_C {R : Type*} [RCLike R] {k : ℕ} {i : Fin k.succ} :
    (pureState_C (e (i : Fin k.succ)) (R := R)).trace = 1 := by
  unfold pureState_C e
  have : ((single (i:Fin k.succ) (0:Fin 1) (1:R)).mulᵣ
          (single (i:Fin k.succ) (0:Fin 1) 1)ᴴ)
      = Matrix.of (fun a b => ite (a = i) (ite (b = i) 1 0) 0
      ) := by
      ext i j
      unfold mulᵣ dotProductᵣ single
      simp
      split_ifs
      all_goals tauto
  simp_rw [this, trace]
  simp


noncomputable def PVM_of_word_of_channel_C
    {R : Type*} [RCLike R]
    {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R}
    (h𝓚 : ∀ (a : α), QuantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM_C (R := R) := by
  have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
      (ρ := ⟨pureState_C (e 0),⟨pureState_psd_C _, basisState_trace_one_C⟩⟩)
        (h𝓚 := h𝓚)
  exact @PVM_of_state_C R _ k.succ acc
      (@krausApplyWord α R _ _ _ word.1 k.succ r word.2 𝓚 (pureState_C (e 0)))
      this.2 this.1

def MOlanguageAcceptedBy_C {R : Type*} [RCLike R] {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R}
    (h𝓚 : ∀ a, QuantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (PVM_of_word_of_channel_C acc (h𝓚) word).p (1 : Fin 2) > 1/2}


noncomputable def PVM_of_word_of_operation
    {R : Type*} [RCLike R]
    {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R}
    (h𝓚 : ∀ (a : α), QuantumOperation (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) :
    PVM_CPTNI (R := R) :=
  have h₁ := krausApplyWord_subNormalizedDensityMatrix
    word.2 h𝓚 ⟨pureState_C (e 0), ⟨pureState_psd_C (e 0), le_of_eq basisState_trace_one_C⟩⟩
  PVM_of_state_CPTNI acc h₁.2 h₁.1

/-- May 9, 2026.
Language accepted by a family of quantum operations, as opposed to quantum channels.
-/
def MOlanguageAcceptedBy_CPTNI {R : Type*} [RCLike R] {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R}
    (h𝓚 : ∀ a, QuantumOperation (𝓚 a)) :=
  {word | (PVM_of_word_of_operation acc (h𝓚) word).p (some (1 : Fin 2)) > 1/2}

def exampleLanguage₀ := @MOlanguageAcceptedBy_CPTNI ℂ _ (Fin 1) 1 0 0 (fun _ _ => !![1]) (by
    intro z
    apply le_of_eq
    ext x y; fin_cases x; fin_cases y
    simp [mul_apply])

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

/-- The matrix !![1 / 2] has trace < 1, but
we are able to use it to define a language:
-/
def exampleLanguage₁ := @MOlanguageAcceptedBy_CPTNI
  ℂ _ (Fin 1) 1 0 0 (fun _ _ => !![1 / 2])
  (by
    intro z
    simp only [QuantumOperation, Nat.succ_eq_add_one, Nat.reduceAdd, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, one_div, Finset.sum_const, Finset.card_singleton, one_smul]
    have : !![(2:ℂ)⁻¹]ᴴ * !![2⁻¹] = !![4⁻¹] := by
      ext i j
      fin_cases i; fin_cases j
      rw [← mulᵣ_eq, mulᵣ]
      simp [dotProduct]
      field_simp
      ring_nf
    rw [this]
    suffices 0 ≤ 1 - !![(4:ℂ)⁻¹] by simp at this;tauto
    have : (1 : Matrix (Fin 1) (Fin 1) ℂ) = !![1] := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this]
    simp only [of_sub_of, sub_cons, head_cons, tail_cons, sub_self, zero_empty, ge_iff_le]
    rw [matrix_1x1_nonneg_iff]
    simp only [sub_nonneg]
    refine inv_le_one_of_one_le₀ ?_
    exact Nat.one_le_ofNat
    )


example (a _ : ℕ) (h : a = 0) :
  (match a with
  |0 => (5:ℝ)
  |Nat.succ _ => 1)
  = 5 := by simp_all only


/--
May 10, 2026.
Even though there is only one state
and it is accepting, because of the trace-loss
the length-one word is not accepted :) -/
lemma exampleLanguage₁_length_one (word : Fin 1 → Fin 1) :
  ¬ ⟨1, word⟩ ∈ exampleLanguage₁ := by
  unfold exampleLanguage₁ MOlanguageAcceptedBy_CPTNI
    PVM_of_word_of_operation PVM_of_state_CPTNI PMF_of_state_CPTNI
  have : e (0 : Fin 1) = !![(1 : ℂ)] := by
    ext x y; fin_cases x; fin_cases y; simp [e]
  simp_rw [this]
  have : word = ![0] := by ext x; fin_cases x; simp
  rw [this]
  have : pureState_C !![(1:ℂ)] = ![1] := by
    unfold pureState_C
    ext x y
    fin_cases x; fin_cases y
    simp [conjTranspose, vecMul]
  simp_rw [this]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, one_div, re_to_complex,
    Complex.sub_re, Complex.one_re, PMF.ofFintype_apply, Option.some.injEq, one_ne_zero, ↓reduceIte,
    gt_iff_lt, Set.mem_setOf_eq, not_lt, le_inv_iff_mul_le, ge_iff_le]
  unfold krausApplyWord
  have : Fin.init ![(0 : Fin 1)] = ![] := by ext z; fin_cases z
  rw [this]
  unfold krausApplyWord krausApply conjTranspose
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, Matrix.map, transpose_apply, of_apply,
    cons_val', cons_val_fin_one, star_inv₀, star_ofNat, vecMul_vecMul, Finset.sum_const,
    Finset.card_singleton, one_smul, ge_iff_le]
  have : ofNNReal ⟨(!![(2:ℂ)⁻¹ * 2⁻¹]).trace.re, by simp⟩ * 2 ≤ 1 := by
    simp only [trace_fin_one_of, Complex.mul_re, Complex.inv_re, Complex.re_ofNat,
      Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat, neg_zero,
      zero_div, mul_zero, sub_zero]
    have : ((2:ℝ)⁻¹ * 2⁻¹) = (2 * 2)⁻¹ := by simp
    simp_rw [this]
    have : (2:ℝ) * 2 = 4 := by linarith
    simp_rw [this]
    refine le_inv_iff_mul_le.mp ?_
    have : ofNNReal ⟨4⁻¹, by simp⟩
      = (4⁻¹ : ENNReal) := by
        refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
        all_goals simp
    rw [this]
    refine ENNReal.inv_le_inv.mpr ?_
    norm_cast
  convert this using 1
  congr
  ext x y
  fin_cases x; fin_cases y
  repeat rw [← mulᵣ_eq, mulᵣ]
  simp [dotProduct, vecHead]





/-- If the start and accept states are the same then
the empty string is accepted in the measure-once setting. -/
lemma MO_language_nonempty_C {α : Type*} {r k : ℕ}
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℂ}
    (h𝓚 : ∀ a, QuantumChannel (𝓚 a)) :
  MOlanguageAcceptedBy_C 0 h𝓚 ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty'.mp ?_
  refine nonempty_subtype.mpr ?_
  use ⟨0,![]⟩
  unfold MOlanguageAcceptedBy_C PVM_of_word_of_channel_C
  unfold PVM_of_state_C PMF_of_state_general
  simp only [Nat.succ_eq_add_one, Fin.isValue, Lean.Elab.WF.paramLet, PMF.ofFintype_apply,
    one_ne_zero, ↓reduceIte, one_div, gt_iff_lt, Set.mem_setOf_eq]
  unfold krausApplyWord
  have : pureState_C (e (0 : Fin k.succ)) * pureState_C (e 0) (R := ℂ) = pureState_C (e 0) :=
    (pureState_projection_C (0 : Fin k.succ) (R := ℂ)).1
  simp_rw [this]
  simp_rw [basisState_trace_one_C]
  simp
