import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

def quantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    (K : r → Matrix q q R) :=
  ∑ i, (K i)ᴴ * K i = 1

def quantumOperation {R : Type*} [RCLike R]
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

lemma quantumChannel.trace_eq
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : quantumChannel K)
    (ρ : Matrix (Fin q) (Fin q) R) :
  (krausApply K ρ).trace = ρ.trace := by
  unfold krausApply
  rw [trace_sum]
  simp_rw [fun i => trace_mul_cycle (C := (K i)ᴴ) (B := ρ) (A := K i)]
  rw [← trace_sum, ← Matrix.sum_mul, hK]
  simp

lemma quantumChannel.trace_eq_one
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : quantumChannel K)
    (ρ : Matrix (Fin q) (Fin q) R) (hρ : ρ.trace = 1) :
    (krausApply K ρ).trace = 1 :=
  quantumChannel.trace_eq hK ρ ▸ hρ

/-- Realizing a quantumChannel as a map on densityMatrices. -/
def krausApply_densityMatrix
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hK : quantumChannel K)
    (ρ : densityMatrix (Fin q) (R := R)) : densityMatrix (Fin q) (R := R) :=
  ⟨krausApply K ρ.1, ⟨krausApply.posSemidef K ρ.2.1,
   quantumChannel.trace_eq_one hK ρ.1 ρ.2.2⟩⟩


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
    (h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (ρ : densityMatrix (Fin q)) :
    (krausApplyWord word 𝓚 ρ.1).PosSemidef ∧ (krausApplyWord word 𝓚 ρ.1).trace = 1 := by
  induction n with
  | zero => exact ρ.2
  | succ n ih =>
    exact (krausApply_densityMatrix (h𝓚 _)
      ⟨krausApplyWord (Fin.init word) 𝓚 ρ.1, ih (Fin.init word)⟩).2

/-- Using a family of quantum channels,
we can iterate over a word and stay within the density matrices. -/
def krausApplyWord_map {α : Type*}
    {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddLeftMono R]
    {n q r : ℕ} (word : Fin n → α)
    (𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R)
    (hq : ∀ a, quantumChannel (𝓚 a))
    (ρ : densityMatrix (Fin q) (R := R)) : densityMatrix (Fin q) (R := R) :=
  ⟨krausApplyWord word 𝓚 ρ.1, krausApplyWord_densityMatrix _ hq _⟩

def e {R : Type*} [One R] [Zero R] {k : ℕ} : Fin k → Matrix (Fin k) (Fin 1) R :=
  fun i => single i 0 1
-- Move pureState to a file Real.lean

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

/-- Feb 1, 2026 -/
lemma quantumOperation_reduces_trace {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : quantumOperation K)
    {ρ : Matrix (Fin q) (Fin q) R} (hρ : 0 ≤ ρ) :
    (krausApply K ρ).trace ≤ ρ.trace := by
  unfold quantumOperation at hK
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

lemma quantumOperation_preserves_trace_le_one
    {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : quantumOperation K)
    {ρ : Matrix (Fin q) (Fin q) R} (hρ : 0 ≤ ρ)
    (hρ₁ : ρ.trace ≤ 1) : (krausApply K ρ).trace ≤ 1 :=
  le_trans (quantumOperation_reduces_trace hK hρ) hρ₁

/--
Feb 1, 2026
Realizing a quantumChannel as a map on densityMatrices. -/
def krausApply_subNormalizedDensityMatrix {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : quantumOperation K)
    (ρ : subNormalizedDensityMatrix (Fin q) (R := R)) :
    subNormalizedDensityMatrix (Fin q) (R := R) :=
  ⟨krausApply K ρ.1, krausApply.posSemidef K ρ.2.1,
    quantumOperation_preserves_trace_le_one hK
      (Matrix.nonneg_iff_posSemidef.mpr ρ.2.1) ρ.2.2
   ⟩

theorem krausApplyWord_subNormalizedDensityMatrix {α : Type*}
    {R : Type*} [RCLike R] {n q r : ℕ} (word : Fin n → α)
    {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R} (h𝓚 : ∀ (a : α), quantumOperation (𝓚 a))
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
    {𝓚 : α → Fin r → Matrix (Fin q) (Fin q) R} (h𝓚 : ∀ a, quantumOperation (𝓚 a))
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
lemma standard_basis_probability_one_C {R : Type*} [RCLike R] {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) R} (hUT : ρ.trace = 1) :
  ∑ a, (pureState_C (e a) * ρ).trace = 1 := by
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

/-- Feb 1, 2026 -/
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
  POVM_PMF (R := R) hUT (by exact nonneg_iff_posSemidef.mpr hPS)

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
    (h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM_C (R := R) := by
  have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
      (ρ := ⟨pureState_C (e 0),⟨pureState_psd_C _, basisState_trace_one_C⟩⟩)
        (h𝓚 := h𝓚)
  exact @PVM_of_state_C R _ k.succ acc
      (@krausApplyWord α R _ _ _ word.1 k.succ r word.2 𝓚 (pureState_C (e 0)))
      this.2 this.1

def MOlanguageAcceptedBy_C {R : Type*} [RCLike R] {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) R}
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (PVM_of_word_of_channel_C acc (h𝓚) word).p (1 : Fin 2) > 1/2}

/-- If the start and accept states are the same then
the empty string is accepted in the measure-once setting. -/
lemma MO_language_nonempty_C {α : Type*} {r k : ℕ}
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℂ}
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) :
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
