import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Kraus.Basic
/-!

# Real

Here we use the transpose rather than the complex conjugate transpose.

-/

open Matrix MatrixOrder ComplexOrder


noncomputable section


def pureState {R : Type*} [Mul R] [Add R] [Zero R] {k : ℕ} (e : Matrix (Fin k) (Fin 1) R) :=
    mulᵣ e e.transpose

lemma pureState_selfAdjoint {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) :
    Matrix.IsHermitian (pureState e) := by
  simp [Matrix.IsHermitian, pureState]

def pureState_projection' {k : ℕ} (e : EuclideanSpace ℝ (Fin k)) (he : ‖e‖ = 1) :
    IsStarProjection (pureState (fun (i : Fin k) (_ : Fin 1) => e i)) := {
      isIdempotentElem := by
        unfold pureState
        simp
        simp [IsIdempotentElem];
        simp [← Matrix.ext_iff, Matrix.mul_apply ];
        simp [← mul_assoc,
          ← Finset.sum_mul];
        simp [mul_assoc, ← Finset.mul_sum _ _ _,
          EuclideanSpace.norm_eq ] at he ⊢;
        simp [← sq, he ]
      isSelfAdjoint := by apply pureState_selfAdjoint
  }

lemma pureState_projection {k : ℕ} (i : Fin k) :
  IsStarProjection (pureState (e i) (R := ℝ)) := {
      isIdempotentElem := by
        unfold IsIdempotentElem pureState e
        simp
      isSelfAdjoint := by apply pureState_selfAdjoint
  }


/-- Projection onto span ⟨e₁, e₂⟩ is indeed a star-projection.
So we could form a PMF with two outcomes (e₁,e₂) vs. e₃.
-/
lemma pureState_projection'' :
    IsStarProjection (pureState (e (0:Fin 3) (R := ℝ))
    + pureState (e (1 : Fin 3))) := {
  isIdempotentElem := by
    unfold IsIdempotentElem
    rw [mul_add]
    repeat rw [add_mul]
    have : pureState (e (0:Fin 3)) * pureState (e 0) (R := ℝ) =
      pureState (e 0) := by
      have := @pureState_projection 3 0
      exact this.isIdempotentElem
    rw [this]
    rw [(pureState_projection 1).isIdempotentElem]
    have : pureState (e (1:Fin 3)) * pureState (e 0) (R := ℝ) = 0 := by
      unfold pureState e
      simp
    rw [this]
    have : pureState (e (0:Fin 3)) * pureState (e 1) (R := ℝ) = 0 := by
      unfold pureState e
      simp
    rw [this]
    simp
  isSelfAdjoint :=
    (pureState_projection 0).isSelfAdjoint.add (pureState_projection 1).isSelfAdjoint
  }

lemma pureState_psd {k : ℕ} (e : Matrix (Fin k) (Fin 1) ℝ) :
  (e.mulᵣ eᵀ).PosSemidef := by
  constructor
  · exact pureState_selfAdjoint _
  · intro x
    suffices 0 ≤ x ⬝ᵥ (e * e.transpose).mulVec x by
      apply psd_versions
      rw [mulᵣ_eq]
      convert this
    have h_expand : x ⬝ᵥ (e * e.transpose).mulVec x =
      (e.transpose.mulVec x) ⬝ᵥ (e.transpose.mulVec x) := by
      simp +decide [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    rw [h_expand, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact mul_self_nonneg _

instance : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedRing

instance :  NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := frobeniusNormedAlgebra

/-- A general reason why `nonneg_trace` below holds.
Can be generalized to let `(e * eᵀ)` be any projection, see above ^^.
-/
lemma nonneg_trace' {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ} (hρ' : ρ.PosSemidef)
  (e : Matrix (Fin n) (Fin 1) ℝ)
  (he : ‖WithLp.toLp 2 fun i ↦ e i 0‖ = 1) -- not really necessary
  : 0 ≤ (pureState e * ρ).trace := by
      apply trace_mul_nonneg hρ'
      have := @pureState_projection' n {ofLp := fun i => e i 0} he
      convert this

lemma nonneg_trace_of_posSemidef {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℝ}
    (hρ' : ρ.PosSemidef) (i : Fin n) :
    0 ≤ (pureState (e i) * ρ).trace := by
  apply nonneg_trace' hρ'
  simp [e, single, PiLp.instNorm]

theorem POVM_PMF.aux₀ {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
  (hρ : ρ.trace = 1) (hρ' : ρ.PosSemidef) :
  (∑ a, ⟨
    (pureState (e a) * ρ).trace,
    nonneg_trace_of_posSemidef hρ' a⟩) = ENNReal.toNNReal 1 := by
  apply NNReal.eq
  unfold pureState e
  simp_rw [pure_state_eq]
  simp_rw [single_row]
  rw [← sum_rows ρ] at hρ
  simp only [trace_sum, NNReal.coe_sum, NNReal.coe_mk, ENNReal.toNNReal_one, NNReal.coe_one] at hρ ⊢
  exact hρ

open ENNReal

lemma standard_basis_probability_one {k : ℕ}
  {ρ : Matrix (Fin k) (Fin k) ℝ} (hUT : ρ.trace = 1) (hPS : ρ.PosSemidef) :
  ∑ a, ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩ = 1 := by
    exact
      (toNNReal_eq_one_iff _).mp
      <| ENNReal.toNNReal_one ▸ POVM_PMF.aux₀ hUT hPS
       ▸ toNNReal_sum (by simp)


/-- A probability measure that gives the probability
of being in the xy-plane, or the z-axis,
for a given PSD trace-one matrix `ρ`.
See `myPVM₂₃` below.
-/
def PVM_PMF₂₃ {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((pureState (e 0) + pureState (e 1)) * ρ).trace, PMF₂₃help hPS⟩
      ⟨(                   pureState (e 2)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩)
  rw [← standard_basis_probability_one hUT hPS]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp_rw [add_mul, trace_add]
  simp
  rfl


lemma one_eq_sum_pureState_R {k : ℕ} :
    1 = ∑ i : Fin k, pureState (e i) (R := ℝ) := by
  unfold pureState e
  ext i j
  simp only [Fin.isValue, transpose_single, mulᵣ_eq, single_mul_single_same, mul_one]
  by_cases H : i = j
  · subst H
    simp only [one_apply_eq, single]
    rw [Finset.sum_apply] -- !
    simp
  · simp only [single]
    rw [Finset.sum_apply] -- !
    symm
    have : (1 : Matrix (Fin k) (Fin k) ℝ) i j = 0 := by
        exact one_apply_ne' fun a ↦ H (id (Eq.symm a))
    rw [this]
    simp only [Finset.sum_apply, of_apply, Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, forall_const, forall_eq, ne_eq]
    exact H



lemma trace_one_sub {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hPS : ρ.PosSemidef) : 0 ≤ ((1 - pureState (e acc)) * ρ).trace := by
  rw [one_eq_sum_pureState_R]
  rw [sum_one_sub₀]
  refine trace_mul_posSemidef_nonneg hPS ?_
  refine posSemidef_sum Finset.univ ?_
  intro i _
  by_cases H : i = acc
  · subst H
    simp only [↓reduceIte]
    exact PosSemidef.zero
  · rw [if_neg H]
    refine posSemidef_of_isStarProjection (pureState (e i)) ?_
    exact pureState_projection i

lemma PMF_of_state.sum_one {k : ℕ} (acc : Fin k)
    {ρ : Matrix (Fin k) (Fin k) ℝ} (hUT : ρ.trace = 1)
    (hPS : ρ.PosSemidef) :
    ∑ i : Fin 2, ofNNReal (ite (i = 0)
      ⟨((1 - pureState (e acc)) * ρ).trace, trace_one_sub _ hPS⟩
      ⟨(     pureState (e acc)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩) = 1 := by
  rw [← standard_basis_probability_one hUT hPS, Fin.sum_univ_two]
  simp_rw [one_eq_sum_pureState_R]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero]
  simp_rw [sub_mul, trace_sub]
  refine (toReal_eq_toReal_iff' (by simp) (by simp)).mp ?_
  have h₀ : ((∑ i, pureState (e i) - pureState (e acc)) * ρ).trace
                                   + (pureState (e acc) * ρ).trace =
                                  ∑ a, (pureState (e a) * ρ).trace := by
    rw [sub_mul, trace_sub, sub_add_cancel, ← trace_sum]
    congr
    apply Matrix.sum_mul
  have h₁ : (∑ a, ofNNReal ⟨(pureState (e a) * ρ).trace, nonneg_trace_of_posSemidef hPS a⟩ ).toReal
           = ∑ a,           (pureState (e a) * ρ).trace := toReal_sum (by simp)
  rw [h₁, ← h₀, toReal_add (by simp) (by simp)]
  have (x : ℝ) (hx : x ≥ 0) : (ofNNReal ⟨x,hx⟩).toReal = x := by rfl
  have h₁ :=
    this (pureState (e acc) * ρ).trace (nonneg_trace_of_posSemidef hPS acc)
  rw [h₁]
  rw [_root_.add_left_inj]
  simp_rw [sub_mul, trace_sub]
  congr

open RCLike

/-- Defining a Bernoulli probability measure by declaring that e_{acc} is the accepted subspace. -/
def PMF_of_state {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PMF (Fin 2) := by
  apply PMF.ofFintype (fun i => ofNNReal <| ite (i = 0)
      ⟨((1 - pureState (e acc)) * ρ).trace, trace_one_sub _ hPS⟩
      ⟨(     pureState (e acc)  * ρ).trace, nonneg_trace_of_posSemidef hPS _⟩)
  exact PMF_of_state.sum_one _ hUT hPS


noncomputable def myPVM {k : ℕ} {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := k
  t := k
  p := POVM_PMF hUT (nonneg_iff_posSemidef.mpr hPS)
  ρ := ρ
  hρ := hPS
  op := fun i : Fin k => pureState (e i)
  pf := by exact fun i ↦ pureState_projection i
  pf' := by intro i; rfl
}


def myPVM₂₃ {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := 3
  t := 2
  p := PVM_PMF₂₃ hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (pureState (e 0) + pureState (e 1)) <| pureState (e 2)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; exact pureState_projection''
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; exact pureState_projection 2
  pf' := by
    intro i
    fin_cases i
    · rfl
    · rfl
}

def PVM_of_state {k : ℕ} (acc : Fin k) {ρ : Matrix (Fin k) (Fin k) ℝ}
    (hUT : ρ.trace = 1) (hPS : Matrix.PosSemidef ρ) : PVM := {
  k := k
  t := 2
  p := PMF_of_state acc hUT hPS
  ρ := ρ
  hρ := hPS
  op := fun i : Fin 2 => ite (i=0)
    (1 - pureState (e acc)) <| pureState (e acc)
  pf := fun i ↦ by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte];
      refine IsStarProjection.one_sub ?_
      exact pureState_projection _
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte];
      exact pureState_projection acc
  pf' := by
    intro i
    fin_cases i
    · unfold PMF_of_state
      simp
    · rfl
}



/-- 1/24/26 -/
def languageAcceptedBy {α : Type*}
  {q r : ℕ} (acceptStateIndex : Fin q.succ)
  (𝓚 : α → Fin r → Matrix (Fin q.succ) (Fin q.succ) ℝ) :=
  {word : Σ n : ℕ, (Fin n → α) |
    krausApplyWord word.2 𝓚 (pureState (e 0)) = pureState (e acceptStateIndex)}
-- now make this probabilistic: PVM_PMF (pureState (e acceptStateIndex)) > 1/2



theorem basisState_trace_one {k : ℕ} {i : Fin k.succ} :
    (pureState (e (i : Fin k.succ)) (R := ℝ)).trace = 1 := by
  unfold pureState e
  have : ((single (i:Fin k.succ) (0:Fin 1) (1:ℝ)).mulᵣ
          (single (i:Fin k.succ) (0:Fin 1) 1)ᵀ)
      = Matrix.of (fun a b => ite (a = i) (ite (b = i) 1 0) 0
      ) := by
      ext i j
      unfold mulᵣ dotProductᵣ single
      simp
      split_ifs
      all_goals tauto
  simp_rw [this, trace]
  simp


/-- The projection-valued measure corresponding to `word`
belong to the measure-once language of KOA `𝓚`.
-/
def PVM_of_word_of_channel {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ}
    (h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM := by
  have := krausApplyWord_densityMatrix (𝓚 := 𝓚) (word := word.2)
      (ρ := ⟨pureState (e 0),⟨pureState_psd _, basisState_trace_one⟩⟩) (h𝓚 := h𝓚)
  exact PVM_of_state acc this.2 this.1


def getPVM₃ {α : Type*} {r : ℕ}
    {𝓚 : α → Fin r → Matrix (Fin (Nat.succ 2)) (Fin (Nat.succ 2)) ℝ}
    (h𝓚 : ∀ (a : α), quantumChannel (𝓚 a)) (word : (n : ℕ) × (Fin n → α)) : PVM :=
  PVM_of_word_of_channel 2 h𝓚 word



/-- 1/25/26
We accept `word` if starting in `e₀` we end up in `e₁` with probability at least 1/2.
-/
def MOlanguageAcceptedBy {α : Type*} {r k : ℕ} (acc : Fin k.succ)
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ}
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  {word | (PVM_of_word_of_channel acc (h𝓚) word).p (1 : Fin 2) > 1/2}
-- quantum channel vs. all quantum channel?



/-- If the start and accept states are the same then
the empty string is accepted in the measure-once setting. -/
lemma MO_language_nonempty {α : Type*} {r k : ℕ}
    {𝓚 : α → Fin r → Matrix (Fin k.succ) (Fin k.succ) ℝ}
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) :
  MOlanguageAcceptedBy 0 h𝓚 ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty'.mp ?_
  refine nonempty_subtype.mpr ?_
  use ⟨0,![]⟩
  unfold MOlanguageAcceptedBy PVM_of_word_of_channel
  unfold PVM_of_state PMF_of_state
  simp only [Nat.succ_eq_add_one, Fin.isValue, Lean.Elab.WF.paramLet, PMF.ofFintype_apply,
    one_ne_zero, ↓reduceIte, one_div, gt_iff_lt, Set.mem_setOf_eq]
  unfold krausApplyWord
  have : pureState (e (0 : Fin k.succ)) * pureState (e 0) (R := ℝ) = pureState (e 0) := by
    suffices IsStarProjection (pureState (e (0 : Fin k.succ))) by exact this.1
    exact pureState_projection 0
  simp only [gt_iff_lt]
  simp_rw [this]
  simp_rw [basisState_trace_one]
  simp


/--
A word is measure-once accepted if after processing it,
the probability of being in state `1 : Fin 2`, is greater than `1/2`.

Measure-Once language accepted by 𝓚 is
{word | Probability that we are in state e₃, and not in the span of e₁,e₂, > 1/2}.
`q = 2` because we haven't generalized myPVM₂₃ yet
-/
def MOlanguageAcceptedBy₃ {α : Type*} {r : ℕ}
    (𝓚 : α → Fin r → Matrix (Fin 3) (Fin 3) ℝ)
    (h𝓚 : ∀ a, quantumChannel (𝓚 a)) : Set ((n : ℕ) × (Fin n → α)) :=
  MOlanguageAcceptedBy 2 h𝓚
