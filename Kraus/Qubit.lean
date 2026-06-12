import Mathlib.LinearAlgebra.PiTensorProduct
import Kraus.Stinespring
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Probability.Distributions.Poisson.Basic

/-!

# Qubits

-/
-- #check Fin.encodeBool
open Matrix MatrixOrder

open Kronecker

noncomputable section

/-- To use `Fin 4 × Fin 4` matrices to manipulate `2` qubits. -/
def transl₂ : Fin 2 × Fin 2 → Fin 4
| (0,0) => 0
| (0,1) => 1
| (1,0) => 2
| (1,1) => 3

/-- To use `Fin 8 × Fin 8` matrices to manipulate `3` qubits. -/
def transl₃ : Fin 2 × Fin 2 × Fin 2 → Fin 8
| (0,0,0) => 0
| (0,0,1) => 1
| (0,1,0) => 2
| (0,1,1) => 3
| (1,0,0) => 4
| (1,0,1) => 5
| (1,1,0) => 6
| (1,1,1) => 7

/-- An "associative variant" for using `Fin 8 × Fin 8` matrices to manipulate `3` qubits. -/
def transl₃'' : (Fin 2 × Fin 2) × Fin 2 → Fin 8
| ((0,0),0) => 0
| ((0,0),1) => 1
| ((0,1),0) => 2
| ((0,1),1) => 3
| ((1,0),0) => 4
| ((1,0),1) => 5
| ((1,1),0) => 6
| ((1,1),1) => 7

noncomputable def transl3 {a b : ℕ} :
    (Fin b → Fin a) → Fin (a ^ b) := by
  have := (Fintype.equivFin (Fin b → Fin a)).toFun
  convert this
  simp

def transl {a b : ℕ} :
    (Fin b → Fin a) → Fin (a ^ b) := by
  exact fun v => finFunctionFinEquiv v


-- | ![0,0,0] => 0
-- | ![0,0,1] => 0
-- | ![0,1,0] => 0
-- | ![0,1,1] => 0
-- | ![1,0,0] => 0
-- | ![1,0,1] => 0
-- | ![1,1,0] => 0
-- | ![1,1,1] => 0

def transl₃' : Fin 2 × Fin 2 × Fin 2 → Fin 8 :=
    fun p => (p.1.mkDivMod p.2.1).mkDivMod p.2.2

example : transl₃ = transl₃' := by
  unfold transl₃ transl₃'
  ext p
  fin_cases p <;> simp


def translate₂ : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun A x y => A (transl₂ x) (transl₂ y)

def translate₃ : Matrix (Fin 8) (Fin 8) ℂ →
  Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  fun A x y => A (transl₃ x) (transl₃ y)

def translate₃' : Matrix (Fin 8) (Fin 8) ℂ →
  Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  fun A x y => A (transl₃'' x) (transl₃'' y)

def toffoli₀ : Matrix (Fin 8) (Fin 8) ℂ := !![
  1, 0, 0, 0,  0, 0, 0, 0;
  0, 1, 0, 0,  0, 0, 0, 0;
  0, 0, 1, 0,  0, 0, 0, 0;
  0, 0, 0, 1,  0, 0, 0, 0;
  0, 0, 0, 0,  1, 0, 0, 0;
  0, 0, 0, 0,  0, 1, 0, 0;
  0, 0, 0, 0,  0, 0, 0, 1;
  0, 0, 0, 0,  0, 0, 1, 0;
]

def cnot₀ : Matrix (Fin 4) (Fin 4) ℂ := !![
  1,0,0,0;
  0,1,0,0;
  0,0,0,1;
  0,0,1,0
]

def toffoli : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  translate₃ toffoli₀

def toffoli' : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  translate₃' toffoli₀

def cnot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := translate₂ cnot₀

open PiTensorProduct

#check (e (0 : Fin 2)) ⊗ₖ ((e (0 : Fin 2)) ⊗ₖ (e (0 : Fin 2)))

example {n : ℕ} : PiTensorProduct ℂ (fun _ : Fin n => Matrix (Fin 2) (Fin 1) ℂ) := by
  refine tprodCoeff ℂ ?_ ?_
  · exact 5
  · intro i
    exact e 0


-- If `b` and `c` aren't both 1 then `toffoli` acts like identity.
lemma toffoli_unchange {a b c : Fin 2}
  (h : ¬ (a = 1 ∧ b = 1)) : toffoli * e a ⊗ₖ (e b ⊗ₖ e c) =
                                      e a ⊗ₖ (e b ⊗ₖ e c) := by
  unfold toffoli translate₃ toffoli₀ kroneckerMap transl₃
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one]
  unfold e single
  simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
  ext i j
  fin_cases j
  simp only [Fin.isValue, Fin.zero_eta, of_apply, and_true]
  fin_cases i
  all_goals
    try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
    try rw [Matrix.mul_apply]
    try simp only [Fin.isValue, cons_val, cons_val_one, cons_val_zero, of_apply, and_true,
      mul_ite, mul_one, mul_zero]
    try rw [Fintype.sum_prod_type]
    try simp only [Fin.isValue, Fin.sum_univ_two]
    try rw [Fintype.sum_prod_type]
    try rw [Fin.sum_univ_two]
    try rw [Fintype.sum_prod_type]
    try repeat rw [Fin.sum_univ_two]
    try
      fin_cases a <;>
      fin_cases b <;>
      fin_cases c <;> all_goals try simp_all

-- If the first two qubits are `1` then `toffoli` flips the third qubit.
lemma toffoli_change (c : Fin 2) :
    toffoli * e (1 : Fin 2) ⊗ₖ (e (1 : Fin 2) ⊗ₖ e c) =
              e (1 : Fin 2) ⊗ₖ (e (1 : Fin 2) ⊗ₖ e (1-c)) := by
  unfold toffoli translate₃ toffoli₀ kroneckerMap transl₃
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one]
  unfold e single
  simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
  ext i j
  fin_cases j
  simp only [Fin.isValue, Fin.zero_eta, of_apply, and_true]
  fin_cases i
  all_goals
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, sub_eq_self, ↓reduceIte, one_ne_zero,
      ite_self]
    rw [mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, cons_val_zero, cons_val, cons_val_one, of_apply, and_true, one_ne_zero,
      ↓reduceIte, ite_self, mul_zero, add_zero, and_self, Finset.sum_const_zero, mul_ite, mul_one,
      zero_add]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, ite_self, add_zero, Finset.sum_ite_eq,
      Finset.mem_univ, zero_add]
    fin_cases c <;> simp_all

lemma kroneckerMap_injective {α β γ δ : Type*}
      {w : Matrix α β ℂ} (hw : w ≠ 0)
      {x y : Matrix (α × γ) (β × δ) ℂ}
      (h₂ : w ⊗ₖ x = w ⊗ₖ y) : x = y := by
        obtain ⟨i, j, hwij⟩ : ∃ i j, w i j ≠ 0 := by
          contrapose! hw
          exact Matrix.ext hw
        ext a b
        have hentry :=
          congrArg
          (fun M => M (i, a) (j, b)) h₂
        simp at hentry
        tauto

lemma kroneckerMap_injective₀ {α β : Type*}
    {w : Matrix α β ℂ} (hw : w ≠ 0)
      {x y : Matrix α β ℂ}
      (h₂ : w ⊗ₖ x = w ⊗ₖ y) : x = y := by
        obtain ⟨i, j, hwij⟩ : ∃ i j, w i j ≠ 0 := by
          contrapose! hw
          exact Matrix.ext hw
        ext a b
        have hentry :=
          congrArg
          (fun M => M (i, a) (j, b)) h₂
        simp at hentry
        tauto


lemma e_ne_zero {z : Fin 2} : (e (R := ℂ) (z : Fin 2)) ≠ 0 := by
      intro hc
      have := congrFun (congrFun hc z) 0
      simp [e, single] at this

theorem toffoli_characterize (a b c : Fin 2) :
    toffoli * e a ⊗ₖ (e b ⊗ₖ e c) =
    ite (a = 1 ∧ b = 1)
    (e a ⊗ₖ (e b ⊗ₖ e (1-c)))
    (e a ⊗ₖ (e b ⊗ₖ e c)) := by
  split_ifs with g₀
  · rw [g₀.1, g₀.2];exact toffoli_change c
  · exact toffoli_unchange g₀

/-- If we inspect the third qubit on input (a,1,1) we find 1-a. -/
lemma negation_using_toffoli (a : Fin 2) :
    toffoli * e (R := ℂ) a ⊗ₖ (e (1 : Fin 2) ⊗ₖ e (1 : Fin 2))
            = e          a ⊗ₖ (e  1          ⊗ₖ e (1 - a)) := by
  rw [toffoli_characterize]
  simp only [Fin.isValue, and_true, sub_self]
  split_ifs with g₀
  · subst a
    rfl
  · fin_cases a
    · simp
    · simp at g₀

lemma partialTraceLeft_tensor_rankOne_basis {R : Type*} [RCLike R]
    {k : Type*} [Fintype k] [DecidableEq k] (i : k)
    (M : Matrix (k × k) (Fin 1 × Fin 1) R) :
    partialTraceLeft (pureState' ((e i) ⊗ₖ M)) = pureState' M := by
  have := (e i) ⊗ₖ M
  have := pureState' ((e i) ⊗ₖ M)
  unfold partialTraceLeft e pureState'
  simp only [kroneckerMap, single, Fin.isValue, of_apply]
  ext a b
  simp_rw [mul_apply]
  rw [Finset.sum_comm]
  repeat rw [Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type]

lemma partialTraceLeft_tensor_rankOne_basis' {R : Type*} [RCLike R]
    {k : Type*} [Fintype k] [DecidableEq k] (i : k)
    (M : Matrix (k) (Fin 1) R) :
    partialTraceLeft (pureState' ((e i) ⊗ₖ M)) = pureState' M := by
  unfold partialTraceLeft pureState' e
  simp only [kroneckerMap, single, Fin.isValue, of_apply]
  ext a b
  simp_rw [mul_apply]
  rw [Finset.sum_comm]
  repeat rw [Fintype.sum_prod_type]
  simp

lemma negation_using_toffoli'' (a : Fin 2) :
    let t := toffoli * e (R := ℂ) a ⊗ₖ (e (1 : Fin 2) ⊗ₖ e (1 : Fin 2))
    (partialTraceLeft (pureState' t))
    = pureState' (e (R := ℂ) 1 ⊗ₖ e (1 - a)) := by
  rw [toffoli_characterize]
  simp only [Fin.isValue, and_true, sub_self]
  split_ifs with g₀
  · subst a
    rw [partialTraceLeft_tensor_rankOne_basis]
    have := @partialTraceLeft_tensor_rankOne_basis
      ℂ _ (Fin 2) _ _ 1 (e 1 ⊗ₖ e 0)
    simp at this ⊢
  · fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, sub_zero]
      rw [partialTraceLeft_tensor_rankOne_basis]
    · simp at g₀

/-- May 21, 2026. Best result so far on computing negation using Toffoli gate. -/
lemma negation_using_toffoli' (a : Fin 2) :
    partialTraceLeft
    (partialTraceLeft
    (pureState'
    (toffoli * e (R := ℂ) a ⊗ₖ (e (1 : Fin 2) ⊗ₖ e (1 : Fin 2)))
    )) = pureState' (e (1 - a)) := by
  rw [negation_using_toffoli'', partialTraceLeft_tensor_rankOne_basis']


noncomputable def
  bit_from_pureState (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 1) (Fin 1) ℂ := by
  have v := !![(0:ℂ);1]
  exact vᴴ * M * v

lemma bit_from_pureState_eq (i : Fin 2) :
  bit_from_pureState (pureState' (e i)) = !![(i.1 : ℂ)] := by
    unfold bit_from_pureState pureState' e
    ext z₀ z₁
    have : z₀ = 0 := Fin.fin_one_eq_zero z₀
    subst z₀
    have : z₁ = 0 := Fin.fin_one_eq_zero _
    subst z₁
    simp only [Fin.isValue, conjTranspose_single, star_one, single_mul_single_same, mul_one,
      of_apply, cons_val', cons_val_fin_one]
    repeat rw [mul_apply]
    simp only [conjTranspose, transpose, of_apply, cons_val', cons_val_fin_one, RCLike.star_def,
      Fin.isValue, Fin.sum_univ_two, cons_val_zero, mul_zero, cons_val_one, mul_one, zero_add]
    rw [mul_apply]
    simp only [Fin.isValue, map_apply, of_apply, single, mul_ite, mul_one, mul_zero,
      Fin.sum_univ_two, cons_val_zero, map_zero, ite_self, and_self, cons_val_one, map_one,
      zero_add]
    split_ifs with g₀
    · rw [g₀];simp
    · fin_cases i
      · simp
      · simp at g₀

lemma bit_from_pureState_eq' (i : Fin 2) :
  bit_from_pureState (pureState' (e i)) 0 0 = (i.1 : ℂ) := by
    rw [bit_from_pureState_eq]
    simp

lemma negation_using_toffoli''' (a : Fin 2) :
    bit_from_pureState (
    partialTraceLeft
    (partialTraceLeft
    (pureState'
    (toffoli * e (R := ℂ) a ⊗ₖ (e (1 : Fin 2) ⊗ₖ e (1 : Fin 2)))))) 0 0
     =  (1 - a) := by
  rw [negation_using_toffoli'', partialTraceLeft_tensor_rankOne_basis']
  rw [bit_from_pureState_eq']
  fin_cases a <;> simp



lemma scratch_off_tensor_general {R : Type*} [RCLike R] {i : Fin 2}
    (M : Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 1) R) :
    partialTraceLeft (((e i) ⊗ₖ M) * ((e i) ⊗ₖ M)ᴴ) = M * Mᴴ := by
  apply partialTraceLeft_tensor_rankOne_basis


/-- correct acc. to https://chatgpt.com/c/6a0ba46b-6c94-83e8-8262-52b4a2dc0954
This can be used to compute negation using the Toffoli gate.
-/
lemma scratch_off_tensor {R : Type*} [RCLike R] {i j k : Fin 2} :
    let v := e (R := R) i ⊗ₖ (e j ⊗ₖ e k)
    let B := v * vᴴ
    let Bl := partialTraceLeft B
    Bl = (e (R := R) j ⊗ₖ (e k))
        * (e (R := R) j ⊗ₖ (e k))ᴴ := by
        apply scratch_off_tensor_general



/-- The usual characterization of the behavior of the Toffoli gate:
`the target bit (third bit) will be inverted if`
`and only if the first and second bits are both 1`
from https://en.wikipedia.org/wiki/Toffoli_gate
-/
theorem toffoli_characterize.TFAE (a b c : Fin 2) :
    [a = 1 ∧ b = 1,
     toffoli * e a ⊗ₖ (e b ⊗ₖ e c) = e a ⊗ₖ (e b ⊗ₖ e (1-c)),
     toffoli * e a ⊗ₖ (e b ⊗ₖ e c) ≠ e a ⊗ₖ (e b ⊗ₖ e c)].TFAE := by
  apply List.tfae_of_cycle
  · apply List.IsChain.cons_cons
    · intro h;rw [h.1,h.2]; exact toffoli_change c
    · apply List.isChain_pair.mpr
      intro h hc
      rw [h] at hc
      have := congrFun (congrFun (kroneckerMap_injective₀ e_ne_zero
        <| kroneckerMap_injective e_ne_zero hc) 0) 0
      simp only [e, single, Fin.isValue, of_apply, and_true] at this
      split_ifs at this <;> simp_all only [Fin.isValue, sub_zero, one_ne_zero]
      repeat fin_cases c <;> simp_all
  · intro h
    contrapose! h
    simp only [ne_eq, Fin.isValue, List.getLastD_eq_getLast?, List.getLast?_singleton,
      Option.getD_some, Decidable.not_not]
    apply toffoli_unchange
    tauto


lemma toffoli_real : star toffoli = toffoli := by
  refine Matrix.ext ?_
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toffoli, translate₃, toffoli₀, transl₃]

lemma toffoli_unitary.aux : star toffoli * toffoli = 1 := by
    refine Matrix.ext ?_
    intro i j
    rw [Matrix.mul_apply]
    repeat (rw [Fintype.sum_prod_type]; rw [Fin.sum_univ_two])
    repeat rw [Fin.sum_univ_two]
    unfold toffoli translate₃ toffoli₀ transl₃
    fin_cases i <;> fin_cases j <;> simp


/-- Prove that toffolo is a unitary circuit. -/
lemma toffoli_unitary : toffoli ∈ unitary _ := by
  constructor
  · exact toffoli_unitary.aux
  · rw [← toffoli_unitary.aux]
    rw [toffoli_real]


-- now we need to measure whether the 1st qubit is e 0
-- should use a hadamard matrix to get nontrivial probabilities
noncomputable def toffoli_probability
    (startState : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 1 × Fin 1 × Fin 1) ℂ) : ℂ := by
  let A := toffoli * startState
  let a :=  A (0,0,0) (0,0,0)
  let b :=  A (0,0,1) (0,0,0)
  let c :=  A (0,1,0) (0,0,0)
  let d :=  A (0,1,1) (0,0,0)
  exact star a * a + star b * b
      + star c * c + star d * d

/-- May 11, 2026. Using `*ᵥ` to simplify matrix structure. -/
noncomputable def toffoli_probability''
    (startState : Fin 2 × Fin 2 × Fin 2 → ℂ) : ℂ := by
  let A := toffoli *ᵥ startState
  let a :=  A (0,0,0)
  let b :=  A (0,0,1)
  let c :=  A (0,1,0)
  let d :=  A (0,1,1)
  exact star a * a + star b * b
      + star c * c + star d * d

noncomputable def toffoli_probability'
    (startState : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 1 × Fin 1 × Fin 1) ℂ) : ℂ :=
  ∑ i : Fin 2 × Fin 2,
    let z := ((toffoli * startState) (0, i.1, i.2) (0,0,0))
    star z * z

lemma toffoli_probability_eq :
  toffoli_probability = toffoli_probability' := by
  ext startState
  unfold toffoli_probability toffoli_probability'
  simp only [Fin.isValue, RCLike.star_def, Prod.mk.eta]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  ring_nf

def ket₀ : Matrix (Fin 2) (Fin 1) ℂ := !![(1 : ℂ); 0]

noncomputable def proj₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  ket₀ * ket₀ᴴ

noncomputable def first_qubit_proj₀ :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  proj₀ ⊗ₖ (1 ⊗ₖ 1)

#check (⊤ : MeasurableSpace (Fin 2))
example : @MeasurableSet (Fin 2) ⊤ {0} := by
  simp
example : ¬ @MeasurableSet (Fin 2) ⊥ {0} := by
  rw [MeasurableSpace.measurableSet_bot_iff]
  simp



noncomputable def gate_probability
  (startState :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 1 × Fin 1 × Fin 1) ℂ) : ℂ :=
by
  let ψ := toffoli * startState
  exact (ψᴴ * first_qubit_proj₀ * ψ) (0,0,0) (0,0,0)

-- Let's try to use `gate_probability` for something:
example : gate_probability ((e 0) ⊗ₖ (e 0 ⊗ₖ (e 0))) = 1 := by
  unfold gate_probability
  unfold first_qubit_proj₀
  unfold toffoli toffoli₀
  unfold translate₃ transl₃
  simp

  sorry

example : toffoli_probability ((e (R := ℂ) (0 : Fin 2)) ⊗ₖ (e 0 ⊗ₖ (e 0))) = 1 := by
  let A := toffoli * ((e (R := ℂ) (0 : Fin 2)) ⊗ₖ (e (0 : Fin 2) ⊗ₖ (e (0 : Fin 2))))
  let a :=  A (0,0,0) (0,0,0)
  let b :=  A (0,0,1) (0,0,0)
  let c :=  A (0,1,0) (0,0,0)
  let d :=  ![A (0,1,1) (0,0,0), A (0,1,0) (0,0,0), A (0,0,1) (0,0,0)]
  change star a * a + star (d 2) * (d 2) + star (d 1) * (d 1) + star (d 0) * (d 0) = 1
  have : a = 1 := by
    unfold a A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    repeat
      try rw [Fintype.sum_prod_type]
      rw [Fin.sum_univ_two]
    simp
  rw [this]
  have : b = 0 := by
    unfold b A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    repeat
      try rw [Fintype.sum_prod_type]
      rw [Fin.sum_univ_two]
    simp
  have : d 2 = 0 := this
  rw [this]
  have : c = 0 := by
    unfold c A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    repeat
      try rw [Fintype.sum_prod_type]
      rw [Fin.sum_univ_two]
    simp
  have : d 1 = 0 := this
  rw [this]
  have : d 0 = 0 := by
    unfold d A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    repeat
      try rw [Fintype.sum_prod_type]
      rw [Fin.sum_univ_two]
    simp
  rw [this]
  simp

lemma cnot_basis (i j : Fin 2) : cnot * (e i ⊗ₖ e j) = ite (i = 0)
                                (e i ⊗ₖ e j)
                                (e i ⊗ₖ e (1-j))
  := by
  fin_cases i <;> fin_cases j <;>
  all_goals
    unfold cnot translate₂ transl₂ cnot₀ e kroneckerMap single
    simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      mul_ite, mul_one, mul_zero, ↓reduceIte]
    ext i j
    fin_cases j
    simp only [Fin.isValue, Fin.zero_eta, of_apply, and_true]
    fin_cases i
    all_goals
      try simp only [Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte, sub_zero, of_apply,
        and_true]
      try rw [Matrix.mul_apply]
      try simp only [Fin.isValue, cons_val_zero, of_apply, and_true, mul_ite, mul_one, mul_zero,
        sub_self, ↓reduceIte]
      try rw [Fintype.sum_prod_type]
      try simp

def swap₃ : Equiv.Perm (Fin 3) := by
  refine {
    toFun := ![1,0,2]
    invFun := ![1,0,2]
    left_inv := by
      intro x
      fin_cases x <;> simp
    right_inv := by
      intro x
      fin_cases x <;> simp
  }

example (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks A 0 1 0

lemma isOne : (1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1,0;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

example : Equiv.Perm (Fin 2 × Fin 2 × Fin 2) := by
  refine {
    toFun := fun (i,j,k) => (i,k,j)
    invFun := fun (i,j,k) => (i,k,j)
    left_inv := by
      intro x
      fin_cases x <;>
      simp
    right_inv := by
      intro x
      fin_cases x <;>
      simp
  }

def f {a b : ℕ} : (Fin a × Fin b ⊕ Fin a × Fin b) →
    Fin a × Fin b × Fin 2 := by
    intro x
    cases x with
    | inl val => exact ⟨val.1, ⟨val.2, 0⟩⟩
    | inr val => exact ⟨val.1, ⟨val.2, 1⟩⟩

def split {a b : ℕ} : Fin a × Fin b × Fin 2 → (Fin a × Fin b ⊕ Fin a × Fin b) :=
    fun (u,v,w) => ite (w = 0) (Sum.inl (u,v)) (Sum.inr (u,v))

def split' {a b : ℕ} : Fin 2 × Fin a × Fin b → (Fin a × Fin b ⊕ Fin a × Fin b) :=
    fun (u,v,w) => ite (u = 0) (Sum.inl (v,w)) (Sum.inr (v,w))


/-- Given a circuit `A` that only touches 2 qubits,
and a permutation `P` of 3 qubits,
get a unitary as `Pᵀ Q P` where `Q = A ⊕ I`. -/
noncomputable def quantumCircuit
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (σ : Equiv.Perm (Fin 2 × Fin 2 × Fin 2)) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  σ.symm.toPEquiv.toMatrix *
    (Matrix.of fun x y => -- turn this into a product
    (Matrix.fromBlocks A 0 0 1) (split' x) (split' y))
     * σ.toPEquiv.toMatrix

def Matrix.fromBlocks_id {a b : ℕ} := fun (A : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
  => (Matrix.fromBlocks A (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) 1)

def Matrix.fromBlocks_split' {a b : ℕ} := fun (A : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
  =>    (Matrix.of fun x y => -- turn this into a product
    (Matrix.fromBlocks A 0 0 1) (split' x) (split' y))

-- generalize this to Fin a, Fin b?
def Matrix.prod_sum {a b : ℕ} : Matrix (Fin 2 × Fin a × Fin b) (Fin a × Fin b ⊕ Fin a × Fin b) ℂ :=
     fun x y => ite (y = split' x) 1 0

def Matrix.sum_prod {a b : ℕ} : Matrix (Fin a × Fin b ⊕ Fin a × Fin b) (Fin 2 × Fin a × Fin b) ℂ :=
     fun x y => ite (x = split' y) 1 0

lemma Matrix.fromBlocks_split'_eq {a b : ℕ} (A : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix.fromBlocks_split' A =
      Matrix.prod_sum * Matrix.fromBlocks_id A * Matrix.sum_prod := by
    unfold Matrix.prod_sum Matrix.sum_prod Matrix.fromBlocks_id
      Matrix.fromBlocks_split' split' fromBlocks
    ext i j
    simp only [Fin.isValue, Prod.mk.eta, of_apply]
    rw [Matrix.mul_apply]
    split_ifs with g₀ g₁ g₂
    · simp only [Sum.elim_inl, Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
      rw [Matrix.mul_apply]
      rw [g₀]
      simp
    · simp only [Sum.elim_inl, Sum.elim_inr, zero_apply, Fin.isValue, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [Matrix.mul_apply]
      rw [g₀]
      simp
    · simp only [Sum.elim_inr, Sum.elim_inl, zero_apply, Fin.isValue, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [Matrix.mul_apply]
      simp
      split_ifs
      simp
    · simp only [Sum.elim_inr, Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
      rw [Matrix.mul_apply]
      simp
      split_ifs
      simp

theorem fromBlocks_unitary
  (A : ↥(unitary (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))) :
  fromBlocks (↑A) 0 0 1 ∈
  unitary (Matrix (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) := by
      have : star (Matrix.fromBlocks A.1 0 0
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) =
        Matrix.fromBlocks (star (A : Matrix (Fin 2 × Fin 2)
        (Fin 2 × Fin 2) ℂ)) (star 0) (star 0) (star 1) := by
          exact ext_iff_trace_mul_left.mpr (congrFun rfl)
      constructor <;>
      · rw [this]
        simp [fromBlocks_multiply]

noncomputable section
def quantumCircuitUnitary'' (A : unitary <| Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (unitary <| Matrix ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))
                        (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) :=
    ⟨Matrix.fromBlocks A 0 0 1, fromBlocks_unitary _⟩

lemma sum_prod_sum_1 : sum_prod (a := 2) (b := 2) * prod_sum (a := 2) (b := 2) = 1 := by
    unfold prod_sum sum_prod split'
    ext i j
    rw [Matrix.mul_apply]
    repeat
      rw [Fintype.sum_prod_type]
      repeat rw [Fin.sum_univ_two]
    fin_cases j
    all_goals
      fin_cases i
      all_goals try simp

lemma blah (A) :
  star (prod_sum (a := 2) (b := 2) * ↑A * sum_prod (a := 2) (b := 2))
  = (prod_sum * star ↑A * sum_prod) := by
    unfold prod_sum sum_prod split'
    ext i j
    rw [Matrix.mul_apply]
    fin_cases j
    all_goals
      fin_cases i
      all_goals try simp
      all_goals sorry
lemma prod_sum_prod_unitary (A : unitary _) :
  prod_sum (a := 2) (b := 2) * A.1 * sum_prod (a := 2) (b := 2) ∈ unitary _ := by
  constructor
  · have := A.2.1

    unfold prod_sum sum_prod split'
    simp
    ext i j
    rw [Matrix.mul_apply]
    simp
    rw [Fintype.sum_prod_type]
    simp
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
    fin_cases i
    fin_cases j
    simp_all
    repeat rw [Matrix.mul_apply]
    simp
    repeat rw [Matrix.mul_apply]
    simp
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
    repeat rw [Matrix.mul_apply]
    simp
    repeat rw [Matrix.mul_apply]
    simp
    all_goals sorry
  · sorry

noncomputable def quantumCircuitUnitary'
    (A : unitary <| Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  : (unitary <| Matrix (Fin 2 × Fin 2 × Fin 2)
                       (Fin 2 × Fin 2 × Fin 2) ℂ) :=
    ⟨(Matrix.of fun x y =>
    (Matrix.fromBlocks A 0 0 1) (split' x) (split' y)), by
    have := @Matrix.fromBlocks_split'_eq (a := 2) (b := 2) A
    unfold fromBlocks_split' at this
    rw [this]
    -- prove that prod_sum * X * sum_prod is unitary whenever X is!
    unfold unitary
    simp
    constructor
    · sorry
    · sorry⟩

noncomputable def quantumCircuitUnitary
    (A : unitary <| Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (σ : Equiv.Perm (Fin 2 × Fin 2 × Fin 2)) :
    (unitary <| Matrix (Fin 2 × Fin 2 × Fin 2)
                       (Fin 2 × Fin 2 × Fin 2) ℂ) := by
    exact ⟨quantumCircuit A σ, by
      unfold quantumCircuit

      sorry⟩
    -- quantumCircuit A σ ∈ unitary _ := by
    -- unfold quantumCircuit
    -- set PT := (Equiv.symm σ).toPEquiv.toMatrix (α := ℂ)
    -- set P := (σ).toPEquiv.toMatrix (α := ℂ)
    -- set Q := (Matrix.of fun x y =>
    -- (Matrix.fromBlocks A 0 0 1) (split x) (split y))
    -- have (U V : unitary (Matrix (Fin 2 × Fin 2 × Fin 2)
    --                              (Fin 2 × Fin 2 × Fin 2) ℂ))

    --   : U * V ∈ unitary _ := by

    --   sorry
    -- sorry
