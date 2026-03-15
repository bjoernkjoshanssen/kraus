import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct

import Mathlib.Analysis.InnerProductSpace.Positive
import Kraus.Basic

import Mathlib.Data.PEquiv
import Mathlib.Data.Matrix.PEquiv

/-!

# Stinespring dilation

-/

open Matrix MatrixOrder

open Kronecker

example : Unit := by
  have : (grudka_C 0 0 0).toLin' (fun a ↦ ite (a=0) 1 0) =
    fun a ↦ ite (a=1) 1 0 := by
    unfold grudka_C
    simp only [Complex.cos_zero, Complex.sin_zero, neg_zero, Fin.isValue]
    ext x
    split_ifs with g₀
    · subst g₀
      simp
      rfl
    simp
    by_cases H : x = 0
    · subst H
      simp
    have : x = 2 := by fin_cases x <;> simp_all
    subst this
    rfl
  have := (@LinearMap.IsPositive ℂ (WithLp 2 (Fin 3 → ℂ)))
    (by
      have := WithLp.map 2 (grudka_C 0 0 0).toLin'

      refine {
        toFun := WithLp.map 2 ((grudka_C 0 0 0).toLin')
        map_add' := by
          intro x y
          generalize grudka_C 0 0 0 = A

          sorry
        map_smul' := sorry
      })

  -- have : (grudka_C 0 0 0).toLin'.IsPositive := by sorry
  sorry

def Matrix.kronecker_map_right {m n : ℕ} {R : Type*} [RCLike R]
  (A : Matrix (Fin n) (Fin n) R) : Matrix ((Fin m) × (Fin n)) ((Fin m) × (Fin n)) R :=
Matrix.kronecker (1 : Matrix (Fin m) (Fin m) R) A

lemma kronecker_map_right_apply {m n : ℕ} {R : Type*} [RCLike R]
  (A : Matrix (Fin n) (Fin n) R) (e₁ : Matrix (Fin m) (Fin 1) R) (e₂ : Matrix (Fin n) (Fin 1) R)
  (hm : m = 2) (hn : n = 2)
  :
  Matrix.kronecker_map_right A * Matrix.kronecker e₁ e₂
    =
  Matrix.kronecker e₁ (A * e₂) := by
  change (A.kronecker_map_right) * (e₁ ⊗ₖ e₂) = e₁ ⊗ₖ (A * e₂)
  unfold kronecker_map_right kroneckerMap kronecker
  unfold kroneckerMap
  simp only
  ext i j
  simp only [of_apply]
  rw [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  subst hm hn
  simp only [of_apply, Fin.sum_univ_two, Fin.isValue]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue]
  fin_cases j
  simp
  ring_nf
  by_cases H : i.1 = 0
  · rw [H]
    generalize A i.2 0 = a
    generalize A i.2 1 = b
    generalize e₁ 0 0 = c
    generalize e₂ 0 0 = d
    generalize e₂ 1 0 = f
    generalize e₁ 1 0 = g
    simp
    ring_nf
  · have : i.1 = 1 := Fin.eq_one_of_ne_zero i.1 H
    rw [this]
    generalize A i.2 0 = a
    generalize A i.2 1 = b
    generalize e₁ 0 0 = c
    generalize e₂ 0 0 = d
    generalize e₂ 1 0 = f
    generalize e₁ 1 0 = g
    simp

def transl₂ : Fin 2 × Fin 2 → Fin 4
| (0,0) => 0
| (0,1) => 1
| (1,0) => 2
| (1,1) => 3

def transl₃ : Fin 2 × Fin 2 × Fin 2 → Fin 8
| (0,0,0) => 0
| (0,0,1) => 1
| (0,1,0) => 2
| (0,1,1) => 3
| (1,0,0) => 4
| (1,0,1) => 5
| (1,1,0) => 6
| (1,1,1) => 7



def translate₂ : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun A x y => A (transl₂ x) (transl₂ y)

def translate₃ : Matrix (Fin 8) (Fin 8) ℂ →
  Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  fun A x y => A (transl₃ x) (transl₃ y)

def toffoli₀ : Matrix (Fin 8) (Fin 8) ℂ := !![
  1,0,0,0, 0,0,0,0;
  0,1,0,0, 0,0,0,0;
  0,0,1,0, 0,0,0,0;
  0,0,0,1, 0,0,0,0;
  0,0,0,0, 1,0,0,0;
  0,0,0,0, 0,1,0,0;
  0,0,0,0, 0,0,0,1;
  0,0,0,0, 0,0,1,0;
]

def cnot₀ : Matrix (Fin 4) (Fin 4) ℂ := !![
  1,0,0,0;
  0,1,0,0;
  0,0,0,1;
  0,0,1,0
]

def toffoli : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := by
  exact translate₃ toffoli₀


def cnot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := by
  exact translate₂ cnot₀
open PiTensorProduct

#check (e (0 : Fin 2)) ⊗ₖ ((e (0 : Fin 2)) ⊗ₖ (e (0 : Fin 2)))

example {n : ℕ} : PiTensorProduct ℂ (fun _ : Fin n => Matrix (Fin 2) (Fin 1) ℂ) := by
  refine tprodCoeff ℂ ?_ ?_
  · exact 5
  · intro i
    exact e 0



example : toffoli * (e (0 : Fin 2)) ⊗ₖ ((e (0 : Fin 2)) ⊗ₖ (e (0 : Fin 2))) =
  (e (0 : Fin 2)) ⊗ₖ ((e (0 : Fin 2)) ⊗ₖ (e (0 : Fin 2))) := by
  unfold toffoli translate₃ toffoli₀ kroneckerMap transl₃
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one]
  all_goals
    unfold e single
    simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
    ext i j
    fin_cases j
    simp only [Fin.isValue, Fin.zero_eta, of_apply, and_true]
    fin_cases i
    all_goals
      try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, zero_ne_one, ↓reduceIte]
      try rw [Matrix.mul_apply]
      try simp only [Fin.isValue, cons_val, cons_val_one, cons_val_zero, of_apply, and_true,
        mul_ite, mul_one, mul_zero]
      try rw [Fintype.sum_prod_type]
      try simp only [Fin.isValue, Fin.sum_univ_two, ↓reduceIte, zero_ne_one, ite_self,
        Finset.sum_const_zero, add_zero]
      try rw [Fintype.sum_prod_type]
      try rw [Fin.sum_univ_two]
      try simp

/-- Prove that toffolo is a legitimate circuit. -/
example : toffoli ∈ unitary _ := by
  have h₀ : star toffoli = toffoli := by
    refine Matrix.ext ?_
    intro i j
    unfold toffoli
    unfold translate₃
    unfold toffoli₀ transl₃
    fin_cases i <;> fin_cases j <;> simp
  have :  star toffoli * toffoli = 1 := by
    rw [h₀]
    refine Matrix.ext ?_
    intro i j
    rw [Matrix.mul_apply]
    repeat (rw [Fintype.sum_prod_type]; rw [Fin.sum_univ_two])
    repeat rw [Fin.sum_univ_two]
    unfold toffoli translate₃ toffoli₀ transl₃
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · exact this
  · rw [h₀] at *
    exact this
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

noncomputable def toffoli_probability'
    (startState : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 1 × Fin 1 × Fin 1) ℂ) : ℂ := by
  let A := toffoli * startState
  exact
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

def ket0 : Matrix (Fin 2) (Fin 1) ℂ := !![(1 : ℂ); 0]

noncomputable def proj0 : Matrix (Fin 2) (Fin 2) ℂ :=
  ket0 * ket0ᴴ
noncomputable def first_qubit_proj0 : Matrix (Fin 2 × Fin 2 × Fin 2)
                               (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker proj0
    (Matrix.kronecker 1 1)

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
  exact (ψᴴ * first_qubit_proj0 * ψ) (0,0,0) (0,0,0)


example : toffoli_probability ((e 0) ⊗ₖ (e 0 ⊗ₖ (e 0))) = 1 := by
  let A := toffoli * ((e 0) ⊗ₖ (e 0 ⊗ₖ (e 0)))
  let a :=  A (0,0,0) (0,0,0)
  let b :=  A (0,0,1) (0,0,0)
  let c :=  A (0,1,0) (0,0,0)
  let d :=  ![A (0,1,1) (0,0,0), A (0,1,0) (0,0,0), A (0,0,1) (0,0,0)]
  change star a * a + star (d 2) * (d 2) + star (d 1) * (d 1) + star (d 0) * (d 0) = 1
  have : a = 1 := by
    unfold a A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
  rw [this]
  have : b = 0 := by
    unfold b A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
  have : d 2 = 0 := this
  rw [this]
  have : c = 0 := by
    unfold c A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
  have : d 1 = 0 := this
  rw [this]
  have : d 0 = 0 := by
    unfold d A toffoli translate₃ toffoli₀ transl₃ e
    rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
  rw [this]
  simp

lemma cnot_basis (i j) : cnot * (e i ⊗ₖ e j) = ite (i = 0)
  (e 0 ⊗ₖ e j)
  (e 1 ⊗ₖ e (1-j))
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


noncomputable def quantumCircuitUnitary''
    (A : unitary <| Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  : (unitary <| Matrix (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2)
                       (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) :=
    ⟨Matrix.fromBlocks A 0 0 1, by
    have : star (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) =
      Matrix.fromBlocks (star (A : Matrix (Fin 2 × Fin 2)
      (Fin 2 × Fin 2) ℂ)) (star 0) (star 0) (star 1) := by
        exact ext_iff_trace_mul_left.mpr (congrFun rfl)
    constructor <;>
    · rw [this]
      simp [fromBlocks_multiply]⟩

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
    repeat
      rw [Fintype.sum_prod_type]
      repeat rw [Fin.sum_univ_two]
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
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    simp
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    simp
    rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    simp
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    simp
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    simp

    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
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
