import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
-- import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Reflection
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic --  Orientation.oangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine --  EuclideanGeometry.oangle
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Reflection
/-!

# Automatic complexity using linear algebra

We define

 * `Al` (linear algebra automatic complexity over a semiring `R`, allowing any vector to be
  initial or final state)

 * `As` (semi-classical automatic complexity over a semiring `R`, allowing only
  standard basis vectors to be initial or final state)

and prove `log_|R| A ≤ Al < As ≤ A`.

The closest of the newcomers to `A` is probably `As ℕ`.
-/

/-- ast for "asterisk": ast δ is what we in mathematics articles would
 call δ^*, the iteration of the transition function δ over a word in.
 To be able to talk about the identity matrix intelligently,
 we assume the field is at least `ℤ / 2ℤ`.
-/
def myf : ℝ × ℝ → ℝ := by
    intro x
    exact x.fst^2+x.snd^2




noncomputable def partial_deriv_x
    (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f x y

noncomputable def partial_deriv_y
    (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
    fun x => deriv fun y => f x y

noncomputable def part_deriv_x
    (f : (Fin 2 → ℝ) → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f ![x, y]

noncomputable def partDeriv_x
    (f : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
    fun x => part_deriv_x f (x 0) (x 1)



theorem suggestion (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ)
    (h : IsLocalExtr f (WithLp.toLp 2 a)) : fderiv ℝ f (WithLp.toLp 2 a) =0 :=
      IsLocalExtr.fderiv_eq_zero h



-- make a repo with this
theorem grad_zero_of_extr (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ) (h₀ : DifferentiableAt ℝ f (WithLp.toLp 2 a))
    (h : IsLocalExtr f (WithLp.toLp 2 a)) : gradient f (WithLp.toLp 2 a) =0 := by
    apply HasGradientAt.gradient
    have h₁ := (hasFDerivAt_iff_hasGradientAt).mp
        (DifferentiableAt.hasFDerivAt h₀)
    rw [IsLocalExtr.fderiv_eq_zero h] at h₁
    simp only [map_zero] at h₁
    exact h₁





example : (!![(1:ℝ),0;0,1]).det = 0 := sorry

def f0 : (Fin 2 → ℝ) → ℝ := by
    intro x
    have := x 0
    have := x 1
    exact (x 0)^2 + (x 1)^2
def f₀ : EuclideanSpace ℝ (Fin 2) → ℝ := by
    intro x
    have := x 0
    have := x 1
    exact (x 0)^2 + (x 1)^2

-- Function of two variables first partial derivative test
-- example (f₀ : EuclideanSpace ℝ (Fin 2) → ℝ) :
--     (hf₀ : )

-- example : f0 ![2,2] = 8 := by
--     simp [f0]
--     linarith

-- def myf'' : ℝ → ℝ → ℝ := by
--     intro x y
--     exact x^2+y^2

-- def myf' : EuclideanSpace ℝ (Fin 2) → ℝ := by
--     intro x y
--     exact x^2+y^2











def astMat {α : Type*} {R : Type*} [Add R] [Mul R] [Zero R] [One R]
  {n q : ℕ} (word : Fin n → α) (matrices : α → Matrix (Fin q) (Fin q) R) :
  Fin q → Fin q → R := match n with
| 0 => fun x y => ite (x=y) 1 0
| Nat.succ m => Matrix.mulᵣ (matrices (word ⟨m,by simp⟩)) (astMat (Fin.init word) matrices)

open Matrix

example {R : Type*} [Mul R] [AddCommMonoid R]
  (q : ℕ) (A B : Matrix (Fin q) (Fin q) R) :
  mulᵣ A B = A * B := by simp only [mulᵣ_eq]

-- /-- Completely positive map in Kraus operator form. -/
-- def CP_apply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
--   {q krausDecompositionLength : ℕ}
--   (krausOperator : Fin krausDecompositionLength → Matrix (Fin q) (Fin q) R)
--   (ρ : Matrix (Fin q) (Fin q) R) : Matrix (Fin q) (Fin q) R :=
--     ∑ i : Fin krausDecompositionLength,
--       krausOperator i * ρ * (krausOperator i).conjTranspose

/-- Completely positive map given by a (not necessarily minimal) Kraus family. -/
def krausApply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R)
  (ρ : Matrix (Fin q) (Fin q) R) : Matrix (Fin q) (Fin q) R :=
  ∑ i : Fin r, K i * ρ * (K i)ᴴ

def quantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
  {q r : ℕ}
  (K : Fin r → Matrix (Fin q) (Fin q) R) : Prop :=
    ∑ i : Fin r, (K i)ᴴ * K i = fun i j => ite (i=j) 1 0


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
| Nat.succ m => krausApply (𝓚 (word ⟨m,by simp⟩))
        (krausApplyWord (Fin.init word) 𝓚 ρ)

/-- The example Kraus operators from QCNC submission. -/
def grudka_Z : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℤ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![0,-1,0;
       1,0,0;
       0,0,1],
    0
  ] -- B
]

def grudka_R : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![0,-1,0;
       1,0,0;
       0,0,1],
    0
  ] -- B
]
open Real
noncomputable def grudka_R' (θ : ℝ) : Fin 2 → Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![
  ![
    !![0,0,0;
       1,0,0;
       0,0,0], !![0,0,0;
                  0,0,-1;
                  0,1,0]
  ], -- A
  ![
    !![cos θ, -sin θ, 0;
       sin θ, cos θ,  0;
       0,     0,      1],
    0
  ] -- B
]

example (θ : ℝ) : (grudka_R' θ 0 0).trace = 0 := by simp [grudka_R']

open Matrix

example (θ : ℝ) {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
    (krausApply (grudka_R' θ 1) ρ).trace = 1 := by
  rw [krausApply, trace]
  unfold grudka_R'
  simp only [diag, sum_apply, mul_apply, conjTranspose_apply]
  simp [Fin.sum_univ_succ]
  rw [trace] at hρ
  simp [Fin.sum_univ_succ] at hρ
  ring_nf
  have := cos_sq_add_sin_sq θ
  have := sin_sq_add_cos_sq θ
  generalize cos θ ^ 2 = c at *
  generalize sin θ ^ 2 = s at *
  have : c = 1 - s := by linarith
  subst this
  linarith


example : quantumChannel (grudka_Z 0) := by
  simp only [quantumChannel, grudka_Z, Int.reduceNeg, Fin.isValue, cons_val', cons_val_fin_one,
    cons_val_zero, conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_transpose,
    Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : quantumChannel (grudka_Z 1) := by
  simp only [quantumChannel, grudka_Z, Int.reduceNeg, Fin.isValue, cons_val', cons_val_fin_one,
    cons_val_one, conjTranspose_eq_transpose_of_trivial, Fin.sum_univ_two, cons_val_zero,
    cons_transpose, Nat.succ_eq_add_one, Nat.reduceAdd, transpose_zero, mul_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : quantumChannel (grudka_R 1) := by
  unfold quantumChannel grudka_R
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ]

example (θ : ℝ) : quantumChannel (grudka_R' θ 1) := by
  unfold quantumChannel grudka_R'
  apply ext
  intro i j
  simp only [sum_apply, mul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> all_goals
      simp
      try linarith
      try repeat rw [← pow_two]
      try exact cos_sq_add_sin_sq θ
      try exact sin_sq_add_cos_sq θ
      sorry

def e₁ : Matrix (Fin 3) (Fin 1) ℝ := ![1, 0, 0]
def e₂ : Matrix (Fin 3) (Fin 1) ℝ := ![0, 1, 0]
def e₃ : Matrix (Fin 3) (Fin 1) ℝ := ![0, 0, 1]
def e : Fin 3 → Matrix (Fin 3) (Fin 1) ℝ :=
  fun i j _ => ite (i=j) 1 0
def pureState (e : Matrix (Fin 3) (Fin 1) ℝ) := mulᵣ e e.transpose

example : pureState e₁ = !![1,0,0;0,0,0;0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureState, e₁, pureState, mulᵣ]

-- Trace exercise: probability of being in the state e₁.
example : (pureState e₁ * (grudka_R' θ 1 0)).trace = cos θ := by
  unfold e₁ grudka_R' pureState
  simp only [mulᵣ_eq, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₂ * (grudka_R' θ 1 0)).trace = cos θ := by
  unfold e₂ grudka_R' pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

example : (pureState e₃ * (grudka_R' θ 1 0)).trace = 1 := by
  unfold e₃ grudka_R' pureState
  simp only [transpose, cons_val', Pi.zero_apply, Pi.one_apply, cons_val_fin_one, mulᵣ_eq,
    Fin.isValue, cons_val_zero, cons_val_one]
  rw [trace]
  simp only [diag, mul_apply]
  simp [Fin.sum_univ_succ]

/-- The positive operator `pureState e₁` is chosen
with probability `(pureState e₁ * ρ).trace`. -/
lemma POVM {ρ : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ : ρ.trace = 1) :
      (pureState e₁ * ρ).trace
    + (pureState e₂ * ρ).trace
    + (pureState e₃ * ρ).trace = 1 := by
  unfold pureState e₁ e₂ e₃
  simp only [transpose, cons_val', Pi.one_apply, Pi.zero_apply, cons_val_fin_one, mulᵣ_eq]
  repeat rw [trace]
  simp only [diag, mul_apply] at hρ ⊢
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, cons_val', Pi.one_apply,
    Pi.zero_apply, cons_val_fin_one, of_apply, Finset.sum_const, Finset.card_singleton, one_smul,
    Fin.sum_univ_succ, cons_val_zero, mul_one, cons_val_succ, mul_zero, Fin.succ_zero_eq_one,
    zero_mul, add_zero, one_mul, zero_add, Finset.sum_singleton,
    Fin.succ_one_eq_two] at hρ ⊢
  rw [trace] at hρ
  simp only [diag_apply] at hρ
  rw [← hρ]
  exact Eq.symm (Fin.sum_univ_three fun i ↦ ρ i i)



-- Now `pureState e₁`, `pureState e₂`, `pureState e₃` form a POVM.


example : krausApplyWord ![0,1] grudka_R (pureState e₁) =
  pureState e₁ := by
  unfold krausApplyWord
  have : Fin.init ![(0:Fin 2),1] = ![0] := by
    ext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [this]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  unfold krausApplyWord
  have : Fin.init ![(0 : Fin 2)] = ![] := by
    ext i
    have := i.2
    simp at this
  rw [this]
  unfold krausApplyWord
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    cons_val_fin_one]
  unfold krausApply
  unfold grudka_R

  simp

  sorry
