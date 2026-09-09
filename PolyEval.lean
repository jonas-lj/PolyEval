import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Polynomial evaluation on an arithmetic progression

To evaluate a polynomial `P` at `x`, `x + h`, `x + 2h`, ..., keep its forward difference table
`table h P.eval x`, whose `j`-th entry is
[`Δ_[h]`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/ForwardDiff.html#fwdDiff)`^[j] P.eval x`,
and repeatedly apply `step`, which replaces every entry `y j` by `y j + y (j + 1)`. The head of the
table then runs through the values of `P` along the progression, at a cost of `P.natDegree`
additions and no multiplications per point.

`step_iterate_zero` proves this for an arbitrary function, and `table_eq_zero_of_lt` shows that for
a polynomial of degree at most `d` the table vanishes above entry `d`, so `d + 1` entries suffice.

The algorithm is described at <https://www.jonaslindstrom.dk/?p=1306>.
-/

open Function fwdDiff

namespace PolyEval

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- The difference table of `f` at `x`: entry `j` is `Δ_[h]^[j] f x`. -/
def table (h : M) (f : M → G) (x : M) : ℕ → G := fun j ↦ Δ_[h]^[j] f x

/-- One iteration of the algorithm: `y j ← y j + y (j + 1)`, for every `j` at once. -/
def step (y : ℕ → G) : ℕ → G := fun j ↦ y j + y (j + 1)

/-- `Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x` -/
theorem fwdDiff_iter_add_right (h : M) (f : M → G) (x : M) (j : ℕ) :
    Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x := by
  rw [iterate_succ_apply' (fwdDiff h) j f]
  simp [fwdDiff]

/-- `step (table h f x) = table h f (x + h)` -/
theorem step_table (h : M) (f : M → G) (x : M) : step (table h f x) = table h f (x + h) := by
  funext j
  exact (fwdDiff_iter_add_right h f x j).symm

/-- `step^[i] (table h f x) = table h f (x + i • h)` -/
theorem step_iterate (h : M) (f : M → G) (x : M) (i : ℕ) :
    step^[i] (table h f x) = table h f (x + i • h) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [iterate_succ_apply, step_table, ih, succ_nsmul]
      abel_nf

/-- `step^[i] (table h f x) 0 = f (x + i • h)` -/
theorem step_iterate_zero (h : M) (f : M → G) (x : M) (i : ℕ) :
    step^[i] (table h f x) 0 = f (x + i • h) := by
  rw [step_iterate]
  simp [table]

section Eval

open Polynomial

variable {R : Type*} [CommRing R]

/-- `Δ_[1] (fun s ↦ g (h * s + x)) t = Δ_[h] g (h * t + x)` -/
theorem fwdDiff_comp_affine (h x : R) (g : R → G) (t : R) :
    Δ_[1] (fun s ↦ g (h * s + x)) t = Δ_[h] g (h * t + x) := by
  simp [fwdDiff, mul_add, add_right_comm]

/-- `Δ_[1]^[n] (fun s ↦ g (h * s + x)) t = Δ_[h]^[n] g (h * t + x)` -/
theorem fwdDiff_iter_comp_affine (n : ℕ) (h x : R) (g : R → G) (t : R) :
    Δ_[1]^[n] (fun s ↦ g (h * s + x)) t = Δ_[h]^[n] g (h * t + x) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        show (Δ_[1] fun s ↦ g (h * s + x)) = fun s ↦ Δ_[h] g (h * s + x) from
          funext (fwdDiff_comp_affine h x g)]
      exact ih (Δ_[h] g)

/-- `P.natDegree < n ⇒ Δ_[h]^[n] P.eval = 0`, for any step `h`. -/
theorem fwdDiff_iter_eval_eq_zero {P : R[X]} {n : ℕ} (hP : P.natDegree < n) (h : R) :
    Δ_[h]^[n] P.eval = 0 := by
  funext x
  have hdeg : (P.comp (C h * X + C x)).natDegree < n := by
    have : (P.comp (C h * X + C x)).natDegree ≤ P.natDegree * 1 :=
      le_trans natDegree_comp_le (Nat.mul_le_mul (le_refl _) natDegree_linear_le)
    omega
  have key := fwdDiff_iter_comp_affine n h x P.eval 0
  rw [show (fun s : R ↦ P.eval (h * s + x)) = (P.comp (C h * X + C x)).eval from by
    funext s; simp, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg] at key
  simpa using key.symm

/-- `P.natDegree ≤ d ⇒ d < j ⇒ table h P.eval x j = 0` -/
theorem table_eq_zero_of_lt {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) (h x : R) {j : ℕ}
    (hj : d < j) : table h P.eval x j = 0 := by
  simp [table, fwdDiff_iter_eval_eq_zero (lt_of_le_of_lt hP hj) h]

/-- `step^[i] (table h P.eval x) 0 = P.eval (x + i * h)` -/
theorem step_iterate_zero_eval (P : R[X]) (h x : R) (i : ℕ) :
    step^[i] (table h P.eval x) 0 = P.eval (x + i * h) := by
  simpa [nsmul_eq_mul] using step_iterate_zero h P.eval x i

end Eval

end PolyEval
