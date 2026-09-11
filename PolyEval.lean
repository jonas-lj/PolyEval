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

An implementation starts from the values of `P` at the first `d + 1` points of the progression and
turns them into the table by repeated differencing, `y j ← y j - y (j - 1)`. `diffPasses` is that
initialisation and `truncate_diffPasses_eval` proves it builds `table`, so
`step_iterate_diffPasses_zero_eval` states correctness of the whole algorithm, initialisation
included, on an array of length `d + 1`.

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

/-- Zero-extension of the length-`d + 1` array `y 0, ..., y d`. -/
def truncate (d : ℕ) (y : ℕ → G) : ℕ → G := fun j ↦ if j ≤ d then y j else 0

/-- One pass of the initialisation: `y j ← y j - y (j - 1)` for `j ≥ k`, leaving `j < k` fixed. -/
def diffPass (k : ℕ) (y : ℕ → G) : ℕ → G := fun j ↦ if k ≤ j then y j - y (j - 1) else y j

/-- The initialisation: the passes `diffPass 1`, ..., `diffPass k`, applied in that order. -/
def diffPasses : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => diffPass (k + 1) (diffPasses k y)

/-- After `k` passes over the values of `f` along the progression, entry `j` holds
`Δ_[h]^[min j k] f (x + (j - min j k) • h)`. -/
theorem diffPasses_apply (h x : M) (f : M → G) (k j : ℕ) :
    diffPasses k (fun i ↦ f (x + i • h)) j = Δ_[h]^[min j k] f (x + (j - min j k) • h) := by
  induction k generalizing j with
  | zero => simp [diffPasses]
  | succ k ih =>
      rw [diffPasses]
      simp only [diffPass]
      by_cases hj : k + 1 ≤ j
      · rw [if_pos hj, ih, ih, min_eq_right (by omega : k ≤ j),
          min_eq_right (by omega : k ≤ j - 1), min_eq_right hj,
          show j - k = (j - (k + 1)) + 1 from by omega, show j - 1 - k = j - (k + 1) from by omega,
          succ_nsmul, ← add_assoc, iterate_succ_apply' (fwdDiff h) k f]
        simp [fwdDiff]
      · rw [if_neg hj, ih, min_eq_left (by omega : j ≤ k), min_eq_left (by omega : j ≤ k + 1)]

/-- The entries `j ≤ k` of the initialisation are those of the difference table. -/
theorem diffPasses_eq_table (h x : M) (f : M → G) {k j : ℕ} (hj : j ≤ k) :
    diffPasses k (fun i ↦ f (x + i • h)) j = table h f x j := by
  rw [diffPasses_apply, min_eq_left hj]
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

/-- The initialisation is correct. For `P` of degree at most `d`, running the differencing passes
on the values of `P` at the first `d + 1` points of the progression, and reading the result as a
length-`d + 1` array, gives exactly `table h P.eval x`. -/
theorem truncate_diffPasses_eval {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) (h x : R) :
    truncate d (diffPasses d fun i ↦ P.eval (x + i * h)) = table h P.eval x := by
  rw [show (fun i : ℕ ↦ P.eval (x + i * h)) = fun i : ℕ ↦ P.eval (x + i • h) from by
    simp [nsmul_eq_mul]]
  funext j
  simp only [truncate]
  by_cases hj : j ≤ d
  · rw [if_pos hj]
    exact diffPasses_eq_table h x P.eval hj
  · rw [if_neg hj]
    exact (table_eq_zero_of_lt hP h x (by omega)).symm

/-- Correctness of the algorithm as implemented on a length-`d + 1` array: initialise it with the
values of `P` at the first `d + 1` points, run the differencing passes, then step `i` times. The
head of the array then holds `P.eval (x + i * h)`. -/
theorem step_iterate_diffPasses_zero_eval {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) (h x : R)
    (i : ℕ) :
    step^[i] (truncate d (diffPasses d fun j ↦ P.eval (x + j * h))) 0 = P.eval (x + i * h) := by
  rw [truncate_diffPasses_eval hP, step_iterate_zero_eval]

end Eval

end PolyEval
