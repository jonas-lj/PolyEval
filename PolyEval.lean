import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial evaluation on an arithmetic progression

To evaluate a polynomial P at x, x + h, x + 2h, ..., keep its forward difference table, whose j-th
entry is y_j = Δ_h^j P(x), where Δ_h f(x) = f(x + h) - f(x). Then repeatedly replace every entry by
y_j + y_{j+1}. The head runs through the values of P, at a cost of deg P additions and no
multiplications per point.

`eval_range_correct` is the whole algorithm, initialisation included, as `Poly::eval_range` in
`fastcrypto-tbls` runs it. Each call of `fastcrypto`'s `next` after the first performs one update,
x is what `fastcrypto` calls `initial`, and h, the spacing of the progression, is its `step`.

Knuth, *The Art of Computer Programming*, Volume 2, section 4.6.4, with the initialisation in
exercise 7. See also <https://www.jonaslindstrom.dk/?p=1306> and
<https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto-tbls/src/polynomial.rs>.
-/

open Function fwdDiff

namespace PolyEval

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- The difference table of f at x. Entry j is the j-th forward difference, y_j = Δ_h^j f(x), where
Δ_h f(x) = f(x + h) - f(x). -/
def table (h : M) (f : M → G) (x : M) : ℕ → G := fun j ↦ Δ_[h]^[j] f x

/-- The update each call of `fastcrypto`'s `next` after the first performs: y_j ← y_j + y_{j+1},
for all j at once. -/
def next (y : ℕ → G) : ℕ → G := fun j ↦ y j + y (j + 1)

/-- Δ_h^j f(x + h) = Δ_h^j f(x) + Δ_h^{j+1} f(x) -/
theorem fwdDiff_iter_add_right (h : M) (f : M → G) (x : M) (j : ℕ) :
    Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x := by
  rw [iterate_succ_apply' (fwdDiff h) j f]
  simp [fwdDiff]

/-- Applying next once to the table of f at x gives the table of f at x + h. -/
theorem next_table (h : M) (f : M → G) (x : M) : next (table h f x) = table h f (x + h) := by
  funext j
  exact (fwdDiff_iter_add_right h f x j).symm

/-- Applying next i times to the table of f at x gives the table of f at x + i·h. -/
theorem next_iterate (h : M) (f : M → G) (x : M) (i : ℕ) :
    next^[i] (table h f x) = table h f (x + i • h) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [iterate_succ_apply, next_table, ih, succ_nsmul]
      abel_nf

/-- After applying next i times to the table of f at x, entry 0 is f(x + i·h). -/
theorem next_iterate_zero (h : M) (f : M → G) (x : M) (i : ℕ) :
    next^[i] (table h f x) 0 = f (x + i • h) := by
  rw [next_iterate]
  simp [table]

/-- The array y_0, ..., y_d read as a function on every index, with everything above d set to
zero. -/
def truncate (d : ℕ) (y : ℕ → G) : ℕ → G := fun j ↦ if j ≤ d then y j else 0

/-- One differencing pass, all entries at once: y_j ← y_j - y_{j-1} for j ≥ k, leaving the entries
below k alone. -/
def diffPass (k : ℕ) (y : ℕ → G) : ℕ → G := fun j ↦ if k ≤ j then y j - y (j - 1) else y j

/-- Passes 1 through k, applied in that order. -/
def diffPasses : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => diffPass (k + 1) (diffPasses k y)

/-- After k passes over the values f(x), f(x + h), f(x + 2h), ..., entry j is
Δ_h^m f(x + (j - m)·h), where m = min(j, k). -/
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

/-- After k passes over the values f(x), f(x + h), f(x + 2h), ..., entry j is Δ_h^j f(x) for
every j ≤ k. -/
theorem diffPasses_eq_table (h x : M) (f : M → G) {k j : ℕ} (hj : j ≤ k) :
    diffPasses k (fun i ↦ f (x + i • h)) j = table h f x j := by
  rw [diffPasses_apply, min_eq_left hj]
  simp [table]

/-- Δ_h^k 0 = 0 -/
private theorem fwdDiff_iter_zero (h : M) (k : ℕ) : Δ_[h]^[k] (0 : M → G) = 0 := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using map_zero (fwdDiff_aux.fwdDiffₗ M G h ^ k)

/-- Δ_h^{d+1} f = 0 and d < j imply Δ_h^j f = 0 -/
theorem fwdDiff_iter_eq_zero_of_lt {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) {j : ℕ}
    (hj : d < j) : Δ_[h]^[j] f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + (d + 1) := ⟨j - (d + 1), by omega⟩
  rw [iterate_add_apply, hf, fwdDiff_iter_zero]

/-- If Δ_h^{d+1} f = 0, then the d passes over the values f(x), f(x + h), ..., f(x + d·h), read as
an array of d + 1 entries, give the table of f at x. -/
theorem truncate_diffPasses {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) (x : M) :
    truncate d (diffPasses d fun j ↦ f (x + j • h)) = table h f x := by
  funext j
  by_cases hj : j ≤ d
  · simpa [truncate, hj] using diffPasses_eq_table h x f hj
  · simp [truncate, hj, table, fwdDiff_iter_eq_zero_of_lt hf (by omega : d < j)]

/-- If Δ_h^{d+1} f = 0, then the d passes over the values f(x), f(x + h), ..., f(x + d·h), read as
an array of d + 1 entries, followed by i applications of next, leave f(x + i·h) in entry 0. -/
theorem next_iterate_diffPasses_zero {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0)
    (x : M) (i : ℕ) :
    next^[i] (truncate d (diffPasses d fun j ↦ f (x + j • h))) 0 = f (x + i • h) := by
  rw [truncate_diffPasses hf, next_iterate_zero]

/-! ### The loops as an implementation runs them

`next` and `diffPass` rewrite the whole array at once, while an implementation writes one entry at
a time. The definitions below are those loops, visit order included, and each is proved equal to
the update it implements. The orders are forced: the update loop reads the entry above the one it
writes, so it must run upwards, and a differencing pass reads the entry below, so it must run
downwards. Reversing either makes it read an entry it has already overwritten.
-/

/-- `fastcrypto`'s `iterate_state`. The writes y_j ← y_j + y_{j+1} for j = 0, 1, ..., k - 1,
performed one entry at a time in increasing j. -/
def iterateState : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => Function.update (iterateState k y) k (iterateState k y k + iterateState k y (k + 1))

/-- The loop turns y into the array whose entry j is y_j + y_{j+1} for j < k, and y_j for j ≥ k. -/
theorem iterateState_apply (k : ℕ) (y : ℕ → G) (j : ℕ) :
    iterateState k y j = if j < k then y j + y (j + 1) else y j := by
  induction k generalizing j with
  | zero => simp [iterateState]
  | succ k ih =>
      rw [iterateState, Function.update_apply, ih, ih, ih]
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all

/-- On an array of d + 1 entries, one run of the loop is one application of next. -/
theorem truncate_iterateState (d : ℕ) (y : ℕ → G) :
    truncate d (iterateState d y) = next (truncate d y) := by
  funext j
  simp only [truncate, next, iterateState_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- On an array of d + 1 entries, i runs of the loop are i applications of next. -/
theorem truncate_iterateState_iterate (d i : ℕ) (y : ℕ → G) :
    truncate d ((iterateState d)^[i] y) = next^[i] (truncate d y) :=
  Semiconj.iterate_right (truncate_iterateState d) i y

/-- One differencing pass as the loop performs it: the writes y_j ← y_j - y_{j-1} for
j = top, top - 1, ..., k, one entry at a time in decreasing j. -/
def computeStatePass (k : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | top + 1, y =>
      if k ≤ top + 1 then computeStatePass k top (Function.update y (top + 1) (y (top + 1) - y top))
      else y

/-- The pass turns y into the array whose entry j is y_j - y_{j-1} for k ≤ j ≤ top, and y_j
elsewhere. -/
theorem computeStatePass_apply {k : ℕ} (hk : 1 ≤ k) (top : ℕ) (y : ℕ → G) (j : ℕ) :
    computeStatePass k top y j = if k ≤ j ∧ j ≤ top then y j - y (j - 1) else y j := by
  induction top generalizing y j with
  | zero => rw [computeStatePass, if_neg (by omega)]
  | succ top ih =>
      rw [computeStatePass]
      by_cases hk' : k ≤ top + 1
      · rw [if_pos hk', ih, Function.update_apply, Function.update_apply]
        split_ifs <;> first | rfl | (exfalso; omega) | simp_all
      · rw [if_neg hk', if_neg (by omega)]

/-- Arrays with the same first d + 1 entries agree at every index up to d. -/
private theorem eq_of_truncate_eq {d : ℕ} {A B : ℕ → G} (hAB : truncate d A = truncate d B) {j : ℕ}
    (hj : j ≤ d) : A j = B j := by
  simpa [truncate, hj] using congrFun hAB j

/-- On an array of d + 1 entries, one pass of the loop is one all-at-once pass, for k ≥ 1. -/
private theorem truncate_computeStatePass {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (y : ℕ → G) :
    truncate d (computeStatePass k d y) = truncate d (diffPass k y) := by
  funext j
  simp only [truncate, diffPass, computeStatePass_apply hk]
  split_ifs <;> first | rfl | tauto

/-- A pass sends arrays with the same first d + 1 entries to arrays with the same first d + 1
entries. -/
private theorem truncate_diffPass_congr {d k : ℕ} {A B : ℕ → G}
    (hAB : truncate d A = truncate d B) :
    truncate d (diffPass k A) = truncate d (diffPass k B) := by
  funext j
  by_cases hj : j ≤ d
  · simp [truncate, diffPass, hj, eq_of_truncate_eq hAB hj,
      eq_of_truncate_eq hAB (show j - 1 ≤ d by omega)]
  · simp [truncate, hj]

/-- Passes 1 through k as the loop performs them, each writing the entries top, top - 1, ..., down
to its own number. `computeState` runs all of them. -/
def computeStatePasses (top : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => computeStatePass (k + 1) top (computeStatePasses top k y)

/-- On an array of d + 1 entries, k passes of the loop are the k all-at-once passes. -/
private theorem truncate_computeStatePasses (d k : ℕ) (y : ℕ → G) :
    truncate d (computeStatePasses d k y) = truncate d (diffPasses k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [computeStatePasses, diffPasses, truncate_computeStatePass (by omega)]
      exact truncate_diffPass_congr ih

/-- `fastcrypto`'s `compute_state`: all d passes over an array of d + 1 entries. -/
def computeState (d : ℕ) (y : ℕ → G) : ℕ → G := computeStatePasses d d y

/-- On an array of d + 1 entries, the initialisation loop builds what the d all-at-once passes
build. -/
theorem truncate_computeState (d : ℕ) (y : ℕ → G) :
    truncate d (computeState d y) = truncate d (diffPasses d y) :=
  truncate_computeStatePasses d d y

/-- If Δ_h^{d+1} f = 0, then initialising an array of d + 1 entries from the values f(x), f(x + h),
..., f(x + d·h) and applying the update loop i times leaves f(x + i·h) in entry 0. -/
theorem iterateState_iterate_computeState_zero {h : M} {f : M → G} {d : ℕ}
    (hf : Δ_[h]^[d + 1] f = 0) (x : M) (i : ℕ) :
    (iterateState d)^[i] (computeState d fun j ↦ f (x + j • h)) 0 = f (x + i • h) := by
  have h0 : ∀ z : ℕ → G, (iterateState d)^[i] z 0 = next^[i] (truncate d z) 0 := fun z ↦ by
    rw [← truncate_iterateState_iterate]
    simp [truncate]
  rw [h0, truncate_computeState]
  exact next_iterate_diffPasses_zero hf x i

section Eval

open Polynomial

variable {R : Type*} [CommRing R]

/-- Differencing s ↦ g(h·s + x) with step 1, at t, gives Δ_h g at h·t + x. -/
private theorem fwdDiff_comp_affine (h x : R) (g : R → G) (t : R) :
    Δ_[1] (fun s ↦ g (h * s + x)) t = Δ_[h] g (h * t + x) := by
  simp [fwdDiff, mul_add, add_right_comm]

/-- Differencing s ↦ g(h·s + x) n times with step 1, at t, gives Δ_h^n g at h·t + x. -/
theorem fwdDiff_iter_comp_affine (n : ℕ) (h x : R) (g : R → G) (t : R) :
    Δ_[1]^[n] (fun s ↦ g (h * s + x)) t = Δ_[h]^[n] g (h * t + x) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        show (Δ_[1] fun s ↦ g (h * s + x)) = fun s ↦ Δ_[h] g (h * s + x) from
          funext (fwdDiff_comp_affine h x g)]
      exact ih (Δ_[h] g)

/-- Δ_h^n P = 0 for deg P < n, at any step h -/
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

/-- Δ_h^n (x ↦ x^k) = 0 for k < n, at any step h -/
theorem fwdDiff_iter_pow_eq_zero {k n : ℕ} (hk : k < n) (h : R) :
    Δ_[h]^[n] (fun x : R ↦ x ^ k) = 0 := by
  have hXk : ((X : R[X]) ^ k).natDegree ≤ k := by
    simpa using le_trans natDegree_pow_le (Nat.mul_le_mul (le_refl k) natDegree_X_le)
  simpa using fwdDiff_iter_eval_eq_zero (lt_of_le_of_lt hXk hk) h

end Eval

/-- A polynomial with coefficients c_0, ..., c_degree in V, as `fastcrypto`'s `Poly<C>` stores them.
Coefficients past `degree` are ignored. -/
structure Poly (V : Type*) where
  degree : ℕ
  coeff : ℕ → V

section Coeffs

open Finset Polynomial

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- P(x) = ∑_{k ≤ degree} x^k · c_k, with coefficients in a module V over R and the variable in R,
a case `Polynomial R` does not describe. This is the function `fastcrypto`'s `Poly::eval`
computes. -/
def Poly.eval (P : Poly V) (x : R) : V := ∑ k ∈ range (P.degree + 1), x ^ k • P.coeff k

/-- For a fixed v, differencing y ↦ p(y)·v n times gives y ↦ (Δ_h^n p)(y)·v. -/
theorem fwdDiff_iter_smul_const (n : ℕ) (h : R) (p : R → R) (v : V) :
    Δ_[h]^[n] (fun y ↦ p y • v) = fun y ↦ (Δ_[h]^[n] p y) • v := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        show (Δ_[h] fun y ↦ p y • v) = fun y ↦ (Δ_[h] p y) • v from by
          funext y; simp [fwdDiff, sub_smul]]
      exact ih (Δ_[h] p)

/-- Δ_h^n P = 0 for degree < n, at any step h -/
theorem Poly.fwdDiff_iter_eval_eq_zero (P : Poly V) {n : ℕ} (hn : P.degree < n) (h : R) :
    Δ_[h]^[n] (P.eval : R → V) = 0 := by
  rw [show (P.eval : R → V) = ∑ k ∈ range (P.degree + 1), fun x : R ↦ x ^ k • P.coeff k from by
    funext x; simp [Poly.eval], fwdDiff_iter_finsetSum]
  refine sum_eq_zero fun k hk ↦ ?_
  have hk' : k < n := by have := mem_range.mp hk; omega
  rw [fwdDiff_iter_smul_const n h (fun x : R ↦ x ^ k) (P.coeff k), fwdDiff_iter_pow_eq_zero hk' h]
  funext x
  simp

/-- Correctness of `Poly::eval_range` in `fastcrypto-tbls`. Initialising an array of d + 1 entries
from the values P(x), P(x + h), ..., P(x + d·h), where d is the degree of P, and applying the
update loop i times leaves P(x + i·h) in entry 0. -/
theorem eval_range_correct (P : Poly V) (h x : R) (i : ℕ) :
    (iterateState P.degree)^[i] (computeState P.degree fun j ↦ P.eval (x + j * h)) 0
      = P.eval (x + i * h) := by
  have hf := P.fwdDiff_iter_eval_eq_zero (Nat.lt_succ_self P.degree) h
  simpa [nsmul_eq_mul] using iterateState_iterate_computeState_zero hf x i

end Coeffs

end PolyEval
