import PolyEval.ForwardDiff

/-!
# Polynomial evaluation on an arithmetic progression

To evaluate a polynomial P at x, x + h, x + 2h, ..., keep its forward difference table, whose j-th
entry is y_j = Δ_h^j P(x), where Δ_h f(x) = f(x + h) - f(x). Then repeatedly replace every entry by
y_j + y_{j+1}. The head runs through the values of P, at a cost of deg P additions and no
multiplications per point.

`eval_range_correct` is the whole algorithm, initialisation included, as `Poly::eval_range` in
`fastcrypto-tbls` runs it. One call of `next` performs one update, and `h` is the spacing of the
progression, which `fastcrypto` calls `step`.

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

/-- One call of `fastcrypto`'s `next`. Every entry gains the one below it, y_j ← y_j + y_{j+1}, for
all j at once. -/
def next (y : ℕ → G) : ℕ → G := fun j ↦ y j + y (j + 1)

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

/-- If Δ_h^{d+1} f = 0, then the d passes over the values f(x), f(x + h), ..., f(x + d·h), read as
an array of d + 1 entries, give the table of f at x. -/
theorem truncate_diffPasses {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) (x : M) :
    truncate d (diffPasses d fun j ↦ f (x + j • h)) = table h f x := by
  funext j
  simp only [truncate]
  by_cases hj : j ≤ d
  · rw [if_pos hj]
    exact diffPasses_eq_table h x f hj
  · rw [if_neg hj]
    simp [table, fwdDiff_iter_eq_zero_of_lt hf (by omega : d < j)]

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
      rw [iterateState, Function.update_apply]
      by_cases hj : j = k
      · subst hj
        rw [if_pos rfl, ih, ih]
        simp
      · rw [if_neg hj, ih]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega : j < k + 1)]
        · rw [if_neg hjk, if_neg (by omega : ¬ j < k + 1)]

/-- On an array of d + 1 entries, one run of the loop is one application of next. -/
theorem truncate_iterateState (d : ℕ) (y : ℕ → G) :
    truncate d (iterateState d y) = next (truncate d y) := by
  funext j
  simp only [truncate, next, iterateState_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- On an array of d + 1 entries, i runs of the loop are i applications of next. -/
theorem truncate_iterateState_iterate (d i : ℕ) (y : ℕ → G) :
    truncate d ((iterateState d)^[i] y) = next^[i] (truncate d y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply, iterate_succ_apply, ih, truncate_iterateState]

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
      · rw [if_pos hk', ih]
        by_cases hjt : j ≤ top
        · rw [Function.update_of_ne (by omega : j ≠ top + 1),
            Function.update_of_ne (by omega : j - 1 ≠ top + 1)]
          by_cases hkj : k ≤ j
          · rw [if_pos ⟨hkj, hjt⟩, if_pos ⟨hkj, by omega⟩]
          · rw [if_neg (by tauto), if_neg (by tauto)]
        · by_cases hjt' : j = top + 1
          · subst hjt'
            rw [if_neg (by omega), if_pos ⟨hk', le_refl _⟩, Function.update_self]
            simp
          · rw [if_neg (by omega), if_neg (by omega),
              Function.update_of_ne (by omega : j ≠ top + 1)]
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
  simp only [truncate, diffPass]
  by_cases hj : j ≤ d
  · rw [if_pos hj, if_pos hj, eq_of_truncate_eq hAB hj,
      eq_of_truncate_eq hAB (by omega : j - 1 ≤ d)]
  · rw [if_neg hj, if_neg hj]

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

section EvalRange

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Correctness of `Poly::eval_range` in `fastcrypto-tbls`. For P(x) = ∑_{k ≤ d} x^k · c_k,
initialising an array of d + 1 entries from the values P(x), P(x + h), ..., P(x + d·h) and
applying the update loop i times leaves P(x + i·h) in entry 0. -/
theorem eval_range_correct (d : ℕ) (c : ℕ → V) (h x : R) (i : ℕ) :
    (iterateState d)^[i] (computeState d fun j ↦ evalCoeffs d c (x + j * h)) 0
      = evalCoeffs d c (x + i * h) := by
  have hf := fwdDiff_iter_evalCoeffs_eq_zero (Nat.lt_succ_self d) c h
  simpa [nsmul_eq_mul] using iterateState_iterate_computeState_zero hf x i

end EvalRange

end PolyEval
