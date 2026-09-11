import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial evaluation on an arithmetic progression

To evaluate a polynomial at `x`, `x + h`, `x + 2h`, ..., keep its forward difference table
`table h P.eval x`, whose `j`-th entry is `Δ_[h]^[j] P.eval x`, and repeatedly replace every entry
`y j` by `y j + y (j + 1)`. The head runs through the values of `P`, at a cost of `P.natDegree`
additions and no multiplications per point.

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

/-- The difference table of `f` at `x`: entry `j` is `Δ_[h]^[j] f x`. -/
def table (h : M) (f : M → G) (x : M) : ℕ → G := fun j ↦ Δ_[h]^[j] f x

/-- One call of `fastcrypto`'s `next`: `y j ← y j + y (j + 1)`, for every `j` at once. -/
def next (y : ℕ → G) : ℕ → G := fun j ↦ y j + y (j + 1)

/-- `Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x` -/
theorem fwdDiff_iter_add_right (h : M) (f : M → G) (x : M) (j : ℕ) :
    Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x := by
  rw [iterate_succ_apply' (fwdDiff h) j f]
  simp [fwdDiff]

/-- `next (table h f x) = table h f (x + h)` -/
theorem next_table (h : M) (f : M → G) (x : M) : next (table h f x) = table h f (x + h) := by
  funext j
  exact (fwdDiff_iter_add_right h f x j).symm

/-- `next^[i] (table h f x) = table h f (x + i • h)` -/
theorem next_iterate (h : M) (f : M → G) (x : M) (i : ℕ) :
    next^[i] (table h f x) = table h f (x + i • h) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [iterate_succ_apply, next_table, ih, succ_nsmul]
      abel_nf

/-- `next^[i] (table h f x) 0 = f (x + i • h)` -/
theorem next_iterate_zero (h : M) (f : M → G) (x : M) (i : ℕ) :
    next^[i] (table h f x) 0 = f (x + i • h) := by
  rw [next_iterate]
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

/-- `Δ_[h]^[k] 0 = 0` -/
theorem fwdDiff_iter_zero (h : M) (k : ℕ) : Δ_[h]^[k] (0 : M → G) = 0 := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using map_zero (fwdDiff_aux.fwdDiffₗ M G h ^ k)

/-- If the `d + 1`-st difference of `f` vanishes then so does every higher one. -/
theorem fwdDiff_iter_eq_zero_of_lt {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) {j : ℕ}
    (hj : d < j) : Δ_[h]^[j] f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + (d + 1) := ⟨j - (d + 1), by omega⟩
  rw [iterate_add_apply, hf, fwdDiff_iter_zero]

/-- The initialisation is correct for any `f` killed by `d + 1` differences: running the
differencing passes on the values of `f` at the first `d + 1` points of the progression, and reading
the result as a length-`d + 1` array, gives exactly `table h f x`. -/
theorem truncate_diffPasses {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) (x : M) :
    truncate d (diffPasses d fun j ↦ f (x + j • h)) = table h f x := by
  funext j
  simp only [truncate]
  by_cases hj : j ≤ d
  · rw [if_pos hj]
    exact diffPasses_eq_table h x f hj
  · rw [if_neg hj]
    simp [table, fwdDiff_iter_eq_zero_of_lt hf (by omega : d < j)]

/-- Correctness of the algorithm on a length-`d + 1` array, for any `f` killed by `d + 1`
differences. -/
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

/-- `fastcrypto`'s `iterate_state`: the update loop `y j ← y j + y (j + 1)`, run for
`j = 0, 1, ..., k - 1` in that order, one entry at a time. -/
def iterateState : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => Function.update (iterateState k y) k (iterateState k y k + iterateState k y (k + 1))

/-- Running the loop upwards leaves every read untouched, so it adds the original `y (j + 1)`. -/
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

/-- On an array of `d + 1` entries, the update loop is `next`. -/
theorem truncate_iterateState (d : ℕ) (y : ℕ → G) :
    truncate d (iterateState d y) = next (truncate d y) := by
  funext j
  simp only [truncate, next, iterateState_apply]
  by_cases hj : j < d
  · rw [if_pos (by omega : j ≤ d), if_pos hj, if_pos (by omega : j ≤ d),
      if_pos (by omega : j + 1 ≤ d)]
  · by_cases hjd : j ≤ d
    · rw [if_pos hjd, if_neg hj, if_pos hjd, if_neg (by omega : ¬ j + 1 ≤ d), add_zero]
    · rw [if_neg hjd, if_neg hjd, if_neg (by omega : ¬ j + 1 ≤ d), add_zero]

/-- `i` runs of the update loop are `i` applications of `next`. -/
theorem truncate_iterateState_iterate (d i : ℕ) (y : ℕ → G) :
    truncate d ((iterateState d)^[i] y) = next^[i] (truncate d y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply, iterate_succ_apply, ih, truncate_iterateState]

/-- One differencing pass `y j ← y j - y (j - 1)`, run for `j = top, top - 1, ..., k` in that
order, one entry at a time. -/
def computeStatePass (k : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | top + 1, y =>
      if k ≤ top + 1 then computeStatePass k top (Function.update y (top + 1) (y (top + 1) - y top))
      else y

/-- Running a pass downwards leaves every read untouched, so it subtracts the original
`y (j - 1)`. -/
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

/-- If two arrays agree on their first `d + 1` entries then they agree at every entry up to `d`. -/
theorem eq_of_truncate_eq {d : ℕ} {A B : ℕ → G} (hAB : truncate d A = truncate d B) {j : ℕ}
    (hj : j ≤ d) : A j = B j := by
  simpa [truncate, hj] using congrFun hAB j

/-- On an array of `d + 1` entries, one differencing pass is `diffPass`. -/
theorem truncate_computeStatePass {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (y : ℕ → G) :
    truncate d (computeStatePass k d y) = truncate d (diffPass k y) := by
  funext j
  simp only [truncate, diffPass, computeStatePass_apply hk]
  by_cases hj : j ≤ d
  · rw [if_pos hj, if_pos hj]
    by_cases hkj : k ≤ j
    · rw [if_pos ⟨hkj, hj⟩, if_pos hkj]
    · rw [if_neg (by tauto), if_neg hkj]
  · rw [if_neg hj, if_neg hj]

/-- A pass only reads entries at or below the one it writes, so it respects agreement on the first
`d + 1` entries. -/
theorem truncate_diffPass_congr {d k : ℕ} {A B : ℕ → G} (hAB : truncate d A = truncate d B) :
    truncate d (diffPass k A) = truncate d (diffPass k B) := by
  funext j
  simp only [truncate, diffPass]
  by_cases hj : j ≤ d
  · rw [if_pos hj, if_pos hj, eq_of_truncate_eq hAB hj,
      eq_of_truncate_eq hAB (by omega : j - 1 ≤ d)]
  · rw [if_neg hj, if_neg hj]

/-- The passes `1, ..., k` of the initialisation, each writing the entries `top`, `top - 1`, ...,
down to the number of the pass. `computeState` runs all of them. -/
def computeStatePasses (top : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => computeStatePass (k + 1) top (computeStatePasses top k y)

/-- On an array of `d + 1` entries, the initialisation loops are `diffPasses`. -/
theorem truncate_computeStatePasses (d k : ℕ) (y : ℕ → G) :
    truncate d (computeStatePasses d k y) = truncate d (diffPasses k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [computeStatePasses, diffPasses, truncate_computeStatePass (by omega)]
      exact truncate_diffPass_congr ih

/-- The initialisation as a whole, `fastcrypto`'s `compute_state`: all `d` passes over an array of
`d + 1` entries. -/
def computeState (d : ℕ) (y : ℕ → G) : ℕ → G := computeStatePasses d d y

/-- On an array of `d + 1` entries, the initialisation is `diffPasses`. -/
theorem truncate_computeState (d : ℕ) (y : ℕ → G) :
    truncate d (computeState d y) = truncate d (diffPasses d y) :=
  truncate_computeStatePasses d d y

/-- Correctness of the algorithm as the loops actually run it, one entry at a time. -/
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

end Eval

section Coeffs

open Finset Polynomial

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- The polynomial function `x ↦ ∑ k ≤ d, x ^ k • c k`, whose coefficients live in a module `V`
over `R` while the variable runs over `R`. This is `fastcrypto`'s `Poly<C>`, whose coefficients are
group elements and whose variable is a scalar, a case `Polynomial R` does not describe. -/
def evalCoeffs (d : ℕ) (c : ℕ → V) : R → V := fun x ↦ ∑ k ∈ range (d + 1), x ^ k • c k

/-- `Δ_[h]^[n] (fun y ↦ p y • v) = fun y ↦ (Δ_[h]^[n] p y) • v` -/
theorem fwdDiff_iter_smul_const (n : ℕ) (h : R) (p : R → R) (v : V) :
    Δ_[h]^[n] (fun y ↦ p y • v) = fun y ↦ (Δ_[h]^[n] p y) • v := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        show (Δ_[h] fun y ↦ p y • v) = fun y ↦ (Δ_[h] p y) • v from by
          funext y; simp [fwdDiff, sub_smul]]
      exact ih (Δ_[h] p)

/-- `d < n ⇒ Δ_[h]^[n] (evalCoeffs d c) = 0`, for any step `h`. -/
theorem fwdDiff_iter_evalCoeffs_eq_zero {d n : ℕ} (hd : d < n) (c : ℕ → V) (h : R) :
    Δ_[h]^[n] (evalCoeffs d c : R → V) = 0 := by
  rw [show (evalCoeffs d c : R → V) = ∑ k ∈ range (d + 1), fun x : R ↦ x ^ k • c k from by
    funext x; simp [evalCoeffs], fwdDiff_iter_finsetSum]
  refine sum_eq_zero fun k hk ↦ ?_
  have hXk : ((X : R[X]) ^ k).natDegree ≤ k := by
    simpa using le_trans natDegree_pow_le (Nat.mul_le_mul (le_refl k) natDegree_X_le)
  have hk' : ((X : R[X]) ^ k).natDegree < n := by
    have := mem_range.mp hk
    omega
  rw [show (fun x : R ↦ x ^ k • c k) = fun x : R ↦ ((X : R[X]) ^ k).eval x • c k from by
    funext x; simp, fwdDiff_iter_smul_const, fwdDiff_iter_eval_eq_zero hk' h]
  funext x
  simp

/-- Correctness of `fastcrypto`'s `Poly::eval_range`. A polynomial over a commutative ring is the
case `V = R`, via `P.eval y = evalCoeffs d P.coeff y` for `P.natDegree ≤ d`. -/
theorem eval_range_correct (d : ℕ) (c : ℕ → V) (h x : R) (i : ℕ) :
    (iterateState d)^[i] (computeState d fun j ↦ evalCoeffs d c (x + j * h)) 0
      = evalCoeffs d c (x + i * h) := by
  have hf := fwdDiff_iter_evalCoeffs_eq_zero (Nat.lt_succ_self d) c h
  simpa [nsmul_eq_mul] using iterateState_iterate_computeState_zero hf x i

end Coeffs

end PolyEval
