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

`step` and `diffPasses` rewrite the whole array at once, while an implementation writes one entry
at a time. `stepSeq` and `diffPassesSeq` are the loops with their visit orders, and
`stepSeq_iterate_diffPassesSeq_zero` is the same correctness statement about them.

The algorithm uses one property of `P` and nothing else: `d + 1` differences annihilate it. So
`truncate_diffPasses` and `step_iterate_diffPasses_zero` assume just `Δ_[h]^[d + 1] f = 0`, for an
arbitrary `f`. `step_iterate_diffPasses_zero_evalCoeffs` is the second flavour they cover, with
coefficients in a module over `R` and the variable in `R`. That is what `fastcrypto` evaluates when
the coefficients are group elements.

The algorithm is Knuth's, *The Art of Computer Programming*, Volume 2, section 4.6.4, where the
initialisation is exercise 7. It is also described at <https://www.jonaslindstrom.dk/?p=1306>. The
implementation these results are stated against is `Poly::eval_range` in `fastcrypto-tbls`,
<https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto-tbls/src/polynomial.rs>.
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

/-- `Δ_[h]^[k] 0 = 0` -/
theorem fwdDiff_iter_zero (h : M) (k : ℕ) : Δ_[h]^[k] (0 : M → G) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iterate_succ_apply', ih]
      funext x
      simp [fwdDiff]

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
theorem step_iterate_diffPasses_zero {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0)
    (x : M) (i : ℕ) :
    step^[i] (truncate d (diffPasses d fun j ↦ f (x + j • h))) 0 = f (x + i • h) := by
  rw [truncate_diffPasses hf, step_iterate_zero]

/-! ### The loops as an implementation runs them

`step` and `diffPass` rewrite the whole array at once, while an implementation writes one entry at
a time. The definitions below are those loops, visit order included, and each is proved equal to
the update it implements. The orders are forced: the update loop reads the entry above the one it
writes, so it must run upwards, and a differencing pass reads the entry below, so it must run
downwards. Reversing either makes it read an entry it has already overwritten.
-/

/-- The update loop `y j ← y j + y (j + 1)`, run for `j = 0, 1, ..., k - 1` in that order, one
entry at a time. -/
def stepSeq : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => Function.update (stepSeq k y) k (stepSeq k y k + stepSeq k y (k + 1))

/-- Running the loop upwards leaves every read untouched, so it adds the original `y (j + 1)`. -/
theorem stepSeq_apply (k : ℕ) (y : ℕ → G) (j : ℕ) :
    stepSeq k y j = if j < k then y j + y (j + 1) else y j := by
  induction k generalizing j with
  | zero => simp [stepSeq]
  | succ k ih =>
      rw [stepSeq, Function.update_apply]
      by_cases hj : j = k
      · subst hj
        rw [if_pos rfl, ih, ih]
        simp
      · rw [if_neg hj, ih]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega : j < k + 1)]
        · rw [if_neg hjk, if_neg (by omega : ¬ j < k + 1)]

/-- On an array of `d + 1` entries, the update loop is `step`. -/
theorem truncate_stepSeq (d : ℕ) (y : ℕ → G) :
    truncate d (stepSeq d y) = step (truncate d y) := by
  funext j
  simp only [truncate, step, stepSeq_apply]
  by_cases hj : j < d
  · rw [if_pos (by omega : j ≤ d), if_pos hj, if_pos (by omega : j ≤ d),
      if_pos (by omega : j + 1 ≤ d)]
  · by_cases hjd : j ≤ d
    · rw [if_pos hjd, if_neg hj, if_pos hjd, if_neg (by omega : ¬ j + 1 ≤ d), add_zero]
    · rw [if_neg hjd, if_neg hjd, if_neg (by omega : ¬ j + 1 ≤ d), add_zero]

/-- `i` runs of the update loop are `i` applications of `step`. -/
theorem truncate_stepSeq_iterate (d i : ℕ) (y : ℕ → G) :
    truncate d ((stepSeq d)^[i] y) = step^[i] (truncate d y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply, iterate_succ_apply, ih, truncate_stepSeq]

/-- One differencing pass `y j ← y j - y (j - 1)`, run for `j = top, top - 1, ..., k` in that
order, one entry at a time. -/
def diffPassSeq (k : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | top + 1, y =>
      if k ≤ top + 1 then diffPassSeq k top (Function.update y (top + 1) (y (top + 1) - y top))
      else y

/-- Running a pass downwards leaves every read untouched, so it subtracts the original
`y (j - 1)`. -/
theorem diffPassSeq_apply {k : ℕ} (hk : 1 ≤ k) (top : ℕ) (y : ℕ → G) (j : ℕ) :
    diffPassSeq k top y j = if k ≤ j ∧ j ≤ top then y j - y (j - 1) else y j := by
  induction top generalizing y j with
  | zero => rw [diffPassSeq, if_neg (by omega)]
  | succ top ih =>
      rw [diffPassSeq]
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

/-- If two arrays agree on their first `d + 1` entries then they agree entrywise below `d`. -/
theorem eq_of_truncate_eq {d : ℕ} {A B : ℕ → G} (hAB : truncate d A = truncate d B) {j : ℕ}
    (hj : j ≤ d) : A j = B j := by
  simpa [truncate, hj] using congrFun hAB j

/-- On an array of `d + 1` entries, one differencing pass is `diffPass`. -/
theorem truncate_diffPassSeq {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (y : ℕ → G) :
    truncate d (diffPassSeq k d y) = truncate d (diffPass k y) := by
  funext j
  simp only [truncate, diffPass, diffPassSeq_apply hk]
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

/-- The initialisation as an implementation runs it: the passes `1, ..., k`, each writing the
entries `top`, `top - 1`, ..., down to the number of the pass. -/
def diffPassesSeq (top : ℕ) : ℕ → (ℕ → G) → (ℕ → G)
  | 0, y => y
  | k + 1, y => diffPassSeq (k + 1) top (diffPassesSeq top k y)

/-- On an array of `d + 1` entries, the initialisation loops are `diffPasses`. -/
theorem truncate_diffPassesSeq (d k : ℕ) (y : ℕ → G) :
    truncate d (diffPassesSeq d k y) = truncate d (diffPasses k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [diffPassesSeq, diffPasses, truncate_diffPassSeq (by omega)]
      exact truncate_diffPass_congr ih

/-- Correctness of the algorithm as the loops actually run it, one entry at a time. -/
theorem stepSeq_iterate_diffPassesSeq_zero {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0)
    (x : M) (i : ℕ) :
    (stepSeq d)^[i] (diffPassesSeq d d fun j ↦ f (x + j • h)) 0 = f (x + i • h) := by
  have h0 : ∀ z : ℕ → G, (stepSeq d)^[i] z 0 = step^[i] (truncate d z) 0 := fun z ↦ by
    rw [← truncate_stepSeq_iterate]
    simp [truncate]
  rw [h0, truncate_diffPassesSeq]
  exact step_iterate_diffPasses_zero hf x i

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
  exact truncate_diffPasses (fwdDiff_iter_eval_eq_zero (by omega) h) x

/-- Correctness of the algorithm as implemented on a length-`d + 1` array: initialise it with the
values of `P` at the first `d + 1` points, run the differencing passes, then step `i` times. The
head of the array then holds `P.eval (x + i * h)`. -/
theorem step_iterate_diffPasses_zero_eval {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) (h x : R)
    (i : ℕ) :
    step^[i] (truncate d (diffPasses d fun j ↦ P.eval (x + j * h))) 0 = P.eval (x + i * h) := by
  rw [truncate_diffPasses_eval hP, step_iterate_zero_eval]

/-- The same, for the loops as an implementation runs them. -/
theorem stepSeq_iterate_diffPassesSeq_zero_eval {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d)
    (h x : R) (i : ℕ) :
    (stepSeq d)^[i] (diffPassesSeq d d fun j ↦ P.eval (x + j * h)) 0 = P.eval (x + i * h) := by
  rw [show (fun j : ℕ ↦ P.eval (x + j * h)) = fun j : ℕ ↦ P.eval (x + j • h) from by
    simp [nsmul_eq_mul]]
  simpa [nsmul_eq_mul] using
    stepSeq_iterate_diffPassesSeq_zero (fwdDiff_iter_eval_eq_zero (by omega) h) x i

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

/-- `truncate d (diffPasses d (values of `evalCoeffs d c`)) = table h (evalCoeffs d c) x` -/
theorem truncate_diffPasses_evalCoeffs (d : ℕ) (c : ℕ → V) (h x : R) :
    truncate d (diffPasses d fun i ↦ evalCoeffs d c (x + i * h)) = table h (evalCoeffs d c) x := by
  rw [show (fun i : ℕ ↦ evalCoeffs d c (x + i * h)) = fun i : ℕ ↦ evalCoeffs d c (x + i • h) from by
    simp [nsmul_eq_mul]]
  exact truncate_diffPasses (fwdDiff_iter_evalCoeffs_eq_zero (Nat.lt_succ_self d) c h) x

/-- Correctness of the algorithm on a length-`d + 1` array of module-valued coefficients:
initialise it with the values of the polynomial at the first `d + 1` points, run the differencing
passes, then step `i` times. The head of the array then holds the value at the `i`-th point. -/
theorem step_iterate_diffPasses_zero_evalCoeffs (d : ℕ) (c : ℕ → V) (h x : R) (i : ℕ) :
    step^[i] (truncate d (diffPasses d fun j ↦ evalCoeffs d c (x + j * h))) 0
      = evalCoeffs d c (x + i * h) := by
  rw [truncate_diffPasses_evalCoeffs, ← nsmul_eq_mul]
  exact step_iterate_zero h (evalCoeffs d c) x i

/-- The same, for the loops as an implementation runs them. -/
theorem stepSeq_iterate_diffPassesSeq_zero_evalCoeffs (d : ℕ) (c : ℕ → V) (h x : R) (i : ℕ) :
    (stepSeq d)^[i] (diffPassesSeq d d fun j ↦ evalCoeffs d c (x + j * h)) 0
      = evalCoeffs d c (x + i * h) := by
  rw [show (fun j : ℕ ↦ evalCoeffs d c (x + j * h)) = fun j : ℕ ↦ evalCoeffs d c (x + j • h) from by
    simp [nsmul_eq_mul]]
  have hf := fwdDiff_iter_evalCoeffs_eq_zero (Nat.lt_succ_self d) c h
  simpa [nsmul_eq_mul] using stepSeq_iterate_diffPassesSeq_zero hf x i

end Coeffs

end PolyEval
