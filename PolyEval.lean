import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial evaluation on an arithmetic progression

To evaluate a polynomial P at x, x + h, x + 2h, ..., keep its forward difference table, whose j-th
entry is y_j = Δ_h^j P(x), where Δ_h f(x) = f(x + h) - f(x). Then repeatedly replace every entry by
y_j + y_{j+1}. The head runs through the values of P, at a cost of deg P additions and no
multiplications per point.

`eval_range_correct` is the whole algorithm as `Poly::eval_range` in `fastcrypto-tbls` runs it, down
to the evaluator it iterates. x is what `fastcrypto` calls `initial`, and h, the spacing of the
progression, is its `step`.

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

/-- The update `fastcrypto`'s `iterate_state` performs, all entries at once: y_j ← y_j + y_{j+1}. -/
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
  have := Semiconj.iterate_right (f := table h f) (ga := (· + h)) (gb := next)
    (fun x ↦ (next_table h f x).symm) i x
  simpa [add_right_iterate] using this.symm

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

/-- Δ_h^{d+1} f = 0 and d < j imply Δ_h^j f = 0 -/
theorem fwdDiff_iter_eq_zero_of_lt {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) {j : ℕ}
    (hj : d < j) : Δ_[h]^[j] f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + (d + 1) := ⟨j - (d + 1), by omega⟩
  rw [iterate_add_apply, hf]
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using map_zero (fwdDiff_aux.fwdDiffₗ M G h ^ k)

/-- If Δ_h^{d+1} f = 0, then the d passes over the values f(x), f(x + h), ..., f(x + d·h), read as
an array of d + 1 entries, give the table of f at x. -/
theorem truncate_diffPasses {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) (x : M) :
    truncate d (diffPasses d fun j ↦ f (x + j • h)) = table h f x := by
  funext j
  by_cases hj : j ≤ d
  · simp [truncate, hj, table, diffPasses_apply]
  · simp [truncate, hj, table, fwdDiff_iter_eq_zero_of_lt hf (by omega : d < j)]

/-- If Δ_h^{d+1} f = 0, then the d passes over the values f(x), f(x + h), ..., f(x + d·h), read as
an array of d + 1 entries, followed by i applications of next, leave f(x + i·h) in entry 0. -/
theorem next_iterate_diffPasses_zero {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0)
    (x : M) (i : ℕ) :
    next^[i] (truncate d (diffPasses d fun j ↦ f (x + j • h))) 0 = f (x + i • h) := by
  rw [truncate_diffPasses hf, next_iterate_zero]

/-! ### The loops as an implementation runs them

`next` and `diffPass` rewrite the whole array at once, while an implementation writes one entry of a
vector at a time. The definitions below are those loops on a vector of d + 1 entries, visit order
included, so every read and write is checked to stay inside it, and each loop is proved equal to the
update it implements. The orders are forced: the update loop reads the entry above the one it
writes, so it must run upwards, and a differencing pass reads the entry below, so it must run
downwards. Reversing either makes it read an entry it has already overwritten.
-/

/-- The vector read as a function on every index, with everything past its end set to zero. -/
def toFun {d : ℕ} (v : Vector G (d + 1)) : ℕ → G := fun j ↦ if h : j < d + 1 then v[j] else 0

/-- toFun v j = v_j for j ≤ d -/
private theorem toFun_of_lt {d j : ℕ} (v : Vector G (d + 1)) (h : j < d + 1) :
    toFun v j = v[j] := by
  simp [toFun, h]

/-- Writing entry i of the vector updates entry i of toFun v. -/
private theorem toFun_set {d i : ℕ} (v : Vector G (d + 1)) (hi : i < d + 1) (a : G) :
    toFun (v.set i a hi) = Function.update (toFun v) i a := by
  funext j
  by_cases hj : j < d + 1
  · by_cases hij : j = i
    · subst hij; simp [toFun, hj]
    · simp [toFun, hj, hij, Ne.symm hij]
  · simp [toFun, hj, show j ≠ i by omega]

/-- The first k writes of `fastcrypto`'s `iterate_state`: y_j ← y_j + y_{j+1} for
j = 0, 1, ..., k - 1, one entry at a time in increasing j. -/
def iterateStateAux (d : ℕ) : (k : ℕ) → k ≤ d → Vector G (d + 1) → Vector G (d + 1)
  | 0, _, v => v
  | k + 1, hk, v =>
      let w := iterateStateAux d k (by omega) v
      w.set k (w[k] + w[k + 1])

/-- `fastcrypto`'s `iterate_state` on d + 1 entries. -/
def iterateState (d : ℕ) (v : Vector G (d + 1)) : Vector G (d + 1) := iterateStateAux d d le_rfl v

/-- The loop turns y into the array whose entry j is y_j + y_{j+1} for j < k, and y_j for j ≥ k. -/
theorem toFun_iterateStateAux (d k : ℕ) (hk : k ≤ d) (v : Vector G (d + 1)) (j : ℕ) :
    toFun (iterateStateAux d k hk v) j
      = if j < k then toFun v j + toFun v (j + 1) else toFun v j := by
  induction k generalizing j with
  | zero => simp [iterateStateAux]
  | succ k ih =>
      simp only [iterateStateAux]
      rw [toFun_set, Function.update_apply, ← toFun_of_lt _ (by omega : k < d + 1),
        ← toFun_of_lt _ (by omega : k + 1 < d + 1), ih, ih, ih]
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all

/-- One run of the loop is one application of next. -/
theorem toFun_iterateState (d : ℕ) (v : Vector G (d + 1)) :
    toFun (iterateState d v) = next (toFun v) := by
  funext j
  rw [iterateState, toFun_iterateStateAux]
  simp only [next]
  split_ifs with hj
  · rfl
  · rw [show toFun v (j + 1) = 0 by simp [toFun, show ¬ j + 1 < d + 1 by omega], add_zero]

/-- i runs of the loop are i applications of next. -/
theorem toFun_iterateState_iterate (d i : ℕ) (v : Vector G (d + 1)) :
    toFun ((iterateState d)^[i] v) = next^[i] (toFun v) :=
  Semiconj.iterate_right (toFun_iterateState d) i v

/-- One differencing pass as the loop performs it: the writes y_j ← y_j - y_{j-1} for
j = top, top - 1, ..., k, one entry at a time in decreasing j. -/
def computeStatePass (d k : ℕ) : (top : ℕ) → top ≤ d → Vector G (d + 1) → Vector G (d + 1)
  | 0, _, v => v
  | top + 1, ht, v =>
      if k ≤ top + 1 then
        computeStatePass d k top (by omega) (v.set (top + 1) (v[top + 1] - v[top]))
      else v

/-- The pass turns y into the array whose entry j is y_j - y_{j-1} for k ≤ j ≤ top, and y_j
elsewhere. -/
theorem toFun_computeStatePass {d k : ℕ} (hk : 1 ≤ k) (top : ℕ) (ht : top ≤ d)
    (v : Vector G (d + 1)) (j : ℕ) :
    toFun (computeStatePass d k top ht v) j
      = if k ≤ j ∧ j ≤ top then toFun v j - toFun v (j - 1) else toFun v j := by
  induction top generalizing v j with
  | zero => rw [computeStatePass, if_neg (by omega)]
  | succ top ih =>
      rw [computeStatePass]
      by_cases hk' : k ≤ top + 1
      · rw [if_pos hk', ih, toFun_set, Function.update_apply, Function.update_apply,
          ← toFun_of_lt _ (by omega : top + 1 < d + 1),
          ← toFun_of_lt _ (by omega : top < d + 1)]
        split_ifs <;> first | rfl | (exfalso; omega) | simp_all
      · rw [if_neg hk', if_neg (by omega)]

/-- One pass of the loop over all d + 1 entries is one all-at-once pass, for k ≥ 1. -/
private theorem toFun_computeStatePass_top {d k : ℕ} (hk : 1 ≤ k) (v : Vector G (d + 1)) :
    toFun (computeStatePass d k d le_rfl v) = truncate d (diffPass k (toFun v)) := by
  funext j
  rw [toFun_computeStatePass hk]
  simp only [truncate, diffPass]
  by_cases hj : j ≤ d
  · split_ifs <;> first | rfl | (exfalso; omega)
  · simp [hj, toFun, show ¬ j < d + 1 by omega]

/-- A pass sends arrays with the same first d + 1 entries to arrays with the same first d + 1
entries. -/
private theorem truncate_diffPass_congr {d k : ℕ} {A B : ℕ → G}
    (hAB : truncate d A = truncate d B) :
    truncate d (diffPass k A) = truncate d (diffPass k B) := by
  have e : ∀ {j}, j ≤ d → A j = B j := fun {j} hj ↦ by simpa [truncate, hj] using congrFun hAB j
  funext j
  by_cases hj : j ≤ d
  · simp [truncate, diffPass, hj, e hj, e (show j - 1 ≤ d by omega)]
  · simp [truncate, hj]

/-- Passes 1 through k as the loop performs them. `computeState` runs all of them. -/
def computeStatePasses (d : ℕ) : ℕ → Vector G (d + 1) → Vector G (d + 1)
  | 0, v => v
  | k + 1, v => computeStatePass d (k + 1) d le_rfl (computeStatePasses d k v)

/-- If toFun v and g agree on the first d + 1 entries, k passes of the loop on v are the k
all-at-once passes on g. -/
private theorem toFun_computeStatePasses {d : ℕ} {v : Vector G (d + 1)} {g : ℕ → G}
    (hg : toFun v = truncate d g) (k : ℕ) :
    toFun (computeStatePasses d k v) = truncate d (diffPasses k g) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
      rw [computeStatePasses, toFun_computeStatePass_top (by omega), ih, diffPasses]
      exact truncate_diffPass_congr (by funext j; by_cases hj : j ≤ d <;> simp [truncate, hj])

/-- `fastcrypto`'s `compute_state`: all d passes over d + 1 entries. -/
def computeState (d : ℕ) (v : Vector G (d + 1)) : Vector G (d + 1) := computeStatePasses d d v

/-- If toFun v and g agree on the first d + 1 entries, the initialisation loop on v builds what the
d all-at-once passes build on g. -/
theorem toFun_computeState {d : ℕ} {v : Vector G (d + 1)} {g : ℕ → G}
    (hg : toFun v = truncate d g) :
    toFun (computeState d v) = truncate d (diffPasses d g) :=
  toFun_computeStatePasses hg d

/-- If Δ_h^{d+1} f = 0, then initialising d + 1 entries from the values f(x), f(x + h), ...,
f(x + d·h) and applying the update loop i times leaves f(x + i·h) in entry 0. -/
theorem iterateState_iterate_computeState_zero {h : M} {f : M → G} {d : ℕ}
    (hf : Δ_[h]^[d + 1] f = 0) (x : M) (i : ℕ) :
    ((iterateState d)^[i] (computeState d (Vector.ofFn fun j ↦ f (x + (j : ℕ) • h))))[0]
      = f (x + i • h) := by
  have hv : toFun (Vector.ofFn fun j : Fin (d + 1) ↦ f (x + (j : ℕ) • h))
      = truncate d (fun j ↦ f (x + j • h)) := by
    funext j
    by_cases hj : j ≤ d
    · simp [toFun, truncate, hj, show j < d + 1 by omega]
    · simp [toFun, truncate, hj, show ¬ j < d + 1 by omega]
  have e := congrFun (toFun_iterateState_iterate d i
    (computeState d (Vector.ofFn fun j ↦ f (x + (j : ℕ) • h)))) 0
  rw [toFun_computeState hv, next_iterate_diffPasses_zero hf x i] at e
  simpa [toFun] using e

/-! ### The evaluator -/

/-- `fastcrypto`'s `PolynomialEvaluator`: the state, whether next has yet to be called, the current
index and the step. -/
structure Evaluator (M G : Type*) (d : ℕ) where
  state : Vector G (d + 1)
  first : Bool
  index : M
  step : M

/-- `fastcrypto`'s `PolynomialEvaluator::new`. -/
def Evaluator.new (d : ℕ) (f : M → G) (initial step : M) : Evaluator M G d where
  state := computeState d (Vector.ofFn fun j ↦ f (initial + (j : ℕ) • step))
  first := true
  index := initial
  step := step

/-- `fastcrypto`'s `next`: it outputs the index and entry 0 of the state, after advancing both
unless this is the first call. -/
def Evaluator.next {d : ℕ} (e : Evaluator M G d) : (M × G) × Evaluator M G d :=
  if e.first then ((e.index, e.state[0]), { e with first := false })
  else
    let e' : Evaluator M G d :=
      { e with index := e.index + e.step, state := iterateState d e.state }
    ((e'.index, e'.state[0]), e')

/-- After i + 1 calls to next, the evaluator holds the state after i updates, at index x + i·h. -/
theorem Evaluator.iterate_next_new {h : M} {f : M → G} {d : ℕ} (x : M) (i : ℕ) :
    (fun e : Evaluator M G d ↦ e.next.2)^[i + 1] (Evaluator.new d f x h)
      = ⟨(iterateState d)^[i] (computeState d (Vector.ofFn fun j ↦ f (x + (j : ℕ) • h))),
          false, x + i • h, h⟩ := by
  induction i with
  | zero => simp [Evaluator.next, Evaluator.new]
  | succ i ih =>
      rw [iterate_succ_apply', ih]
      simp [Evaluator.next, iterate_succ_apply', succ_nsmul, add_assoc]

/-- If Δ_h^{d+1} f = 0, then call i of next outputs (x + i·h, f(x + i·h)). -/
theorem Evaluator.next_iterate_new {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0)
    (x : M) (i : ℕ) :
    ((fun e : Evaluator M G d ↦ e.next.2)^[i] (Evaluator.new d f x h)).next.1
      = (x + i • h, f (x + i • h)) := by
  cases i with
  | zero =>
      have := iterateState_iterate_computeState_zero hf x 0
      simp_all [Evaluator.next, Evaluator.new]
  | succ i =>
      rw [Evaluator.iterate_next_new]
      have := iterateState_iterate_computeState_zero hf x (i + 1)
      simp_all [Evaluator.next, iterate_succ_apply', succ_nsmul, add_assoc]

section Eval

open Polynomial

variable {R : Type*} [CommRing R]

/-- Differencing s ↦ g(h·s + x) n times with step 1, at t, gives Δ_h^n g at h·t + x. -/
theorem fwdDiff_iter_comp_affine (n : ℕ) (h x : R) (g : R → G) (t : R) :
    Δ_[1]^[n] (fun s ↦ g (h * s + x)) t = Δ_[h]^[n] g (h * t + x) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply, iterate_succ_apply,
        show (Δ_[1] fun s ↦ g (h * s + x)) = fun s ↦ Δ_[h] g (h * s + x) from
          funext fun t ↦ by simp [fwdDiff, mul_add, add_right_comm]]
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

/-- Correctness of `Poly::eval_range` in `fastcrypto-tbls`: call i of next on the evaluator for P,
started at x with step h, outputs (x + i·h, P(x + i·h)). -/
theorem eval_range_correct (P : Poly V) (x h : R) (i : ℕ) :
    ((fun e : Evaluator R V P.degree ↦ e.next.2)^[i] (Evaluator.new P.degree P.eval x h)).next.1
      = (x + i * h, P.eval (x + i * h)) := by
  simpa [nsmul_eq_mul] using
    Evaluator.next_iterate_new (P.fwdDiff_iter_eval_eq_zero (Nat.lt_succ_self P.degree) h) x i

end Coeffs

end PolyEval
