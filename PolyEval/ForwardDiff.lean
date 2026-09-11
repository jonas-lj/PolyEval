import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Forward differences

Facts about Δ_h f(x) = f(x + h) - f(x) on their own, before any of the algorithm that uses them.
Mathlib proves the vanishing results for step size 1 only, and the algorithm needs an arbitrary
step, which `fwdDiff_iter_comp_affine` supplies by rescaling the variable.
-/

open Function fwdDiff

namespace PolyEval

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- Δ_h^j f(x + h) = Δ_h^j f(x) + Δ_h^{j+1} f(x) -/
theorem fwdDiff_iter_add_right (h : M) (f : M → G) (x : M) (j : ℕ) :
    Δ_[h]^[j] f (x + h) = Δ_[h]^[j] f x + Δ_[h]^[j + 1] f x := by
  rw [iterate_succ_apply' (fwdDiff h) j f]
  simp [fwdDiff]

/-- Δ_h^k 0 = 0 -/
private theorem fwdDiff_iter_zero (h : M) (k : ℕ) : Δ_[h]^[k] (0 : M → G) = 0 := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using map_zero (fwdDiff_aux.fwdDiffₗ M G h ^ k)

/-- Δ_h^{d+1} f = 0 and d < j imply Δ_h^j f = 0 -/
theorem fwdDiff_iter_eq_zero_of_lt {h : M} {f : M → G} {d : ℕ} (hf : Δ_[h]^[d + 1] f = 0) {j : ℕ}
    (hj : d < j) : Δ_[h]^[j] f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + (d + 1) := ⟨j - (d + 1), by omega⟩
  rw [iterate_add_apply, hf, fwdDiff_iter_zero]

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

section Coeffs

open Finset Polynomial

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- The polynomial function P(x) = ∑_{k ≤ d} x^k · c_k, with coefficients c_k in a module V over R
and the variable running over R. This is `fastcrypto`'s `Poly<C>`, whose coefficients are group
elements and whose variable is a scalar, a case `Polynomial R` does not describe. -/
def evalCoeffs (d : ℕ) (c : ℕ → V) : R → V := fun x ↦ ∑ k ∈ range (d + 1), x ^ k • c k

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

/-- Δ_h^n P = 0 for d < n, at any step h, where P(x) = ∑_{k ≤ d} x^k · c_k. -/
theorem fwdDiff_iter_evalCoeffs_eq_zero {d n : ℕ} (hd : d < n) (c : ℕ → V) (h : R) :
    Δ_[h]^[n] (evalCoeffs d c : R → V) = 0 := by
  rw [show (evalCoeffs d c : R → V) = ∑ k ∈ range (d + 1), fun x : R ↦ x ^ k • c k from by
    funext x; simp [evalCoeffs], fwdDiff_iter_finsetSum]
  refine sum_eq_zero fun k hk ↦ ?_
  have hk' : k < n := by have := mem_range.mp hk; omega
  rw [fwdDiff_iter_smul_const n h (fun x : R ↦ x ^ k) (c k), fwdDiff_iter_pow_eq_zero hk' h]
  funext x
  simp

end Coeffs

end PolyEval
