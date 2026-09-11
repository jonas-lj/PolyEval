# polyeval

A Lean 4 formalisation of the algorithm for evaluating a polynomial on an arithmetic progression,
as implemented by [`Poly::eval_range`][eval_range] in `fastcrypto-tbls`.

The algorithm is Knuth's, *The Art of Computer Programming*, Volume 2, section 4.6.4, where the
initialisation is exercise 7. It is also described [here](https://www.jonaslindstrom.dk/?p=1306).

To evaluate `P` at `x`, `x + h`, `x + 2h`, ..., keep the forward difference table of `P` at `x` and
repeatedly replace every entry `y j` by `y j + y (j + 1)`; the head of the table runs through the
values of `P`. Each point then costs `deg P` additions and no multiplications, against the `deg P`
additions and `deg P` multiplications of Horner's rule.

## Main results

* `PolyEval.step_iterate_zero` — the algorithm is correct for an arbitrary function:

  ```lean
  theorem step_iterate_zero (h : M) (f : M → G) (x : M) (i : ℕ) :
      step^[i] (table h f x) 0 = f (x + i • h)
  ```

* `PolyEval.table_eq_zero_of_lt` — for a polynomial of degree at most `d` the table vanishes above
  entry `d`, so `d + 1` entries suffice and the algorithm is finite.

* `PolyEval.step_iterate_diffPasses_zero_eval` — correctness of the whole algorithm on an array of
  length `d + 1`, initialisation included:

  ```lean
  theorem step_iterate_diffPasses_zero_eval {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) (h x : R)
      (i : ℕ) :
      step^[i] (truncate d (diffPasses d fun j ↦ P.eval (x + j * h))) 0 = P.eval (x + i * h)
  ```

  Here `diffPasses d` is the differencing triangle `y j ← y j - y (j - 1)` that an implementation
  runs on the values of `P` at the first `d + 1` points, and `truncate d` reads the result as a
  length-`d + 1` array. `PolyEval.truncate_diffPasses_eval` is the step that identifies it with the
  difference table.

* `PolyEval.step_iterate_diffPasses_zero` — the same statement for an arbitrary `f` killed by
  `d + 1` differences. Being a polynomial is used nowhere else, so each flavour of polynomial only
  has to supply that one hypothesis.

* `PolyEval.step_iterate_diffPasses_zero_evalCoeffs` — the flavour whose coefficients live in a
  module `V` over `R` while the variable runs over `R`:

  ```lean
  theorem step_iterate_diffPasses_zero_evalCoeffs (d : ℕ) (c : ℕ → V) (h x : R) (i : ℕ) :
      step^[i] (truncate d (diffPasses d fun j ↦ evalCoeffs d c (x + j * h))) 0
        = evalCoeffs d c (x + i * h)
  ```

  This is the shape of `fastcrypto`'s `Poly<C>`, whose coefficients are group elements and whose
  variable is a scalar. `Polynomial R` does not describe those, since it puts the coefficients and
  the variable in the same ring. A ring is a module over itself, so this statement also covers
  `Poly<C::ScalarType>`.

* `PolyEval.fwdDiff_iter_eval_eq_zero` — `Δ_[h]^[n] P.eval = 0` when `P.natDegree < n`. Mathlib has
  this only for step size `1` (`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`); this generalises it
  to an arbitrary step. `PolyEval.fwdDiff_iter_evalCoeffs_eq_zero` is the module-valued counterpart.

[eval_range]: https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto-tbls/src/polynomial.rs
