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

## The implementation

Line links are pinned to commit [`45ec479`][eval_range_pinned], since line numbers move.

| Lean | fastcrypto |
| --- | --- |
| `evalCoeffs d c` | the coefficients of [`Poly<C>`][poly], summed by [`eval`][eval] |
| `d` | [`degree`][degree], the index of the last non-zero coefficient |
| the values at the first `d + 1` points | [`new`][new] |
| `diffPasses d` | [`compute_state`][compute_state] |
| `truncate d` | `state` being a [`Vec` of `d + 1` entries][evaluator] |
| `step` | [`iterate_state`][iterate_state] |
| `step^[i] ... 0` | [`next`][next], which skips the update on the first call |
| `step_iterate_diffPasses_zero_evalCoeffs` | [`eval_range`][eval_range_pinned] |

Four details of the correspondence are worth stating, since the theorem does not see them.

* The array is `degree() + 1` long rather than one per coefficient. Dropping zero leading
  coefficients leaves the function unchanged, so the degree hypothesis still holds.
* [`simple_from_evaluations`][simple_from_evaluations] runs one extra update before its first
  yield and labels it index 1. The same theorem covers it, started at 0, with output `i` reached
  after `i + 1` updates.
* Index arithmetic is checked and the iterator ends rather than wrapping, so the points really are
  the arithmetic progression.
* [`eval_range`][eval_range] evaluates directly when `m` is 0 or `u16::MAX`, or when the degree is
  at least `u16::MAX`. Those branches never reach the algorithm.

What the alignment still rests on, and Lean does not check: that Horner's rule in [`eval`][eval]
computes the polynomial, that a `Vec` of `d + 1` entries behaves like a function that is zero above
`d`, that each in-place loop equals the all-at-once update its visit order implies, and that a
`ShareIndex` converts to a scalar compatibly with the arithmetic on indices.

[eval_range]: https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto-tbls/src/polynomial.rs
[poly]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L26
[degree]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L45-L47
[eval]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L137-L150
[eval_range_pinned]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L157-L179
[evaluator]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L642-L647
[new]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L653-L673
[simple_from_evaluations]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L676-L688
[compute_state]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L690-L698
[iterate_state]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L700-L704
[next]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L710-L721
