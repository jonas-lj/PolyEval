# polyeval

A Lean 4 formalisation of the algorithm for evaluating a polynomial on an arithmetic progression,
as implemented by [`Poly::eval_range`][eval_range] in `fastcrypto-tbls`.

The algorithm is Knuth's, *The Art of Computer Programming*, Volume 2, section 4.6.4, where the
initialisation is exercise 7. It is also described [here](https://www.jonaslindstrom.dk/?p=1306).

To evaluate $P$ at $x, x + h, x + 2h, \dots$, keep the forward difference table of $P$ at $x$,

$$y_j = \Delta_h^j P(x), \qquad \Delta_h f(x) = f(x + h) - f(x),$$

and repeatedly replace every entry by

$$y_j \leftarrow y_j + y_{j + 1}.$$

The head $y_0$ then runs through $P(x), P(x + h), P(x + 2h), \dots$, at a cost of $\deg P$
additions and no multiplications per point, against the $\deg P$ additions and $\deg P$
multiplications of Horner's rule.

## Main results

* `PolyEval.eval_range_correct` — correctness of the algorithm as an implementation runs it:

  ```lean
  theorem eval_range_correct (P : Poly V) (h x : R) (i : ℕ) :
      (iterateState P.degree)^[i] (computeState P.degree fun j ↦ P.eval (x + j * h)) 0
        = P.eval (x + i * h)
  ```

  Read the left-hand side inside out, which is also the order things happen: the values of the
  polynomial at the first `d + 1` points, the initialisation loops, `i` runs of the update loop,
  then the head of the array. Each loop carries its visit order, so it lines up with the code
  statement by statement.

  A `Poly V` has its coefficients in a module `V` over `R` and its variable in `R`, which is the
  shape of `fastcrypto`'s `Poly<C>`. `Polynomial R` does not describe those, since it puts the
  coefficients and the variable in the same ring. A ring is a module over itself, so this also
  covers `Poly<C::ScalarType>`, and a `Polynomial R` of degree at most `d` is the `Poly R` with
  that degree and the same coefficients.

* `PolyEval.iterateState_iterate_computeState_zero` — the same for an arbitrary `f` killed by
  `d + 1` differences. Being a polynomial is used nowhere else, so that one hypothesis is all a
  polynomial has to supply.

* `PolyEval.truncate_iterateState` and `PolyEval.truncate_computeState` — each loop, visit order
  included, agrees with the all-at-once update it implements. These carry the read-before-write
  reasoning that writing one entry at a time relies on.

* `PolyEval.next_iterate_diffPasses_zero` — the same correctness statement one layer down, about
  `next` and `diffPasses`, which rewrite the whole array at once. `PolyEval.truncate_diffPasses` is
  the step identifying the initialised array with the difference table.

* `PolyEval.next_iterate_zero` — the heart of it, for an arbitrary function and an untruncated
  table:

  ```lean
  theorem next_iterate_zero (h : M) (f : M → G) (x : M) (i : ℕ) :
      next^[i] (table h f x) 0 = f (x + i • h)
  ```

* `PolyEval.fwdDiff_iter_eval_eq_zero` — $\Delta_h^n P = 0$ whenever $\deg P < n$. Mathlib proves
  this for step size $1$ only, as `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`, and this
  generalises it to an arbitrary step. `PolyEval.fwdDiff_iter_evalCoeffs_eq_zero` is the
  module-valued counterpart, and it is what makes `d + 1` entries enough.

## The implementation

Line links are pinned to commit [`45ec479`][eval_range_pinned], since line numbers move.

| Lean | fastcrypto |
| --- | --- |
| `Poly V` | [`Poly<C>`][poly] |
| `P.eval` | [`eval`][eval] |
| `d`, that is `P.degree` | [`degree`][degree], the index of the last non-zero coefficient |
| the values at the first `d + 1` points | [`new`][new] |
| `computeState d` | [`compute_state`][compute_state] |
| `truncate d` | `state` being a [`Vec` of `d + 1` entries][evaluator] |
| `iterateState d` | [`iterate_state`][iterate_state] |
| `(iterateState d)^[i] ... 0` | [`next`][next], which skips the update on the first call |
| `eval_range_correct` | [`eval_range`][eval_range_pinned] |

`iterateState` and `computeState` are named for the Rust functions they model, and write one entry
at a time in the order those loops visit them. `PolyEval.truncate_iterateState` and
`PolyEval.truncate_computeState` prove that each agrees with the all-at-once update it implements.
This is what pins the loop directions down. The update loop reads the entry above the one it
writes, so it has to run upwards, and a differencing pass reads the entry below, so it has to run
downwards. Reversing either would read an entry it had already overwritten.

Three details of the correspondence are worth stating, since the theorem does not see them.

* The array is `degree() + 1` long rather than one per coefficient. Dropping zero leading
  coefficients leaves the function unchanged, so summing only up to `degree()` gives the same
  polynomial.
* Index arithmetic is checked and the iterator ends rather than wrapping, so the points really are
  the arithmetic progression.
* [`eval_range`][eval_range] evaluates directly when `m` is 0 or `u16::MAX`, or when the degree is
  at least `u16::MAX`. Those branches never reach the algorithm.

What the alignment still rests on, and Lean does not check: that Horner's rule in [`eval`][eval]
computes the polynomial, that the loops never index outside the array, which is what makes it sound
to treat the entries past its end as zero, and that a `ShareIndex` converts to a scalar compatibly
with the arithmetic on indices.

[eval_range]: https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto-tbls/src/polynomial.rs
[poly]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L26
[degree]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L45-L47
[eval]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L137-L150
[eval_range_pinned]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L157-L179
[evaluator]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L642-L647
[new]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L653-L673
[compute_state]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L690-L698
[iterate_state]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L700-L704
[next]: https://github.com/MystenLabs/fastcrypto/blob/45ec479119f0feaebc65c1665cbfbda9b629bdb2/fastcrypto-tbls/src/polynomial.rs#L710-L721
