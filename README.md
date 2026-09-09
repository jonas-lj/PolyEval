# polyeval

A Lean 4 formalisation of the algorithm for evaluating a polynomial on an arithmetic progression
presented [here](https://www.jonaslindstrom.dk/?p=1306).

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

* `PolyEval.fwdDiff_iter_eval_eq_zero` — `Δ_[h]^[n] P.eval = 0` when `P.natDegree < n`. Mathlib has
  this only for step size `1` (`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`); this generalises it
  to an arbitrary step.
