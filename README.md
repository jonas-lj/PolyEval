# polyeval

A Lean 4 formalisation of the algorithm behind [`Poly::eval_range`][eval_range] in
`fastcrypto-tbls`, which evaluates a polynomial on an arithmetic progression. The algorithm is
Knuth's, *The Art of Computer Programming*, Volume 2, section 4.6.4, with the initialisation in
exercise 7, and is described [here](https://www.jonaslindstrom.dk/?p=1306).

To evaluate $P$ at $x, x + h, x + 2h, \dots$, keep the forward difference table

$$y_j = \Delta_h^j P(x), \qquad \Delta_h f(x) = f(x + h) - f(x),$$

and repeatedly replace every entry by $y_j + y_{j + 1}$. The head $y_0$ runs through the values of
$P$, at $\deg P$ additions and no multiplications per point, against the $\deg P$ additions and
$\deg P$ multiplications of Horner's rule.

## The theorem

```lean
theorem eval_range_correct (P : Poly V) (x h : R) (i : ℕ) :
    State.iterate^[i] (State.init P x h) 0 = P.eval (x + i * h)
```

`State.init P x h` evaluates $P$ at the first $d + 1$ points and runs the initialisation loop, as
[`new`][new] does. `State.iterate` runs the update loop, reading the array length from the state as
[`iterate_state`][iterate_state] reads it from the vector. So entry 0 after $i$ runs is the value at
the $i$-th point. Both loops write one entry at a time, in the order the Rust visits them.

A `Poly V` has its coefficients in a module `V` over `R` and its variable in `R`, the shape of
[`Poly<C>`][poly]. A ring is a module over itself, so this covers `Poly<C::ScalarType>` too.

## The implementation

Line links are pinned to commit [`45ec479`][eval_range_pinned], since line numbers move.

| Lean | fastcrypto |
| --- | --- |
| `Poly V` | [`Poly<C>`][poly] |
| `P.eval` | [`eval`][eval] |
| `d`, that is `P.degree` | [`degree`][degree] |
| `State` | [`state`][evaluator], a `Vec` of `d + 1` entries that knows its length |
| `State.init P x h` | the state [`new`][new] builds |
| `computeState d` | [`compute_state`][compute_state] |
| `iterateState d` | [`iterate_state`][iterate_state] |
| `State.iterate^[i]`, entry 0 | [`next`][next], which skips the update on the first call |
| `eval_range_correct` | [`eval_range`][eval_range_pinned] |

Lean does not check that Horner's rule in [`eval`][eval] computes the polynomial, nor that a
`ShareIndex` converts to a scalar compatibly with the arithmetic on indices.

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
