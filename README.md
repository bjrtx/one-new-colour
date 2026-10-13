# One new colour suffices for stepping up

A Lean 4 formalisation accompanying the paper *One New Colour Suffices for
Stepping Up* by Bruno Jartoux.

A negative stepping-up lemma carries a Ramsey failure `n ↛ (s_i)^r_{i<k}` from
uniformity `r` to `r + 1`, over the ground set `2^n`, at the cost of larger
goals and some number `η(r)` of additional colours. Keeping the goals minimal
(`s_i + 1` for the old colours, `r + 2` for the new ones), this development
proves, for `k ≥ 2` and all `s_i > r`,

- `n ↛ (s_i)^r_{i<k}  ⟹  2^n ↛ ((s_i + 1)_{i<k}, r + 2)^{r+1}_{k+1}` for `r ≥ 5`,
- `n ↛ (s_i)^4_{i<k}  ⟹  2^n ↛ ((s_i + 1)_{i<k}, 6, 6)^5_{k+2}`,

improving the colour counts of Jartoux, Keller, Smorodinsky and Yuditsky
(SIAM J. Discrete Math. 36 (2022), Theorem 1.2). Both hold more generally for
an arbitrary cardinal ground set, cardinal goals and an ordinal number of
colours, and the finitary statements are derived from the infinitary ones.

## Main statements

| | finitary (`SteppingUpLemma/Arrow.lean`) | infinitary (`SteppingUpLemma/Infinitary.lean`) |
|---|---|---|
| `η(r) = 1`, `r ≥ 5` | `SteppingUp.stepping_up_eta_one` | `SteppingUp.Infinitary.stepping_up_eta_one` |
| `η(4) = 2` | `SteppingUp.stepping_up_eta_two_r4` | `SteppingUp.Infinitary.stepping_up_eta_two_r4` |
| `η(3) = 1` (JKSY's, reproved) | `SteppingUp.stepping_up_eta_one_r3` | `SteppingUp.Infinitary.stepping_up_eta_one_r3` |

There is no `sorry`, and no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. The combinatorial core, a table of 69 classes checked against
621 constraints, is decided by the Lean kernel.

## Building

The project builds against Lean `v4.33.0` and Mathlib `v4.33.0`.

```
lake exe cache get
lake build
```

Two further targets are kept out of the default build:

- `lake build Challenge` states the two new results against Mathlib alone,
  with `sorry` in place of the proofs; the two `sorry` warnings are expected.
- `lake build Enumerations` prints the 621 constraints listed in the paper's
  appendix and recomputes the other counts the paper quotes.

Docstrings refer to the paper by its LaTeX labels, such as `lem:B` or
`thm:stab`.

## Licence

Apache-2.0; see `LICENSE`.
