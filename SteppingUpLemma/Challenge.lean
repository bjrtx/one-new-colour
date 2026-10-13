/-
  # Challenge: one new colour suffices for stepping up

  A partition relation `n → (s_0, …, s_{k-1})^r` says that every colouring of
  the `r`-subsets of an `n`-element set in `k` colours has, for some colour
  `i`, a set of `s i` points all of whose `r`-subsets get colour `i`. Its
  negation `n ↛ (s_i)^r` asserts a colouring with no such set.

  A *stepping-up lemma* propagates such a failure one level of uniformity up:
  from `n ↛ (s_i)^r` to `2^n ↛ (s'_i)^{r+1}`. The classical constructions pay
  for the extra uniformity in one of two currencies — larger goals `s'_i`, or
  extra colours. Fixing the goals at the smallest interesting value `s_i + 1`,
  write `η(r)` for the number of *additional* colours needed.

  Jartoux, Keller, Smorodinsky and Yuditsky (SIAM J. Discrete Math. 36 (2022),
  Theorem 1.2) achieve `η(3) = 1`, `η(4) = 3`, and, for `r ≥ 5`, `η(r) = 2`
  for odd `r` and `3` for even `r`. (Their arXiv version, 2103.12627v1, states
  the two parities the other way round; its construction is the same, with a
  third new colour exactly when `r` is even.) The theorems below improve the
  last two: one additional colour suffices for every `r ≥ 5`, and two rather
  than three suffice at `r = 4`.

  Each is stated twice. The finitary form, over a ground set of `n` naturals,
  is the one the Ramsey-number application uses. The infinitary form, in the
  `Infinitary` namespace below, is the primary one: the ground-set size and
  each colour's target size are arbitrary cardinals, the colour count is an
  arbitrary ordinal, and the finitary form is a transport of it rather than a
  separate construction. A solution is expected to prove all four.

  This module is deliberately self-contained: it imports only Mathlib, states
  the vocabulary it needs, and leaves the theorems as `sorry`.

  ## Reading the statements

  `Arrow n r k s` is the positive relation, so each theorem's hypothesis and
  conclusion are both negations of it: a colouring witnessing the failure
  downstairs is turned into one witnessing the failure upstairs.

  Colourings are *total* functions `Finset ℕ → Fin k`, with the colour bound
  carried in the type. Nothing is claimed about their values on sets that are
  not `r`-subsets of the ground set, so totality is not a strengthening of the
  sources' formulation, which colours only the `r`-subsets.

  The ground set upstairs is `2^n` points, and `Arrow` quantifies over
  `X ⊆ range n`: it is a statement about a ground set of that *size* and
  nothing else, invariant under any bijection of the ground set.

  `stepSizesEtaOne r s` and `stepSizesR4 s` are the stepped-up goals: `s i + 1`
  in each recycled colour `i < k`, and a constant in each new colour. The
  constants (`r + 2` at `r ≥ 5`, `6` at `r = 4`) are what the constructions
  achieve; they are not free parameters.

  `2 ≤ k` is a hypothesis rather than an offset `k + 2` in the statement,
  because it is a mathematical side condition and not a well-definedness
  requirement: `Arrow n r k s` is perfectly well formed at `k = 0`, and the
  offset form would force the conclusion's colour count to be written
  `k + 2 + 1` and would obscure the parallel `5 ≤ r` bound.

  Infinitarily, the colour count `k` is an ordinal, so a colour is an element
  of `Set.Iio k` and `i < k` needs no side condition; the ground set upstairs
  is `Set Ordinal`, standing in for `2 ^ κ` via `𝒫(κ) ≃ 2^κ`. Only the
  uniformity `r` stays a natural number, since it counts the elements of a
  `Finset`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace SteppingUp

open Finset

/-- Erdős–Rado arrow relation `n → (s 0, …, s (k-1))^r`. -/
def Arrow (n r k : ℕ) (s : Fin k → ℕ) : Prop :=
  -- Under every colouring with colours in {0, ... , k - 1} ...
  ∀ f : Finset ℕ → Fin k,
  -- there is a colour `i` and a subset of {0, ... , n - 1} of cardinality
  -- `s i`, every `r`-subset of which gets colour `i`.
    ∃ i : Fin k, ∃ X ⊆ range n, #X = s i ∧ ∀ T ⊆ X, #T = r → f T = i

/-- The target sizes for the stepped-up relation at `r ≥ 5`: `s i + 1` in the
old colours, `r + 2` in the single new one. -/
def stepSizesEtaOne (r : ℕ) {k : ℕ} (s : Fin k → ℕ) (j : Fin (k + 1)) : ℕ :=
  if h : j < k then s ⟨j, h⟩ + 1 else r + 2

/-- The target sizes for the stepped-up relation at `r = 4`: `s i + 1` in the
old colours, `6` in either of the two new ones. -/
def stepSizesR4 {k : ℕ} (s : Fin k → ℕ) (j : Fin (k + 2)) : ℕ :=
  if h : j < k then s ⟨j, h⟩ + 1 else 6

/-- **The stepping-up lemma with `η(r) = 1` for `r ≥ 5`.**

If some colouring of the `r`-subsets of `n` points in `k` colours has no
monochromatic set of size `s i` in colour `i`, then some colouring of the
`(r+1)`-subsets of `2^n` points in `k + 1` colours has no monochromatic set of
size `s i + 1` in any recycled colour `i`, nor of size `r + 2` in the new one.

Improves JKSY Theorem 1.2, which pays `η(r) = 2` for odd `r` and `3` for
even `r`. -/
theorem stepping_up_eta_one (k n r : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hr : 5 ≤ r) (hn : r < n)
    (hs : ∀ i, r + 1 ≤ s i)
    (h : ¬ Arrow n r k s) :
    ¬ Arrow (2 ^ n) (r + 1) (k + 1) (stepSizesEtaOne r s) := by
  sorry

/-- **The stepping-up lemma with `η(4) = 2`.**

The same statement one level lower, where two new colours are needed rather
than one. Improves JKSY Theorem 1.2, which pays `η(4) = 3`. -/
theorem stepping_up_eta_two_r4 (k n : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hn : 4 < n)
    (hs : ∀ i, 5 ≤ s i)
    (h : ¬ Arrow n 4 k s) :
    ¬ Arrow (2 ^ n) 5 (k + 2) (stepSizesR4 s) := by
  sorry

/-! ## The infinitary form

The same two results with every finite quantity replaced by its transfinite
counterpart. These are the primary statements; the finitary theorems above are
obtained from them by transport. -/

namespace Infinitary

open Cardinal

/-- The stepped-up ground set: `Set Ordinal` plays the role of `2 ^ κ`. -/
abbrev SetOrd := Set Ordinal

/-- `X` is monochromatic in colour `i` for the `r`-subset colouring `f`. -/
def Mono {V : Type*} {k : Ordinal} (f : Finset V → Set.Iio k) (r : ℕ) (X : Set V)
    (i : Set.Iio k) : Prop :=
  ∀ T : Finset V, (↑T ⊆ X) → T.card = r → f T = i

/-- `κ → (s 0, …, s (k-1))^r`, the cardinal partition relation with the vertex
type `V` left generic, mirroring `Arrow` exactly (there specialised to
`V = ℕ`, `κ = n`, `k : ℕ`). The vertex universe size `κ`, the colour count
`k : Ordinal` and the per-colour target sizes `s` are fully general; only the
sought witnesses' arity `r` stays a natural number. Colour indices live in
`Set.Iio k`, so `i < k` needs no side condition. -/
def ArrowsTo (V : Type*) (κ : Cardinal) (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal) : Prop :=
  ∀ Vfull : Set V, #Vfull = κ →
  ∀ f : Finset V → Set.Iio k,
    ∃ i : Set.Iio k, ∃ X ⊆ Vfull, #X = s i ∧ Mono f r X i

/-- The stepped-up target sizes: `s i + 1` in the old colours, `r + 2` in each
of the new ones. Shared by both cases — only the number of new colours
differs. -/
noncomputable def stepSizes (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal) (j : Ordinal) :
    Cardinal :=
  if j < k then s j + 1 else (r : Cardinal) + 2

/-- **The infinitary stepping-up lemma with `η(r) = 1` for `r ≥ 5`**, of which
`SteppingUp.stepping_up_eta_one` is the finitary shadow. -/
theorem stepping_up_eta_one (κ : Cardinal) (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k) (hr : 5 ≤ r)
    (hs : ∀ i, i < k → (r + 1 : Cardinal) ≤ s i)
    (h : ¬ ArrowsTo Ordinal κ r k s) :
    ¬ ArrowsTo SetOrd (2 ^ κ) (r + 1) (k + 1) (stepSizes r k s) := by
  sorry

/-- **The infinitary stepping-up lemma with `η(4) = 2`**, of which
`SteppingUp.stepping_up_eta_two_r4` is the finitary shadow. This is the one
case that genuinely needs more than one new colour. -/
theorem stepping_up_eta_two_r4 (κ : Cardinal) (k : Ordinal) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k)
    (hs : ∀ i, i < k → (5 : Cardinal) ≤ s i)
    (h : ¬ ArrowsTo Ordinal κ 4 k s) :
    ¬ ArrowsTo SetOrd (2 ^ κ) 5 (k + 2) (stepSizes 4 k s) := by
  sorry

end Infinitary

/-! ## Two candidate rephrasings of the finitary statements

Both say the finitary result in the infinitary vocabulary, at vertex type `ℕ`:
`Arrow n r k s` is exactly `ArrowsTo ℕ n r k` applied to the corresponding
size family, so nothing is gained or lost, only spelled differently. They
differ in how the per-colour target sizes are supplied.

`AltA` keeps the finitary family `s : Fin k → ℕ` and carries it into
`Ordinal → Cardinal` along `ordSizes`. That is the mechanical translation, but
it costs three auxiliary declarations — `ordSizes` is a dependent definition,
so stating it at all requires `onat` and a proof that `onat` respects the
bound.

`AltB` drops the finitary family: `s` is an arbitrary `Ordinal → Cardinal`.
It needs no new vocabulary whatever, and makes the finitary theorem differ
from the infinitary one in exactly two visible respects — the vertex type is
`ℕ` rather than `Ordinal`/`SetOrd`, and the sizes are natural-number casts.
The price is `hsn : ∀ i < k, s i ≤ n`, which no other statement here needs:
without it `s` may exceed `n`, where the hypothesis is vacuous — no subset of
an `n`-set has that size — and the conclusion becomes a Ramsey lower bound
with nothing to derive it from. In `AltA` that bound is free, carried by the
type of `s`.

Exactly one of `AltA`, `AltB` and the `Arrow` phrasing at the top of this file
should survive; the other two are to be deleted. -/

namespace AltA

open Infinitary Cardinal

/-- The natural number that a `< ω` ordinal names. Junk (`0`) above `ω`. -/
noncomputable def onat (o : Ordinal) : ℕ := o.card.toNat

@[simp, norm_cast] lemma onat_natCast (m : ℕ) : onat (m : Ordinal) = m := by
  simp [onat]

/-- An ordinal below a natural bound *is* a natural cast. -/
lemma exists_natCast_eq {o : Ordinal} {n : ℕ} (h : o < n) :
    ∃ m : ℕ, o = (m : Ordinal) :=
  Ordinal.lt_omega0.1 (h.trans (Ordinal.natCast_lt_omega0 n))

lemma onat_lt {o : Ordinal} {n : ℕ} (h : o < n) : onat o < n := by
  obtain ⟨m, rfl⟩ := exists_natCast_eq h; exact_mod_cast h

/-- A finitary size family read as an infinitary one: `0` outside `Fin k`. -/
noncomputable def ordSizes {k : ℕ} (s : Fin k → ℕ) (j : Ordinal) : Cardinal :=
  if h : j < (k : Ordinal) then (s ⟨onat j, onat_lt h⟩ : Cardinal) else 0

/-- **`η(r) = 1` for `r ≥ 5`, finitary, in the `ArrowsTo` vocabulary.** -/
theorem stepping_up_eta_one (k n r : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hr : 5 ≤ r) (hn : r < n)
    (hs : ∀ i, r + 1 ≤ s i)
    (h : ¬ ArrowsTo ℕ n r k (ordSizes s)) :
    ¬ ArrowsTo ℕ (2 ^ n) (r + 1) (k + 1) (stepSizes r k (ordSizes s)) := by
  sorry

/-- **`η(4) = 2`, finitary, in the `ArrowsTo` vocabulary.** -/
theorem stepping_up_eta_two_r4 (k n : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hn : 4 < n)
    (hs : ∀ i, 5 ≤ s i)
    (h : ¬ ArrowsTo ℕ n 4 k (ordSizes s)) :
    ¬ ArrowsTo ℕ (2 ^ n) 5 (k + 2) (stepSizes 4 k (ordSizes s)) := by
  sorry

end AltA

namespace AltB

open Infinitary Cardinal

/-- **`η(r) = 1` for `r ≥ 5`, finitary, in the `ArrowsTo` vocabulary.**

The ground set is a set of `n` naturals and the stepped-up one a set of `2 ^ n`
naturals. `hsn` has no counterpart in the other statements: it is what makes
the sizes finite, which is what stands in for a finitary size family here. -/
theorem stepping_up_eta_one (k n r : ℕ) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k) (hr : 5 ≤ r) (hn : r < n)
    (hs : ∀ i < k, r + 1 ≤ s i)
    (hsn : ∀ i < k, s i ≤ n)
    (h : ¬ ArrowsTo ℕ n r k s) :
    ¬ ArrowsTo ℕ (2 ^ n) (r + 1) (k + 1) (stepSizes r k s) := by
  sorry

/-- **`η(4) = 2`, finitary, in the `ArrowsTo` vocabulary.** -/
theorem stepping_up_eta_two_r4 (k n : ℕ) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k) (hn : 4 < n)
    (hs : ∀ i < k, 5 ≤ s i)
    (hsn : ∀ i < k, s i ≤ n)
    (h : ¬ ArrowsTo ℕ n 4 k s) :
    ¬ ArrowsTo ℕ (2 ^ n) 5 (k + 2) (stepSizes 4 k s) := by
  sorry

end AltB

end SteppingUp
