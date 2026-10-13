/-
  The stepped-up colouring and the infinitary stepping-up lemma, the
  infinitary form of JKSY's Theorem 1.2. Built on the
  combinatorial infrastructure (`part`/`IsDegenerate`/`delta`/`deltaFinset`,
  `exists_nondegenerate_subset_card`, `powersetCard_deltaFinset`) in
  `SteppingUpLemma.Encoding.Delta`.

  * The partition relation `ArrowsTo` is phrased with cardinal sizes
    throughout (`Cardinal.mk`, written `#`) rather than `Arrow.lean`'s
    `Fin k → ℕ`-indexed tuple of target sizes `s`. Colourings take values in
    `Set.Iio k`, the ordinals below `k`, so the colour bound is carried by
    the type — the infinitary counterpart of `Arrow.lean`'s `Fin k`. That is
    what lets `stepColourOf` and the three `stepColour*` constructions state
    their colour counts (`k + 1`, `k + 2`) in their own signatures instead of
    in separate `_lt` lemmas.

  * `stepSizes`' successor step `s i + 1` is literal `Cardinal` addition, so
    infinite cardinals absorb the `+ 1` (`c + 1 = c`
    when `ℵ₀ ≤ c`), and the same per-colour formula is
    correct whether `s i` is finite or infinite, with no case split needed
    at that level. `stepping_up_of_colouring` needs no such case split
    either: `mono_degenerate` and `isDegenerate_of_mono` are both uniform in
    `#X`, the first because `card_delta` is.

  * The file proves one stepping-up theorem per value of `r`, all of them
    instances of a single `stepping_up_of_colouring`:

      - `stepping_up_eta_one` — `η(r) = 1` for `r ≥ 5`, `stepColourEtaOne`
        from the `c★` table, a single new colour (`k + 1`);
      - `stepping_up_eta_two_r4` — `η(4) = 2`, `stepColourR4` from the `c4`
        table, two new colours (`k + 2`);
      - `stepping_up_eta_one_r3` — `η(3) = 1`, `stepColourR3` from the `c3`
        table, a single new colour (`k + 1`).

    All three rest on `propext`/`Classical.choice`/`Quot.sound` alone.
    Every finite check in the development is reduced by the kernel; none is
    decided by compiled evaluation.

    The improved colourings come from the tree colour tables of
    `SteppingUpLemma.Colouring.Table`, through the `toTree` translation of
    `Encoding/Delta.lean`, via one shared bridge lemma
    `not_mono_of_isValidTable` that is abstract in the colour type. All three
    share the `δ`-pushdown machinery, stated against an abstract colouring
    `F` satisfying `RecyclesOnDegenerate`/`ProperNotMono`, and all three
    share the same target sizes `stepSizes`; only the colour *count* differs.
-/
import SteppingUpLemma.Encoding.Delta
import SteppingUpLemma.Colouring.Table
import SteppingUpLemma.Bridge

namespace SteppingUp.Infinitary

open SteppingUp.Encoding
open Lean.Parser.Tactic
open Cardinal

set_option linter.style.openClassical false
open scoped Classical

/-- Sets of ordinals: a subset of `κ` stands for a point of the stepped-up
ground set `2^κ`. -/
abbrev SetOrd := Set Ordinal

/- Only these names, not the whole `SteppingUp.Bridge` namespace: opening
`SteppingUp` wholesale would make `Mono`, `IsDegenerate` and `toTree`
ambiguous against this file's own. -/
open SteppingUp.Bridge (IsValidTable mem_sSet_iff mem_sSet4_iff
  isValidTable_of_isValidAt isValidTable_of_isValidAt4)

section «Ordinal arithmetic helpers»

/-- **`k`-arithmetic helpers.
The idiomatic Mathlib replacements strip the shared left-fixed `k` —
`lt_add_of_pos_right` for a
strictly positive increment (available since `Ordinal` has
`AddLeftStrictMono`/`AddLeftReflectLT`, but *not* `AddRightStrictMono`:
adding on a fixed *left* summand is strict, adding a fixed *right* summand is
only monotone) — and close the residual pure-`ℕ`-cast numeral comparison.
Together with `self_lt_add_one`/`self_lt_add_two`/`add_one_lt_add_two` below,
these cover every `k`-comparison the colour bounds need. -/
private lemma zero_lt_of_two_le {k : Ordinal} (hk : 2 ≤ k) : (0 : Ordinal) < k :=
  lt_of_lt_of_le (by simp) hk

private lemma one_lt_of_two_le {k : Ordinal} (hk : 2 ≤ k) : (1 : Ordinal) < k :=
  lt_of_lt_of_le (by simp) hk

end «Ordinal arithmetic helpers»

section «The infinitary arrow relation»

/-

1. Vertices of the stepped-up relation are `Set Ordinal`, but `disc`'s splitting
   positions — and hence `delta`'s output — are bare `Ordinal`s.
   So the "old" colouring that `stepColour`
   recurses into via `delta` must live *one level down*, on `Finset
   Ordinal` rather than `Finset SetOrd`: it colours the *base*
   relation (vertices = ordinals themselves, arity `r`), while `stepColour`
   produces the *stepped-up* colouring (vertices = sets of ordinals, arity
   `r + 1`). `Mono`/`ArrowsTo` are therefore stated generically in the
   vertex type `V`, so the same machinery instantiates at both `Ordinal`
   (base level) and `Set Ordinal` (stepped-up level).
-/

/-- `X` is monochromatic in colour `i` for the `r`-subset colouring `f`. -/
def Mono {V : Type*} {k : Ordinal} (f : Finset V → Set.Iio k) (r : ℕ) (X : Set V)
    (i : Set.Iio k) : Prop :=
  ∀ T : Finset V, (↑T ⊆ X) → T.card = r → f T = i

/-- `κ → (s 0, …, s (k-1))^r`, the cardinal partition relation with vertex
type `V` left generic, mirroring `Arrow.lean`'s `Arrow` exactly (there
specialised to `V = ℕ`, `κ = n`, `k : ℕ`). All three of the vertex *universe*
size `κ`, the colour *count* `k : Ordinal`, and the per-colour *target* sizes
`s : Ordinal → Cardinal` are fully general infinite cardinals/ordinals; only
the sought monochromatic witnesses' *arity* `r` stays a natural number.
Colour indices live in `Set.Iio k`, so `i < k` needs no side condition. -/
def ArrowsTo (V : Type*) (κ : Cardinal) (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal) : Prop :=
  ∀ Vfull : Set V, #Vfull = κ →
  ∀ f : Finset V → Set.Iio k,
    ∃ i : Set.Iio k, ∃ X ⊆ Vfull, #X = s i ∧ Mono f r X i

end «The infinitary arrow relation»

section «Final integration»

/-- What every stepped-up colouring in this file has in common, and the only
thing the `δ`-pushdown lemmas below actually need: on a *degenerate* set the
colour is `fr` of its `δ`-image. Abstracting it lets one copy of each pushdown
lemma serve all three of `stepColourEtaOne`, `stepColourR4` and
`stepColourR3`. -/
def RecyclesOnDegenerate {k K : Ordinal} (F : Finset SetOrd → Set.Iio K)
    (fr : Finset Ordinal → Set.Iio k) : Prop :=
  ∀ T : Finset SetOrd, IsDegenerate T → (F T : Ordinal) = fr (deltaFinset T)

/-- The other half of what the pushdown lemmas need from a colouring: no
*proper* set of size `r + 2` is monochromatic in colour `i`. Supplied in
every case by `not_mono_of_isValidTable`, at the case's own colour table. -/
def ProperNotMono {K : Ordinal} (F : Finset SetOrd → Set.Iio K) (r : ℕ) (i : Set.Iio K) : Prop :=
  ∀ Y : Finset SetOrd, Y.card = r + 2 → ¬ IsDegenerate Y → ¬ Mono F (r + 1) Y i

/-- Degenerate tree case: a monochromatic degenerate tree in an old colour `i`
pushes down to a monochromatic set for `fr` via `δ`.

One statement for finite and infinite `X` alike. The `Mono` half never looks at
`#X`: handed an `r`-subset `U` of `δ X`, it picks the `2r` points of `X` that
witness `U`'s discs and applies `powersetCard_deltaFinset` to *that* finite
set — so (I2) staying finitary costs nothing here (`lem:I2-inf`). The cardinality
half is `card_delta`, which is uniform in its own right. -/
lemma mono_degenerate {r : ℕ} {k K : Ordinal} {fr : Finset Ordinal → Set.Iio k}
    {F : Finset SetOrd → Set.Iio K} {X : Set SetOrd} {i : Set.Iio K}
    (hik : (i : Ordinal) < k)
    (hF : RecyclesOnDegenerate F fr) (hdegenerate : IsDegenerate X) (hr : 3 ≤ r)
    (hXne : X.Nonempty) (hmono : Mono F (r + 1) X i) :
    Mono fr r (delta X) ⟨i, hik⟩ ∧ #(delta X) + 1 = #X := by
  refine ⟨?_, card_delta hXne hdegenerate⟩
  intro U hU hUcard
  -- Pull back `U`'s discs to the pairs of `X` that realise them, and work
  -- inside the finite set `X'` those pairs span.
  have hUdelta : ∀ u ∈ U, ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ disc x y = u := by
    intro u hu
    obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩ := hU (Finset.mem_coe.2 hu)
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  choose! xf hxf yf hyf hxyf hdiscf using hUdelta
  set X' : Finset SetOrd := U.biUnion (fun u ↦ {xf u, yf u}) with hX'def
  -- Both endpoints of each disc land in `X'`; that is all three uses below need.
  have hmemX' : ∀ u ∈ U, xf u ∈ X' ∧ yf u ∈ X' := fun u hu =>
    ⟨hX'def ▸ Finset.mem_biUnion.2 ⟨u, hu, by simp⟩,
      hX'def ▸ Finset.mem_biUnion.2 ⟨u, hu, by simp⟩⟩
  have hX'subX : ↑X' ⊆ X := by
    intro z hz
    rw [hX'def, Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨u, hu, hz⟩ := hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    exacts [hxf u hu, hyf u hu]
  have hX'degenerate : IsDegenerate X' := hdegenerate.subset hX'subX
  have hX'ne : X'.Nonempty :=
    (Finset.card_pos.1 (by omega : 0 < U.card)).elim fun u hu => ⟨xf u, (hmemX' u hu).1⟩
  have hUsubDeltaX' : U ⊆ deltaFinset X' := fun u hu => by
    rw [← Finset.mem_coe, coe_deltaFinset_of_finite X'.finite_toSet]
    exact ⟨(xf u, yf u), ⟨(hmemX' u hu).1, (hmemX' u hu).2, hxyf u hu⟩, hdiscf u hu⟩
  have hUmemPS : U ∈ (deltaFinset X').powersetCard r :=
    Finset.mem_powersetCard.2 ⟨hUsubDeltaX', hUcard⟩
  rw [powersetCard_deltaFinset hX'ne hX'degenerate r, Finset.mem_image] at hUmemPS
  obtain ⟨T, hT, hTU⟩ := hUmemPS
  rw [Finset.mem_powersetCard] at hT
  have hTsubX : ↑T ⊆ X := (Finset.coe_subset.2 hT.1).trans hX'subX
  have hstep : (F T : Ordinal) = fr (deltaFinset T) := hF T (hdegenerate.subset hTsubX)
  exact Subtype.ext (by rw [← hTU, ← hstep, hmono T hTsubX hT.2])

/-- Every monochromatic set of size `≥ r + 2` is a degenerate tree.

One statement covers finite and infinite witnesses: `exists_nondegenerate_subset_card`
is uniform in `#X`, so no case split on `X.Finite` is needed here. -/
lemma isDegenerate_of_mono {r : ℕ} {K : Ordinal} {F : Finset SetOrd → Set.Iio K}
    {X : Set SetOrd} {i : Set.Iio K}
    (hnm : ProperNotMono F r i) (hr : 3 ≤ r) (hX : (r + 2 : Cardinal) ≤ #X)
    (hmono : Mono F (r + 1) X i) :
    IsDegenerate X := by
  intro a ha b hb c hc d hd hab hbc hcd hcon
  obtain ⟨T, hTX, hTcard, hTnotdegenerate⟩ :=
    exists_nondegenerate_subset_card
      (· a ha b hb c hc d hd hab hbc hcd hcon) (show 4 ≤ r + 2 by omega)
      (by exact_mod_cast hX)
  exact hnm _ hTcard hTnotdegenerate (fun _ hU ↦ hmono _ (hU.trans hTX))

/-- `δ`'s output always lands back inside any ambient bound `V0` that every
element of the source set is itself a subset of: `disc x y` is a *member* of
the symmetric difference of `x` and `y` (`disc_mem_symmDiff`), and that
symmetric difference is a subset of `V0` whenever `x, y ⊆ V0`. Stated for an
arbitrary bound `V0`, the vertex universe not being a fixed initial
segment. -/
lemma delta_subset_of_subset {S : Set SetOrd} {V0 : Set Ordinal}
    (hS : ∀ x ∈ S, x ⊆ V0) : delta S ⊆ V0 := by
  rintro z ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩
  dsimp only [Function.uncurry] at hx hy hxy ⊢
  rcases disc_mem_symmDiff hxy with ⟨h, _⟩ | ⟨h, _⟩
  · exact hS _ hx h
  · exact hS _ hy h

/-- The target sizes of the stepped-up relation for the strengthened
colouring: `s i + 1` in the old colours, `r + 2` in each of the new ones.
Shared by all three cases — only the number of new colours differs. -/
noncomputable def stepSizes (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal) (j: Ordinal): Cardinal :=
  if j < k then s j + 1 else (r : Cardinal) + 2

set_option maxHeartbeats 1000000 in
universe u v in
/-- **The infinitary stepping-up lemma, over an arbitrary stepped-up
colouring.** Every concrete case (`stepping_up_eta_one` and
`stepping_up_eta_one_r3` with one new colour, `stepping_up_eta_two_r4` with
two) is this
theorem instantiated at its own colouring; nothing in the argument below
depends on *which* colouring is used, only on the three properties
`hrec`/`hnm`/`hflt`.

`mkF` takes the base colouring `fr` as an argument because `fr` is produced
inside the proof, by unfolding the failure of `ArrowsTo … r k s`; its three
hypotheses are correspondingly quantified over `fr`.-/
theorem stepping_up_of_colouring (κ : Cardinal.{u + 1}) (r : ℕ) (k K : Ordinal.{v})
    (s : Ordinal.{v} → Cardinal.{u + 1})
    (mkF : (Finset Ordinal.{u} → Set.Iio k) → Finset (SetOrd.{u}) → Set.Iio K)
    (hk : 2 ≤ k) (hr : 3 ≤ r) (hkK : k ≤ K)
    (hs : ∀ i, i < k → (r + 1 : Cardinal.{u + 1}) ≤ s i)
    (hrec : ∀ fr, RecyclesOnDegenerate (mkF fr) fr)
    (hnm : ∀ fr, ∀ j, ProperNotMono (mkF fr) r j)
    (h : ¬ ArrowsTo Ordinal.{u} κ r k s) :
    ¬ ArrowsTo (Set Ordinal.{u}) (2 ^ κ) (r + 1) K (stepSizes r k s) := by
  unfold ArrowsTo at h
  push Not at h
  obtain ⟨V0, hV0card, fr, hbad⟩ := h
  intro hArrow2
  set Vfull2 : Set SetOrd := 𝒫 V0 with hVfull2_def
  have hVfull2card : #Vfull2 = 2 ^ κ := by
    rw [hVfull2_def, Cardinal.mk_powerset, hV0card]
  set f2 : Finset SetOrd → Set.Iio K :=
    fun S ↦ if S.card = r + 1 then mkF fr S else ⟨0, (zero_lt_of_two_le hk).trans_le hkK⟩
    with hf2_def
  obtain ⟨j, X, hXVfull2, hXcard, hXmono⟩ := hArrow2 Vfull2 hVfull2card f2
  have hrec := hrec fr
  have hNM := hnm fr j
  have hMono_eq : Mono (mkF fr) (r + 1) X j := by
    intro T hT hTcard
    have := hXmono T hT hTcard
    simpa [hf2_def, hTcard] using this
  have hstepSizes_ge : (r + 2 : Cardinal) ≤ stepSizes r k s j := by
    unfold stepSizes
    split_ifs with hjk
    · have hle := hs j hjk
      calc (r : Cardinal) + 2 = r + 1 + 1 := by ring
        _ ≤ s j + 1 := by gcongr
    · exact le_refl _
  have hXsize : (r + 2 : Cardinal) ≤ #X := hXcard ▸ hstepSizes_ge
  have hXsubV0 : ∀ x ∈ X, x ⊆ V0 := fun _ ↦ (hXVfull2 ·)
  by_cases hjk : (j : Ordinal) < k
  · -- Old colour: `X` reduces to a degenerate tree witness contradicting `hbad`.
    have hXcard' : #X = s j + 1 := by simp [hXcard, stepSizes, hjk]
    have hdegenerateX : IsDegenerate X := isDegenerate_of_mono hNM hr hXsize hMono_eq
    have hDeltaSub : delta X ⊆ V0 := delta_subset_of_subset hXsubV0
    have hXne : X.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      simp [hcon] at hXsize
    obtain ⟨hMonoDelta, hDeltaCard⟩ := mono_degenerate hjk hrec hdegenerateX hr hXne hMono_eq
    -- `#(δ X) + 1 = #X = s j + 1`, and `+ 1` is injective on cardinals even
    -- though addition is not cancellative.
    exact hbad ⟨j, hjk⟩ _ hDeltaSub
      (Cardinal.add_one_inj.1 (hDeltaCard.trans hXcard')) hMonoDelta
  · -- New colour: `stepSizes` gives exactly `r + 2`, always finite; no
    -- degenerate tree can realise it, and `hnm` rules out proper trees.
    have hXcard2 : #X = (r + 2 : Cardinal) := by simp [hXcard, stepSizes, hjk]
    have hXfin : X.Finite := by
      rw [← Set.finite_coe_iff, ← Cardinal.mk_lt_aleph0_iff, hXcard2]
      exact_mod_cast (Cardinal.natCast_lt_aleph0 : ((r + 2 : ℕ) : Cardinal) < ℵ₀)
    set Xf : Finset SetOrd := hXfin.toFinset
    have hXfcoe : ↑Xf = X := hXfin.coe_toFinset
    have hXfcard : Xf.card = X.ncard := by rw [← Set.ncard_coe_finset Xf, hXfcoe]
    have hXncardEq : X.ncard = r + 2 := by
      have : X.ncard = ((r + 2 : ℕ) : Cardinal) := by
        rw [Set.cast_ncard hXfin, hXcard2]; push_cast; ring
      exact_mod_cast this
    have hmonoXf : Mono (mkF fr) (r + 1) Xf j := hXfcoe ▸ hMono_eq
    by_cases hdegenerateXf : IsDegenerate Xf
    · obtain ⟨T, hTXf, hTcard⟩ := Finset.exists_subset_card_eq (s := Xf) (n := r + 1) (by omega)
      have hTdegenerate : IsDegenerate T :=
        hdegenerateXf.subset (Finset.coe_subset.mpr hTXf)
      have hstepT : (mkF fr T : Ordinal) = fr (deltaFinset T) := hrec T hTdegenerate
      rw [hmonoXf T (Finset.coe_subset.mpr hTXf) hTcard] at hstepT
      exact hjk (by rw [hstepT]; exact (fr (deltaFinset ↑T)).2)
    · exact hNM _ (by rw [hXfcard, hXncardEq]) hdegenerateXf hmonoXf

end «Final integration»

section «Colour tables and the toTree bridge»

/-! The tree machinery of `SteppingUp.Trees` is ground-set agnostic, so the colour
tables (`c★`, `c4`, `c3`) and their validity theorems are used verbatim; only
the `toTree` correspondence (`Encoding/Delta.lean`) is specific to the
`Finset SetOrd` form.

All three cases (`η = 1` for `r ≥ 5`, `η = 2` for `r = 4`, `η = 1` for
`r = 3`) differ only in the colour type, the table, the set of
*new* colours and the value map. The bridge is therefore stated once, over an
abstract table, and instantiated per case. -/

/-- The stepped-up colouring induced by a tree colour table `c` and a
translation `val` of its colours into ordinals: degenerate sets recycle an old
colour via `fr ∘ δ`, proper ones go through `c` via `toTree`. -/
noncomputable def stepColourOf {C : Type} {k K : Ordinal} (hkK : k ≤ K) (val : C → Set.Iio K)
    (c : SteppingUp.Trees.Tree → C)
    (fr : Finset Ordinal → Set.Iio k) (S : Finset SetOrd) : Set.Iio K :=
  if IsDegenerate S then ⟨fr (deltaFinset S), (fr (deltaFinset S)).2.trans_le hkK⟩
  else val (c (toTree S))

lemma stepColourOf_of_degenerate {C : Type} {k K : Ordinal} {hkK : k ≤ K} {val : C → Set.Iio K}
    {c : SteppingUp.Trees.Tree → C}
    {fr : Finset Ordinal → Set.Iio k} {S : Finset SetOrd}
    (hdegenerate : IsDegenerate S) :
    (stepColourOf hkK val c fr S : Ordinal) = fr (deltaFinset S) := by
  simp [stepColourOf, hdegenerate]

lemma stepColourOf_of_not_degenerate {C : Type} {k K : Ordinal} {hkK : k ≤ K}
    {val : C → Set.Iio K} {c : SteppingUp.Trees.Tree → C}
    {fr : Finset Ordinal → Set.Iio k} {S : Finset SetOrd}
    (hdegenerate : ¬ IsDegenerate S) :
    stepColourOf hkK val c fr S = val (c (toTree S)) := by
  simp [stepColourOf, hdegenerate]

/-- **Key non-monochromaticity lemma**, this setting's form of
`SteppingUp.Bridge.not_mono_of_isValidTable`: the shared argument plus the
one-line translation of `Mono` into "every one-element erasure gets colour
`i`". -/
lemma not_mono_of_isValidTable {C : Type} {K : Ordinal}
    {val : C → Set.Iio K} {c : SteppingUp.Trees.Tree → C} {sset : SteppingUp.Trees.Tree → Finset C}
    {New : C → Prop} {k : Ordinal} {hkK : k ≤ K} {r : ℕ} {fr : Finset Ordinal → Set.Iio k}
    {X : Finset SetOrd} {i : Set.Iio K}
    (hinj : Function.Injective val) (hnew : ∀ n, New n → k ≤ (val n : Ordinal))
    (hmem : ∀ (Y : SteppingUp.Trees.Tree) (x : C), x ∈ sset Y ↔
      ∃ Y' ∈ BinaryTree.dels Y, Y'.core.isSome ∧ c Y' = x)
    (hvalid : IsValidTable sset New r)
    (hX : X.card = r + 2) (hdegenerate : ¬ IsDegenerate X) :
    ¬ Mono (stepColourOf hkK val c fr) (r + 1) X i := by
  intro hmono
  refine SteppingUp.Bridge.not_mono_of_isValidTable (i := (i : Ordinal))
    (F := fun S ↦ (stepColourOf hkK val c fr S : Ordinal))
    toTree (fun _ ↦ lv_toTree) mem_dels_toTree_iff
    (Subtype.val_injective.comp hinj) hnew hmem hvalid
    (fun _ hd ↦ by
      rw [stepColourOf_of_degenerate (isDegenerate_toTree_iff.1 hd)]; exact (fr _).2)
    (fun _ hd ↦ by
      rw [stepColourOf_of_not_degenerate (mt isDegenerate_toTree_iff.2 hd)]; rfl)
    hX (mt isDegenerate_toTree_iff.1 hdegenerate) ?_
  exact fun _ hx ↦ congrArg Subtype.val (hmono _ (Finset.coe_subset.2 (Finset.erase_subset _ _))
    (by rw [Finset.card_erase_of_mem hx, hX]; omega))

/-- `k < k + 1` with `1` the `Ordinal` literal. -/
private lemma self_lt_add_one {k : Ordinal} : k < k + 1 := by simp

end «Colour tables and the toTree bridge»

section «η = 1 colouring for r ≥ 5 (infinitary)»

/-- Translates `c★`'s `EtaColour` output into an actual colour: `c0 ↦ 0`,
`c1 ↦ 1` (the two recycled old colours), `cN ↦ k` (the single new one). -/
noncomputable def etaColourVal (k : Ordinal) : SteppingUp.Trees.EtaColour → Ordinal
  | .c0 => 0
  | .c1 => 1
  | .cN => k

universe u in
/-- `0`, `1` and `k` are pairwise distinct as soon as `2 ≤ k`, so the three
`EtaColour`s really are three different colours. The universe of `k` is named
so that the `0 ≠ 1` fact lands in it rather than in a fresh `Ordinal.{0}`. -/
lemma etaColourVal_injective {k : Ordinal.{u}} (hk : 2 ≤ k) :
    Function.Injective (etaColourVal k) := by
  have h01 : (0 : Ordinal) ≠ 1 := zero_ne_one
  have h10 : (1 : Ordinal) ≠ 0 := h01.symm
  have h0k : 0 ≠ k := (zero_lt_of_two_le hk).ne
  have hk0 : k ≠ 0 := h0k.symm
  have h1k : 1 ≠ k := (one_lt_of_two_le hk).ne
  have hk1 : k ≠ 1 := h1k.symm
  intro d e h
  cases d <;> cases e <;> simp only [etaColourVal] at h <;>
    first
      | rfl
      | exact absurd h (by assumption)

/-- The one new colour has value `k`, which is what separates it from the
recycled `fr ∘ δ` values. -/
private lemma le_etaColourVal_of_new {k : Ordinal} :
    ∀ n : SteppingUp.Trees.EtaColour, n = .cN → k ≤ etaColourVal k n := by
  rintro n rfl; exact le_refl k

/-- The `c0`/`c1`/`cN` → `0`/`1`/`k` translation is always `< k + 1`. -/
private lemma etaColourVal_lt {k : Ordinal} (hk : 2 ≤ k) (c : SteppingUp.Trees.EtaColour) :
    etaColourVal k c < k + 1 := by
  cases c <;> simp only [etaColourVal]
  · exact (zero_lt_of_two_le hk).trans self_lt_add_one
  · exact (one_lt_of_two_le hk).trans self_lt_add_one
  · exact self_lt_add_one

/-- `F_{r+1}` with a *single* new colour, from `c★`. The `k + 1`-boundedness
that used to be a separate `stepColourEtaOne_lt` is now carried by the type. -/
noncomputable def stepColourEtaOne {k : Ordinal} (hk : 2 ≤ k)
    (fr : Finset Ordinal → Set.Iio k) : Finset SetOrd → Set.Iio (k + 1) :=
  stepColourOf self_lt_add_one.le (fun x ↦ ⟨etaColourVal k x, etaColourVal_lt hk x⟩)
    SteppingUp.Trees.cStarTree fr

lemma stepColourEtaOne_of_degenerate {k : Ordinal} {hk : 2 ≤ k}
    {fr : Finset Ordinal → Set.Iio k}
    {S : Finset SetOrd} (hdegenerate : IsDegenerate S) :
    (stepColourEtaOne hk fr S : Ordinal) = fr (deltaFinset S) :=
  stepColourOf_of_degenerate hdegenerate

/-- For `r ≥ 5`, no proper `X` of size `r + 2` is
`stepColourEtaOne`-monochromatic: `not_mono_of_isValidTable` at `c★`. -/
lemma not_mono_of_not_isDegenerate_etaOne {k : Ordinal} {r : ℕ}
    {fr : Finset Ordinal → Set.Iio k} {X : Finset SetOrd} {i : Set.Iio (k + 1)}
    (hk : 2 ≤ k) (hr : 5 ≤ r)
    (hX : X.card = r + 2) (hdegenerate : ¬ IsDegenerate X) :
    ¬ Mono (stepColourEtaOne hk fr) (r + 1) X i :=
  not_mono_of_isValidTable
    (fun _ _ h ↦ etaColourVal_injective hk (congrArg Subtype.val h)) le_etaColourVal_of_new
    (mem_sSet_iff _) (isValidTable_of_isValidAt (SteppingUp.Trees.cStar_isValidAt r hr))
    hX hdegenerate

/-- **The infinitary stepping-up lemma with `η(r) = 1`, for `r ≥ 5`**: the
colouring `stepColourEtaOne`, built from `c★` via the `toTree` bridge, needs
exactly one new colour. The finitary `SteppingUp.stepping_up_eta_one` is
obtained from this theorem by transport (`SteppingUpLemma.Arrow`). -/
theorem stepping_up_eta_one (κ : Cardinal) (r : ℕ) (k : Ordinal) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k) (hr : 5 ≤ r)
    (hs : ∀ i, i < k → (r + 1 : Cardinal) ≤ s i)
    (h : ¬ ArrowsTo Ordinal κ r k s) :
    ¬ ArrowsTo SetOrd (2 ^ κ) (r + 1) (k + 1) (stepSizes r k s) :=
  stepping_up_of_colouring κ r k (k + 1) s (stepColourEtaOne hk) hk (by omega)
    self_lt_add_one.le hs
    (fun _ _ ↦ stepColourEtaOne_of_degenerate)
    (fun _ _ _ ↦ not_mono_of_not_isDegenerate_etaOne hk hr)
    h

end «η = 1 colouring for r ≥ 5 (infinitary)»

section «η = 2 colouring for r = 4 (infinitary)»

/-! The paper's `prop:r4`. Unlike `r ≥ 5` and `r = 3` this case
genuinely needs *two* new colours, so it cannot reuse `EtaColour`; the tree
side supplies `SteppingUp.Trees.Colour4` and `SteppingUp.Trees.c4` instead. -/

/-- `k < k + 2` with `2` the `Ordinal` literal. -/
private lemma self_lt_add_two {k : Ordinal} : k < k + 2 := by simp

/-- `k + 1 < k + 2` with both literals `Ordinal`s. -/
private lemma add_one_lt_add_two {k : Ordinal} : k + 1 < k + 2 := by
  simp

/-- Translates `c4`'s `Colour4` output into an actual colour: `c0 ↦ 0`,
`c1 ↦ 1` (recycled), `n0 ↦ k`, `n1 ↦ k + 1` (the two new colours). -/
noncomputable def colour4Val (k : Ordinal) : SteppingUp.Trees.Colour4 → Ordinal
  | .c0 => 0
  | .c1 => 1
  | .n0 => k
  | .n1 => k + 1

universe u in
/-- `0`, `1`, `k` and `k + 1` are pairwise distinct as soon as `2 ≤ k`. As for
`etaColourVal_injective`, the universe of `k` has to be named so that
`zero_ne_one` lands in it. -/
lemma colour4Val_injective {k : Ordinal.{u}} (hk : 2 ≤ k) :
    Function.Injective (colour4Val k) := by
  have h01 : (0 : Ordinal.{u}) ≠ 1 := zero_ne_one
  have h10 : (1 : Ordinal.{u}) ≠ 0 := h01.symm
  have h0k : (0 : Ordinal.{u}) ≠ k := (zero_lt_of_two_le hk).ne
  have hk0 : k ≠ (0 : Ordinal.{u}) := h0k.symm
  have h1k : (1 : Ordinal.{u}) ≠ k := (one_lt_of_two_le hk).ne
  have hk1 : k ≠ (1 : Ordinal.{u}) := h1k.symm
  have h0k1 : (0 : Ordinal.{u}) ≠ k + 1 := ((zero_lt_of_two_le hk).trans self_lt_add_one).ne
  have hk10 : k + 1 ≠ (0 : Ordinal.{u}) := h0k1.symm
  have h1k1 : (1 : Ordinal.{u}) ≠ k + 1 := ((one_lt_of_two_le hk).trans self_lt_add_one).ne
  have hk11 : k + 1 ≠ (1 : Ordinal.{u}) := h1k1.symm
  have hkk1 : k ≠ k + 1 := self_lt_add_one.ne
  have hk1k : k + 1 ≠ k := hkk1.symm
  intro d e h
  cases d <;> cases e <;> simp only [colour4Val] at h <;>
    first
      | rfl
      | exact absurd h (by assumption)

/-- Both new colours are `≥ k`, which is what separates them from the
recycled `fr ∘ δ` values. -/
private lemma le_colour4Val_of_new {k : Ordinal} :
    ∀ n : SteppingUp.Trees.Colour4, (n = .n0 ∨ n = .n1) → k ≤ colour4Val k n := by
  rintro n (rfl | rfl) <;> simp [colour4Val]


/-- The `c0`/`c1`/`n0`/`n1` → `0`/`1`/`k`/`k + 1` translation is `< k + 2`. -/
private lemma colour4Val_lt {k : Ordinal} (hk : 2 ≤ k) (c : SteppingUp.Trees.Colour4) :
    colour4Val k c < k + 2 := by
  cases c <;> simp only [colour4Val]
  · exact (zero_lt_of_two_le hk).trans self_lt_add_two
  · exact (one_lt_of_two_le hk).trans self_lt_add_two
  · exact self_lt_add_two
  · exact add_one_lt_add_two

/-- `F_5` for the exceptional case `r = 4`, with *two* new colours, from
`c4`. The `k + 2`-boundedness is carried by the type. -/
noncomputable def stepColourR4 {k : Ordinal} (hk : 2 ≤ k)
    (fr : Finset Ordinal → Set.Iio k) : Finset SetOrd → Set.Iio (k + 2) :=
  stepColourOf self_lt_add_two.le (fun x ↦ ⟨colour4Val k x, colour4Val_lt hk x⟩)
    SteppingUp.Trees.c4 fr

lemma stepColourR4_of_degenerate {k : Ordinal} {hk : 2 ≤ k} {fr : Finset Ordinal → Set.Iio k}
    {S : Finset SetOrd} (hdegenerate : IsDegenerate S) :
    (stepColourR4 hk fr S : Ordinal) = fr (deltaFinset S) :=
  stepColourOf_of_degenerate hdegenerate

/-- At `r = 4`, no proper `X` of size `6` is `stepColourR4`-monochromatic:
`not_mono_of_isValidTable` at `c4`. -/
lemma not_mono_of_not_isDegenerate_r4 {k : Ordinal}
    {fr : Finset Ordinal → Set.Iio k} {X : Finset SetOrd} {i : Set.Iio (k + 2)}
    (hk : 2 ≤ k)
    (hX : X.card = 4 + 2) (hdegenerate : ¬ IsDegenerate X) :
    ¬ Mono (stepColourR4 hk fr) (4 + 1) X i :=
  not_mono_of_isValidTable
    (fun _ _ h ↦ colour4Val_injective hk (congrArg Subtype.val h)) le_colour4Val_of_new
    (mem_sSet4_iff _) (isValidTable_of_isValidAt4 SteppingUp.Trees.isValidAt4_c4) hX hdegenerate

/-- **The infinitary stepping-up lemma with `η(4) = 2`** (the second half of
the paper's `thm:infinite`): the colouring `stepColourR4`, built from `c4` via the
`toTree` bridge, needs two new colours. This is the one case that genuinely
needs more than one.

The tree-level input `SteppingUp.Trees.isValidAt4_c4` is discharged by `decide`
over `treesL 6`, the structurally recursive enumeration, so this theorem
carries no reflection axiom — nor does its finitary counterpart. -/
theorem stepping_up_eta_two_r4 (κ : Cardinal) (k : Ordinal) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k)
    (hs : ∀ i, i < k → (5 : Cardinal) ≤ s i)
    (h : ¬ ArrowsTo Ordinal κ 4 k s) :
    ¬ ArrowsTo SetOrd (2 ^ κ) 5 (k + 2) (stepSizes 4 k s) :=
  stepping_up_of_colouring κ 4 k (k + 2) s (stepColourR4 hk) hk (by omega)
    self_lt_add_two.le (by exact_mod_cast hs)
    (fun _ _ ↦ stepColourR4_of_degenerate)
    (fun _ _ _ ↦ not_mono_of_not_isDegenerate_r4 hk)
    h

end «η = 2 colouring for r = 4 (infinitary)»

section «η = 1 colouring for r = 3 (infinitary)»

/-! This case shares everything with `r ≥ 5` except the table: same colour type
`SteppingUp.Trees.EtaColour`, same value map `etaColourVal`, same single new colour and
hence the same `k + 1` colour count — only `SteppingUp.Trees.c★` is replaced by
`SteppingUp.Trees.c3`, and `r` is fixed at `3`.

So this case costs almost nothing beyond the table itself. -/

/-- `F_4` for `r = 3`, with a single new colour, from `c3`. The `k + 1`-bound
is carried by the type. -/
noncomputable def stepColourR3 {k : Ordinal} (hk : 2 ≤ k)
    (fr : Finset Ordinal → Set.Iio k) : Finset SetOrd → Set.Iio (k + 1) :=
  stepColourOf self_lt_add_one.le (fun x ↦ ⟨etaColourVal k x, etaColourVal_lt hk x⟩)
    SteppingUp.Trees.c3 fr

lemma stepColourR3_of_degenerate {k : Ordinal} {hk : 2 ≤ k} {fr : Finset Ordinal → Set.Iio k}
    {S : Finset SetOrd} (hdegenerate : IsDegenerate S) :
    (stepColourR3 hk fr S : Ordinal) = fr (deltaFinset S) :=
  stepColourOf_of_degenerate hdegenerate

/-- At `r = 3`, no proper `X` of size `5` is `stepColourR3`-monochromatic:
`not_mono_of_isValidTable` at `c3`. -/
lemma not_mono_of_not_isDegenerate_r3 {k : Ordinal}
    {fr : Finset Ordinal → Set.Iio k} {X : Finset SetOrd} {i : Set.Iio (k + 1)}
    (hk : 2 ≤ k)
    (hX : X.card = 3 + 2) (hdegenerate : ¬ IsDegenerate X) :
    ¬ Mono (stepColourR3 hk fr) (3 + 1) X i :=
  not_mono_of_isValidTable
    (fun _ _ h ↦ etaColourVal_injective hk (congrArg Subtype.val h)) le_etaColourVal_of_new
    (mem_sSet_iff _) (isValidTable_of_isValidAt SteppingUp.Trees.isValidAt_c3) hX hdegenerate

/-- **The infinitary stepping-up lemma with `η(3) = 1`**: the colouring
`stepColourR3`, built from `c3` via the `toTree` bridge, needs exactly one
new colour.

As for `r = 4`, the tree-level input `SteppingUp.Trees.isValidAt_c3` is discharged by
`decide` over `treesL 5`, so this theorem carries no reflection axiom.

Unlike `stepping_up_eta_one` and `stepping_up_eta_two_r4`, this is not an
improvement on JKSY: `η(3) = 1` is already theirs. It is reproved here so
that all three cases come from one construction. -/
theorem stepping_up_eta_one_r3 (κ : Cardinal) (k : Ordinal) (s : Ordinal → Cardinal)
    (hk : 2 ≤ k)
    (hs : ∀ i, i < k → 4 ≤ s i)
    (h : ¬ ArrowsTo Ordinal κ 3 k s) :
    ¬ ArrowsTo SetOrd (2 ^ κ) 4 (k + 1) (stepSizes 3 k s) :=
  stepping_up_of_colouring κ 3 k (k + 1) s (stepColourR3 hk) hk (by omega)
    self_lt_add_one.le (by exact_mod_cast hs)
    (fun _ _ ↦ stepColourR3_of_degenerate)
    (fun _ _ _ ↦ not_mono_of_not_isDegenerate_r3 hk)
    h

end «η = 1 colouring for r = 3 (infinitary)»

end SteppingUp.Infinitary
