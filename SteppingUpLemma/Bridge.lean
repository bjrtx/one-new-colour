/-
  The setting-independent half of the tree-to-colouring bridge.

  `SteppingUp.Infinitary` turns a *tree* colour table into a colouring of
  `(r+1)`-sets, and then has to prove that no proper set of size `r + 2` is
  monochromatic. That argument uses nothing about the ambient setting beyond
  two facts relating `toTree` to cardinality and deletion, and nothing about
  the colour type beyond a linear order.

  This module isolates both: `not_mono_of_isValidTable` is that argument,
  taking the translation and those two facts as ordinary arguments.

-/
import SteppingUpLemma.Colouring.R4

namespace SteppingUp.Bridge

open SteppingUp.Trees

section «Valid colour tables»

/-- Validity of a tree colour table: every
proper `(r+2)`-tree either realises at least colours among its proper deletions,
or realises a single *new* colour and has a degenerate deletion.

`sset` is left abstract rather than written as an image so that no
`DecidableEq` instance enters the statement; what the bridge needs of it is
supplied separately as `hmem`. -/
def IsValidTable {C : Type*} (sset : Tree → Finset C) (New : C → Prop) (r : ℕ) : Prop :=
  ∀ Y : Tree, Y.numLeaves = r + 2 → Y.core.isSome →
    2 ≤ (sset Y).card ∨ (∃ n, New n ∧ n ∈ sset Y) ∧ hasDegenerateDel Y

/-- Membership in `sSet`, unfolded to the deletion it comes from. -/
lemma mem_sSet_iff (c : Tree → EtaColour) (T : Tree) (x : EtaColour) :
    x ∈ sSet c T ↔ ∃ Y' ∈ BinaryTree.dels T, Y'.core.isSome ∧ c Y' = x := by
  simp [sSet, List.mem_toFinset, and_assoc]

/-- Membership in `sSet4`, unfolded to the deletion it comes from. -/
lemma mem_sSet4_iff (c : Tree → Colour4) (T : Tree) (x : Colour4) :
    x ∈ sSet4 c T ↔ ∃ Y' ∈ BinaryTree.dels T, Y'.core.isSome ∧ c Y' = x := by
  simp [sSet4, List.mem_toFinset, and_assoc]

/-- `IsValidAt`, in the abstract form the bridge consumes: its single new
colour is `cN`. -/
lemma isValidTable_of_isValidAt {c : Tree → EtaColour} {r : ℕ} (h : IsValidAt c r) :
    IsValidTable (sSet c) (· = EtaColour.cN) r :=
  fun Y h1 h2 ↦ (h Y h1 h2).imp id fun hh ↦ ⟨⟨_, rfl, hh.1⟩, hh.2⟩

/-- `IsValidAt4`, in the abstract form the bridge consumes: its two new
colours are `n0` and `n1`. With both sides stated by membership this is an
`Or.imp` like `isValidTable_of_isValidAt`; only the two-colour disjunction
has to be folded into the existential. -/
lemma isValidTable_of_isValidAt4 {c : Tree → Colour4} {r : ℕ} (h : IsValidAt4 c r) :
    IsValidTable (sSet4 c) (fun n ↦ n = .n0 ∨ n = .n1) r :=
  fun Y h1 h2 ↦ (h Y h1 h2).imp id fun hh ↦
    ⟨hh.1.elim (fun hm ↦ ⟨_, Or.inl rfl, hm⟩) fun hm ↦ ⟨_, Or.inr rfl, hm⟩, hh.2⟩

end «Valid colour tables»

section «Non-monochromaticity»

set_option maxHeartbeats 1000000 in
/-- Key non-monochromaticity lemma. For a table
valid at level `r`, a proper set `X` of size `r + 2` cannot have all of its
one-element erasures coloured alike.

All the combinatorial content sits in `hvalid`; this lemma is only the `tree`
translation of it. Monochromaticity enters already applied to the erasures
(`hmono`) rather than as a `Mono` predicate: `Mono` is stated over an ambient
*set* of vertices, which this argument never needs to mention. Converting is
one line at the call site.

The two hypotheses on `val` are what make the translation faithful: `hinj`
separates the colours in the "`≥ 2` colours among proper deletions" branch,
and `hnew` — deliberately an inequality `k ≤ val n` rather than an equation,
since `Colour4` has *two* new colours with different values — contradicts
`hdegLt` in the "one new colour plus a degenerate deletion" branch. -/
lemma not_mono_of_isValidTable {V C Col : Type*} [DecidableEq V] [LinearOrder Col]
    (tree : Finset V → Tree)
    (lv_tree : ∀ S : Finset V, 1 ≤ S.card → (tree S).numLeaves = S.card)
    (mem_dels : ∀ S : Finset V, 2 ≤ S.card → ∀ Y : Tree,
      Y ∈ BinaryTree.dels (tree S) ↔ ∃ x ∈ S, Y = tree (S.erase x))
    {val : C → Col} {c : Tree → C} {sset : Tree → Finset C} {New : C → Prop}
    {k : Col} {r : ℕ} {X : Finset V} {i : Col} {F : Finset V → Col}
    (hinj : Function.Injective val) (hnew : ∀ n, New n → k ≤ val n)
    (hmem : ∀ (Y : Tree) (x : C), x ∈ sset Y ↔
      ∃ Y' ∈ BinaryTree.dels Y, Y'.core.isSome ∧ c Y' = x)
    (hvalid : IsValidTable sset New r)
    (hdegLt : ∀ S, (tree S).core.isNone → F S < k)
    (hproper : ∀ S, ¬ (tree S).core.isNone → F S = val (c (tree S)))
    (hX : X.card = r + 2) (hXnd : ¬ (tree X).core.isNone)
    (hmono : ∀ x ∈ X, F (X.erase x) = i) :
    False := by
  have hX2 : 2 ≤ X.card := by omega
  have hcoreSome : (tree X).core.isSome := by
    rw [Option.isSome_iff_ne_none]
    exact fun hnone ↦ hXnd (by simp [hnone])
  have hv := hvalid (tree X) (by rw [lv_tree X (by omega), hX]) hcoreSome
  -- A deletion whose tree is proper comes from an erasure that is itself proper.
  have hndel {Y : Tree} {x : V} : Y = tree (X.erase x) → Y.core.isSome →
      ¬ (tree (X.erase x)).core.isNone := by
    intro _ _ _ ; simp_all
  -- ... and on such an erasure `hmono` pins down the colour `c` assigns to it.
  have hval {x} : x ∈ X → ¬(tree (X.erase x)).core.isNone →
      val (c (tree (X.erase x))) = i := by
    intro hx hnotdeg
    rw [← hproper _ hnotdeg]
    exact hmono x hx
  rcases hv with hcard2 | ⟨⟨n, hn, hsingle⟩, hdegeneratedel⟩
  · -- Two proper deletions get distinct table colours, hence distinct colours.
    obtain ⟨cY1, hcY1mem, cY2, hcY2mem, hne⟩ := Finset.one_lt_card.1 hcard2
    rw [hmem] at hcY1mem hcY2mem
    obtain ⟨Y1, hY1dels, hY1some, hY1eq⟩ := hcY1mem
    obtain ⟨Y2, hY2dels, hY2some, hY2eq⟩ := hcY2mem
    obtain ⟨x1, hx1X, hx1eq⟩ := (mem_dels X hX2 Y1).1 hY1dels
    obtain ⟨x2, hx2X, hx2eq⟩ := (mem_dels X hX2 Y2).1 hY2dels
    have hv1 := hval hx1X (hndel hx1eq hY1some)
    have hv2 := hval hx2X (hndel hx2eq hY2some)
    rw [show c (tree (X.erase x1)) = cY1 by rw [← hx1eq]; exact hY1eq] at hv1
    rw [show c (tree (X.erase x2)) = cY2 by rw [← hx2eq]; exact hY2eq] at hv2
    exact hne (hinj (hv1.trans hv2.symm))
  · -- All proper deletions get the new colour `n`, whose value is `≥ k`; but
    -- `X` also has a degenerate deletion, whose colour is `< k`.
    rw [hmem] at hsingle
    obtain ⟨Y1, hY1dels, hY1some, hY1eq⟩ := hsingle
    obtain ⟨x1, hx1X, hx1eq⟩ := (mem_dels X hX2 Y1).1 hY1dels
    have hv1 := hval hx1X (hndel hx1eq hY1some)
    rw [show c (tree (X.erase x1)) = n by rw [← hx1eq]; exact hY1eq] at hv1
    obtain ⟨Y2, hY2dels, hY2degenerate⟩ := by
      simpa! [hasDegenerateDel] using hdegeneratedel
    obtain ⟨x2, hx2X, hx2eq⟩ := (mem_dels X hX2 Y2).1 hY2dels
    have hdeg2 : (tree (X.erase x2)).core.isNone := by
      rw [← hx2eq]; simpa using hY2degenerate
    have hlt := hdegLt _ hdeg2
    rw [hmono x2 hx2X, ← hv1] at hlt
    exact absurd (hnew n hn) (not_le.2 hlt)

end «Non-monochromaticity»

end SteppingUp.Bridge
