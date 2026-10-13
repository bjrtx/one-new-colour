/-
  How a set of subsets of an ordinal splits, and what "degenerate" means for
  one.

  This is the ground-set half of the development, and it is independent of the
  colouring: it rests on `SteppingUpLemma.Tree` alone. `disc` and `sIdx` split
  a set at the least ordinal where two of its members disagree, `part` names
  the two halves, and `LexLT` orders the members. `IsDegenerate` is the paper's
  "no crossing quadruple", and the transfinite peeling at the end is what
  replaces, for an infinite set, the recursion that terminates for a finite
  one.

  `SteppingUpLemma.Encoding.Delta` builds `δ` and the tree encoding on top.

  DESIGN CHOICES.
  * Vertices are `SetOrd`, standing for "characteristic function of a
    subset of some ordinal".

  * `r`-element subsets of the vertex universe are `Finset SetOrd`.
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.SetTheory.Cardinal.EventuallyConst
import SteppingUpLemma.Tree

namespace SteppingUp.Encoding

open Lean.Parser.Tactic
open Cardinal

/- `SetOrd` membership isn't decidable in general (arbitrary ordinals), and this file
relies on classical membership decisions pervasively (`part`, `LexLT`, degenerate tree reasoning);
threading explicit `Decidable` instances or scoping `open Classical in` through every affected
declaration isn't practical here. -/
set_option linter.style.openClassical false
open scoped Classical

/-- Sets of ordinals: a subset of `κ` stands for a point of the stepped-up
ground set `2^κ`. -/
abbrev SetOrd := Set Ordinal

variable {x y z : SetOrd} {S T : Set SetOrd}

/-- Syntactic sugar for `Bool` values. -/
notation (priority := 1001) "⊥" => false
/-- Syntactic sugar for `Bool` values. -/
notation (priority := 1001) "⊤" => true

section «splitting ordinals»

/-- The discrepancy of `x` and `y` is the least ordinal on which
the characteristic sets `x` and `y` disagree (the minimum of their symmetric
difference), or `0` when `x = y`. -/
noncomputable def disc (x y : SetOrd) : Ordinal := sInf (symmDiff x y)

lemma disc_comm (x y : SetOrd) : disc x y = disc y x := by
  rw [disc, disc, symmDiff_comm]

/-- `x` and `y` differ at `disc x y`, provided they differ at all. -/
lemma disc_mem_symmDiff (h : x ≠ y) :
    disc x y ∈ (x \ y) ∪ (y \ x) :=
  csInf_mem (by simpa [← Set.symmDiff_def] using h)

/-- Below the discrepancy, `x` and `y` agree. -/
lemma mem_iff_of_lt_disc {α : Ordinal} (ht : α < disc x y) : α ∈ x ↔ α ∈ y := by
  have : α ∉ (x \ y) ∪ (y \ x) := (not_le.mpr ht) ∘ csInf_le'
  constructor <;> simp_all

/-- Extends the definition of `disc` to a whole set rather than a pair.
The least point of disagreement anywhere in `S`. -/
noncomputable def sIdx (S : Set SetOrd) : Ordinal :=
  sInf ((Function.uncurry disc) '' S.offDiag)

/-- Elements of `S` whose membership of the discrepancy
ordinal matches `b` (`⊥` gives `S₀`, the elements missing it; `⊤` gives `S₁`,
the elements containing it). -/
def part (b : Bool) (S : Set SetOrd) : Set SetOrd :=
  {x ∈ S | bif b then sIdx S ∈ x else sIdx S ∉ x}

lemma part_bot_union_part_top : part ⊥ S ∪ part ⊤ S = S := by grind [part]

/-- `part_bot_union_part_top`, with the `b`-side named first. -/
lemma parts_union {b : Bool} : part b S ∪ part (!b) S = S := by
  cases b <;> simp_all [part_bot_union_part_top, Set.union_comm]

lemma parts_disjoint {b : Bool} : Disjoint (part b S) (part (!b) S) := by grind [part]

/-- An element of `S` missing one part lies in the other. -/
lemma mem_part_of_notMem {b : Bool} (hx : x ∈ S) (h : x ∉ part (!b) S) : x ∈ part b S := by
  rw [← parts_union (S := S) (b := b)] at hx
  simp_all

/-- Deleting one part of `S` leaves the other. -/
lemma sdiff_part (b : Bool) : S \ part (!b) S = part b S := by
  grind [part]

/-- Every pair in `S` splits at or above `sIdx S`. -/
lemma sIdx_le_disc (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : sIdx S ≤ disc x y :=
  csInf_le' ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩

/-- The split of a "crossing" subset is inherited from the ambient set. -/
lemma sIdx_of_subset {S L R : Set SetOrd}
    (hL : L.Nonempty) (hR : R.Nonempty) (hLS : L ⊆ part ⊥ S) (hRS : R ⊆ part ⊤ S) :
    sIdx (L ∪ R) = sIdx S ∧ part ⊥ (L ∪ R) = L ∧ part ⊤ (L ∪ R) = R := by
  set j := sIdx S with hj
  have hLS' : L ⊆ S := hLS.trans (fun _ hx => hx.1)
  have hRS' : R ⊆ S := hRS.trans (fun _ hx => hx.1)
  have hLbit : ∀ x ∈ L, j ∉ x := fun _ hx => (hLS hx).2
  have hRbit : ∀ x ∈ R, j ∈ x := fun _ hx => (hRS hx).2
  obtain ⟨x, hx⟩ := hL
  obtain ⟨y, hy⟩ := hR
  have hxj : j ∉ x := hLbit x hx
  have hyj : j ∈ y := hRbit y hy
  have hxy : x ≠ y := fun heq ↦ (heq ▸ hxj) hyj

  -- Equality: a strict `<` would force `x`, `y` to agree at `j`, contradicting
  -- that `x ∈ part ⊥ S` and `y ∈ part ⊤ S`.
  have heq : j = disc x y :=
    eq_of_le_of_not_lt (sIdx_le_disc (hLS' hx) (hRS' hy) hxy)
      (fun hlt => absurd ((mem_iff_of_lt_disc hlt).mpr hyj) hxj)
  have hxLR : x ∈ L ∪ R := Set.mem_union_left R hx
  have hyLR : y ∈ L ∪ R := Set.mem_union_right L hy
  have hidx : sIdx (L ∪ R) = j := by
    refine le_antisymm ((sIdx_le_disc hxLR hyLR hxy).trans_eq heq.symm)
      (le_csInf ⟨disc x y, (x, y), ⟨hxLR, hyLR, hxy⟩, rfl⟩ ?_)
    rintro o ⟨⟨x', y'⟩, ⟨hx', hy', hxy'⟩, rfl⟩
    exact sIdx_le_disc (hx'.elim (hLS' ·) (hRS' ·)) (hy'.elim (hLS' ·) (hRS' ·)) hxy'
  refine ⟨hidx.trans hj, ?_, ?_⟩
    <;> ext x <;> simp only [part, Set.mem_ofPred_eq, hidx] <;> constructor
    <;> (try rintro ⟨ _ | _, _ ⟩)
    <;> simp_all


end «splitting ordinals»

section «Lexicographic order and degenerate trees»

/-- The strict lexicographic order on characteristic sets: at the first
point of disagreement, `x` is missing the bit that `y` has. -/
def LexLT (x y : SetOrd) : Prop := disc x y ∈ y \ x

/-- Notation for `LexLT`. -/
scoped infix:50 " ≺ " => LexLT

/-- This relation is trichotomous. -/
lemma lexLT_trichotomous : ∀ (a b : SetOrd.{u_1}), ¬ a ≺ b → ¬ b ≺ a → a = b := fun
  _ _ hab hba => by_contra fun hne => absurd (disc_mem_symmDiff hne) (by simp_all [LexLT, disc_comm])


/-- If `x` and `y` agree below `t`, `x` lacks the bit at `t` and `y` has it,
then `t` is exactly `disc x y`. -/
lemma disc_eq_of_agree_before_and_differ_at {t : Ordinal}
    (hagree : ∀ s < t, (s ∈ x ↔ s ∈ y)) (hx : t ∉ x) (hy : t ∈ y) :
    disc x y = t := by
  refine le_antisymm (csInf_le' (Or.inr ⟨hy, hx⟩)) ?_
  by_contra! hlt
  rcases disc_mem_symmDiff (·.symm ▸ hy |> hx : x ≠ y) <;> simp_all [hagree _ hlt]

/-- Matching lemma for `LexLT` itself. -/
lemma lexLT_of_agree_before_and_differ_at {t : Ordinal}
    (hagree : ∀ s < t, (s ∈ x ↔ s ∈ y)) (hx : t ∉ x) (hy : t ∈ y) : x ≺ y := by
  have : disc x y = t := disc_eq_of_agree_before_and_differ_at hagree hx hy
  split_ands <;> simp_all


/-- Transitivity of the lexicographic order. -/
lemma lexLT_trans {x y z : SetOrd} (hxy : x ≺ y) (hyz : y ≺ z) : x ≺ z := by
  obtain ⟨hxy1, hxy2⟩ := hxy
  obtain ⟨hyz1, hyz2⟩ := hyz
  rcases lt_trichotomy (disc x y) (disc y z) with hlt | heqdisc | hlt
  · -- the earlier (least) split wins: `disc x z = disc x y`.
    exact lexLT_of_agree_before_and_differ_at
      (fun s hs => (mem_iff_of_lt_disc hs).trans (mem_iff_of_lt_disc (hs.trans hlt)))
      hxy2 ((mem_iff_of_lt_disc hlt).mp hxy1)
  · -- impossible: `y` would both contain and lack the common split point.
    simp_all
  · -- mirror image, with `disc y z` the earlier split.
    exact lexLT_of_agree_before_and_differ_at
      (fun s hs => (mem_iff_of_lt_disc (hs.trans hlt)).trans (mem_iff_of_lt_disc hs))
      (fun h => hyz2 ((mem_iff_of_lt_disc hlt).mp h)) hyz1


instance instIsStrictTotalOrderLexLT : IsStrictTotalOrder SetOrd LexLT where
  irrefl := by simp [LexLT]
  trichotomous := lexLT_trichotomous
  trans a b c := lexLT_trans

/-- The linear order on sets of ordinals given by `LexLT`. -/
@[instance_reducible] noncomputable
def instLinearOrderLexLT : LinearOrder SetOrd := linearOrderOfSTO LexLT

lemma lexLT_ne (h : x ≺ y) : x ≠ y :=
  @ne_of_lt SetOrd instLinearOrderLexLT.toPreorder x y h

/-- `S` is degenerate if it has no four-element subset of "crossing type". -/
def IsDegenerate (S : Set SetOrd) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≺ b → b ≺ c → c ≺ d →
    ¬ (disc b c < disc a b ∧ disc b c < disc c d)

/-- A set with at most one element is vacuously degenerate. -/
lemma isDegenerate_of_subsingleton (hS : S.Subsingleton) : IsDegenerate S :=
    fun a ha _ hb _ _ _ _ hab _ _ _ => absurd hab (hS ha hb ▸ irrefl a)

lemma IsDegenerate.subset (h : IsDegenerate S) (hTS : T ⊆ S) : IsDegenerate T :=
  fun _ ha _ hb _ hc _ hd ↦ h _ (hTS ha) _ (hTS hb) _ (hTS hc) _ (hTS hd)

/-- A pair straddling the two parts splits exactly at `sIdx S`. -/
lemma disc_eq_sIdx_of_cross {b : Bool} (hx : x ∈ part b S) (hy : y ∈ part (!b) S) : disc x y = sIdx S := by
  have key : ∀ {u v : SetOrd}, u ∈ part ⊥ S → v ∈ part ⊤ S → disc u v = sIdx S := by
    intro u v hu hv
    have : u ≠ v := (· ▸ hu |>.2 hv.2)
    rcases lt_or_eq_of_le (sIdx_le_disc hu.1 hv.1 this) with hlt | heq
    · exact absurd ((mem_iff_of_lt_disc hlt).mpr hv.2) hu.2
    · exact heq.symm
  cases b
  · exact key hx hy
  · rw [disc_comm]; exact key hy hx

/-- Two distinct elements on the same side split strictly above `sIdx S`. -/
lemma sIdx_lt_disc_of_part {b : Bool} {S : Set SetOrd} {x y : SetOrd}
    (hx : x ∈ part b S) (hy : y ∈ part b S) (hxy : x ≠ y) : sIdx S < disc x y := by
  by_contra hnlt
  have heq := eq_of_le_of_not_lt (sIdx_le_disc hx.1 hy.1 hxy) hnlt
  cases b <;> simp only [part, cond_true, cond_false, Set.mem_ofPred_eq] at hx hy
    <;> rcases (heq ▸ disc_mem_symmDiff hxy : sIdx S ∈ x \ y ∪ y \ x)
    <;> simp_all

/-- Everything on the `0`-side lexicographically precedes everything on the
`1`-side. -/
lemma part_bot_lexLT_part_top {S : Set SetOrd} {x y : SetOrd}
    (hx : x ∈ part ⊥ S) (hy : y ∈ part ⊤ S) : x ≺ y := by
  rw [LexLT, disc_eq_sIdx_of_cross hx hy]
  exact ⟨hy.2, hx.2⟩

/-- Membership in `part b S` propagates upward for `b = ⊤`, downward for `b = ⊥`. -/
lemma mem_part_of_lexLT {S : Set SetOrd} {k m : SetOrd} {b : Bool}
    (hk : k ∈ part b S) (hm : m ∈ S) (hkm : bif b then k ≺ m else m ≺ k) :
    m ∈ part b S := by
  -- Both sides run the same argument; only which half `m` falls into, and
  -- hence the order of the two `≺` steps, depends on `b`.
  by_contra hm0
  have hmU : m ∈ part ⊥ S ∪ part ⊤ S := by rw [part_bot_union_part_top]; exact hm
  cases b with
  | true =>
    simp only [cond_true] at hkm
    exact irrefl k (Trans.trans hkm (part_bot_lexLT_part_top (hmU.resolve_right hm0) hk))
  | false =>
    simp only [cond_false] at hkm
    exact irrefl k (Trans.trans (part_bot_lexLT_part_top hk (hmU.resolve_left hm0)) hkm)

/-- A (finite) set with cardinality > 1 is nontrivial. -/
lemma nontrivial_of_one_lt_ncard (h: 1 < Set.ncard T) : T.Nontrivial :=
  (Set.one_lt_ncard_iff_nontrivial_and_finite.mp h).left


/-- A `≺`-ordered pair out of any nontrivial set, with no finiteness
hypothesis: `Set.Nontrivial`
is definitionally `∃ x ∈ s, ∃ y ∈ s, x ≠ y`, so no `Set.Finite` bookkeeping is needed
at all. First piece of the `Cardinal`-valued-target roadmap: this is what lets
`isDegenerate_iff_rec`'s recursive structure generalize to infinite degenerate trees. -/
lemma exists_lexLT_pair_of_nontrivial {S : Set SetOrd} (h : S.Nontrivial) :
    ∃ a ∈ S, ∃ b ∈ S, a ≺ b := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  rcases trichotomous_of LexLT a b with h' | h' | h'
  · exact ⟨a, ha, b, hb, h'⟩
  · exact absurd h' hab
  · exact ⟨b, hb, a, ha, h'⟩

/-- Finiteness-free version of `part_nonempty`, needed for the same reason as
`exists_lexLT_pair_of_nontrivial` above. Indexing by `b` covers both sides at
once. -/
lemma part_nonempty_of_nontrivial {b : Bool} {S : Set SetOrd} (hS : S.Nontrivial) :
    (part b S).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hS
  have hSne : ((Function.uncurry disc) '' S.offDiag).Nonempty :=
    ⟨disc x y, (x, y), ⟨hx, hy, hxy⟩, rfl⟩
  -- an `sInf` of a nonempty set of ordinals is attained, by well-ordering
  obtain ⟨⟨x', y'⟩, ⟨hx', hy', hxy'⟩, hdisc⟩ :
      ∃ p ∈ S.offDiag, disc p.1 p.2 = sIdx S := csInf_mem hSne
  dsimp only at hx' hy' hxy' hdisc
  cases b <;> rcases disc_mem_symmDiff hxy' with h | h
  · exact ⟨y', hy', by rw [← hdisc]; exact h.2⟩
  · exact ⟨x', hx', by rw [← hdisc]; exact h.2⟩
  · exact ⟨x', hx', by rw [← hdisc]; exact h.1⟩
  · exact ⟨y', hy', by rw [← hdisc]; exact h.1⟩


/-- `part b S` of a genuine (`≥ 2`-element) set is nonempty: dual to
`Arrow.lean`'s `part_nonempty`, proved directly from `csInf_mem` and
`disc_mem_symmDiff` rather than via `min'`/`max'`. (No finiteness hypothesis is
needed: `2 ≤ S.ncard` already forces `S` to be finite, since `Set.ncard` is
`0` on infinite sets.) Indexing by `b` covers both sides at once. -/
lemma part_nonempty {b : Bool} {S : Set SetOrd} (hS : 2 ≤ S.ncard) :
    (part b S).Nonempty :=
  part_nonempty_of_nontrivial <| nontrivial_of_one_lt_ncard (by omega : 1 < S.ncard)

/-- `(part b S).Finite` follows from `S.Finite` alone. Repeated verbatim
throughout Block C. Unifies `part_finite_of_finite ⊥`/`part_finite_of_finite ⊤`. -/
lemma part_finite_of_finite {b : Bool} {S : Set SetOrd} (hSfin : S.Finite) :
    (part b S).Finite :=
  hSfin.subset (fun _ hx => hx.1)

/-- Finiteness-free version of `isDegenerate_iff_rec`: the singleton side is stated as a
literal set equality (`∃ p0, part ⊥ S = {p0}`) rather than `(part ⊥ S).ncard = 1`,
which is what lets *both* directions drop finiteness at once — the backward
direction's proof is otherwise identical to `isDegenerate_iff_rec`'s, since it only ever
uses the singleton witness `hp0eq`/`hp1eq` and pure `LexLT`/membership reasoning,
never `S.Finite`/`.ncard`. First payoff of the `Cardinal`-valued-target roadmap:
this is the fact a later transfinite "peel the singleton side" construction over
infinite degenerate trees needs. -/
lemma isDegenerate_iff_rec_of_nontrivial (hS : S.Nontrivial) :
    IsDegenerate S ↔ ((∃ p0, part ⊥ S = {p0}) ∧ IsDegenerate (part ⊤ S)) ∨
              ((∃ p1, part ⊤ S = {p1}) ∧ IsDegenerate (part ⊥ S)) := by
  constructor
  · intro hdegenerate
    have hnot_both : ¬ ((part ⊥ S).Nontrivial ∧ (part ⊤ S).Nontrivial) := by
      rintro ⟨h0, h1⟩
      obtain ⟨a, ha, b, hb, hab⟩ := exists_lexLT_pair_of_nontrivial h0
      obtain ⟨c, hc, d, hd, hcd⟩ := exists_lexLT_pair_of_nontrivial h1
      have hbc : b ≺ c := part_bot_lexLT_part_top hb hc
      have hbc_eq : disc b c = sIdx S := disc_eq_sIdx_of_cross hb hc
      refine hdegenerate a ha.1 b hb.1 c hc.1 d hd.1 hab hbc hcd ⟨?_, ?_⟩ <;> rw [hbc_eq]
      · exact sIdx_lt_disc_of_part ha hb (lexLT_ne hab)
      · exact sIdx_lt_disc_of_part hc hd (lexLT_ne hcd)
    rw [not_and_or, Set.not_nontrivial_iff, Set.not_nontrivial_iff] at hnot_both
    -- Whichever side is the subsingleton is in fact a singleton — the parts of
    -- a nontrivial `S` are nonempty — and the other side inherits degeneracy.
    have mk b: (part b S).Subsingleton →
        (∃ p, part b S = {p}) ∧ IsDegenerate (part (!b) S) := fun h =>
      ⟨Set.exists_eq_singleton_iff_nonempty_subsingleton.2
        ⟨part_nonempty_of_nontrivial hS, h⟩, hdegenerate.subset fun _ hx => hx.1⟩
    exact hnot_both.imp (mk ⊥) (mk ⊤)
  · rintro (⟨h0, hdegenerate1⟩ | ⟨h1, hdegenerate0⟩)
    · obtain ⟨p0, hp0eq⟩ := h0
      rintro a ha b hb c hc d hd hab hbc hcd ⟨h1lt, h2lt⟩
      by_cases haP0 : a ∈ part ⊥ S
      · have hbP1 : b ∈ part ⊤ S := by
          have hbnot0 : b ∉ part ⊥ S := by
            intro hbmem
            rw [hp0eq, Set.mem_singleton_iff] at haP0 hbmem
            exact lexLT_ne hab (haP0.trans hbmem.symm)
          exact mem_part_of_notMem hb hbnot0
        have hcP1 : c ∈ part ⊤ S := mem_part_of_lexLT hbP1 hc hbc
        have hab_eq : disc a b = sIdx S := disc_eq_sIdx_of_cross haP0 hbP1
        have hbc_lt : sIdx S < disc b c := sIdx_lt_disc_of_part hbP1 hcP1 (lexLT_ne hbc)
        exact lt_irrefl _ ((h1lt.trans_eq hab_eq).trans hbc_lt)
      · have haP1 : a ∈ part ⊤ S := mem_part_of_notMem ha haP0
        have hbP1 : b ∈ part ⊤ S := mem_part_of_lexLT haP1 hb hab
        have hcP1 : c ∈ part ⊤ S := mem_part_of_lexLT hbP1 hc hbc
        have hdP1 : d ∈ part ⊤ S := mem_part_of_lexLT hcP1 hd hcd
        exact absurd ⟨h1lt, h2lt⟩ (hdegenerate1 a haP1 b hbP1 c hcP1 d hdP1 hab hbc hcd)
    · obtain ⟨p1, hp1eq⟩ := h1
      rintro a ha b hb c hc d hd hab hbc hcd ⟨h1lt, h2lt⟩
      by_cases hdP1 : d ∈ part ⊤ S
      · have hcP0 : c ∈ part ⊥ S := by
          have hcnot1 : c ∉ part ⊤ S := by
            intro hcmem
            rw [hp1eq, Set.mem_singleton_iff] at hdP1 hcmem
            exact lexLT_ne hcd (hcmem.trans hdP1.symm)
          exact mem_part_of_notMem hc hcnot1
        have hbP0 : b ∈ part ⊥ S := mem_part_of_lexLT hcP0 hb hbc
        have hcd_eq : disc c d = sIdx S := disc_eq_sIdx_of_cross hcP0 hdP1
        have hbc_lt : sIdx S < disc b c := sIdx_lt_disc_of_part hbP0 hcP0 (lexLT_ne hbc)
        exact lt_irrefl _ ((h2lt.trans_eq hcd_eq).trans hbc_lt)
      · have hdP0 : d ∈ part ⊥ S := mem_part_of_notMem hd hdP1
        have hcP0 : c ∈ part ⊥ S := mem_part_of_lexLT hdP0 hc hcd
        have hbP0 : b ∈ part ⊥ S := mem_part_of_lexLT hcP0 hb hbc
        have haP0 : a ∈ part ⊥ S := mem_part_of_lexLT hbP0 ha hab
        exact absurd ⟨h1lt, h2lt⟩ (hdegenerate0 a haP0 b hbP0 c hcP0 d hdP0 hab hbc hcd)

/-- `isDegenerate_iff_rec_of_nontrivial` with the singleton sides counted rather
than named. No finiteness hypothesis: `2 ≤ S.ncard` already forces `S` finite
(`Set.ncard` is `0` on infinite sets), and `Set.ncard_eq_one` holds
unconditionally, so the two statements are the same fact. -/
lemma isDegenerate_iff_rec {S : Set SetOrd} (hS : 2 ≤ S.ncard) :
    IsDegenerate S ↔ ((part ⊥ S).ncard = 1 ∧ IsDegenerate (part ⊤ S)) ∨
              ((part ⊤ S).ncard = 1 ∧ IsDegenerate (part ⊥ S)) := by
  simp only [Set.ncard_eq_one]
  exact isDegenerate_iff_rec_of_nontrivial (nontrivial_of_one_lt_ncard (by omega))

end «Lexicographic order and degenerate trees»

section «Transfinite peeling of infinite degenerate trees»

/-! Turn `isDegenerate_iff_rec_of_nontrivial`'s "one side is a singleton" fact into a
transfinite recursion, peeling one element off at a time. This section builds
the recursion and its two basic invariants (stays a degenerate tree; antitone); it does
*not* attempt termination/stabilization, the identification with `delta`, or the
cardinality theorem itself — those are separate, later pieces. -/

/-- One step of the peeling process: discard the singleton side of a nontrivial
degenerate tree, keeping the other (possibly still infinite) side. Junk value `S`
itself when `S` isn't a nontrivial degenerate tree (already a fixed point). -/
noncomputable def peelOnce (S : Set SetOrd) : Set SetOrd :=
  if _h : S.Nontrivial ∧ IsDegenerate S then
    if ∃ p0, part ⊥ S = {p0} then part ⊤ S else part ⊥ S
  else S

lemma peelOnce_subset {S : Set SetOrd} : peelOnce S ⊆ S := by
  unfold peelOnce
  split_ifs <;> first | exact fun _ hx => hx.1 | exact Set.Subset.refl S

/-- `peelOnce` preserves `IsDegenerate`. -/
lemma peelOnce_isDegenerate (hdegenerate : IsDegenerate S) : IsDegenerate (peelOnce S) := by
  unfold peelOnce
  split_ifs <;> first | exact hdegenerate.subset (fun _ hx => hx.1) | exact hdegenerate

/-- `peelOnce` removes *exactly one point*. -/
lemma diff_peelOnce_singleton (hS : S.Nontrivial) (hdegenerate : IsDegenerate S) :
    ∃ p ∈ S, S \ peelOnce S = {p} := by
  rw [peelOnce, dif_pos ⟨hS, hdegenerate⟩]
  by_cases h0 : ∃ p0, part ⊥ S = {p0}
  · rw [if_pos h0]
    obtain ⟨p0, hp0eq⟩ := h0
    refine ⟨p0, (hp0eq ▸ Set.mem_singleton p0 : p0 ∈ part ⊥ S).1, ?_⟩
    rw [show S \ part ⊤ S = part ⊥ S from sdiff_part ⊥, hp0eq]
  · rw [if_neg h0]
    rcases (isDegenerate_iff_rec_of_nontrivial hS).1 hdegenerate with ⟨h0', _⟩ | ⟨⟨p1, hp1eq⟩, _⟩
    · exact absurd h0' h0
    · refine ⟨p1, (hp1eq ▸ Set.mem_singleton p1 : p1 ∈ part ⊤ S).1, ?_⟩
      rw [show S \ part ⊥ S = part ⊤ S from sdiff_part ⊤, hp1eq]

lemma peelOnce_ssubset_of_nontrivial {S : Set SetOrd} (hS : S.Nontrivial)
    (hdegenerate : IsDegenerate S) : peelOnce S ⊂ S := by
  obtain ⟨p, hpS, hdiff⟩ := diff_peelOnce_singleton hS hdegenerate
  refine (Set.ssubset_iff_of_subset peelOnce_subset).2 ⟨p, hpS, ?_⟩
  have hp' : p ∈ S \ peelOnce S := by rw [hdiff]; exact Set.mem_singleton p
  exact hp'.2

/-- The transfinite peeling sequence: `remaining S 0 = S`, each successor step
peels one element via `peelOnce`, and at limit stages we take stock of what has
survived every earlier stage. Mirrors `Ordinal.derivFamily`'s use of
`Ordinal.limitRecOn` (`Mathlib.SetTheory.Ordinal.FixedPoint`), with a constant
`Set SetOrd` motive in place of `derivFamily`'s constant `Ordinal` one. -/
noncomputable def remaining (S : Set SetOrd) (a : Ordinal) : Set SetOrd :=
  Ordinal.limitRecOn a S (fun _ => peelOnce) (fun c _ ih => ⋂ b : Set.Iio c, ih _ b.2)

@[simp]
lemma remaining_zero (S : Set SetOrd) : remaining S 0 = S :=
  Ordinal.limitRecOn_zero ..

@[simp]
lemma remaining_add_one (S : Set SetOrd) (a : Ordinal) :
    remaining S (a + 1) = peelOnce (remaining S a) :=
  Ordinal.limitRecOn_add_one ..

lemma remaining_limit (S : Set SetOrd) {a : Ordinal} :
    Order.IsSuccLimit a → remaining S a = ⋂ b : Set.Iio a, remaining S b :=
  Ordinal.limitRecOn_limit _ _ _ _

lemma remaining_isDegenerate {S : Set SetOrd} (hdegenerate : IsDegenerate S) (a : Ordinal) :
    IsDegenerate (remaining S a) := by
  induction a using Ordinal.limitRecOn with
  | zero => rwa [remaining_zero]
  | add_one a ih => rw [remaining_add_one]; exact peelOnce_isDegenerate ih
  | limit a hlim ih =>
    rw [remaining_limit S hlim]
    obtain ⟨b0, hb0⟩ := hlim.nonempty_Iio
    exact (ih b0 hb0).subset (Set.iInter_subset (fun b : Set.Iio a => remaining S b) ⟨b0, hb0⟩)

lemma remaining_antitone (S : Set SetOrd) : Antitone (remaining S) := by
  have key : ∀ x y, y ≤ x → remaining S x ⊆ remaining S y := by
    intro x
    induction x using Ordinal.limitRecOn with
    | zero =>
      exact fun _ hy ↦ by rw [nonpos_iff_eq_zero.1 hy]
    | add_one x ih =>
      intro y hy
      rcases eq_or_lt_of_le hy with rfl | hlt
      · rfl
      · have hyx : y ≤ x := Order.lt_add_one_iff.1 hlt
        have hstep : remaining S (x + 1) ⊆ remaining S x := by
          rw [remaining_add_one]; exact peelOnce_subset
        exact hstep.trans (ih y hyx)
    | limit x hlim ih =>
      intro y hy
      rcases eq_or_lt_of_le hy with rfl | hlt
      · rfl
      · rw [remaining_limit S hlim]
        exact Set.iInter_subset (fun c : Set.Iio x => remaining S c) ⟨y, hlt⟩
  exact fun a b ↦ key b a

universe u in
/-- The peeling process stabilizes, and once stable, there is nothing left to
peel: the stable value is no longer `Nontrivial`. Stabilization itself is
`Ordinal.eventuallyConst_of_antitone`'s cofinality argument (no explicit numeric
bound needed) applied to `remaining_antitone`; if the stable value were still
`Nontrivial`, `peelOnce` would still force a proper decrease at the next step,
contradicting stability. The existential's bound variables need the explicit
`Ordinal.{u+1}` annotation (relative to `S`'s own `Ordinal.{u}`) rather than a
bare `Ordinal` — `remaining`'s index-ordinal universe is independent of its
elements' universe, and leaving it implicit here lets Lean's statement
elaboration pick a universe metavariable unconnected to the one the proof
(via the `Small.{u+1} (Set (SetOrd.{u}))` self-instance) actually needs. -/
lemma remaining_eventually_not_nontrivial {S : Set (SetOrd.{u})}
    (hdegenerate : IsDegenerate S) :
    ∃ i : Ordinal.{u+1}, ¬ (remaining S i).Nontrivial ∧
      ∀ j : Ordinal.{u+1}, i ≤ j → remaining S j = remaining S i := by
  obtain ⟨i, hi⟩ :=  Ordinal.eventuallyConst_of_antitone (remaining_antitone S)
    |> Filter.eventuallyConst_atTop.1
  refine ⟨i, fun hnt => ?_, hi⟩
  have heq : peelOnce (remaining S i) = remaining S i := by
    rw [← remaining_add_one]; exact hi (i + 1) (lt_add_one i).le
  have hssub := heq ▸ peelOnce_ssubset_of_nontrivial hnt (remaining_isDegenerate hdegenerate i)
  exact absurd hssub (lt_irrefl _)

universe u in
/-- Sharpening of `remaining_eventually_not_nontrivial`: the *least* ordinal at
which peeling stops, so that `remaining` genuinely peels one point at a time
for every earlier stage. -/
lemma remaining_stabilizes {S : Set (SetOrd.{u})} (hdegenerate : IsDegenerate S) :
    ∃ i0 : Ordinal.{u+1}, ¬ (remaining S i0).Nontrivial ∧
      ∀ b : Ordinal.{u+1}, b < i0 → (remaining S b).Nontrivial := by
  obtain ⟨i, hi, -⟩ := remaining_eventually_not_nontrivial hdegenerate
  have hne : {j : Ordinal.{u+1} | ¬ (remaining S j).Nontrivial}.Nonempty := ⟨i, hi⟩
  refine ⟨sInf {j : Ordinal.{u+1} | ¬ (remaining S j).Nontrivial}, csInf_mem hne, fun _ hb => ?_⟩
  exact by_contra (notMem_of_lt_csInf' hb)

/-- The single point removed from `remaining S b` at stage `b`, when peeling is
still active there; junk value `∅` otherwise. -/
noncomputable def removedPt (S : Set SetOrd) (b : Ordinal) : SetOrd :=
  if h : (remaining S b).Nontrivial ∧ IsDegenerate (remaining S b) then
    Classical.choose (diff_peelOnce_singleton h.1 h.2)
  else ∅

lemma removedPt_spec {b : Ordinal}
    (hnt : (remaining S b).Nontrivial) (hdegenerate : IsDegenerate (remaining S b)) :
    removedPt S b ∈ remaining S b ∧ remaining S b \ remaining S (b + 1) = {removedPt S b} := by
  rw [removedPt, dif_pos ⟨hnt, hdegenerate⟩, remaining_add_one]
  exact Classical.choose_spec (diff_peelOnce_singleton hnt hdegenerate)

/-- The point removed at stage `b` is genuinely gone from the very next stage. -/
lemma removedPt_notMem_succ {b : Ordinal}
    (hnt : (remaining S b).Nontrivial) (hdegenerate : IsDegenerate (remaining S b)) :
    removedPt S b ∉ remaining S (b + 1) := by
  have hmem : removedPt S b ∈ remaining S b \ remaining S (b + 1) :=
    (removedPt_spec hnt hdegenerate).2 ▸ rfl
  exact hmem.2

variable {α : Type*} {S : Set SetOrd}

/-- Shared engine behind `removedPt_injOn` and its later `delta`-side mirror
`sIdx_remaining_injOn`: both are "some value attached to stage `b`, drawn from
a container `Q` that's monotone under `remaining`'s antitone chain, is gone
from `Q` one step later and hence from every later stage" — `Q := id` for
`removedPt` itself, `Q := delta` for the `sIdx`-of-`remaining` values.

This one is not `private`, unlike the two lemmas it is built from: its
`delta`-side use sits in `SteppingUpLemma.Encoding.Delta`, on the far side of
the module boundary.
Factored once here since the two instances are the same argument, not just
similarly-shaped statements — the same pattern used throughout the file's
`part ⊥`/`part ⊤`-symmetry "Mirror of X" pairs, each unified behind a single
`Bool`-parametrized lemma. -/
private lemma notMem_of_lt_of_notMem_succ (hdegenerate : IsDegenerate S)
    {i0 : Ordinal} (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial)
    {f : Ordinal → α} {Q : Set SetOrd → Set α}
    (hQmono : ∀ {T T' : Set SetOrd}, T ⊆ T' → Q T ⊆ Q T')
    (hnotmem_succ : ∀ {b : Ordinal}, (remaining S b).Nontrivial → IsDegenerate (remaining S b) →
      f b ∉ Q (remaining S (b + 1)))
    {b c : Ordinal} (hbc : b < c) (hci0 : c < i0) : f b ∉ Q (remaining S c) :=
  fun hmem => hnotmem_succ (hlt b (hbc.trans hci0)) (remaining_isDegenerate hdegenerate b)
    (hQmono (remaining_antitone S (Order.add_one_le_iff.2 hbc)) hmem)

private lemma ne_of_lt_of_notMem_succ (hdegenerate : IsDegenerate S)
    {i0 : Ordinal} (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial)
    {f : Ordinal → α} {Q : Set SetOrd → Set α}
    (hQmono : ∀ {T T' : Set SetOrd}, T ⊆ T' → Q T ⊆ Q T')
    (hnotmem_succ : ∀ {b : Ordinal}, (remaining S b).Nontrivial → IsDegenerate (remaining S b) →
      f b ∉ Q (remaining S (b + 1)))
    (hmem_self : ∀ {b : Ordinal}, (remaining S b).Nontrivial → IsDegenerate (remaining S b) →
      f b ∈ Q (remaining S b))
    {b c : Ordinal} (hbc : b < c) (hci0 : c < i0) : f b ≠ f c := fun heq =>
  notMem_of_lt_of_notMem_succ hdegenerate hlt hQmono hnotmem_succ hbc hci0
    (heq ▸ hmem_self (hlt c hci0) (remaining_isDegenerate hdegenerate c))

lemma injOn_of_lt_of_notMem_succ (hdegenerate : IsDegenerate S)
    {i0 : Ordinal} (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial)
    {f : Ordinal → α} {Q : Set SetOrd → Set α}
    (hQmono : ∀ {T T' : Set SetOrd}, T ⊆ T' → Q T ⊆ Q T')
    (hnotmem_succ : ∀ {b : Ordinal}, (remaining S b).Nontrivial → IsDegenerate (remaining S b) →
      f b ∉ Q (remaining S (b + 1)))
    (hmem_self : ∀ {b : Ordinal}, (remaining S b).Nontrivial → IsDegenerate (remaining S b) →
      f b ∈ Q (remaining S b)) :
    Set.InjOn f (Set.Iio i0) := fun b hb c hc hbc => by
  rcases lt_trichotomy b c with h | h | h
  · exact absurd hbc (ne_of_lt_of_notMem_succ hdegenerate hlt hQmono hnotmem_succ hmem_self h hc)
  · exact h
  · exact absurd hbc.symm (ne_of_lt_of_notMem_succ hdegenerate hlt hQmono hnotmem_succ hmem_self h hb)

lemma removedPt_injOn (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    Set.InjOn (removedPt S) (Set.Iio i0) :=
  injOn_of_lt_of_notMem_succ hdegenerate hlt (·) removedPt_notMem_succ
    (removedPt_spec · · |>.1)

/-- Every point dropped from `S` by stage `β` was removed at some concrete
successor stage `c < β`: the crux fact making peeling exhaustive. A point can
only vanish at a limit stage if it was already missing from every earlier
stage (`remaining_limit`), so limit stages contribute no new departures. -/
lemma exists_removedPt_lt_of_not_mem (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    ∀ β : Ordinal, β ≤ i0 → ∀ x ∈ S, x ∉ remaining S β → ∃ c < β, x = removedPt S c := by
  intro β
  induction β using Ordinal.limitRecOn with
  | zero => intro _ x hx hx0; rw [remaining_zero] at hx0; exact absurd hx hx0
  | add_one c ih =>
    intro hle x hx hxc1
    by_cases hxc : x ∈ remaining S c
    · have hci0 : c < i0 := Order.add_one_le_iff.1 hle
      have hspec := (removedPt_spec (hlt c hci0) (remaining_isDegenerate hdegenerate c)).2
      have hxeq : x = removedPt S c := by
        have hxmem : x ∈ remaining S c \ remaining S (c + 1) := ⟨hxc, hxc1⟩
        rwa [hspec, Set.mem_singleton_iff] at hxmem
      exact ⟨c, lt_add_one c, hxeq⟩
    · have hcle : c ≤ i0 := le_of_lt (Order.add_one_le_iff.1 hle)
      obtain ⟨d, hd, hxeq⟩ := ih hcle x hx hxc
      exact ⟨d, hd.trans (lt_add_one c), hxeq⟩
  | limit c hc ih =>
    intro hle x hx hxc
    rw [remaining_limit S hc, Set.mem_iInter, not_forall] at hxc
    obtain ⟨⟨b, hb⟩, hxb⟩ := hxc
    obtain ⟨d, hd, hxeq⟩ := ih b hb (hb.le.trans hle) x hx hxb
    exact ⟨d, hd.trans hb, hxeq⟩

lemma removedPt_surjOn (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    Set.SurjOn (removedPt S) (Set.Iio i0) (S \ remaining S i0) := fun x hx =>
  let ⟨c, hc, hxeq⟩ := exists_removedPt_lt_of_not_mem hdegenerate hlt i0 le_rfl x hx.1 hx.2
  ⟨c, hc, hxeq.symm⟩

lemma remaining_subset_self {b : Ordinal} : remaining S b ⊆ S :=
  le_of_le_of_eq (remaining_antitone S bot_le) (remaining_zero _)

lemma removedPt_mapsTo (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    Set.MapsTo (removedPt S) (Set.Iio i0) (S \ remaining S i0) := fun b hb => by
  have hspec := removedPt_spec (hlt b hb) (remaining_isDegenerate hdegenerate b)
  refine ⟨remaining_subset_self hspec.1, fun hmem => ?_⟩
  exact removedPt_notMem_succ (hlt b hb) (remaining_isDegenerate hdegenerate b)
    (remaining_antitone S (Order.add_one_le_iff.2 hb) hmem)

end «Transfinite peeling of infinite degenerate trees»

end SteppingUp.Encoding
