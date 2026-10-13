/-
  The map `δ`, and the encoding of a finite set of vertices as a tree.

  `δ S` collects the split indices of `S` (`Δ(S)` of the paper's
  `def:split`), `deltaFinset` is its `Finset` form, `powersetCard_deltaFinset`
  is (I2) of `sec:bridge`, and `toTree` is the correspondence (I1),
  `obs:encoding` — the point at which this tower meets the colouring one.

  Built on `SteppingUpLemma.Encoding.Splitting`, which supplies `disc`, `sIdx`,
  `part`, `LexLT`, `IsDegenerate` and the transfinite peeling.
-/
import SteppingUpLemma.Encoding.Splitting

namespace SteppingUp.Encoding

open Lean.Parser.Tactic
open Cardinal

/- `Set Ordinal` membership isn't decidable in general (arbitrary ordinals), and this file
relies on classical membership decisions pervasively (`part`, `LexLT`, degenerate tree reasoning);
threading explicit `Decidable` instances or scoping `open Classical in` through every affected
declaration isn't practical here. -/
set_option linter.style.openClassical false
open scoped Classical

variable {x y z : SetOrd} {S T : Set SetOrd} {p : SetOrd} {b : Bool}

section «The map δ»

/-- `δ S = {disc x y : x ≠ y ∈ S}`; finite when `S` is (see `delta_finite`).
Defined for a general `Set (Set
Ordinal)` rather than only a `Finset`, matching `sIdx`'s generality: `part ⊥
S`/`part ⊤ S` for `S : Finset SetOrd` are themselves plain `Set`s (only
*provably* finite, not `Finset`s by type), so `delta` needs to accept them
directly in the induction below. -/
noncomputable def delta (S : Set SetOrd) : SetOrd := (Function.uncurry disc) '' S.offDiag

lemma delta_finite (hS : S.Finite) : (delta S).Finite :=
  .image _ (.offDiag hS)

/-- Peeling one element off `δ`: adding a fresh point `p` contributes exactly
its splits with the rest, on top of `δ T`. -/
lemma delta_insert_of_notMem (hp : p ∉ T) :
    delta (insert p T) = (disc p) '' T ∪ delta T := by
  ext
  simp only [delta, Set.offDiag_insert hp, Set.image_union, Set.singleton_prod,
    Set.prod_singleton, Set.image_image, Set.mem_union, Set.mem_image, Function.uncurry_apply_pair]
  grind only [disc_comm]

end «The map δ»

section «Proper subsets of a prescribed size»

/-! `exists_nondegenerate_subset_card` cuts a proper set down (or pads it up)
to any prescribed size `≥ 4`. It is uniform in `#S`: the crossing quadruple
that witnesses properness is finite, and any superset of it inside `S` is
again proper, so the argument never inspects whether `S` is finite. An earlier
version peeled a large finite `S` down one element at a time, which needed the
"type" `t(S) ∈ ℕ × ℕ` and its reduction lemmas, and ran only for finite `S`;
all of that went with the induction. -/


lemma ncard_part0_add_part1 (hSfin : S.Finite) : S.ncard = (part ⊥ S).ncard + (part ⊤ S).ncard := by
  conv_lhs => rw [← part_bot_union_part_top (S := S)]
  exact Set.ncard_union_eq parts_disjoint (part_finite_of_finite hSfin)
    (part_finite_of_finite hSfin)

lemma part_ncard_lt (hSfin : S.Finite) (hS : 2 ≤ S.ncard) :
    (part b S).ncard < S.ncard := by
  have := ncard_part0_add_part1 hSfin
  have hpos : 0 < (part (!b) S).ncard :=
      (Set.ncard_pos (part_finite_of_finite hSfin)).2 (part_nonempty hS)
  cases b <;> simp at hpos <;> omega


/-- Removing an element of `part b S` shrinks that side by exactly that element
and leaves `part (!b) S` untouched. -/
lemma remove_from_part
    (hS2 : 2 ≤ S.ncard) (hp : p ∈ part b S) (hcard : 2 ≤ (part b S).ncard) :
    part b (S \ {p}) = part b S \ {p} ∧ part (!b) (S \ {p}) = part (!b) S := by
  have hne : (part b S \ {p}).Nonempty :=
    nontrivial_of_one_lt_ncard (T := part b S) (by omega) |>.exists_ne p
  have hone : (part (!b) S).Nonempty := part_nonempty hS2
  -- Deleting `p` from its own side leaves the two sides covering `S \ {p}`.
  have heq : (part b S \ {p}) ∪ part (!b) S = S \ {p} := by
    conv_rhs => rw [← parts_union (S := S) (b := b)]
    rw [Set.union_sdiff_distrib,
      Set.sdiff_singleton_eq_self (Set.disjoint_left.1 parts_disjoint hp)]
  -- `sIdx_of_subset` is stated with the `⊥` side first, so the two cases feed
  -- it the same pair in opposite orders and read its conclusion accordingly.
  cases b with
  | false =>
    simp only [Bool.not_false] at heq hone ⊢
    have hres := heq ▸ sIdx_of_subset hne hone Set.sdiff_subset (fun _ => id)
    exact ⟨hres.2.1, hres.2.2⟩
  | true =>
    simp only [Bool.not_true] at heq hone ⊢
    have hres := sIdx_of_subset hone hne (fun _ => id) Set.sdiff_subset
    rw [Set.union_comm, heq] at hres
    exact ⟨hres.2.2, hres.2.1⟩

/-- A set of cardinality at least `m` contains a `Finset` of size exactly `m`
disjoint from a given finite `T0 ⊆ S` — enough of `S` to pad `T0` up to `m`. -/
private lemma exists_finset_pad {T0 : Finset SetOrd}
    (hT0 : ↑T0 ⊆ S) {m : ℕ} (hm : T0.card ≤ m)
    (hmS : (m : Cardinal) ≤ #S) :
    ∃ E : Finset SetOrd, ↑E ⊆ S \ ↑T0 ∧ E.card = m - T0.card := by
  by_cases hfin : S.Finite
  · have hn : m ≤ S.ncard := by
      rw [← Set.cast_ncard hfin] at hmS; exact_mod_cast hmS
    have hsplit : (S \ T0).ncard + T0.card = S.ncard := by
      rw [← Set.ncard_coe_finset T0]
      exact Set.ncard_sdiff_add_ncard_of_subset hT0 hfin
    obtain ⟨t, hts, htcard⟩ := Set.exists_subset_card_eq (n := m - T0.card)
      (s := S \ T0) (by omega)
    have htfin : t.Finite := (hfin.sdiff).subset hts
    refine ⟨htfin.toFinset, by rwa [htfin.coe_toFinset], ?_⟩
    rw [← Set.ncard_coe_finset, htfin.coe_toFinset, htcard]
  · have hinf : S.Infinite := hfin
    exact (hinf.sdiff T0.finite_toSet).exists_subset_card_eq _

/-- Every proper `S` with at least `m ≥ 4` elements has a proper subset of size
exactly `m`.

Properness supplies four elements `a ≺ b ≺ c ≺ d` of "crossing type"; pad that
quadruple up to `m` with further points of `S`. Degeneracy is inherited by
subsets (`IsDegenerate.subset`), so any superset of a proper set is proper and
no combinatorial work is needed.
-/
lemma exists_nondegenerate_subset_card {m : ℕ}
    (h : ¬ IsDegenerate S) (hm : 4 ≤ m) (hmS : (m : Cardinal) ≤ #S) :
    ∃ T : Finset SetOrd, ↑T ⊆ S ∧ T.card = m ∧
      ¬ IsDegenerate T := by
  -- properness supplies a crossing quadruple
  have h' := h
  unfold IsDegenerate at h'
  push Not at h'
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hbc, hcd, hcon⟩ := h'
  have hac : a ≺ c := Trans.trans hab hbc
  have had : a ≺ d := Trans.trans hac hcd
  have hbd : b ≺ d := Trans.trans hbc hcd
  have hab' : a ≠ b := @ne_of_lt _ instLinearOrderLexLT.toPreorder _ _ hab
  have hac' : a ≠ c := lexLT_ne hac
  have had' : a ≠ d := lexLT_ne had
  have hbc' : b ≠ c := lexLT_ne hbc
  have hbd' : b ≠ d := lexLT_ne hbd
  have hcd' : c ≠ d := lexLT_ne hcd
  set T0 : Finset SetOrd := {a, b, c, d} with hT0def
  have hT0card : T0.card = 4 := by
    rw [hT0def]
    repeat rw [Finset.card_insert_of_notMem (by simp_all)]
    simp
  have hT0sub : ↑T0 ⊆ S := by
    rw [hT0def]
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have haT0 : a ∈ T0 := by simp [hT0def]
  have hbT0 : b ∈ T0 := by simp [hT0def]
  have hcT0 : c ∈ T0 := by simp [hT0def]
  have hdT0 : d ∈ T0 := by simp [hT0def]

  -- pad it up to `m` inside `S`
  obtain ⟨E, hEsub, hEcard⟩ := exists_finset_pad hT0sub (by omega) hmS
  have hEdisj : Disjoint T0 E := by
    rw [Finset.disjoint_left]
    exact fun x hxT0 hxE ↦ (hEsub hxE).2 hxT0
  refine ⟨T0 ∪ E, ?_, ?_, ?_⟩
  · rw [Finset.coe_union]
    exact Set.union_subset hT0sub (hEsub.trans Set.sdiff_subset)
  · rw [Finset.card_union_of_disjoint hEdisj, hEcard]
    omega
  · exact fun hdegenerateUnion ↦ (
      (hdegenerateUnion.subset (by rw [Finset.coe_union]; exact Set.subset_union_left))
      a haT0 b hbT0 c hcT0 d hdT0 hab hbc hcd
    ) hcon

end «Proper subsets of a prescribed size»

section «delta as a Finset»

/-- `delta S` as a `Finset Ordinal`, for feeding to a `Finset Ordinal → ℕ`
base-level colouring (junk value `∅` if `delta S` happens to be infinite,
which never occurs at the call sites below since `S` is always finite
there). -/
noncomputable def deltaFinset (S : Set SetOrd) : Finset Ordinal :=
  if h : (delta S).Finite then h.toFinset else ∅

lemma coe_deltaFinset_of_finite (hSfin : S.Finite) : deltaFinset S = delta S := by
  simp [deltaFinset, delta_finite hSfin]

lemma card_deltaFinset_of_finite (hSfin : S.Finite) : (deltaFinset S).card = (delta S).ncard := by
  exact coe_deltaFinset_of_finite hSfin ▸ Set.ncard_coe_finset _ |>.symm

end «delta as a Finset»

section «Assembly infrastructure: powersetCard_deltaFinset and friends»

/-! The `delta_insert`/`powersetCard_deltaFinset` layer; feeds
`mono_degenerate`/`isDegenerate_of_mono` in `Infinitary.lean`. -/

variable {S T: Set SetOrd}

/-- Inserting the `part b`-singleton `p` into a nonempty subset of the other
part adds exactly `sIdx S` to its `δ`-image. -/
private lemma delta_insert
    (hpmem : p ∈ part b S) (hTsub : T ⊆ part (!b) S) (hTne : T.Nonempty) :
    delta (insert p T) = insert (sIdx S) (delta T) := by
  have hpnotmem : p ∉ T := Set.disjoint_left.1 parts_disjoint hpmem ∘ (hTsub ·)
  -- Every point of `T` is on the far side of `p`, so `disc p` is constant on it.
  rw [delta_insert_of_notMem hpnotmem,
    Set.image_congr (g := fun _ => sIdx S) (fun _ hy => disc_eq_sIdx_of_cross hpmem (hTsub hy)),
    hTne.image_const, Set.insert_eq]

lemma sIdx_mem_delta_of_nontrivial (hS : S.Nontrivial) : sIdx S ∈ delta S := by
  unfold sIdx delta
  exact csInf_mem ((Set.offDiag_nonempty.2 hS).image (Function.uncurry disc))

lemma delta_mono (h : S ⊆ T) : delta S ⊆ delta T :=
  Set.image_mono (Set.offDiag_mono h)

/-- `peelOnce` keeps one whole part and discards the other; `b` names the side
it keeps. Extracted from `diff_peelOnce_singleton`, which records only that the
discarded side is a singleton — here we also need to know that a dropped point
and a surviving one sit on *opposite* sides, which is what makes their split
index `sIdx`. -/
private lemma exists_peelOnce_eq_part (hS : S.Nontrivial)
    (hdegenerate : IsDegenerate S) :
    ∃ b : Bool, peelOnce S = part b S ∧ S \ peelOnce S = part (!b) S := by
  rw [peelOnce, dif_pos ⟨hS, hdegenerate⟩]
  split_ifs
  exacts [⟨⊤, rfl, sdiff_part ⊥⟩, ⟨⊥, rfl, sdiff_part ⊤⟩]

/-- The point added to `delta` by peeling is genuinely new: `sIdx S` splits a
pair straddling the two parts, so it is strictly below every split occurring
inside the surviving one. -/
lemma sIdx_notMem_delta_peelOnce (hS : S.Nontrivial) (hdegenerate : IsDegenerate S) :
    sIdx S ∉ delta (peelOnce S) := by
  obtain ⟨b, hb, -⟩ := exists_peelOnce_eq_part hS hdegenerate
  rw [hb]
  rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, hz⟩
  exact absurd hz (sIdx_lt_disc_of_part hx hy hxy).ne'


/-- Mirror of `sIdx_notMem_delta_peelOnce` phrased at the `remaining`-chain level:
the `sIdx` contributed at stage `b` is genuinely new to `delta` too, once peeling
moves past it. -/
lemma sIdx_remaining_notMem_succ {b : Ordinal}
    (hnt : (remaining S b).Nontrivial) (hdegenerate : IsDegenerate (remaining S b)) :
    sIdx (remaining S b) ∉ delta (remaining S (b + 1)) := by
  rw [remaining_add_one]
  exact sIdx_notMem_delta_peelOnce hnt hdegenerate

/-- `b ↦ sIdx (remaining S b)` is injective on `Set.Iio i0`: the `delta`-side
mirror of `removedPt_injOn`. -/
lemma sIdx_remaining_injOn (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    Set.InjOn (fun b => sIdx (remaining S b)) (Set.Iio i0) :=
  injOn_of_lt_of_notMem_succ hdegenerate hlt delta_mono sIdx_remaining_notMem_succ
    (fun hnt _ => sIdx_mem_delta_of_nontrivial hnt)

lemma sIdx_remaining_mem_delta {i0 : Ordinal}
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) {b : Ordinal} (hb : b < i0) :
    sIdx (remaining S b) ∈ delta S :=
  delta_mono remaining_subset_self (sIdx_mem_delta_of_nontrivial (hlt b hb))

/-- The stage at which peeling separates a given pair `x ≠ y`: both survive to
`remaining S c`, and the next step drops one of them.

Such a stage exists below `i0` because `remaining S i0` is too small to hold
both points, and it cannot be a limit: at limits `remaining` is an
intersection, so a pair surviving at every earlier stage survives the limit
too. That leaves a successor, which is the stage wanted. -/
private lemma exists_separating_stage {i0 : Ordinal}
    (hi0 : ¬ (remaining S i0).Nontrivial) {x y : Set Ordinal}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ c < i0, x ∈ remaining S c ∧ y ∈ remaining S c ∧
      ¬ (x ∈ remaining S (c + 1) ∧ y ∈ remaining S (c + 1)) := by
  set B := {b | ¬ (x ∈ remaining S b ∧ y ∈ remaining S b)} with hBdef
  have hi0B : i0 ∈ B := fun hi => hi0 ⟨x, hi.1, y, hi.2, hxy⟩
  have hboth {b} : b < sInf B → x ∈ remaining S b ∧ y ∈ remaining S b :=
    fun hb => not_not.1 (notMem_of_lt_csInf' hb)
  have hBmem : sInf B ∈ B := csInf_mem ⟨i0, hi0B⟩
  -- `sInf B` is neither `0` nor a limit, so it is a successor.
  rcases Ordinal.zero_or_succ_or_isSuccLimit (sInf B) with hz | ⟨c, hc⟩ | hlim
  · exact absurd (show x ∈ remaining S (sInf B) ∧ y ∈ remaining S (sInf B) by
      rw [hz, remaining_zero]; exact ⟨hx, hy⟩) hBmem
  · rw [Order.succ_eq_add_one] at hc
    have hcs : c < sInf B := hc ▸ lt_add_one c
    exact ⟨c, lt_of_lt_of_le hcs (csInf_le' hi0B), (hboth hcs).1, (hboth hcs).2, hc ▸ hBmem⟩
  · refine absurd ?_ hBmem
    rw [remaining_limit S hlim]
    exact ⟨Set.mem_iInter.2 fun b => (hboth b.2).1,
      Set.mem_iInter.2 fun b => (hboth b.2).2⟩

/-- Surjectivity of the enumeration `b ↦ sIdx (remaining S b)`: *every* point of
`δ S` is the split index of some peeling stage. Together with
`sIdx_remaining_injOn` this makes `δ S` a faithful copy of the stages below
`i0`.

Given `o = disc x y`, take the stage `c` that separates `x` from `y`. Exactly
one of them is dropped there, and `peelOnce` drops a whole part, so the two lie
on opposite sides of `remaining S c` — precisely the situation in which `disc`
computes `sIdx`. -/
lemma delta_subset_image_sIdx_remaining (hdegenerate : IsDegenerate S) {i0 : Ordinal}
    (hi0 : ¬ (remaining S i0).Nontrivial)
    (hlt : ∀ b, b < i0 → (remaining S b).Nontrivial) :
    delta S ⊆ (fun b => sIdx (remaining S b)) '' Set.Iio i0 := by
  rintro o ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩
  dsimp only [Function.uncurry] at hx hy hxy ⊢
  obtain ⟨c, hc, hxc, hyc, hsep⟩ := exists_separating_stage hi0 hx hy hxy
  refine ⟨c, hc, ?_⟩
  have hntc := hlt c hc
  have hdegc := remaining_isDegenerate hdegenerate c
  obtain ⟨b, hpeel, hdrop⟩ := exists_peelOnce_eq_part hntc hdegc
  obtain ⟨q, -, hq⟩ := diff_peelOnce_singleton hntc hdegc
  rw [remaining_add_one] at hsep
  -- A point of `remaining S c` that does not survive the step is `q`; so at
  -- most one of `x`, `y` is dropped, and by `hsep` exactly one is.
  have hdropped : ∀ {u : Set Ordinal}, u ∈ remaining S c →
      u ∉ peelOnce (remaining S c) → u = q := fun hu hu' =>
    Set.mem_singleton_iff.1 (hq ▸ ⟨hu, hu'⟩)
  -- The dropped point and the surviving one lie on opposite sides.
  have key : ∀ {u v : Set Ordinal}, u ∈ remaining S c → u ∉ peelOnce (remaining S c) →
      v ∈ peelOnce (remaining S c) → disc u v = sIdx (remaining S c) := by
    intro u v hu hu' hv'
    rw [disc_comm]
    exact disc_eq_sIdx_of_cross (hpeel ▸ hv' : v ∈ part b (remaining S c))
      (hdrop ▸ ⟨hu, hu'⟩ : u ∈ part (!b) (remaining S c))
  by_cases hxin : x ∈ peelOnce (remaining S c)
  · rw [disc_comm]
    exact (key hyc (fun h => hsep ⟨hxin, h⟩) hxin).symm
  · have hyin : y ∈ peelOnce (remaining S c) := by
      by_contra hyin
      exact hxy ((hdropped hxc hxin).trans (hdropped hyc hyin).symm)
    exact (key hxc hxin hyin).symm

/-- **`obs:deltaCard-inf`, uniformly.** No finiteness hypothesis, and no case split
on one: the peeling of `S` is run transfinitely, and its stages below `i0`
biject at the same time with `S` minus whatever peeling leaves behind
(`removedPt`) and with `δ S` (`sIdx ∘ remaining`). Comparing the two bijections
gives `#(δ S) = #(S \ remaining S i0)`, where `remaining S i0` is a
subsingleton.

The one case analysis left is not about finiteness but about that terminal set:
peeling normally halts on a single leftover point, but on an infinite `S` it
can instead exhaust the set. When it does, `i0` is a limit — peeling leaves a
point standing at `0` and at every successor stage — so the stages, and hence
`δ S`, are infinite and absorb the `+ 1` unaided. -/
lemma card_delta (hS : S.Nonempty)
    (hdegenerate : IsDegenerate S) : #(delta S) + 1 = #S := by
  obtain ⟨i0, hi0nt, hlt⟩ := remaining_stabilizes hdegenerate
  have hbijR : Set.BijOn (removedPt S) (Set.Iio i0) (S \ remaining S i0) :=
    ⟨removedPt_mapsTo hdegenerate hlt, removedPt_injOn hdegenerate hlt,
      removedPt_surjOn hdegenerate hlt⟩
  have hbijD : Set.BijOn (fun b => sIdx (remaining S b)) (Set.Iio i0) (delta S) :=
    ⟨fun _ hb => sIdx_remaining_mem_delta hlt hb, sIdx_remaining_injOn hdegenerate hlt,
      delta_subset_image_sIdx_remaining hdegenerate hi0nt hlt⟩
  have hmk : #(↥(S \ remaining S i0)) = #(delta S) :=
    Cardinal.mk_congr (hbijR.equiv.symm.trans hbijD.equiv)
  have hsplit : #S = #(delta S) + #(remaining S i0) := by
    rw [← hmk]
    conv_lhs => rw [← Set.sdiff_union_of_subset
      (remaining_subset_self (S := S) (b := i0))]
    rw [Cardinal.mk_union_of_disjoint Set.disjoint_sdiff_left]
  rcases (Set.not_nontrivial_iff.1 hi0nt).eq_empty_or_singleton with hemp | ⟨p, hps⟩
  · -- Peeling exhausted `S`, so `i0` is a limit and there are infinitely many stages.
    have hlim : Order.IsSuccLimit i0 := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit i0 with hz | ⟨c, hc⟩ | hlim
      · rw [hz, remaining_zero] at hemp; exact absurd hemp hS.ne_empty
      · -- A successor stage still leaves the point that survived the last peel.
        rw [Order.succ_eq_add_one] at hc
        subst hc
        have hntc := hlt c (lt_add_one c)
        obtain ⟨q, -, hq⟩ := diff_peelOnce_singleton hntc (remaining_isDegenerate hdegenerate c)
        obtain ⟨u, hu, v, hv, huv⟩ := hntc
        have hdropped : ∀ {w : Set Ordinal}, w ∈ remaining S c → w = q := by
          intro w hw
          refine Set.mem_singleton_iff.1 (hq ▸ ⟨hw, fun hw' => ?_⟩)
          rw [← remaining_add_one, hemp] at hw'
          exact hw'
        exact absurd ((hdropped hu).trans (hdropped hv).symm) huv
      · exact hlim
    have hIioInf : (Set.Iio i0).Infinite :=
      Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : Ordinal))
        Nat.cast_injective fun n =>
          lt_of_lt_of_le (Ordinal.natCast_lt_omega0 n) (Ordinal.omega0_le_of_isSuccLimit hlim)
    have : Infinite ↥(Set.Iio i0) := hIioInf.to_subtype
    have hDinf : Infinite ↥(delta S) := Infinite.of_injective _ hbijD.equiv.injective
    have hzero : #(↥(remaining S i0)) = 0 := by rw [hemp]; simp
    rw [hsplit, hzero, add_zero]
    exact Cardinal.add_one_eq (Cardinal.aleph0_le_mk_iff.2 hDinf)
  · rw [hsplit, hps, Cardinal.mk_singleton]

/-- `part b` of a literal `Finset SetOrd` `S`, agreeing with the
`Set`-level `part b` of `↑S`. -/
noncomputable def partFin (b : Bool) (S : Finset SetOrd) : Finset SetOrd :=
  S.filter (fun x => bif b then sIdx S ∈ x else sIdx S ∉ x)

lemma coe_partFin (b : Bool) (S : Finset SetOrd) :
    partFin b S = part b S := by
  simp only [partFin, Bool.cond_prop, Finset.coe_filter, part, SetLike.mem_coe]

lemma card_partFin (b : Bool) (S : Finset SetOrd) :
    (partFin b S).card = (part b S).ncard := by
  rw [← Set.ncard_coe_finset (partFin b S), coe_partFin]

/-- `parts_disjoint`, transported to the `Finset` level through `coe_partFin`.
`b`-indexed for the same reason: one statement serves both orientations. -/
lemma partFin_disjoint {b : Bool} (S : Finset SetOrd) :
    Disjoint (partFin b S) (partFin (!b) S) := by
  rw [← Finset.disjoint_coe, coe_partFin, coe_partFin]
  exact parts_disjoint

lemma partFin_card_lt {b : Bool} {S : Finset SetOrd} (hS : 2 ≤ S.card) :
    (partFin b S).card < S.card := by
  rw [card_partFin, ← Set.ncard_coe_finset S]
  exact part_ncard_lt S.finite_toSet (by rwa [Set.ncard_coe_finset])

/-- The two `partFin` halves cover `S`. `Finset`-level counterpart of
`part_bot_union_part_top`. -/
lemma partFin_union (S : Finset SetOrd) : partFin ⊥ S ∪ partFin ⊤ S = S := by
  apply Finset.coe_injective
  rw [Finset.coe_union, coe_partFin, coe_partFin, part_bot_union_part_top]

/-- The two `partFin` halves partition `S`'s cardinality. -/
lemma partFin_card_add (S : Finset SetOrd) :
    (partFin ⊥ S).card + (partFin ⊤ S).card = S.card := by
  have hdisj : Disjoint (partFin ⊥ S) (partFin ⊤ S) := partFin_disjoint S
  rw [← Finset.card_union_of_disjoint hdisj, partFin_union]

/-- Neither half is empty once `S` has at least two elements. `part_nonempty`
read through `coe_partFin`; nothing is needed of `S` beyond its cardinality. -/
lemma partFin_nonempty {b : Bool} {S : Finset SetOrd} (hS : 2 ≤ S.card) :
    (partFin b S).Nonempty := by
  rw [← Finset.coe_nonempty, coe_partFin]
  exact part_nonempty (by rwa [Set.ncard_coe_finset])

/-- Each half of a `partFin` split is a *strict* subset. -/
lemma partFin_ssub {b : Bool} {S : Finset SetOrd} (hS : 2 ≤ S.card) :
    partFin b S ⊂ S := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨by unfold partFin; exact Finset.filter_subset _ _, ?_⟩
  have : (partFin b S).card < S.card := partFin_card_lt hS
  intro
  simp_all

/-- Recursive characterisation of `IsDegenerate S`. -/
lemma isDegenerate_iff_rec_fin {S : Finset SetOrd} (hS : 2 ≤ S.card) :
    IsDegenerate S ↔
      ((partFin ⊥ S).card = 1 ∧ IsDegenerate (partFin ⊤ S)) ∨
      ((partFin ⊤ S).card = 1 ∧ IsDegenerate (partFin ⊥ S)) := by
  rw [isDegenerate_iff_rec (by rwa [Set.ncard_coe_finset]), card_partFin ⊥, card_partFin ⊤,
    coe_partFin ⊥, coe_partFin ⊤]

/-- `Finset`-level counterpart of `delta_insert`, bridged via
`coe_deltaFinset_of_finite` and `Finset.coe_inj` (a `Finset` is determined by
its coercion to `Set`). -/
private lemma deltaFinset_insert {T : Finset SetOrd}
    (hpmem : p ∈ part b S)
    (hTsub : ↑T ⊆ part (!b) S) (hTne : T.Nonempty) :
    deltaFinset ↑(insert p T) =
      insert (sIdx S) (deltaFinset T) := by
  have hSetEq : delta ↑(insert p T) = insert (sIdx S) (delta T) := by
    rw [Finset.coe_insert]
    exact delta_insert hpmem hTsub (Finset.coe_nonempty.mpr hTne)
  apply Finset.coe_injective
  rw [coe_deltaFinset_of_finite (insert p T).finite_toSet, hSetEq, Finset.coe_insert,
    coe_deltaFinset_of_finite T.finite_toSet]

/-- `Finset`-level cardinality of `deltaFinset`: `card_delta` (`Cardinal`-valued,
and the only place the counting actually happens) cast down to `Finset.card`.
Everything but the first line is that cast — `S.finite_toSet` is what makes it
legitimate, via `Set.cast_ncard`, `card_deltaFinset_of_finite` and
`Set.ncard_coe_finset`. -/
lemma card_deltaFinset_eq {S : Finset SetOrd} (hS : S.Nonempty)
    (hdegenerate : IsDegenerate S) :
    (deltaFinset S).card + 1 = S.card := by
  have h := card_delta (Finset.coe_nonempty.mpr hS) hdegenerate
  rw [← Set.cast_ncard (delta_finite S.finite_toSet),
    ← Set.cast_ncard S.finite_toSet] at h
  rw [card_deltaFinset_of_finite S.finite_toSet, ← Set.ncard_coe_finset S]
  exact_mod_cast h

/-- Shared "insert-peel" step of `powersetCard_deltaFinset`'s recursive case:
both the `part ⊥`-singleton and `part ⊤`-singleton branches there reduce to
exactly this, after peeling the singleton `p` off `S = insert p Tpart` — only
which side `p`/`Tpart` sit on (justifying `hnotmem`/`hinsert`) differs between
the two callers, and that difference is entirely confined to how *they*
derive these hypotheses, not to this lemma's own proof. Factoring it out
turns two ~80-line near-duplicate blocks in `powersetCard_deltaFinset` into
two short calls. -/
private lemma powersetCard_deltaFinset_insert_step {S Tpart : Finset SetOrd}
    {p : SetOrd} {n : ℕ} (hSeq : S = insert p Tpart) (hpnotmem : p ∉ Tpart)
    (hgen : deltaFinset S = insert (sIdx S) (deltaFinset Tpart))
    (hnotmem : sIdx S ∉ deltaFinset Tpart)
    (hinsert : ∀ U ⊆ Tpart, U.Nonempty →
      deltaFinset ↑(insert p U) = insert (sIdx S) (deltaFinset U))
    (hIH : (deltaFinset Tpart).powersetCard n = (Tpart.powersetCard (n + 1)).image
        (fun T : Finset SetOrd => deltaFinset T))
    (hIH1 : (deltaFinset Tpart).powersetCard (n + 1) =
      (Tpart.powersetCard (n + 1 + 1)).image
        (fun T : Finset SetOrd => deltaFinset T)) :
    (deltaFinset S).powersetCard (n + 1) =
      (S.powersetCard (n + 1 + 1)).image
        (fun T : Finset SetOrd => deltaFinset T) := by
  rw [hgen]
  conv_rhs => rw [hSeq]
  rw [Finset.powersetCard_succ_insert hnotmem, Finset.powersetCard_succ_insert hpnotmem,
    Finset.image_union]
  congr 1
  · ext W
    constructor
    · intro hW
      obtain ⟨V, hV, hVW⟩ := Finset.mem_image.1 hW
      rw [hIH, Finset.mem_image] at hV
      obtain ⟨U, hU, hUV⟩ := hV
      rw [Finset.mem_powersetCard] at hU
      have hUne : U.Nonempty := Finset.card_pos.1 (by omega)
      exact Finset.mem_image.2 ⟨insert p U,
        Finset.mem_image.2 ⟨U, Finset.mem_powersetCard.2 hU, rfl⟩,
        by rw [hinsert U hU.1 hUne, hUV, hVW]⟩
    · intro hW
      obtain ⟨W', hW', hWeq⟩ := Finset.mem_image.1 hW
      obtain ⟨U, hU, hUW'⟩ := Finset.mem_image.1 hW'
      rw [Finset.mem_powersetCard] at hU
      have hUne : U.Nonempty := Finset.card_pos.1 (by omega)
      have hWeq2 : deltaFinset ↑(insert p U) = W := by rw [hUW']; exact hWeq
      exact Finset.mem_image.2 ⟨deltaFinset U,
        by rw [hIH, Finset.mem_image]; exact ⟨U, Finset.mem_powersetCard.2 hU, rfl⟩,
        by rw [← hWeq2, hinsert U hU.1 hUne]⟩

/-- (I2) of `sec:bridge`, `Finset`-level: `[δ S]^r = δ " [S]^{r+1}` for
`S : Finset SetOrd`, stated with `deltaFinset` throughout since
`Finset.powersetCard` forces genuine `Finset` arguments; the recursion stays
within `Finset SetOrd` via `partFin ⊥`/`partFin ⊤` above. -/
lemma powersetCard_deltaFinset {S : Finset SetOrd} (hS : S.Nonempty)
    (hdegenerate : IsDegenerate S) (r : ℕ) :
    (deltaFinset S).powersetCard r =
      (S.powersetCard (r + 1)).image
        (fun T : Finset SetOrd => deltaFinset T) := by
  induction S using Finset.strongInductionOn generalizing r with
  | _ S ih =>
    rcases r with _ | n
    · rw [Finset.powersetCard_zero]
      have hconst : ∀ V ∈ S.powersetCard 1, deltaFinset V = ∅ := by
        intro V hV
        rw [Finset.mem_powersetCard] at hV
        obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hV.2
        have hSetEmpty : delta V = ∅ := by
          rw [hy, Finset.coe_singleton, Set.eq_empty_iff_forall_notMem]
          intro z ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, _⟩
          rw [Set.mem_singleton_iff] at ha hb
          exact hab (ha.trans hb.symm)
        apply Finset.coe_injective
        rw [coe_deltaFinset_of_finite V.finite_toSet, hSetEmpty, Finset.coe_empty]
      have hne1 : (S.powersetCard 1).Nonempty :=
        Finset.powersetCard_nonempty.2 (by have := Finset.card_pos.2 hS; omega)
      ext U
      simp only [Finset.mem_singleton, Finset.mem_image]
      constructor
      · intro hU
        obtain ⟨V, hV⟩ := hne1
        exact ⟨V, hV, by rw [hU]; exact hconst V hV⟩
      · exact fun ⟨V, hV, hVeq⟩ ↦ hVeq ▸ hconst V hV
    · rcases Nat.lt_or_ge S.card 2 with hlt | hge
      · have hlhs : (deltaFinset S).powersetCard (n + 1) = ∅ := by
          rw [Finset.powersetCard_eq_empty]
          have hc := card_deltaFinset_eq hS hdegenerate
          omega
        have hrhs : (S.powersetCard (n + 1 + 1)).image
            (fun T : Finset SetOrd => deltaFinset T) = ∅ := by
          rw [Finset.powersetCard_eq_empty.2 (by omega), Finset.image_empty]
        rw [hlhs, hrhs]
      · -- One side is a singleton. The two cases are the same argument with
        -- the roles of `⊥` and `⊤` exchanged, so index it by the singleton
        -- side `b`; `!b` is then the side the recursion descends into.
        have branch : ∀ b : Bool, (partFin b S).card = 1 →
            IsDegenerate (partFin (!b) S) →
            (deltaFinset S).powersetCard (n + 1) =
              (S.powersetCard (n + 1 + 1)).image
                (fun T : Finset SetOrd => deltaFinset T) := by
          intro b hb hdegenerate'
          obtain ⟨p, hpeq⟩ := Finset.card_eq_one.1 hb
          have hpmem : p ∈ partFin b S := hpeq ▸ Finset.mem_singleton_self p
          have hpnotmem : p ∉ partFin (!b) S :=
            Finset.disjoint_left.1 (partFin_disjoint S) (hpeq ▸ Finset.mem_singleton_self p)
          have hpeqSet : part b S = {p} := by
            rw [← coe_partFin b, hpeq, Finset.coe_singleton]
          have hpmemSet : p ∈ part b S := by
            rw [hpeqSet]; exact Set.mem_singleton p
          have hSeqSet : ↑S =
              insert p (part (!b) S) := by
            conv_lhs => rw [← parts_union (b := b) (S := S), hpeqSet]
            rw [Set.insert_eq]
          have hSeq : S = insert p (partFin (!b) S) := by
            apply Finset.coe_injective
            rw [Finset.coe_insert, coe_partFin (!b)]
            exact hSeqSet
          have hTne : (partFin (!b) S).Nonempty := partFin_nonempty hge
          have hgen : deltaFinset S =
              insert (sIdx S)
                (deltaFinset (partFin (!b) S)) := by
            conv_lhs => rw [hSeq]
            exact deltaFinset_insert hpmemSet (by rw [coe_partFin (!b)]) hTne
          have hnotmem : sIdx S ∉
              deltaFinset (partFin (!b) S) := by
            rw [← Finset.mem_coe, coe_deltaFinset_of_finite (partFin (!b) S).finite_toSet]
            rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, hz⟩
            rw [coe_partFin (!b)] at hx hy
            exact lt_irrefl _ (hz ▸ sIdx_lt_disc_of_part hx hy hxy)
          have hT_ssub : partFin (!b) S ⊂ S := partFin_ssub hge
          have hinsert : ∀ U ⊆ partFin (!b) S, U.Nonempty →
              deltaFinset ↑(insert p U) =
                insert (sIdx S) (deltaFinset U) :=
            fun U hU hUne => deltaFinset_insert hpmemSet
              (by rw [← coe_partFin (!b)]; exact_mod_cast hU) hUne
          exact powersetCard_deltaFinset_insert_step hSeq hpnotmem hgen hnotmem hinsert
            (ih (partFin (!b) S) hT_ssub hTne hdegenerate' n)
            (ih (partFin (!b) S) hT_ssub hTne hdegenerate' (n + 1))
        rcases (isDegenerate_iff_rec_fin hge).1 hdegenerate with ⟨h0, hd1⟩ | ⟨h1, hd0⟩
        · exact branch ⊥ h0 hd1
        · exact branch ⊤ h1 hd0

end «Assembly infrastructure: powersetCard_deltaFinset and friends»

section «toTree: the Finset SetOrd → Tree correspondence»

/-- The tree built from a finite set of sets-of-ordinals by iterated
splitting, with `partFin` playing the role `part` plays at the `Set` level;
`partFin_ssub` is what makes the recursion terminate. -/
noncomputable def toTree (S : Finset SetOrd) : SteppingUp.Trees.Tree :=
  if _ : S.card ≤ 1 then .nil
  else .node (toTree (partFin ⊥ S)) (toTree (partFin ⊤ S))
termination_by S.card
decreasing_by all_goals exact partFin_card_lt (by omega)


/-- `(toTree S).numLeaves = S.card`, for nonempty `S`. -/
lemma lv_toTree {S : Finset SetOrd} (hS : 1 ≤ S.card) :
    (toTree S).numLeaves = S.card := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rw [toTree]
    split_ifs with h <;> simp only [BinaryTree.numLeaves]
    · omega
    · have hS2 : 2 ≤ S.card := by omega
      rw [ih _ (partFin_ssub hS2) (Finset.card_pos.2 (partFin_nonempty (b := ⊥) hS2)),
        ih _ (partFin_ssub hS2) (Finset.card_pos.2 (partFin_nonempty (b := ⊤) hS2))]
      exact partFin_card_add S


/-- `isDegenerate_of_subsingleton` at the `Finset` level. -/
lemma isDegenerate_of_card_le_one {S : Finset SetOrd} (hS : S.card ≤ 1) :
    IsDegenerate S :=
  isDegenerate_of_subsingleton fun _ ha _ hb =>
    Finset.card_le_one.1 hS _ (by exact_mod_cast ha) _ (by exact_mod_cast hb)

/-- Unfolding `toTree` at a set with `≥ 2` elements. -/
lemma toTree_eq_node {T : Finset SetOrd} (hT2 : 2 ≤ T.card) :
    toTree T = SteppingUp.Trees.Tree.node (toTree (partFin ⊥ T)) (toTree (partFin ⊤ T)) := by
  rw [toTree]; exact dif_neg (by omega)

/-- Imported fact (I2)-flavoured bridge: `toTree S` is a degenerate *tree*
exactly when `S` is a degenerate *set*. -/
lemma isDegenerate_toTree_iff {S : Finset SetOrd} :
    (toTree S).core.isNone ↔ IsDegenerate S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rw [toTree]
    split_ifs with h
    · simp only [BinaryTree.core, Option.isNone_none, true_iff]
      exact isDegenerate_of_card_le_one (by omega)
    · have h2 : 2 ≤ S.card := by omega
      have hLne := Finset.card_pos.2 (partFin_nonempty (b := ⊥) h2)
      have hRne := Finset.card_pos.2 (partFin_nonempty (b := ⊤) h2)
      have hlvL : (toTree (partFin ⊥ S)).numLeaves = (partFin ⊥ S).card := lv_toTree hLne
      have hlvR : (toTree (partFin ⊤ S)).numLeaves = (partFin ⊤ S).card := lv_toTree hRne
      have hnode := SteppingUp.Trees.core_isNone_eq_ite
        (toTree (partFin ⊥ S)) (toTree (partFin ⊤ S))
      simp only [hlvL, hlvR] at hnode
      rw [isDegenerate_iff_rec_fin h2, hnode]
      split_ifs with h' h''
      · have hLnil : toTree (partFin ⊥ S) = .nil := by
          have := lv_toTree (S := partFin ⊥ S) (by omega)
          rw [hlvL] at this
          cases htl : toTree (partFin ⊥ S) using BinaryTree.unitRecOn with
          | base => rfl
          | ind A B =>
            simp only [htl, BinaryTree.numLeaves] at hlvL
            have := A.numLeaves_pos; have := B.numLeaves_pos
            omega
        rw [ih (partFin ⊤ S) (partFin_ssub h2)]
        constructor
        · exact (Or.inl ⟨h', ·⟩)
        · rintro (⟨-, hd⟩ | ⟨h1, hd⟩)
          · exact hd
          · exact isDegenerate_of_card_le_one (by omega)
      · rw [ih (partFin ⊥ S) (partFin_ssub h2)]
        constructor
        · exact (Or.inr ⟨h'', ·⟩)
        · rintro (⟨h1, hd⟩ | ⟨-, hd⟩)
          · exact absurd h1 h'
          · exact hd
      · simp only [false_iff]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact h' h1
        · exact h'' h1

/-- Erasing the single element of a singleton `part b S` leaves `part (!b) S`.
The companion fact for `≥ 2`-element parts is `remove_from_part` above. -/
lemma erase_singleton {x : SetOrd}
    (hx : x ∈ part b S) (h0 : (part b S).ncard = 1) : S \ {x} = part (!b) S := by
  have hpb : part b S = {x} := by
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h0
    rw [ha] at hx ⊢
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
  ext y
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyS, hyx⟩
    have hynb : y ∉ part b S := by rw [hpb]; simpa using hyx
    have hu : y ∈ part b S ∪ part (!b) S := by rw [parts_union]; exact hyS
    exact hu.resolve_left hynb
  · intro hy
    refine ⟨hy.1, ?_⟩
    rintro rfl
    exact (Set.disjoint_left.1 parts_disjoint hx) hy

/-- `Finset`-level `remove_from_part`: erasing an element of `partFin b S`
shrinks that side by exactly that element and leaves the other side alone. -/
lemma erase_partFin {S : Finset SetOrd} {x : SetOrd}
    (hS2 : 2 ≤ S.card) (hx : x ∈ partFin b S) (hcard : 2 ≤ (partFin b S).card) :
    partFin b (S.erase x) = (partFin b S).erase x ∧
      partFin (!b) (S.erase x) = partFin (!b) S := by
  have hxSet : x ∈ part b S := by
    rw [← coe_partFin]; exact_mod_cast hx
  obtain ⟨h1, h2⟩ :=
    remove_from_part (by rwa [Set.ncard_coe_finset]) hxSet
      (by rw [← card_partFin]; exact hcard)
  refine ⟨Finset.coe_injective ?_, Finset.coe_injective ?_⟩
  <;> simp_all only [coe_partFin, Finset.coe_erase]

/-- `Finset`-level `erase_singleton`. -/
lemma erase_singleton_fin {S : Finset SetOrd} {x : SetOrd}
    (hx : x ∈ partFin b S) (h0 : (partFin b S).card = 1) :
    S.erase x = partFin (!b) S := by
  apply Finset.coe_injective
  simp only [Finset.coe_erase, coe_partFin]
  exact erase_singleton (by rw [← coe_partFin]; exact_mod_cast hx)
    (by rw [← card_partFin]; exact h0)

/-- Erasing one element from a part with `≥ 2` elements leaves it nonempty. -/
lemma partFin_erase_nonempty {S : Finset SetOrd} {x : Set Ordinal}
    (hx : x ∈ partFin b S) (h2 : 2 ≤ (partFin b S).card) :
    ((partFin b S).erase x).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega

/-- Erasing one element from `S` leaves `≥ 2` elements, given the erased-from
part alone already has `≥ 2` and the other part is nonempty. -/
lemma card_erase_ge_two {S : Finset SetOrd} {x : Set Ordinal}
    (hb2 : 2 ≤ (partFin b S).card) (hLne : (partFin ⊥ S).Nonempty)
    (hRne : (partFin ⊤ S).Nonempty) (hxS : x ∈ S) : 2 ≤ (S.erase x).card := by
  rw [Finset.card_erase_of_mem hxS]
  have hsum := partFin_card_add S
  have hL1 := Finset.card_pos.2 hLne
  have hR1 := Finset.card_pos.2 hRne
  cases b <;> omega

/-- **Imported fact (I1)**: `dels` on `toTree S` matches one-element erasure on
`S` itself. With `lv_toTree`/`isDegenerate_toTree_iff` this completes the
tree/`Finset SetOrd` bridge. -/
lemma mem_dels_toTree_iff :
    ∀ S : Finset SetOrd, 2 ≤ S.card → ∀ Y : SteppingUp.Trees.Tree,
      Y ∈ BinaryTree.dels (toTree S) ↔ ∃ x ∈ S, Y = toTree (S.erase x) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS2 Y
    have hLne : (partFin ⊥ S).Nonempty := partFin_nonempty (b := ⊥) hS2
    have hRne : (partFin ⊤ S).Nonempty := partFin_nonempty (b := ⊤) hS2
    have hlvL : (toTree (partFin ⊥ S)).numLeaves = (partFin ⊥ S).card :=
      lv_toTree (Finset.card_pos.2 hLne)
    have hlvR : (toTree (partFin ⊤ S)).numLeaves = (partFin ⊤ S).card :=
      lv_toTree (Finset.card_pos.2 hRne)
    have htoTreeS : toTree S =
        SteppingUp.Trees.Tree.node (toTree (partFin ⊥ S)) (toTree (partFin ⊤ S)) :=
      toTree_eq_node hS2
    have hdels : BinaryTree.dels (toTree S) =
        (if (toTree (partFin ⊥ S)).numLeaves = 1 then [toTree (partFin ⊤ S)]
         else (BinaryTree.dels (toTree (partFin ⊥ S))).map
           (SteppingUp.Trees.Tree.node · (toTree (partFin ⊤ S)))) ++
        (if (toTree (partFin ⊤ S)).numLeaves = 1 then [toTree (partFin ⊥ S)]
         else (BinaryTree.dels (toTree (partFin ⊤ S))).map
           (SteppingUp.Trees.Tree.node (toTree (partFin ⊥ S)))) := by
      rw [htoTreeS]; exact SteppingUp.Trees.dels_eq_ite _ _
    rw [hdels, hlvL, hlvR, List.mem_append]
    have hunion : ∀ b : Bool, partFin b S ∪ partFin (!b) S = S := by
      rintro ⟨_|_⟩ <;> simp [partFin_union S, Finset.union_comm]
    have hbranch : ∀ b : Bool, Y ∈ (if (partFin b S).card = 1 then [toTree (partFin (!b) S)]
        else (BinaryTree.dels (toTree (partFin b S))).map
          (bif b then (SteppingUp.Trees.Tree.node (toTree (partFin (!b) S)) ·)
           else (SteppingUp.Trees.Tree.node · (toTree (partFin (!b) S))))) →
        ∃ x ∈ S, Y = toTree (S.erase x) := by
      intro b hmem
      split_ifs at hmem with hb
      · rw [List.mem_singleton] at hmem
        obtain ⟨x0, hx0eq⟩ := Finset.card_eq_one.1 hb
        have hx0 : x0 ∈ partFin b S := hx0eq ▸ Finset.mem_singleton_self x0
        have hxS : x0 ∈ S := hunion b ▸ Finset.mem_union_left _ hx0
        refine ⟨x0, hxS, ?_⟩
        rw [erase_singleton_fin hx0 hb, hmem]
      · have hb' : 2 ≤ (partFin b S).card := by
          have := Finset.card_pos.2 (partFin_nonempty (b := b) hS2); omega
        rw [List.mem_map] at hmem
        obtain ⟨Y0, hY0mem, rfl⟩ := hmem
        obtain ⟨x, hxb, rfl⟩ := (ih (partFin b S) (partFin_ssub hS2) hb' Y0).1 hY0mem
        have hxS : x ∈ S := hunion b ▸ Finset.mem_union_left _ hxb
        have hxne : ((partFin b S).erase x).Nonempty := partFin_erase_nonempty hxb hb'
        have hScard2 : 2 ≤ (S.erase x).card := card_erase_ge_two hb' hLne hRne hxS
        obtain ⟨hpL, hpR⟩ := erase_partFin hS2 hxb hb'
        exact ⟨x, hxS, by
          rw [toTree_eq_node hScard2]; cases b <;> rw [← hpL, ← hpR] <;> rfl⟩
    -- Conversely, an erasure inside `partFin b S` lands in the `b`-th half of
    -- `dels`. Same shape as `hbranch`, run backwards.
    have hback : ∀ (b : Bool) (x : Set Ordinal), x ∈ partFin b S →
        toTree (S.erase x) ∈ (if (partFin b S).card = 1 then [toTree (partFin (!b) S)]
          else (BinaryTree.dels (toTree (partFin b S))).map
            (bif b then (SteppingUp.Trees.Tree.node (toTree (partFin (!b) S)) ·)
             else (SteppingUp.Trees.Tree.node · (toTree (partFin (!b) S))))) := by
      intro b x hxb
      by_cases hb : (partFin b S).card = 1
      · rw [erase_singleton_fin hxb hb, if_pos hb]
        exact List.mem_singleton_self _
      · have hb' : 2 ≤ (partFin b S).card := by
          have := Finset.card_pos.2 (partFin_nonempty (b := b) hS2); omega
        have hxS : x ∈ S := hunion b ▸ Finset.mem_union_left _ hxb
        have hScard2 : 2 ≤ (S.erase x).card := card_erase_ge_two hb' hLne hRne hxS
        obtain ⟨hpL, hpR⟩ := erase_partFin hS2 hxb hb'
        rw [if_neg hb, List.mem_map]
        refine ⟨toTree ((partFin b S).erase x),
          (ih (partFin b S) (partFin_ssub hS2) hb' _).2 ⟨x, hxb, rfl⟩, ?_⟩
        rw [toTree_eq_node hScard2]
        cases b <;> rw [← hpL, ← hpR] <;> rfl
    constructor
    · rintro (hmem | hmem) <;> exact hbranch _ hmem
    · rintro ⟨x, hxS, rfl⟩
      rw [← partFin_union S, Finset.mem_union] at hxS
      exact hxS.imp (hback ⊥ x) (hback ⊤ x)

end «toTree: the Finset SetOrd → Tree correspondence»

end SteppingUp.Encoding
