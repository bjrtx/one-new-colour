/-
  `sec:classes` and `sec:validity` of the paper: the colouring
  problem and its validity condition
  (`IsValidAt`), folded classes (`tau`, `allDelta0Classes`), and the
  constraint a single proper tree imposes (`hasDegenerateDel_iff`, `prof`,
  `reduction_to_profiles`).
-/
import SteppingUpLemma.Tree

namespace SteppingUp.Trees
open BinaryTree

section «The colouring and its validity»

/-- The three colours available: two recycled (`c0`, `c1`) and one new
(`cN`). -/
inductive EtaColour where
  | c0 | c1 | cN
  deriving DecidableEq

/-- `cat(T)`, the paper's `ad(T)` (`def:valid`): some one-leaf deletion of `T` is a
degenerate tree. -/
def hasDegenerateDel (T : Tree) : Bool := (∂T).any (·.core.isNone)

/-- The colours realised by proper one-leaf deletions of `T`
under a colouring `c` of proper `(r + 1)`-trees. -/
def sSet (c : Tree → EtaColour) (T : Tree) : Finset EtaColour :=
  ∂T |>.filter (·.core.isSome) |>.toFinset.image c

/-- Validity at level `r` (`def:valid`): every proper `(r + 2)`-tree
either realises `≥ 2` colours among its proper deletions, or
realises `cN` together with a degenerate tree deletion. -/
def IsValidAt (c : Tree → EtaColour) (r : ℕ) : Prop :=
  ∀ T, #T = r + 2 →  T.core.isSome →
    2 ≤ (sSet c T).card ∨ EtaColour.cN ∈ sSet c T ∧ hasDegenerateDel T

/-- Core of the first part of `lem:del-analysis`:
A proper tree on `≥ 5` leaves has a proper deletion. -/
lemma exists_false_mem_dels {T : Tree} (hp : 5 ≤ #T)
    (hproper : T.core.isSome) :
    ∃ Y ∈ ∂T, Y.core.isSome := by
  cases T using BinaryTree.unitRecOn with
  | base => simp at hp
  | ind A B =>
    have hA1 := A.numLeaves_pos
    have hB1 := B.numLeaves_pos
    by_cases hA : #A = 1
    · simp at hA; subst A
      simp_all
    · by_cases hB : #B = 1
      · simp at hB ; subst B
        simp_all
      · have hA2 : 2 ≤ #A := by omega
        have hB2 : 2 ≤ #B := by omega
        simp only [numLeaves] at hp
        -- Delete from whichever side has `≥ 3` leaves: that side keeps `≥ 2`,
        -- so the new node is its own core (`core_node_of_two_le`).
        by_cases hA3 : 3 ≤ #A
        · obtain ⟨A', hmem, hlv⟩ := exists_mem_dels hA2
          exact ⟨A' △ B, mem_dels_node_left hmem,
            by simp [core_node_of_two_le (L := A') (R := B)]⟩
        · obtain ⟨B', hmem, hlv⟩ := exists_mem_dels hB2
          exact ⟨A △ B', mem_dels_node_right hmem,
            by simp [core_node_of_two_le (L := A) (R := B')]⟩

end «The colouring and its validity»

section «Folded classes»

/-- The fold `\hat{\cdot} : ℕ → {2,3,4,5}` (the hat of `def:kappa`). -/
def fold (x : ℕ) : ℕ := if x < 4 then x else 4 + (x - 4) % 2

/-- A basic property of the fold. -/
@[simp]
lemma fold_eq_two_iff {x : ℕ} : fold x = 2 ↔ x = 2 := by
  unfold fold; split <;> omega

lemma fold_pred_of_five_le {p : ℕ} (hp : 5 ≤ p) :
    (fold p, fold (p - 1)) = if p % 2 = 1 then (5, 4) else (4, 5) := by
  unfold fold
  split_ifs <;> congr <;> omega

/-- A "class" `(a, b, λ, ρ)` is well-formed (an admissible class of `sec:classes`) when
`a, b ∈ {2,3,4,5}` and `a ≤ 3 → λ`, `b ≤ 3 → ρ` (the `ε` coordinate of a
class is unconstrained). -/
def IsClass (a b : ℕ) (lam rho : Bool) : Prop :=
  a ∈ ({2, 3, 4, 5} : Finset ℕ) ∧ b ∈ ({2, 3, 4, 5} : Finset ℕ) ∧
    (a ≤ 3 → lam) ∧ (b ≤ 3 → rho)

/-- The folded class of a proper tree, `σ` of `def:kappa`; `none` on
degenerate trees. -/
def tau (T : Tree) : Option CoreSignature :=
  T.signature.map (fun ⟨a, b, lam, rho, d⟩ ↦ ⟨fold a, fold b, lam, rho, d⟩)

/-- Force `δ := false`. Wrapping a tree in a fresh leaf preserves its core but
adds a leaf, pushing peel depth up by one — so it drives `δ` to `false`
(`tau_wrap`). -/
def eraseDelta (c : CoreSignature) : CoreSignature := { c with delta := false }


@[simp] lemma eraseDelta_idem (c : CoreSignature) :
    eraseDelta (eraseDelta c) = eraseDelta c := rfl

/-- `List.toFinset` commutes with `map`/`image`. -/
private lemma toFinset_map_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext; simp

/-- The `36` well-formed classes with `δ = 0`, enumerated directly. -/
def allDelta0Classes : Finset Signature :=
  ((({2, 3, 4, 5} : Finset ℕ) ×ˢ {2, 3, 4, 5} ×ˢ {true, false} ×ˢ {true, false}).filter
    fun p ↦ (p.1 ≤ 3 → p.2.2.1) ∧ (p.2.1 ≤ 3 → p.2.2.2)).image
    fun p ↦ ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, false⟩

lemma card_allDelta0Classes : allDelta0Classes.card = 36 := by
  decide

/-- The colour a class-valued table `c` assigns to a tree `T`, via `τ`
(`T ↦ c(τ(T))`, the paper's `c ∘ σ` of `def:valid`). -/
def treeColour (c : CoreSignature → EtaColour) (T : Tree) : EtaColour :=
  (tau T).map c |>.getD .c0

end «Folded classes»

section «The constraint imposed by one proper tree»

/-- If `B`'s leaf count is `≠ 1`, a one-leaf-deletion of `A` re-attached to `B`
is a degenerate tree iff `A` has exactly `2` leaves (so the deletion is its
unique `1`-leaf one) and `B` is itself a degenerate tree.

`b` names the side the deletion is re-attached on, so one statement covers both
orientations: at `b = true` the deletion happens in the left child, at
`b = false` in the right. -/
private lemma any_core_isNone_map_node {b : Bool} {A B : Tree} (hB1 : #B ≠ 1) :
    ((∂A).map (fun A' ↦ bif b then A' △ B else B △ A')).any (·.core.isNone) ↔
      #A = 2 ∧ B.core.isNone := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyisDegenerate⟩
    obtain ⟨A', hA'mem : A' ∈ ∂A, rfl⟩ := List.mem_map.mp hy
    have : #A' + 1 = #A := lv_of_mem_dels hA'mem
    cases b <;> cases A' <;> cases B <;> simp_all
  · rintro ⟨hA2, hBdegenerate⟩
    cases b <;> simp_all

/-- `lem:anatomy`, the `cat(T)` consequence: `T`'s core sides
`L, R` give a degenerate tree deletion of `T` exactly when one side has `2`
leaves and the other is a degenerate tree. The full case-by-case description of
`dels(T)` (used to prove `reduction_to_profiles` below) is not separately
stated. -/
lemma hasDegenerateDel_iff {T L R : Tree} (hcore : T.core = some (L, R)) :
    hasDegenerateDel T = true ↔
      (#L = 2 ∧ R.core.isNone) ∨ (#R = 2 ∧ L.core.isNone) := by
  induction T using BinaryTree.unitRecOn with
  | base => simp at hcore
  | ind A B ihA ihB =>
    have hA1 := A.numLeaves_pos
    have hB1 := B.numLeaves_pos
    have := two_le_of_core hcore
    unfold hasDegenerateDel dels
    split
    · -- A = .nil
      have : B ≠ nil := by intro; subst_vars; simp at hcore
      simp_all [hasDegenerateDel]
    · -- A ≠ .nil
      split
      · -- B = .nil
        simp_all [hasDegenerateDel]
      · -- B ≠ .nil
        have hA: #A ≠ 1 := by simpa
        have hB: #B ≠ 1 := by simpa
        have : (A △ B).core = some (A, B) := core_node_of_two_le
        obtain ⟨rfl, rfl⟩ := hcore ▸ this
        rw [List.any_append, Bool.or_eq_true]
        exact or_congr (any_core_isNone_map_node (b := true) hB)
          (any_core_isNone_map_node (b := false) hA)

/-- The extended profile of a tree (`def:prof`). The `E`-coordinate of the
tex — the *set* of `core.isNone`-values among `T`'s one-leaf deletions — is
carried here as the two booleans `anyNone`/`anySome` rather than as a
`Finset Bool`, which is the same information (`E` is a subset of a two-element
type) in a form the kernel can compute with: no `Quot`, and a `DecidableEq`
that synthesises even when `Prof` is nested inside another `Finset`.
`(core T).isNone` itself is dropped, since it is already recoverable as
`(prof T).cls = none`. -/
structure Prof where
  /-- Some one-leaf deletion of the tree is degenerate. -/
  anyNone : Bool
  /-- Some one-leaf deletion of the tree is proper. -/
  anySome : Bool
  /-- The folded `δ = 0` class; `none` for degenerate trees. -/
  cls : Option CoreSignature

/-- The extended profile of a tree: which of `degenerate`/`proper` occur
among its one-leaf deletions, together with its own folded signature. -/
def prof (T : Tree) : Prof :=
  ⟨(∂T).any (·.core.isNone), (∂T).any (·.core.isSome), (tau T).map eraseDelta⟩

/-- The common profile of every degenerate tree with at least two leaves. -/
def degenerateProf : Prof := ⟨true, false, none⟩

/-- The tex's `E`-coordinate in its original `Finset` form: an image over `∂T`
of a function of the degeneracy bit collapses to at most two singletons,
selected by the same two conditions `prof` records as `anyNone`/`anySome`.
`Prof` itself carries only those booleans. -/
lemma image_isNone_eq {α : Type*} [DecidableEq α] (l : List Tree) (g : Bool → α) :
    l.toFinset.image (fun T ↦ g T.core.isNone) =
      (if l.any (·.core.isNone) then {g true} else ∅) ∪
      (if l.any (·.core.isSome) then {g false} else ∅) := by
  ext x
  simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_union, List.any_eq_true]
  constructor
  · rintro ⟨T, hT, rfl⟩
    rcases hc : T.core
    · exact Or.inl (by rw [if_pos ⟨T, hT, by simp [hc]⟩]; simp)
    · exact Or.inr (by rw [if_pos ⟨T, hT, by simp [hc]⟩]; simp)
  · rintro (hx | hx) <;> split_ifs at hx with h <;> simp at hx
    <;> obtain ⟨T, hT, hTc⟩ := h
    <;> exact ⟨T, hT, by subst hx; cases hc : T.core <;> simp_all⟩

/-- The dropped `core.isNone` coordinate is recoverable from `prof`'s
remaining `.2` (`widehat σ`) coordinate alone: it is `none` exactly on
degenerate trees. -/
lemma core_isNone_eq_of_prof_eq {T T' : Tree} (h : prof T = prof T') :
    T.core = none ↔ T'.core = none := by
  rcases hZ : T.core with rfl | _ <;> rcases hZ' :  T'.core with rfl | _
  <;> simp [prof, tau, signature, hZ, hZ', Prof.mk.injEq] at h
  <;> tauto

/-- `S(T)`, class-valued (a table colours classes, as in `def:valid`): the
classes realised by proper one-leaf deletions of `T`, independent
of any particular colouring. `dels`' degenerate tree entries drop out
automatically since `tau` is `none` on them. -/
def sClasses (T : Tree) : Finset CoreSignature :=
  ∂T |>.filterMap tau |>.toFinset

/-- The two notions of `S(T)` agree once a class-valued table `c` is fixed:
`sSet (treeColour c) T` (colours) is the image of `sClasses T`
(classes) under `c`. -/
lemma sSet_eq_image_sClasses (c : CoreSignature → EtaColour) (T : Tree) :
    sSet (treeColour c) T = (sClasses T).image c := by
  have hkey {Y} : Y.core.isSome ↔ ∃ cls, tau Y = some cls := by
    unfold tau signature
    cases Y.core <;> simp
  ext colour
  unfold sSet sClasses treeColour
  simp only [List.mem_toFinset, Finset.mem_image, List.mem_filter, List.mem_filterMap]
  constructor
  · rintro ⟨Y, ⟨_, hYdegenerate⟩, _⟩
    obtain ⟨cls, _⟩ := hkey.mp hYdegenerate
    use! cls, Y; simp_all
  · rintro ⟨_, ⟨Y, _, _⟩, _⟩
    use Y ; simp_all

/-- Attaching `n` leaves above `T` on the right increases `lv` by `n`
and leaves `core` untouched, as long as `T` already has `≥ 2` leaves. -/
@[simp]
def peelN : Nat → Tree → Tree
  | 0, T => T
  | n + 1, T => (peelN n T) △ .nil

@[simp]
lemma lv_peelN {n T} : #(peelN n T) = n + #T := by
  induction n with simp_all [add_right_comm]

@[simp]
lemma core_peelN {n T} : (peelN n T).core = T.core := by
  induction n with simp_all

/-- Wrapping a tree in a fresh leaf keeps its core but adds a leaf, so the
result has peel depth `≥ 1`: its class is the original's with `δ` erased.
(`le_lv_of_core` is what rules out `a + b = #T + 1`.) -/
private lemma tau_wrap {T : Tree} {w : Tree → Tree} (hw : (w T).core = T.core)
    (hwlv : #(w T) = #T + 1) : tau (w T) = (tau T).map eraseDelta := by
  unfold tau signature
  rw [hw, hwlv]
  cases hc : T.core with
  | none => rfl
  | some p =>
    obtain ⟨L, R⟩ := p
    have hδ : decide (#L + #R = #T + 1) = false := by
      have := le_lv_of_core hc
      simp only [decide_eq_false_iff_not]
      omega
    simp [eraseDelta, hδ]

/-- List form of `tau_wrap`: applying a leaf-wrapping to every element of a
list erases `δ` throughout. -/
private lemma filterMap_tau_map_wrap (w : Tree → Tree)
    (hw : ∀ T, (w T).core = T.core) (hwlv : ∀ T, #(w T) = #T + 1) (l : List Tree) :
    (l.map w).filterMap tau = (l.filterMap tau).map eraseDelta := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, tau_wrap (hw a) (hwlv a), ih]
    cases tau a <;> rfl


/-- The anatomy lemma's "peel chain" (item (1)): peeling `T` down towards its
core `(L, R)` either does nothing (`T` already is the core-point) or
contributes exactly the fixed class `(P̂, Q̂, [P + Q = r + 1], u, v)` to
`sClasses T`, on top of whatever `node L R` itself contributes. Proved by
the same induction as `hasDegenerateDel_iff`; unlike a `classReduction`-shaped
statement, this recursion needs no tie between `r` and `T.numLeaves` since both
sides use the *same*, fixed `r` throughout. -/
lemma sClasses_eq_of_core {T L R : Tree} (hcore : T.core = some (L, R)) :
    sClasses T =
      if #T = #L + #R then sClasses (L △ R)
      else {(⟨fold (#L), fold (#R), L.core.isNone, R.core.isNone,
              decide (#L + #R = #T - 1)⟩ : CoreSignature)}
            ∪ (sClasses (L △ R)).image eraseDelta := by
  induction T using BinaryTree.unitRecOn with
  | base => simp at hcore
  | ind A B ihA ihB =>
    have hA1 := A.numLeaves_pos
    have hB1 := B.numLeaves_pos
    by_cases hA : #A = 1
    · -- `A = nil`: the node contributes exactly `tau B` on top of `sClasses B`,
      -- since `core`/`tau` are blind to a `nil` wrapper (`core_of_nil_node`).
      simp only [nil_iff_numLeaves_one] at hA
      subst A
      have hcoreB : B.core = some (L, R) := by simpa using hcore
      have hBge : #L + #R ≤ #B := le_lv_of_core hcoreB
      have hB2 := two_le_of_core hcoreB
      have hB1' : #B ≠ 1 := by omega
      have hleaf1 : #(nil : Tree) = 1 := rfl
      have hdels : ∂(.nil △ B) = [B] ++ (∂B).map (.nil △ ·) := by
        rw [dels_eq_ite, if_pos hleaf1, if_neg hB1']; rfl
      have htauB : tau B = some (⟨fold (#L), fold (#R), L.core.isNone, R.core.isNone,
          decide (#L + #R = #B)⟩ : CoreSignature) := by
        simp [tau, signature, hcoreB]
      have hsplit : sClasses (.nil △ B) =
          {(⟨fold (#L), fold (#R), L.core.isNone,
            R.core.isNone, decide (#L + #R = #B)⟩ : CoreSignature)} ∪
            (sClasses B).image eraseDelta := by
        unfold sClasses
        rw [hdels, List.filterMap_append,
          filterMap_tau_map_wrap (.nil △ ·) (fun _ ↦ core_of_nil_node)
            (fun _ ↦ by simp only [numLeaves]; omega)]
        simp [htauB, toFinset_map_eq_image]
      have hXne : #(.nil △ B) ≠ #L + #R := by simp only [numLeaves]; omega
      have hXsub : #(.nil △ B) - 1 = #B := by simp only [numLeaves]; omega
      rw [hsplit, if_neg hXne, hXsub, ihB hcoreB]
      by_cases hBe : #B = #L + #R
      · rw [if_pos hBe]
      · rw [if_neg hBe, Finset.image_union, Finset.image_singleton, eraseDelta,
          decide_eq_false (by omega : ¬(#L + #R = #B)),
          Finset.image_image, ← Finset.union_assoc, Finset.union_self]
        rfl
    · by_cases hB : #B = 1
      · simp at hB
        subst B
        have hcoreA : A.core = some (L, R) := by simpa using hcore
        have hleaf1 : #(nil : Tree) = 1 := rfl
        have hA1' : #A ≠ 1 := hA
        have hAge : #L + #R ≤ #A := le_lv_of_core hcoreA
        have hdels : ∂(A △ .nil) = (∂A).map (· △ .nil) ++ [A] := by
          conv_lhs => simp [dels]
          aesop
        have htauA : tau A = some (⟨fold (#L), fold (#R),
            L.core.isNone, R.core.isNone, decide (#L + #R = #A)⟩ : CoreSignature) := by
          simp [tau, signature, hcoreA]
        have hsplit : sClasses (A △ .nil) =
            {(⟨fold (#L), fold (#R), L.core.isNone,
              R.core.isNone, decide (#L + #R = #A)⟩ : CoreSignature)} ∪
              (sClasses A).image eraseDelta := by
          unfold sClasses
          rw [hdels, List.filterMap_append,
            filterMap_tau_map_wrap (· △ .nil) (fun _ ↦ core_of_node_nil)
              (fun _ ↦ by simp only [numLeaves]),
            List.toFinset_append,
            show ([A] : List Tree).filterMap (tau) =
              [(⟨fold (#L), fold (#R), L.core.isNone,
                R.core.isNone, decide (#L + #R = #A)⟩ : CoreSignature)] by
            rw [List.filterMap_cons, List.filterMap_nil, htauA]]
          rw [Finset.union_comm]
          simp [toFinset_map_eq_image]
        have hXne : #(A △ .nil) ≠ #L + #R := by
          simp only [numLeaves] at hAge ⊢; omega
        have hXsub : #(A △ .nil) - 1 = #A := by simp only [numLeaves]; omega
        rw [hsplit, if_neg hXne, hXsub, ihA hcoreA]
        by_cases hAe : #A = #L + #R
        · rw [if_pos hAe]
        · rw [if_neg hAe, Finset.image_union, Finset.image_singleton, eraseDelta,
            decide_eq_false (by omega : ¬(#L + #R = #A)),
            Finset.image_image, ← Finset.union_assoc, Finset.union_self]
          rfl
      · have ⟨rfl, rfl⟩ : A = L ∧ B = R := by
          have : (A △ B).core = some (A, B) := by
            conv_lhs => rw [core_eq_ite]
            rw [if_pos ⟨by omega, by omega⟩]
          rw [this] at hcore; simpa using hcore
        simp


/-- If `f a = some (h a)` for every `a ∈ l`, `filterMap f` on `l` never drops
anything, so its `toFinset` is the `image` of `h`. -/
private lemma toFinset_filterMap_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {l : List α} {h : α → β} {f : α → Option β} (hc : ∀ a ∈ l, f a = some (h a)) :
    (l.filterMap f).toFinset = l.toFinset.image h := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons, hc a List.mem_cons_self, List.toFinset_cons,
      ih (hc · <| List.mem_cons_of_mem a ·), List.toFinset_cons,
      Finset.image_insert]

/-- If `f` is constant (`= c`) on a nonempty list `l`, `filterMap f`'s
`toFinset` collapses to `c.toFinset`. -/
private lemma toFinset_filterMap_const {α β : Type*} [DecidableEq β] {l : List α} (hl : l ≠ [])
    {f : α → Option β} {c : Option β} (hc : ∀ a ∈ l, f a = c) :
    (l.filterMap f).toFinset = c.toFinset := by
  cases c with
  | none => simp [List.filterMap_eq_nil_iff.mpr hc]
  | some x =>
    -- `f` is `some x` everywhere on `l`, so `filterMap f` is a constant `map`.
    have hrepl : l.filterMap f = List.replicate l.length x :=
      (List.filterMap_eq_map_iff_forall_eq_some.2 hc).trans (by simp)
    have hlen : l.length ≠ 0 := Nat.ne_zero_of_lt (List.length_pos_of_ne_nil hl)
    rw [hrepl, Option.toFinset_some, List.toFinset_replicate_of_ne_zero hlen]

/-- The anatomy lemma's base case (items (2), (3)): the classes realised by
`node L R` itself (`M = 0`), split on whether each side's leaf-count is
`≥ 3` (giving a class per deletion, mirroring `any_core_isNone_map_node`) or
exactly `2` (giving at most the single class `tau` of the *other* side,
via `core_of_node_nil`/`core_of_nil_node`). -/
private lemma sClasses_node (L R : Tree) (hL2 : 2 ≤ #L) (hR2 : 2 ≤ #R) :
    sClasses (L △ R) =
      (if 3 ≤ #L then
        (∂L).toFinset.image
          (⟨fold (#L - 1), fold (#R), ·.core.isNone, R.core.isNone, true⟩)
       else ((tau R).map eraseDelta).toFinset) ∪
      (if 3 ≤ #R then
        (∂ R).toFinset.image
          (⟨fold (#L), fold (#R - 1), L.core.isNone, ·.core.isNone, true⟩)
       else ((tau L).map eraseDelta).toFinset) := by
  have hdels : ∂(L △ R) =
      (∂L).map (.node · R) ++ (∂ R).map (.node L) := by
    conv_lhs => rw [dels_eq_ite]
    repeat rw [if_neg (by omega)]
    rfl
  unfold sClasses
  rw [hdels, List.filterMap_append, List.toFinset_append]
  congr 1
  · rw [List.filterMap_map]
    by_cases hL3 : 3 ≤ #L
    · rw [if_pos hL3]
      apply toFinset_filterMap_eq_image
      intro L' hL'
      have hL'lv : #L' + 1 = #L := lv_of_mem_dels hL'
      have hcore' : (L' △ R).core = some (L', R) := by
        rw [core_eq_ite, if_pos ⟨by omega, hR2⟩]
      simp [hL'lv.symm, tau, signature, hcore', numLeaves]
    · rw [if_neg hL3]
      have hL2' : #L = 2 := by omega
      have hconst : ∀ L' ∈ ∂L, tau (L' △ R) = (tau R).map eraseDelta := by
        intro L' hL'
        have hL'lv : #L' + 1 = #L := lv_of_mem_dels hL'
        have hL'1 : #L' = 1 := by omega
        rw [nil_iff_numLeaves_one.mp hL'1]
        exact tau_wrap (w := (.nil △ ·)) core_of_nil_node (by simp only [numLeaves]; omega)
      have hLne : ∂L ≠ [] :=
        fun hnil ↦
        have hlen := length_dels hL2
        by rw [hnil] at hlen; simp only [List.length_nil] at hlen; omega
      exact toFinset_filterMap_const hLne hconst
  · rw [List.filterMap_map]
    by_cases hR3 : 3 ≤ #R
    · rw [if_pos hR3]
      apply toFinset_filterMap_eq_image
      intro R' hR'
      have hR'lv : #R = #R' + 1 := (lv_of_mem_dels hR').symm
      have hcore' : core (.node L R') = some (L, R') := by
        rw [core_eq_ite, if_pos ⟨hL2, by omega⟩]
      simp [hR'lv, tau, signature, hcore', numLeaves]
    · rw [if_neg hR3]
      have hR2' : #R = 2 := by omega
      have hconst : ∀ R' ∈ ∂ R, tau (L △ R') = (tau L).map eraseDelta := by
        intro R' hR'
        have hR'lv : #R' + 1 = #R := lv_of_mem_dels hR'
        have hR'1 : #R' = 1 := by omega
        rw [nil_iff_numLeaves_one.mp hR'1]
        exact tau_wrap (w := (· △ .nil)) core_of_node_nil (by simp only [numLeaves])
      have hRne : ∂ R ≠ [] :=
        fun hnil ↦
        have hlen := length_dels hR2; by simp [hnil] at hlen; omega
      exact toFinset_filterMap_const hRne hconst

/-- The concrete transcription of `lem:B`'s formula: item (1) (the
peel-chain class, present iff `1 ≤ m`), item (2) (`L`'s own deletions via
`profL.1` when `foldP ≥ 3`, else the *other* side's own class via
`profR.2`), item (3) symmetrically, and `cat(T)` per `lem:anatomy`
(`hasDegenerateDel_iff`). `degL`/`degR` (`(core L).isNone`/`(core R).isNone`) are
passed separately from `profL`/`profR`, since `prof` no longer bundles them. -/
def classReduction
    (foldP foldPm1 : ℕ) (testP : Bool) (foldQ foldQm1 : ℕ) (testQ : Bool) (m : ℕ)
    (degL degR : Bool) (profL profR : Prof) :
    Finset CoreSignature × Bool :=
  ((if 1 ≤ m then {⟨foldP, foldQ, degL, degR, m = 1⟩} else ∅) ∪
    (if testP then
      ((if profL.anyNone then {⟨foldPm1, foldQ, true, degR, m = 0⟩}
        else ∅) ∪
       (if profL.anySome then {⟨foldPm1, foldQ, false, degR, m = 0⟩}
        else ∅))
     else profR.cls.toFinset) ∪
    (if testQ then
      ((if profR.anyNone then {⟨foldP, foldQm1, degL, true, m = 0⟩}
        else ∅) ∪
       (if profR.anySome then {⟨foldP, foldQm1, degL, false, m = 0⟩}
        else ∅))
     else profL.cls.toFinset),
   (foldP = 2 ∧ degR = true) ∨ (foldQ = 2 ∧ degL = true))

/-- `prof T`'s own class is exactly `tau T` with `δ` erased. This now holds
by `rfl`: `prof` is *defined* as `(tau T).map eraseDelta`. Kept as a named
lemma so call sites can rewrite in either direction without unfolding `prof`. -/
private lemma tau_eq_prof_snd (T : Tree) : (tau T).map eraseDelta = (prof T).cls := rfl

/-- `prof`'s own class already carries `δ = false`, so erasing again is a
no-op. -/
@[simp] private lemma image_eraseDelta_prof (T : Tree) :
    ((prof T).cls).toFinset.image eraseDelta = ((prof T).cls).toFinset := by
  rw [← tau_eq_prof_snd T]
  cases tau T <;> simp

/-- `lem:B` ("reduction to profiles"): `(sClasses T, cat(T))`
for a proper `(r + 2)`-tree `T` with core `(L, R)` is a function of
`(L.numLeaves, R.numLeaves, min M 2, prof L, prof R)` alone, where `M = r + 2 - L.numLeaves - R.numLeaves` —
and, per the explicit formula in the tex, the dependence on `L.numLeaves`/`R.numLeaves`
themselves is only through their folds `(fold (L.numLeaves), fold (L.numLeaves - 1),
3 ≤ L.numLeaves)` (symmetrically for `R`); in particular the witnessing function
`classReduction` is genuinely independent of `r` (this is what
`cSet_subset_cSetLe14` below exploits — stated directly in terms of
`classReduction`, rather than behind an existential, so that its main
branch's insensitivity to `.2.2` (`classReduction_eq_of_degenerateE`) can be used
too). -/
lemma reduction_to_profiles :
    ∀ r T L R, T.core = some (L, R) → #T = r + 2 →
      T.core.isSome ->
      classReduction (fold (#L)) (fold (#L - 1)) (decide (3 ≤ #L))
        (fold (#R)) (fold (#R - 1)) (decide (3 ≤ #R))
        (min (r + 2 - #L - #R) 2) (L.core.isNone) (R.core.isNone)
        (prof L) (prof R) =
        (sClasses T, hasDegenerateDel T) := by
  rintro r T L R hcore hXlv hXdegenerate
  have hL2 : 2 ≤ #L := (two_le_of_core hcore).1
  have hR2 : 2 ≤ #R := (two_le_of_core hcore).2
  have hPQ : #L + #R ≤ r + 2 := hXlv ▸ le_lv_of_core hcore
  have hfoldL2 : fold (#L) = 2 ↔ #L = 2 := fold_eq_two_iff
  have hfoldR2 : fold (#R) = 2 ↔ #R = 2 := fold_eq_two_iff
  have hdegenerate2 : hasDegenerateDel T =
      decide ((fold (#L) = 2 ∧ R.core.isNone = true) ∨
        (fold (#R) = 2 ∧ L.core.isNone = true)) := by
    cases h : hasDegenerateDel T with
    | true =>
      symm; rw [decide_eq_true_iff]
      rcases (hasDegenerateDel_iff hcore).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hfoldL2.mpr h1, h2⟩
      · exact Or.inr ⟨hfoldR2.mpr h1, h2⟩
    | false =>
      symm; rw [decide_eq_false_iff_not]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd ((hasDegenerateDel_iff hcore).mpr (Or.inl ⟨hfoldL2.mp h1, h2⟩)) (by simp [h])
      · exact absurd ((hasDegenerateDel_iff hcore).mpr (Or.inr ⟨hfoldR2.mp h1, h2⟩)) (by simp [h])
  have hSclasses : sClasses T =
      (classReduction (fold (#L)) (fold (#L - 1)) (decide (3 ≤ #L))
        (fold (#R)) (fold (#R - 1)) (decide (3 ≤ #R))
        (min (r + 2 - #L - #R) 2) (L.core.isNone) (R.core.isNone)
        (prof L) (prof R)).1 := by
    rw [sClasses_eq_of_core hcore, sClasses_node L R hL2 hR2,
      tau_eq_prof_snd R, tau_eq_prof_snd L]
    unfold classReduction
    -- normalise `decide (3 ≤ _) = true` to `3 ≤ _`, so that the `split_ifs`
    -- below pairs `classReduction`'s guards with `sClasses_node`'s.
    simp only [decide_eq_true_iff]
    have hsum : #L + #R ≤ #T := le_lv_of_core hcore
    set M := r + 2 - #L - #R with hMdef
    -- `∂`-indexed images become `prof`-indexed ones, uniformly in the `δ` bit.
    have hLimg : ∀ d : Bool, (∂L).toFinset.image
        (⟨fold (#L - 1), fold (#R), ·.core.isNone, R.core.isNone, d⟩) =
        ((if (prof L).anyNone then
            {(⟨fold (#L - 1), fold (#R), true, R.core.isNone, d⟩ : CoreSignature)} else ∅) ∪
         (if (prof L).anySome then
            {(⟨fold (#L - 1), fold (#R), false, R.core.isNone, d⟩ : CoreSignature)}
          else ∅)) := by
      intro d
      exact image_isNone_eq (∂L)
        (fun ε => (⟨fold (#L - 1), fold (#R), ε, R.core.isNone, d⟩ : CoreSignature))
    have hRimg : ∀ d : Bool, (∂ R).toFinset.image
        (⟨fold (#L), fold (#R - 1), L.core.isNone, ·.core.isNone, d⟩) =
        ((if (prof R).anyNone then
            {(⟨fold (#L), fold (#R - 1), L.core.isNone, true, d⟩ : CoreSignature)} else ∅) ∪
         (if (prof R).anySome then
            {(⟨fold (#L), fold (#R - 1), L.core.isNone, false, d⟩ : CoreSignature)}
          else ∅)) := by
      intro d
      exact image_isNone_eq (∂ R)
        (fun ε => (⟨fold (#L), fold (#R - 1), L.core.isNone, ε, d⟩ : CoreSignature))
    by_cases hM0 : #T = #L + #R
    · -- peel depth `0`: `T` *is* its core, so there is no peel-chain class and
      -- every deletion keeps `δ = true = decide (M = 0)`.
      have hm : min M 2 = 0 := by omega
      simp [hM0, hm, hLimg, hRimg]
    · -- peel depth `≥ 1`: the peel-chain class appears, and `eraseDelta` drives
      -- every core-side deletion's `δ` to `false = decide (M = 0)`.
      have hm1 : 1 ≤ min M 2 := by omega
      have hδ : decide (#L + #R = #T - 1) = decide (min M 2 = 1) := by
        simp only [decide_eq_decide]; omega
      have hm0 : decide (min M 2 = 0) = false := by
        simp only [decide_eq_false_iff_not]; omega
      have hM0' : decide (M = 0) = false := by
        simp only [decide_eq_false_iff_not]; omega
      rw [if_neg hM0, hδ, if_pos hm1, Finset.image_union, hLimg, hRimg]
      split_ifs <;>
        simp [eraseDelta, hM0', Finset.insert_comm]
  rw [Prod.mk.injEq]
  exact ⟨hSclasses.symm, hdegenerate2.symm⟩

end «The constraint imposed by one proper tree»

section «Named small trees»

/-- The unique `4`-leaf proper. -/
@[match_pattern] def fourLeaves : Tree := (.nil △ .nil) △ (.nil △ .nil)

/-- A `5`-leaf proper (`fourLeaves` with one leaf refined). -/
def fiveLeavesProper : Tree :=
  ((.nil △ .nil) △ .nil) △ (.nil △ .nil)

end «Named small trees»

end SteppingUp.Trees
