/-
  Unlabelled binary trees, their `core` (the paper's `def:core`),
  one-leaf deletions `dels` (`def:dels`), and the `signature` invariant
  `κ` (`σ` of `def:kappa`, before folding).
-/
import Mathlib.Data.Tree.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SteppingUp.Trees
open BinaryTree

section «Binary trees»

/-- Unlabelled binary trees. -/
abbrev Tree := BinaryTree Unit
/-- Match pattern that discards the `Unit` value. -/
@[match_pattern] abbrev Tree.node : Tree → Tree → Tree := BinaryTree.node ()

@[inherit_doc] scoped prefix:arg "#" => BinaryTree.numLeaves

@[simp]
lemma nil_iff_numLeaves_one : #T = 1 ↔ T = .nil := by
  rcases T with _ | ⟨_, l, r⟩ <;> simp
  linarith only [l.numLeaves_pos, r.numLeaves_pos]

@[simp]
lemma nil_nil_iff_numleaves_two : #T = 2 ↔ T = .nil △ .nil := by
  rcases T with _ | ⟨_, _ | ⟨_, ll, lr⟩, _ | ⟨_, rl, rr⟩⟩ <;> simp
  <;> (try have := rl.numLeaves_pos; have := rr.numLeaves_pos)
  <;> (try have := ll.numLeaves_pos; have := lr.numLeaves_pos)
  <;>  omega

/-! ### A kernel-reducible enumeration

The obvious enumerator, Mathlib's `BinaryTree.treesOfNumNodesEq`, is defined
by well-founded recursion, and the kernel cannot reduce those at all, so a
`decide` over it is impossible however small the check. `treeLevels` builds
the same trees bottom-up and is structurally recursive on its argument, so
the kernel does reduce it. `mem_treesL` below is what lets the finite checks
at `r = 3, 4` be discharged by `decide` rather than by compiled evaluation --
which is what keeps the development free of any reflection axiom. -/

/-- All trees on `1, …, n` leaves, level by level: `treeLevels n` has length
`n`, and its `i`-th entry lists the trees on `i + 1` leaves. -/
def treeLevels : ℕ → List (List Tree)
  | 0 => []
  | (n + 1) =>
      let prev := treeLevels n
      let next : List Tree :=
        if n = 0 then [.nil]
        else (List.range n).flatMap fun i =>
          (prev.getD i []).flatMap fun L =>
            (prev.getD (n - 1 - i) []).map (L △ ·)
      prev ++ [next]

/-- The trees on `p` leaves. -/
def treesL (p : ℕ) : List Tree := (treeLevels p).getD (p - 1) []

@[simp] lemma treeLevels_length : ∀ n, (treeLevels n).length = n
  | 0 => rfl
  | (n + 1) => by simp [treeLevels, treeLevels_length n]

/-- Each level extends the previous, so entries below the old length agree. -/
lemma treeLevels_getD_succ {i n : ℕ} (h : i < n) :
    (treeLevels (n + 1)).getD i [] = (treeLevels n).getD i [] := by
  simp only [treeLevels]
  rw [List.getD_append]
  simpa using h

lemma treeLevels_getD_of_le {i m n : ℕ} (hmn : m ≤ n := by omega) (hi : i < m := by omega) :
    (treeLevels n).getD i [] = (treeLevels m).getD i [] := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · rw [treeLevels_getD_succ (by omega), ih (by omega)]
    · have : m = n + 1 := by omega
      subst this; rfl

/-- `treesL` is complete: every tree appears at its own leaf count. This is
the direction the checks need, being applied to an arbitrary tree of the
given size. -/
lemma mem_treesL (T : Tree) : T ∈ treesL #T := by
  induction T with
  | nil => decide
  | node _ L R ihL ihR =>
    have hL := L.numLeaves_pos
    have hR := R.numLeaves_pos
    have hlv : #(L △ R) = #L + #R := rfl
    have hpos : 0 < #L + #R := by omega
    unfold treesL
    rw [hlv]
    obtain ⟨n, hn⟩ : ∃ n, #L + #R = n + 1 := ⟨#L + #R - 1, by omega⟩
    rw [hn]
    simp only [Nat.add_sub_cancel, treeLevels]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [treeLevels_length, Nat.sub_self, List.getD_cons_zero]
    rw [if_neg (by omega)]
    refine List.mem_flatMap.2 ⟨#L - 1, List.mem_range.2 (by omega), ?_⟩
    refine List.mem_flatMap.2 ⟨L, ?_, ?_⟩
    · rw [treeLevels_getD_of_le (m := #L)]
      exact ihL
    · refine List.mem_map.2 ⟨R, ?_, rfl⟩
      have : n - 1 - (#L - 1) = #R - 1 := by omega
      rw [this, treeLevels_getD_of_le (m := #R)]
      exact ihR

end «Binary trees»

section «Core of a tree»

/-- The core of a tree (`def:core`): `none` for degenerate trees, otherwise
the two subtrees flanking the "genuine" branch point. -/
@[simp]
def _root_.BinaryTree.core : Tree → Option (Tree × Tree)
  | .nil => none
  | .node .nil T | .node T .nil => T.core
  | .node L R => some (L, R)

@[simp]
lemma core_of_nil_node : core (.nil △ T) = core T := by
  simp

@[simp]
lemma core_of_node_nil : core (T △ .nil) = core T := by
  cases T <;> simp

/-- Every tree with at most `3` leaves lacks a core. -/
lemma core_isNone_of_lv_le_three {T : Tree} (h : #T ≤ 3) : T.core = none := by
  induction T using BinaryTree.unitRecOn with
  | base => rfl
  | ind l r ihl ihr =>
    cases l using BinaryTree.unitRecOn with
    | base => exact ihr (by simp at h ⊢; omega)
    | ind ll lr =>
      simp only [numLeaves] at h ihl
      cases r using BinaryTree.unitRecOn with
      | base => exact ihl (by simp at h ⊢; omega)
      | ind rl rr =>
        have := ll.numLeaves_pos
        have := lr.numLeaves_pos
        have := rl.numLeaves_pos
        have := rr.numLeaves_pos
        simp only [numLeaves] at h
        omega

/-- Restates `core`'s `.isNone`'s `node` case in the old if-then-else shape (via
`lv` instead of matching directly on `.nil`), so that proofs written against
that shape keep working unchanged after `rw [core_isNone_eq_ite]; rw [...]`. -/
lemma core_isNone_eq_ite (L R : Tree) : (core (L △ R)).isNone =
    if #L = 1 then R.core.isNone
    else if #R = 1 then L.core.isNone
    else false := by
  rcases L with _ | ⟨_, Ll, Lr⟩ <;> rcases R with _ | ⟨_, Rl, Rr⟩ <;>
    (try have h1 := Ll.numLeaves_pos) <;> (try have h2 := Lr.numLeaves_pos) <;>
    (try have h3 := Rl.numLeaves_pos) <;> (try have h4 := Rr.numLeaves_pos) <;>
    split_ifs <;> simp_all <;> omega

/-- Restates `core`'s `node` case in the old if-then-else shape (via `lv`
instead of matching directly on `.nil`), so that proofs written against that
shape keep working unchanged after `rw [core_eq_ite]; rw [...]` is replaced by
`rw [core_eq_ite]; rw [...]`. -/
lemma core_eq_ite (L R : Tree) : core (L △ R) =
    if #L ≥ 2 ∧ #R ≥ 2 then some (L, R)
    else if #L = 1 ∧ #R ≥ 2 then R.core
    else if #L ≥ 2 ∧ #R = 1 then L.core
    else none := by
  rcases L with _ | ⟨_, Ll, Lr⟩ <;> rcases R with _ | ⟨_, Rl, Rr⟩ <;>
    (try have h1 := Ll.numLeaves_pos) <;> (try have h2 := Lr.numLeaves_pos) <;>
    (try have h3 := Rl.numLeaves_pos) <;> (try have h4 := Rr.numLeaves_pos) <;>
    split_ifs <;> simp_all  <;> omega


/-- Converse of `two_le_of_core`: a node whose two sides both have `≥ 2`
leaves *is* its own core, so in particular it is proper. -/
lemma core_node_of_two_le {L R : Tree} (hL : 2 ≤ #L := by omega) (hR : 2 ≤ #R := by omega) :
    core (L △ R) = some (L, R) := by
  rw [core_eq_ite, if_pos ⟨hL, hR⟩]

/-- The two trees returned by `core` always have `≥ 2` leaves each. -/
lemma two_le_of_core {T L R : Tree} (h : core T = some (L, R)) :
    2 ≤ #L ∧ 2 ≤ #R := by
  induction T using BinaryTree.unitRecOn with
  | base => simp at h
  | ind A B ihA ihB =>
    rw [core_eq_ite] at h
    split_ifs at h
    · injections h; subst_vars; tauto
    · exact ihB h
    · exact ihA h

/-- The core always fits within the tree: `L.numLeaves + R.numLeaves ≤ T.numLeaves`
whenever `core T = some (L, R)`. -/
lemma le_lv_of_core {T L R : Tree} (h : core T = some (L, R)) :
    #L + #R ≤ #T := by
  induction T using BinaryTree.unitRecOn with
  | base => simp at h
  | ind A B ihA ihB =>
    rw [core_eq_ite] at h; simp only [numLeaves]
    split_ifs at h
    · injections h; subst_vars; tauto
    · have := ihB h; omega
    · have := ihA h; omega

end «Core of a tree»

section «Leaf deletions»

/-- One-leaf deletions (`def:dels`). -/
@[simp]
def _root_.BinaryTree.dels : Tree → List Tree
  | .nil => []
  | .node L R =>
    (match L with |.nil => [R] | _ => (dels L).map (· △ R)) ++
    (match R with |.nil => [L] | _ => (dels R).map (.node L))

@[inherit_doc]
scoped prefix:arg (priority:=10001) "∂" => dels


/-- Restates `dels`'s `node` case in the if-then-else shape. -/
lemma dels_eq_ite (L R : Tree) : ∂(L △ R) =
    (if #L = 1 then [R] else  (· △ R) <$> ∂L) ++
    (if #R = 1 then [L] else (L △ ·) <$> ∂ R) := by
  rcases L with _ | ⟨_, Ll, Lr⟩ <;> rcases R with _ | ⟨_, Rl, Rr⟩ <;>
    simp only [dels] <;>
    (try have h1 := Ll.numLeaves_pos) <;> (try have h2 := Lr.numLeaves_pos) <;>
    (try have h3 := Rl.numLeaves_pos) <;> (try have h4 := Rr.numLeaves_pos) <;>
    split_ifs <;> simp_all <;> omega

/-- Deleting inside a node's left side, when that side is not a lone leaf. -/
lemma mem_dels_node_left {L R L' : Tree} (h : L' ∈ ∂L) :
    L' △ R ∈ ∂(L △ R) := by
  rcases L <;> simp at h ⊢ ; tauto


/-- Mirror of `mem_dels_node_left`, deleting inside the right side. -/
lemma mem_dels_node_right {L R R' : Tree} (h : R' ∈ ∂ R) :
    L △ R' ∈ ∂(L △ R) := by
  rcases R <;> simp at h ⊢ ; tauto

/-- Every tree in `∂T` has `|T| - 1` leaves (`def:dels`). -/
lemma lv_of_mem_dels {T Y : Tree} (h : Y ∈ ∂T) : #Y + 1 = #T := by
  induction T using BinaryTree.unitRecOn generalizing Y with
  | base => simp at h
  | ind L R ihL ihR =>
    rcases L with rfl | ⟨_, Ll, Lr⟩ <;> rcases R with rfl | ⟨_, Rl, Rr⟩ <;>
      simp only [dels, List.mem_append, List.mem_singleton, List.mem_map] at h ihL ihR
    · rcases h with rfl | rfl <;> simp
    · rcases h with rfl | ⟨y, hy, rfl⟩
      · simp; omega
      · have := ihR hy; simp only [numLeaves] at ⊢ this; omega
    · rcases h with ⟨y, hy, rfl⟩ | rfl
      · have := ihL hy; simp only [numLeaves, Nat.add_right_cancel_iff] at ⊢ this; omega
      · simp
    · rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · have := ihL hy; simp only [numLeaves] at ⊢ this; omega
      · have := ihR hy; simp only [numLeaves] at ⊢ this; omega


/-- The list `∂T` has one entry per leaf of `T`, deleted in turn (`def:dels`). -/
lemma length_dels {T : Tree} (h : 2 ≤ #T) : (∂T).length = #T := by
  induction T using BinaryTree.unitRecOn with
  | base => simp only [numLeaves] at h ⊢; omega
  | ind L R ihL ihR =>
    have hL1 := L.numLeaves_pos
    have hR1 := R.numLeaves_pos
    rw [dels_eq_ite, List.length_append]
    by_cases #L = 1 <;> by_cases #R = 1
    · simp_all
    · simp_all [ihR (by omega)]
    · simp_all [ihL (by omega)]
    · simp_all [ihL (by omega), ihR (by omega)]

/-- A tree with `≥ 2` leaves has at least one deletion (`length_dels`). -/
lemma dels_ne_nil {T : Tree} (h : 2 ≤ #T) : ∂T ≠ [] := by
  intro hnil
  have hlen := length_dels h
  simp only [hnil, List.length_nil] at hlen
  omega

/-- A tree with `≥ 2` leaves has a deletion, necessarily of one fewer leaf
(`dels_ne_nil` + `lv_of_mem_dels`). -/
lemma exists_mem_dels {T : Tree} (h : 2 ≤ #T) : ∃ T' ∈ ∂T, #T' + 1 = #T := by
  cases hd : ∂T with
  | nil => exact absurd hd (dels_ne_nil h)
  | cons T' _ =>
    have hmem : T' ∈ ∂T := hd ▸ List.mem_cons_self
    exact ⟨T', by simp, lv_of_mem_dels hmem⟩

/-- Degeneracy is hereditary (the remark after `def:deg-set`): degeneracy of
a tree (`core.isNone`) is closed under one-leaf deletion. -/
lemma core_isNone_of_mem_dels {T Y : Tree} (hdegenerate : T.core.isNone)
    (hY : Y ∈ ∂T) :
    core Y = none := by
  induction T using BinaryTree.unitRecOn generalizing Y with
  | base => simp [dels] at hY
  | ind L R ihL ihR =>
    rw [dels_eq_ite, List.mem_append] at hY
    by_cases hL : #L = 1
    · simp at hL
      subst L
      simp only [numLeaves, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
        nil_iff_numLeaves_one, List.map_eq_map, core,
        Option.isNone_iff_eq_none] at hY hdegenerate
      rcases hY with rfl | hright
      · exact hdegenerate
      · by_cases hR : #R = 1
        · simp_all
        · simp_all
          obtain ⟨_, h, rfl⟩ := hright
          simp [ihR h]
    · cases R using BinaryTree.unitRecOn with
      | base =>
        simp only [hL, ↓reduceIte, List.map_eq_map, List.mem_map, numLeaves,
          List.mem_cons, List.not_mem_nil, or_false] at hY
        rw [core_of_node_nil] at hdegenerate
        rcases hY with ⟨L', hL'mem, rfl⟩ | rfl
        · simp
          exact ihL hdegenerate hL'mem
        · simpa using hdegenerate
      | ind _ _ => cases L using BinaryTree.unitRecOn <;> simp_all

end «Leaf deletions»

section «Signatures and the invariant κ»

/-- The signature `(a, b, λ, ρ, δ)` of a tree with a core: the leaf-counts of
the core's two sides, whether each side's own core is `none`, and the `δ`-bit
recording peel depth zero. -/
structure Signature where
  /-- Leaf-count of the core's left side. -/
  a : ℕ
  /-- Leaf-count of the core's right side. -/
  b : ℕ
  /-- Whether the left side is itself degenerate, i.e. `(core L).isNone`. -/
  lam : Bool
  /-- Whether the right side is itself degenerate, i.e. `(core R).isNone`. -/
  rho : Bool
  /-- Peel depth zero: `a + b = #T`. -/
  delta : Bool
  deriving DecidableEq

/-- A *folded* signature is one whose `a`/`b` have been capped by `fold`, as
the paper's `σ` always is: it lands in `{2,3,4,5}²`, whereas
`BinaryTree.signature` below carries the raw leaf-counts. The two are the
same type, so this is a statement of intent rather than something the
elaborator checks; `tau` is the map that establishes it. -/
abbrev CoreSignature := Signature

/-- The invariant `κ` (`σ` of `def:kappa`, before folding):
`(L.numLeaves, R.numLeaves, (core L).isNone, (core R).isNone)` when
`core T = some (L, R)`, else `none`. -/
def _root_.BinaryTree.signature (T : Tree) : Option Signature :=
  T.core >>= fun (L, R) ↦
    (⟨#L, #R, L.core.isNone, R.core.isNone, decide (#L + #R = #T)⟩ : Signature)

/-- `signature`'s `δ` coordinate is not free: it records peel depth zero, so
it is determined by the other two coordinates and `#T`. -/
lemma delta_of_signature {T : Tree} {a b : ℕ} {lam rho d : Bool}
    (h : signature T = some ⟨a, b, lam, rho, d⟩) : d = decide (a + b = #T) := by
  unfold signature at h
  cases hcore : T.core with
  | none => simp_all
  | some _ =>
    rw [hcore] at h
    injections h; simp_all

/-- `lem:kappa-basic`, first half: both sides of the core have
`≥ 2` leaves. -/
lemma two_le_of_kappa {T : Tree} {a b : ℕ} {lam rho d : Bool}
    (h : signature T = some ⟨a, b, lam, rho, d⟩) : 2 ≤ a ∧ 2 ≤ b := by
  unfold signature at h
  cases hcore : T.core with
  | none => simp [hcore] at h
  | some _ =>
    rw [hcore] at h; injections h; subst_eqs
    exact two_le_of_core hcore

/-- `lem:kappa-basic`, second half: a core side with `≤ 3` leaves
is automatically a degenerate tree. -/
lemma core_isNone_of_kappa_le_three {T : Tree} {a b : ℕ} {lam rho d : Bool}
    (h : signature T = some ⟨a, b, lam, rho, d⟩) :
    (a ≤ 3 → lam = true) ∧ (b ≤ 3 → rho = true) := by
  unfold signature at h
  cases hcore : T.core with
  | none => simp [hcore] at h
  | some _ =>
    rw [hcore] at h
    injections h
    subst_eqs
    constructor <;> intro h <;>  simp [core_isNone_of_lv_le_three h]

end «Signatures and the invariant κ»

end SteppingUp.Trees
