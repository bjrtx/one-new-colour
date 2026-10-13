/-
  `sec:main` of the paper: the colouring table `c★` (`tab:cstar`)
  and the main theorem
  (`cStar_isValidAt`).

  The rest of the development lives in the imported modules: `Colouring/Basic.lean`
  (`sec:classes` and `sec:validity`: the colouring framework, folded classes
  and the one-tree constraint), `Colouring/Stabilisation.lean` (`sec:stab`),
  and `Colouring/R4.lean` (`sec:r4`, `r = 3, 4`).
-/
import Mathlib.Tactic.ITauto
import SteppingUpLemma.Colouring.Stabilisation
import SteppingUpLemma.Colouring.R4

namespace SteppingUp.Trees
open BinaryTree

section «The table and the main theorem»

/-- The colour table `c★`: `69` classes, of which `25`
receive `cN`. Classes not listed return `c0` as a junk value; they are not
realised as `τ_r(T)` for any tree `T` (`SteppingUp.Trees.Counts.card_realisedClasses`). -/
def cStar : CoreSignature → EtaColour
  | ⟨2, 2, ⊤, ⊤, ⊥⟩ => .cN
  | ⟨2, 3, ⊤, ⊤, ⊥⟩ => .c0
  | ⟨2, 4, ⊤, ⊥, ⊥⟩ => .c1
  | ⟨2, 4, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨2, 4, ⊤, ⊥, ⊤⟩ => .c0
  | ⟨2, 4, ⊤, ⊤, ⊤⟩ => .cN
  | ⟨2, 5, ⊤, ⊥, ⊥⟩ => .cN
  | ⟨2, 5, ⊤, ⊤, ⊥⟩ => .c0
  | ⟨2, 5, ⊤, ⊥, ⊤⟩ => .c0
  | ⟨2, 5, ⊤, ⊤, ⊤⟩ => .cN
  | ⟨3, 2, ⊤, ⊤, ⊥⟩ => .c0
  | ⟨3, 3, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨3, 3, ⊤, ⊤, ⊤⟩ => .c1
  | ⟨3, 4, ⊤, ⊥, ⊥⟩ => .cN
  | ⟨3, 4, ⊤, ⊤, ⊥⟩ => .cN
  | ⟨3, 4, ⊤, ⊥, ⊤⟩ => .cN
  | ⟨3, 4, ⊤, ⊤, ⊤⟩ => .c0
  | ⟨3, 5, ⊤, ⊥, ⊥⟩ => .c1
  | ⟨3, 5, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨3, 5, ⊤, ⊥, ⊤⟩ => .c1
  | ⟨3, 5, ⊤, ⊤, ⊤⟩ => .c1
  | ⟨4, 2, ⊥, ⊤, ⊥⟩ => .cN
  | ⟨4, 2, ⊤, ⊤, ⊥⟩ => .cN
  | ⟨4, 2, ⊥, ⊤, ⊤⟩ => .c0
  | ⟨4, 2, ⊤, ⊤, ⊤⟩ => .cN
  | ⟨4, 3, ⊥, ⊤, ⊥⟩ => .c1
  | ⟨4, 3, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨4, 3, ⊥, ⊤, ⊤⟩ => .c1
  | ⟨4, 3, ⊤, ⊤, ⊤⟩ => .c1
  | ⟨4, 4, ⊥, ⊥, ⊥⟩ => .c1
  | ⟨4, 4, ⊥, ⊤, ⊥⟩ => .c1
  | ⟨4, 4, ⊤, ⊥, ⊥⟩ => .c1
  | ⟨4, 4, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨4, 4, ⊥, ⊥, ⊤⟩ => .c0
  | ⟨4, 4, ⊥, ⊤, ⊤⟩ => .c0
  | ⟨4, 4, ⊤, ⊥, ⊤⟩ => .c0
  | ⟨4, 4, ⊤, ⊤, ⊤⟩ => .c0
  | ⟨4, 5, ⊥, ⊥, ⊥⟩ => .cN
  | ⟨4, 5, ⊥, ⊤, ⊥⟩ => .cN
  | ⟨4, 5, ⊤, ⊥, ⊥⟩ => .cN
  | ⟨4, 5, ⊤, ⊤, ⊥⟩ => .cN
  | ⟨4, 5, ⊥, ⊥, ⊤⟩ => .c0
  | ⟨4, 5, ⊥, ⊤, ⊤⟩ => .cN
  | ⟨4, 5, ⊤, ⊥, ⊤⟩ => .c0
  | ⟨4, 5, ⊤, ⊤, ⊤⟩ => .cN
  | ⟨5, 2, ⊥, ⊤, ⊥⟩ => .c1
  | ⟨5, 2, ⊤, ⊤, ⊥⟩ => .c0
  | ⟨5, 2, ⊥, ⊤, ⊤⟩ => .c0
  | ⟨5, 2, ⊤, ⊤, ⊤⟩ => .cN
  | ⟨5, 3, ⊥, ⊤, ⊥⟩ => .cN
  | ⟨5, 3, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨5, 3, ⊥, ⊤, ⊤⟩ => .cN
  | ⟨5, 3, ⊤, ⊤, ⊤⟩ => .c1
  | ⟨5, 4, ⊥, ⊥, ⊥⟩ => .cN
  | ⟨5, 4, ⊥, ⊤, ⊥⟩ => .cN
  | ⟨5, 4, ⊤, ⊥, ⊥⟩ => .cN
  | ⟨5, 4, ⊤, ⊤, ⊥⟩ => .cN
  | ⟨5, 4, ⊥, ⊥, ⊤⟩ => .cN
  | ⟨5, 4, ⊥, ⊤, ⊤⟩ => .c0
  | ⟨5, 4, ⊤, ⊥, ⊤⟩ => .cN
  | ⟨5, 4, ⊤, ⊤, ⊤⟩ => .c0
  | ⟨5, 5, ⊥, ⊥, ⊥⟩ => .c1
  | ⟨5, 5, ⊥, ⊤, ⊥⟩ => .c1
  | ⟨5, 5, ⊤, ⊥, ⊥⟩ => .c1
  | ⟨5, 5, ⊤, ⊤, ⊥⟩ => .c1
  | ⟨5, 5, ⊥, ⊥, ⊤⟩ => .c1
  | ⟨5, 5, ⊥, ⊤, ⊤⟩ => .c1
  | ⟨5, 5, ⊤, ⊥, ⊤⟩ => .c1
  | ⟨5, 5, ⊤, ⊤, ⊤⟩ => .c1
  | _ => .c0

/-- The colouring of trees induced by `c★`, the paper's `c★ ∘ σ`. -/
abbrev cStarTree : Tree → EtaColour := treeColour cStar

/-! ### Closing `cStar_isValidAt_of_le_14` via a bounded, decidable check

Rather than brute-forcing over every tree with up to `16` leaves (still far
too many), this reuses `classReduction`'s own genuinely-`r`-independent
formula (`reduction_to_profiles`): every `(sClasses T, hasDegenerateDel T)` is
`classReduction` applied to `L`, `R`'s *reduced* data, and — since
`exists_le_eleven_of_mem_profSet` already bounds any tree's full profile
data by a representative with `≤ 11` leaves — the space of possible
`(foldP, foldPm1, testP, profL)` tuples is itself finite and small
(`profileData` below), independent of `r` entirely. Checking `c★`'s
validity over the *finite product* of that data (`79 × 79 × 3 = 18723`
combinations) is then a single decidable computation. -/

/-- Tags "which profile shape" a `(foldP, foldPm1, testP)` triple pairs
with: `(0, 0, ⊥, ⊥)` for the degenerate tree profile, `(1, 1, ⊥,
⊥)` for the size-`4` exceptional profile (both sentinels, outside
`allDelta0Classes`'s range `{2,…,5}²`), or a genuine member of
`allDelta0Classes` for a `classProf`-derived profile. This indirection
avoids embedding `Bool × Finset Bool × Option (…)` — whose `DecidableEq`
fails to synthesize once nested inside an outer `Finset`'s element type —
directly in `profileData`; `profileOfTag` recovers the actual profile only
where it is actually needed (fed straight into `classReduction`, never
itself placed inside a `Finset`). -/
def profileOfTag : Signature → Bool × Prof
  | ⟨0, 0, ⊥, ⊥, ⊥⟩ => (⊤, degenerateProf)
  | ⟨1, 1, ⊥, ⊥, ⊥⟩ => (⊥, ⟨⊤, ⊥, some ⟨2, 2, ⊤, ⊤, ⊥⟩⟩)
  | tag => (⊥, classProf tag)

/-- `allDelta0Classes` as a `List`: the `36` well-formed classes with
`δ = ⊥`, enumerated directly rather than by `Finset` product and filter,
so that `profileData` below stays kernel-computable.
`mem_allDelta0ClassesL_iff` identifies the two. -/
def allDelta0ClassesL : List Signature :=
  (([2, 3, 4, 5] ×ˢ [2, 3, 4, 5] ×ˢ [⊤, ⊥] ×ˢ [⊤, ⊥]).map
      fun (a, b, lam, rho) => (⟨a, b, lam, rho, ⊥⟩ : Signature)).filter
    fun c => (!decide (c.a ≤ 3) || c.lam) && (!decide (c.b ≤ 3) || c.rho)

/-- The representative leaf-count standing for `n` in `profileData`.

The closing check reads `n` only through `fold n`, `fold (n - 1)` and
`decide (3 ≤ n)`, and by `fold_pred_of_five_le` those depend, for `n ≥ 5`, on
the parity of `n` alone. So `2, …, 11` collapses to five representatives.
The representative must be the *largest* member of its class, not the
smallest: the check is guarded by `m = 2 ∨ 7 ≤ t1.1 + t2.1 + m`, which is
monotone in `n`, so a smaller representative would verify strictly fewer
instances than the consumers rely on. -/
def repN (n : ℕ) : ℕ := if 5 ≤ n then 10 + (n % 2) else n

/-- The four properties of `repN` the reduction needs: it lies in the
collapsed range, it does not decrease `n` (guard monotonicity), and it leaves
the three quantities the check actually reads unchanged. -/
lemma repN_spec {n : ℕ} (h2 : 2 ≤ n) (h11 : n ≤ 11) :
    repN n ∈ [2, 3, 4, 10, 11] ∧ n ≤ repN n ∧
      fold (repN n) = fold n ∧ fold (repN n - 1) = fold (n - 1) ∧
      decide (3 ≤ repN n) = decide (3 ≤ n) := by
  simp_all! [repN, fold] ; split_ifs <;> omega

/-- `repN` preserves the "exact, or reduced and `≥ 10`" disjunction. -/
lemma repN_or {a n : ℕ} (h : (n ≤ 11 ∧ a = n) ∨ 10 ≤ a) :
    (n ≤ 11 ∧ repN a = n) ∨ 10 ≤ repN a := by
  unfold repN
  rcases h <;> split_ifs <;> omega

/-- The `(n, tag)` pairs the closing check quantifies over: for *any* tree `L`
with `2 ≤ L.numLeaves`, some element matches `L`'s reduced size and profile
(`exists_mem_profileData` below).

`n` is a *representative* leaf count (`repN`), not `L`'s own, but it is still
a genuine leaf count rather than just a fold-image — `profileData_closure`
needs that to state the side condition that keeps the closing check sound. A
class's own `(n, class)` pairing is included only when `n` is large enough to
realise it (`class.a + class.b ≤ n`), and every proper witness pairs with an
`n` genuinely realising that shape. Unlike `class`-pairings, the degenerate
tree profile is realisable at *every* size, and the size-`4` exceptional
profile at exactly `n = 4`.

The leaf-count component
ranges over `repN`'s five representatives rather than all of `2, …, 11`; the
list has `79` entries and no duplicates. -/
def profileData : List (ℕ × Signature) :=
  ([2, 3, 4, 10, 11].map (fun n => (n, (⟨0, 0, ⊥, ⊥, ⊥⟩ : Signature)))) ++
  (([2, 3, 4, 10, 11].flatMap fun n =>
      allDelta0ClassesL.map (n, ·)).filter
    (fun p => decide (p.2.a + p.2.b ≤ p.1))) ++
  [(4, (⟨1, 1, ⊥, ⊥, ⊥⟩ : Signature))]

/-- `profileData` written out as a literal. -/
lemma profileData_lit_eq : profileData =
  [(2,⟨0,0,⊥,⊥,⊥⟩), (3,⟨0,0,⊥,⊥,⊥⟩), (4,⟨0,0,⊥,⊥,⊥⟩),
  (10,⟨0,0,⊥,⊥,⊥⟩), (11,⟨0,0,⊥,⊥,⊥⟩), (4,⟨2,2,⊤,⊤,⊥⟩),
  (10,⟨2,2,⊤,⊤,⊥⟩), (10,⟨2,3,⊤,⊤,⊥⟩), (10,⟨2,4,⊤,⊤,⊥⟩),
  (10,⟨2,4,⊤,⊥,⊥⟩), (10,⟨2,5,⊤,⊤,⊥⟩), (10,⟨2,5,⊤,⊥,⊥⟩),
  (10,⟨3,2,⊤,⊤,⊥⟩), (10,⟨3,3,⊤,⊤,⊥⟩), (10,⟨3,4,⊤,⊤,⊥⟩),
  (10,⟨3,4,⊤,⊥,⊥⟩), (10,⟨3,5,⊤,⊤,⊥⟩), (10,⟨3,5,⊤,⊥,⊥⟩),
  (10,⟨4,2,⊤,⊤,⊥⟩), (10,⟨4,2,⊥,⊤,⊥⟩), (10,⟨4,3,⊤,⊤,⊥⟩),
  (10,⟨4,3,⊥,⊤,⊥⟩), (10,⟨4,4,⊤,⊤,⊥⟩), (10,⟨4,4,⊤,⊥,⊥⟩),
  (10,⟨4,4,⊥,⊤,⊥⟩), (10,⟨4,4,⊥,⊥,⊥⟩), (10,⟨4,5,⊤,⊤,⊥⟩),
  (10,⟨4,5,⊤,⊥,⊥⟩), (10,⟨4,5,⊥,⊤,⊥⟩), (10,⟨4,5,⊥,⊥,⊥⟩),
  (10,⟨5,2,⊤,⊤,⊥⟩), (10,⟨5,2,⊥,⊤,⊥⟩), (10,⟨5,3,⊤,⊤,⊥⟩),
  (10,⟨5,3,⊥,⊤,⊥⟩), (10,⟨5,4,⊤,⊤,⊥⟩), (10,⟨5,4,⊤,⊥,⊥⟩),
  (10,⟨5,4,⊥,⊤,⊥⟩), (10,⟨5,4,⊥,⊥,⊥⟩), (10,⟨5,5,⊤,⊤,⊥⟩),
  (10,⟨5,5,⊤,⊥,⊥⟩), (10,⟨5,5,⊥,⊤,⊥⟩), (10,⟨5,5,⊥,⊥,⊥⟩),
  (11,⟨2,2,⊤,⊤,⊥⟩), (11,⟨2,3,⊤,⊤,⊥⟩), (11,⟨2,4,⊤,⊤,⊥⟩),
  (11,⟨2,4,⊤,⊥,⊥⟩), (11,⟨2,5,⊤,⊤,⊥⟩), (11,⟨2,5,⊤,⊥,⊥⟩),
  (11,⟨3,2,⊤,⊤,⊥⟩), (11,⟨3,3,⊤,⊤,⊥⟩), (11,⟨3,4,⊤,⊤,⊥⟩),
  (11,⟨3,4,⊤,⊥,⊥⟩), (11,⟨3,5,⊤,⊤,⊥⟩), (11,⟨3,5,⊤,⊥,⊥⟩),
  (11,⟨4,2,⊤,⊤,⊥⟩), (11,⟨4,2,⊥,⊤,⊥⟩), (11,⟨4,3,⊤,⊤,⊥⟩),
  (11,⟨4,3,⊥,⊤,⊥⟩), (11,⟨4,4,⊤,⊤,⊥⟩), (11,⟨4,4,⊤,⊥,⊥⟩),
  (11,⟨4,4,⊥,⊤,⊥⟩), (11,⟨4,4,⊥,⊥,⊥⟩), (11,⟨4,5,⊤,⊤,⊥⟩),
  (11,⟨4,5,⊤,⊥,⊥⟩), (11,⟨4,5,⊥,⊤,⊥⟩), (11,⟨4,5,⊥,⊥,⊥⟩),
  (11,⟨5,2,⊤,⊤,⊥⟩), (11,⟨5,2,⊥,⊤,⊥⟩), (11,⟨5,3,⊤,⊤,⊥⟩),
  (11,⟨5,3,⊥,⊤,⊥⟩), (11,⟨5,4,⊤,⊤,⊥⟩), (11,⟨5,4,⊤,⊥,⊥⟩),
  (11,⟨5,4,⊥,⊤,⊥⟩), (11,⟨5,4,⊥,⊥,⊥⟩), (11,⟨5,5,⊤,⊤,⊥⟩),
  (11,⟨5,5,⊤,⊥,⊥⟩), (11,⟨5,5,⊥,⊤,⊥⟩), (11,⟨5,5,⊥,⊥,⊥⟩),
  (4,⟨1,1,⊥,⊥,⊥⟩)] := by decide


lemma mem_allDelta0ClassesL_iff {c : Signature} :
    c ∈ allDelta0ClassesL ↔ c ∈ allDelta0Classes := by
  obtain ⟨ca, cb, clam, crho, cdelta⟩ := c
  rw [mem_allDelta0Classes_iff]
  unfold allDelta0ClassesL IsClass
  simp only [List.mem_filter, List.mem_map, List.mem_product, Prod.exists, List.mem_cons,
    List.not_mem_nil, or_false, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton, Signature.mk.injEq]
  constructor
  · rintro ⟨⟨a, b, lam, rho, ⟨ha, hb, hlam, hrho⟩, rfl, rfl, rfl, rfl, rfl⟩, h1, h2⟩
    exact ⟨⟨by itauto, by itauto, by itauto, by itauto⟩, rfl⟩
  · rintro ⟨⟨ha, hb, h1, h2⟩, rfl⟩
    exact ⟨⟨ca, cb, clam, crho, ⟨by itauto, by itauto, by cases clam <;> tauto,
      by cases crho <;> tauto⟩, rfl, rfl, rfl, rfl, rfl⟩, by tauto, by tauto⟩

/-- Every tree's reduced `(size, profile)` data matches `profileOfTag` at
some element of `profileData`, either *exactly* (`t.1 = T.numLeaves`, when
`T.numLeaves ≤ 11` already) or with `10 ≤ t.1` (when `T.numLeaves` needed reducing, via
`exists_le_eleven_of_mem_profSet`'s own "already small, or reduced and
`≥ 10`" guarantee) — this disjunction is what lets
`cStar_isValidAt_of_le_14` establish the reachability side condition needed
by `profileData_closure`. Splits on `prof T`'s three possible shapes: the
degenerate tree profile (any size), the size-`4` exceptional profile (`E =
{⊤}` alone, the exception in `lem:del-analysis`'s first part), or a `classProf`-derived profile
(size `≥ 5`, via `prof_eq_classProf`). -/
private lemma exists_mem_profileData {T : Tree} (hL2 : 2 ≤ #T) :
    ∃ t ∈ profileData, ((#T ≤ 11 ∧ t.1 = #T) ∨ 10 ≤ t.1) ∧
      fold t.1 = fold (#T) ∧ fold (t.1 - 1) = fold (#T - 1) ∧
      decide (3 ≤ t.1) = decide (3 ≤ #T) ∧
      (profileOfTag t.2).1 = T.core.isNone ∧ (profileOfTag t.2).2 = prof T := by
  have hprofL : prof T ∈ ProfSet (#T) := ⟨T, rfl, rfl⟩
  obtain ⟨a', ha'2, ha'11, ha'or, ⟨L', hL'lv, hL'prof⟩, hfoldA1, hfoldA2, htestA⟩ :=
    exists_le_eleven_of_mem_profSet (#T) hL2 (prof T) hprofL
  have htestA' : decide (3 ≤ a') = decide (3 ≤ #T) := by rw [decide_eq_decide]; exact htestA
  -- Collapse `a'` to its representative; everything the check reads is preserved.
  obtain ⟨hrmem, hrle, hrfold1, hrfold2, hrtest⟩ := repN_spec ha'2 ha'11
  have hfoldA1' : fold (repN a') = fold (#T) := by rw [hrfold1]; exact hfoldA1
  have hfoldA2' : fold (repN a' - 1) = fold (#T - 1) := by rw [hrfold2]; exact hfoldA2
  have htestA'' : decide (3 ≤ repN a') = decide (3 ≤ #T) := by rw [hrtest]; exact htestA'
  have ha'or' := repN_or ha'or

  rcases hdegenerate : L'.core with _ | ⟨A, B⟩
  · have hdegL : T.core = none :=
      (core_isNone_eq_of_prof_eq hL'prof).mp hdegenerate
    refine ⟨(repN a', (⟨0, 0, ⊥, ⊥, ⊥⟩ : Signature)), ?_, ha'or', hfoldA1', hfoldA2',
      htestA'', ?_, ?_⟩
    · exact List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨repN a', hrmem, rfl⟩))))
    · rw [hdegL]; rfl
    · change (profileOfTag (⟨0, 0, ⊥, ⊥, ⊥⟩ : Signature)).2 = prof T
      rw [show (profileOfTag (⟨0, 0, ⊥, ⊥, ⊥⟩ : Signature)).2 = degenerateProf from rfl,
        ← hL'prof, prof_eq_degenerate_profile (by omega) hdegenerate]
  · have hdegLisNone : T.core.isNone = ⊥ := by
      by_contra!
      have := core_isNone_eq_of_prof_eq hL'prof
      simp_all
    have hk : L'.signature =
        some (⟨#A, #B, A.core.isNone, B.core.isNone, decide (#A + #B = #L')⟩ : Signature) := by
      unfold signature; rw [hdegenerate]; rfl
    have hAB2 := two_le_of_core hdegenerate
    by_cases ha'4 : a' = 4
    · -- the size-`4` exceptional profile: `L'` is forced to be `fourLeaves`.
      obtain ⟨hA2, hB2⟩ : #A = 2 ∧ #B = 2 := by
        have := le_lv_of_core hdegenerate; omega
      have hL'eq : L' = fourLeaves := by
        rw [eq_node_of_core_of_lv_eq hdegenerate (by omega), nil_nil_iff_numleaves_two.mp hA2,
          nil_nil_iff_numleaves_two.mp hB2]
        rfl
      subst ha'4
      refine ⟨(4, (⟨1, 1, ⊥, ⊥, ⊥⟩ : Signature)), ?_, ha'or, hfoldA1, hfoldA2,
        htestA', ?_, ?_⟩
      · exact List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
      · rw [hdegLisNone]; rfl
      · change (profileOfTag (⟨1, 1, ⊥, ⊥, ⊥⟩ : Signature)).2 = prof T
        rw [show (profileOfTag (⟨1, 1, ⊥, ⊥, ⊥⟩ : Signature)).2 =
              (⟨⊤, ⊥, some (⟨2, 2, ⊤, ⊤, ⊥⟩ : CoreSignature)⟩ : Prof) from rfl,
          ← hL'prof, hL'eq]
        rfl
    · have hlv4 : ¬ #L' ≤ 3 :=
        fun h ↦ by simp [core_isNone_of_lv_le_three h] at hdegenerate
      have ha'5 : 5 ≤ a' := by rw [hL'lv] at hlv4; omega
      have hmem :
          (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature) ∈
            allDelta0Classes := by
        rw [mem_allDelta0Classes_iff]
        exact ⟨⟨fold_mem_of_two_le hAB2.1, fold_mem_of_two_le hAB2.2,
          (core_isNone_of_kappa_le_three hk).1 ∘ fold_le_three_iff.mp,
          (core_isNone_of_kappa_le_three hk).2 ∘ fold_le_three_iff.mp⟩, rfl⟩
      have hfoldA := fold_mem_of_two_le hAB2.1
      have htagne1 : (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature) ≠
          (⟨(0 : ℕ), (0 : ℕ), ⊥, ⊥, ⊥⟩ : Signature) := by
        intro h; simp only [Signature.mk.injEq] at h; simp_all
      have htagne2 : (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature) ≠
          (⟨(1 : ℕ), (1 : ℕ), ⊥, ⊥, ⊥⟩ : Signature) := by
        intro h; simp only [Signature.mk.injEq] at h; simp_all
      have hface : fold (#A) + fold (#B) ≤ a' := by
        have h1 := fold_le_self (x := #A); have h2 := fold_le_self (x := #B)
        have h3 := le_lv_of_core hdegenerate
        omega
      refine ⟨(repN a', (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature)),
        ?_, ha'or', hfoldA1', hfoldA2', htestA'', ?_, ?_⟩
      · refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
        refine List.mem_filter.2 ⟨?_, by simp; omega⟩
        exact List.mem_flatMap.2 ⟨repN a', hrmem,
          List.mem_map.2 ⟨_, mem_allDelta0ClassesL_iff.2 hmem, rfl⟩⟩
      · simp_all [profileOfTag]
      · change (profileOfTag
            (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature)).2 = prof T
        rw [show (profileOfTag
              (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature)).2 =
              classProf (⟨fold (#A), fold (#B), A.core.isNone, B.core.isNone, ⊥⟩ : Signature) by
            simp_all [profileOfTag],
          ← hL'prof]
        exact (prof_eq_classProf (by rw [hL'lv]; omega) (by rw [hdegenerate]; rfl) hk).symm

/-- `classReduction`'s first component with `++`/`[]` in place of `∪`/`∅`.

Same elements, but no `Quot`: `Finset` is `Multiset` is `Quotient (List _)`,
and reducing `Finset.union` and `Finset.image` in the kernel means reducing
`Quot.lift` and a `DecidableEq` dedup at every step, and that cost compounds
with the size of the sets being combined. Over the whole table the list form
takes the kernel 64s where the `Finset` form took 245s.

A separate definition rather than a retyping of `classReduction`: that is
consumed a dozen times over in `Colouring/Basic` and `Colouring/Stabilisation`
(`reduction_to_profiles`, `classReduction_eq_of_degenerateE`, the
`mem_cSetLe14` helpers), all of which would need reproving for no gain. It
lives in this module, downstream of those, so that iterating on it rebuilds
only this file. -/
def classReductionL
    (foldP foldPm1 : ℕ) (testP : Bool) (foldQ foldQm1 : ℕ) (testQ : Bool) (m : ℕ)
    (degL degR : Bool) (profL profR : Prof) : List CoreSignature :=
  (if 1 ≤ m then [(⟨foldP, foldQ, degL, degR, decide (m = 1)⟩ : Signature)] else []) ++
    (if testP then
      ((if profL.anyNone then [(⟨foldPm1, foldQ, ⊤, degR, decide (m = 0)⟩ : Signature)] else []) ++
       (if profL.anySome then [(⟨foldPm1, foldQ, ⊥, degR, decide (m = 0)⟩ : Signature)] else []))
     else profR.cls.toList) ++
    (if testQ then
      ((if profR.anyNone then [(⟨foldP, foldQm1, degL, ⊤, decide (m = 0)⟩ : Signature)] else []) ++
       (if profR.anySome then [(⟨foldP, foldQm1, degL, ⊥, decide (m = 0)⟩ : Signature)] else []))
     else profL.cls.toList)

/-- The bridge: the list form carries exactly `classReduction`'s first
component. -/
lemma classReductionL_toFinset (foldP foldPm1 : ℕ) (testP : Bool)
    (foldQ foldQm1 : ℕ) (testQ : Bool) (m : ℕ) (degL degR : Bool) (profL profR : Prof) :
    (classReductionL foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL profR).toFinset
      = (classReduction foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL profR).1 := by
  ext x
  unfold classReductionL classReduction
  cases profL.cls <;> cases profR.cls <;> split_ifs <;> simp_all <;> itauto

/-- `classReduction`'s image under `c★`, as a list-derived `Finset`. -/
lemma closure_image (foldP foldPm1 : ℕ) (testP : Bool)
    (foldQ foldQm1 : ℕ) (testQ : Bool) (m : ℕ) (degL degR : Bool) (profL profR : Prof) :
    (classReduction foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL profR).1.image cStar
      = ((classReductionL foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL profR).map
          cStar).toFinset := by
  rw [← classReductionL_toFinset]
  ext x
  simp


/-! ### A colour summary the kernel can afford

`sClasses`' image under `c★` is asked only two questions: does it have two
distinct colours, and does it contain `cN`. Answering them by `map`, `dedup`
and `length` builds two intermediate lists per triple and compares colours
pairwise. Three booleans answer the same questions without allocating, and
over the closure check that is worth about a third of the kernel's time. -/

/-- Which of the three colours occur in `l`'s image under `c★`. Structural
rather than a `foldl`, because the bridge lemmas below are proved by
induction on `l`. -/
def bits : List CoreSignature → Bool × Bool × Bool
  | [] => (false, false, false)
  | c :: t =>
      let b := bits t
      match cStar c with
      | .c0 => (true, b.2.1, b.2.2)
      | .c1 => (b.1, true, b.2.2)
      | .cN => (b.1, b.2.1, true)

lemma bits_c0 (l : List CoreSignature) : (bits l).1 = true ↔ EtaColour.c0 ∈ l.map cStar := by
  induction l with
  | nil => simp [bits]
  | cons c t ih => cases h : cStar c <;> simp [bits, h, ih]

lemma bits_c1 (l : List CoreSignature) : (bits l).2.1 = true ↔ EtaColour.c1 ∈ l.map cStar := by
  induction l with
  | nil => simp [bits]
  | cons c t ih => cases h : cStar c <;> simp [bits, h, ih]

lemma bits_cN (l : List CoreSignature) : (bits l).2.2 = true ↔ EtaColour.cN ∈ l.map cStar := by
  induction l with
  | nil => simp [bits]
  | cons c t ih => cases h : cStar c <;> simp [bits, h, ih]

/-- Two distinct colours present means the deduplicated image has at least two. -/
lemma two_le_dedup {l : List EtaColour} {x y : EtaColour}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) : 2 ≤ l.dedup.length := by
  have hx' : x ∈ l.dedup := List.mem_dedup.2 hx
  have hy' : y ∈ l.dedup := List.mem_dedup.2 hy
  have hsub : ({x, y} : Finset EtaColour) ⊆ l.dedup.toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simpa using ‹_ ∈ l.dedup›
  have hcard : 2 ≤ l.dedup.toFinset.card :=
    calc 2 = ({x, y} : Finset EtaColour).card := (Finset.card_pair hxy).symm
      _ ≤ _ := Finset.card_le_card hsub
  calc 2 ≤ l.dedup.toFinset.card := hcard
    _ = l.dedup.dedup.length := List.card_toFinset _
    _ = l.dedup.length := by rw [List.dedup_idem]

/-- The summary form implies the check as `profileData_closure` states it. -/
lemma closure_of_bits {l : List CoreSignature} {ad : Bool}
    (h : ((((bits l).1 && (bits l).2.1) || ((bits l).1 && (bits l).2.2) ||
            ((bits l).2.1 && (bits l).2.2)) || ((bits l).2.2 && ad)) = true) :
    2 ≤ (l.map cStar).dedup.length ∨ (EtaColour.cN ∈ l.map cStar ∧ ad = true) := by
  rcases Bool.or_eq_true_iff.1 h with htwo | hn
  · left
    rcases Bool.or_eq_true_iff.1 htwo with h1 | h1
    · rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
      · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h2
        exact two_le_dedup ((bits_c0 l).1 ha) ((bits_c1 l).1 hb) (by decide)
      · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h2
        exact two_le_dedup ((bits_c0 l).1 ha) ((bits_cN l).1 hb) (by decide)
    · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h1
      exact two_le_dedup ((bits_c1 l).1 ha) ((bits_cN l).1 hb) (by decide)
  · obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 hn
    exact Or.inr ⟨(bits_cN l).1 ha, hb⟩

/-! ### The check, split as thm:stab splits it

`classReductionL` consults a side's folded class only on that side's `= 2`
branch; with both sides `≥ 3` it reads no more than the two `E`-booleans.
So the `78` entries of `profileData` with `n ≥ 3` collapse to the `10` below,
and the enumeration drops from `79 × 79 × 3` to about `800` triples. This is
the Lean counterpart of thm:stab's "both `|L|, |R| ≥ 3`" case. -/

/-- The closure check as a `Bool`, on exactly the data it reads. -/
def closureCheck (fP fPm : ℕ) (tP : Bool) (fQ fQm : ℕ) (tQ : Bool) (m : ℕ)
    (dL dR : Bool) (pL pR : Prof) : Bool :=
  let l := classReductionL fP fPm tP fQ fQm tQ m dL dR pL pR
  ((((bits l).1 && (bits l).2.1) || ((bits l).1 && (bits l).2.2) ||
      ((bits l).2.1 && (bits l).2.2)) ||
    ((bits l).2.2 && (classReduction fP fPm tP fQ fQm tQ m dL dR pL pR).2))

/-- The check at a pair of `profileData` entries. -/
def closureAt (t1 t2 : ℕ × Signature) (m : ℕ) : Bool :=
  closureCheck (fold t1.1) (fold (t1.1 - 1)) (decide (3 ≤ t1.1))
    (fold t2.1) (fold (t2.1 - 1)) (decide (3 ≤ t2.1)) m
    (profileOfTag t1.2).1 (profileOfTag t2.2).1
    (profileOfTag t1.2).2 (profileOfTag t2.2).2

/-- With both sides `≥ 3`, the check ignores both folded classes. -/
lemma closureCheck_of_test (fP fPm fQ fQm m : ℕ) (dL dR : Bool) (pL pR pL' pR' : Prof)
    (hL1 : pL.anyNone = pL'.anyNone) (hL2 : pL.anySome = pL'.anySome)
    (hR1 : pR.anyNone = pR'.anyNone) (hR2 : pR.anySome = pR'.anySome) :
    closureCheck fP fPm true fQ fQm true m dL dR pL pR
      = closureCheck fP fPm true fQ fQm true m dL dR pL' pR' := by
  unfold closureCheck classReductionL classReduction
  simp [hL1, hL2, hR1, hR2]

/-- One entry per value of the data the `≥ 3` branch reads. -/
def profileDataReps : List (ℕ × Signature) :=
  [(3, ⟨0, 0, ⊥, ⊥, ⊥⟩), (4, ⟨0, 0, ⊥, ⊥, ⊥⟩), (10, ⟨0, 0, ⊥, ⊥, ⊥⟩),
   (11, ⟨0, 0, ⊥, ⊥, ⊥⟩), (4, ⟨2, 2, ⊤, ⊤, ⊥⟩), (10, ⟨2, 2, ⊤, ⊤, ⊥⟩),
   (10, ⟨2, 4, ⊤, ⊥, ⊥⟩), (11, ⟨2, 2, ⊤, ⊤, ⊥⟩), (11, ⟨2, 4, ⊤, ⊥, ⊥⟩),
   (4, ⟨1, 1, ⊥, ⊥, ⊥⟩)]

/-- The single entry with `n = 2`, where the other side's class is read. -/
def profileDataSmall : List (ℕ × Signature) := [(2, ⟨0, 0, ⊥, ⊥, ⊥⟩)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma closure_big :
    ∀ t1 ∈ profileDataReps, ∀ t2 ∈ profileDataReps, ∀ m ∈ [0, 1, 2],
      (m = 2 ∨ 7 ≤ t1.1 + t2.1 + m) → closureAt t1 t2 m = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma closure_left2 :
    ∀ t1 ∈ profileDataSmall, ∀ t2 ∈ profileData, ∀ m ∈ [0, 1, 2],
      (m = 2 ∨ 7 ≤ t1.1 + t2.1 + m) → closureAt t1 t2 m = true := by
  rw [profileData_lit_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma closure_right2 :
    ∀ t1 ∈ profileData, ∀ t2 ∈ profileDataSmall, ∀ m ∈ [0, 1, 2],
      (m = 2 ∨ 7 ≤ t1.1 + t2.1 + m) → closureAt t1 t2 m = true := by
  rw [profileData_lit_eq]
  decide +kernel

/-- Every `profileData` entry with `n ≥ 3` is matched by a representative,
with the same size and the same data the `≥ 3` branch reads. -/
private lemma reps_cover :
    ∀ t ∈ profileData, decide (3 ≤ t.1) = true →
      ∃ r ∈ profileDataReps, r.1 = t.1 ∧
        (profileOfTag r.2).1 = (profileOfTag t.2).1 ∧
        (profileOfTag r.2).2.anyNone = (profileOfTag t.2).2.anyNone ∧
        (profileOfTag r.2).2.anySome = (profileOfTag t.2).2.anySome := by
  rw [profileData_lit_eq]
  decide

/-- Entries are of size `2` or at least `3`. -/
private lemma small_or_big :
    ∀ t ∈ profileData, t ∈ profileDataSmall ∨ decide (3 ≤ t.1) = true := by
  rw [profileData_lit_eq]
  decide

set_option maxRecDepth 1000000 in
/-- The check over all of `profileData`, assembled from the three branches:
both sides `≥ 3` (via representatives), or one side `= 2`. -/
private lemma profileData_closureL :
    ∀ t1 ∈ profileData, ∀ t2 ∈ profileData, ∀ m ∈ [0, 1, 2],
      (m = 2 ∨ 7 ≤ t1.1 + t2.1 + m) → closureAt t1 t2 m = true := by
  intro t1 h1 t2 h2 m hm hg
  rcases small_or_big t1 h1 with hs1 | hb1
  · exact closure_left2 t1 hs1 t2 h2 m hm hg
  rcases small_or_big t2 h2 with hs2 | hb2
  · exact closure_right2 t1 h1 t2 hs2 m hm hg
  obtain ⟨r1, hr1mem, hr1sz, hr1d, hr1n, hr1s⟩ := reps_cover t1 h1 hb1
  obtain ⟨r2, hr2mem, hr2sz, hr2d, hr2n, hr2s⟩ := reps_cover t2 h2 hb2
  have key : closureAt t1 t2 m = closureAt r1 r2 m := by
    unfold closureAt
    rw [hr1sz, hr2sz, hr1d, hr2d, hb1, hb2]
    exact (closureCheck_of_test _ _ _ _ _ _ _ _ _ _ _ hr1n hr1s hr2n hr2s).symm
  rw [key]
  exact closure_big r1 hr1mem r2 hr2mem m hm (by rw [hr1sz, hr2sz]; exact hg)

/-- The actual decidable check: `c★` validates `classReduction`'s output for
every `(t1, t2, m)` drawn from `profileData × profileData × {0, 1, 2}`,
*provided* the triple is actually reachable from some genuine level-`r`
proper tree (`r ≥ 5`): either `m = 2` (unconstrained — the "far from `T`'s own
core" branch, reachable by taking `r` as large as needed), or `m < 2`, which
pins `m` down *exactly* to `T`'s own peel amount, forcing `7 ≤ t1.1 + t2.1 +
m` (`r = t1.1 + t2.1 + m - 2 ≥ 5`). Without this side condition the check is
unsound: `profileData` deliberately over-generates `(n, class)` pairings
that are individually realisable but not *jointly* compatible with every
`m`, and `c★` is not required to (and does not) validate those spurious
combinations.

Checked by the kernel, not by compiled evaluation, which took two changes.
The check is stated over `profileData` but run over the literal it is equal
to: against the generator the kernel re-reduces it inside the nested
quantifier and the cost grows faster than the number of pairs, whereas
against the literal it is linear in them. And it runs over `classReductionL`
rather than `classReduction`, trading `Finset` for `List` and so `Quot` for
nothing; that is the larger of the two savings, 245s of kernel time down to
64s.

`decide +kernel`, not plain `decide`. The latter reduces the check twice ---
once in the elaborator to confirm it is `true`, then again in the kernel when
type-checking the emitted `of_decide_eq_true` --- and only the kernel pass
earns the absence of a reflection axiom, so the elaborator's is waste. It was
most of this declaration: 64.7s of elaboration against 3.05s, with the kernel
unmoved at around 75s either way. The axioms are unchanged: `propext`,
`Classical.choice`, `Quot.sound`. -/
private lemma profileData_closure :
    ∀ t1 ∈ profileData, ∀ t2 ∈ profileData, ∀ m ∈ [0, 1, 2],
      (m = 2 ∨ 7 ≤ t1.1 + t2.1 + m) →
      2 ≤ ((classReduction (fold t1.1) (fold (t1.1 - 1)) (decide (3 ≤ t1.1))
              (fold t2.1) (fold (t2.1 - 1)) (decide (3 ≤ t2.1)) m
              (profileOfTag t1.2).1 (profileOfTag t2.2).1
              (profileOfTag t1.2).2 (profileOfTag t2.2).2).1.image cStar).card ∨
        (EtaColour.cN ∈ (classReduction (fold t1.1) (fold (t1.1 - 1)) (decide (3 ≤ t1.1))
              (fold t2.1) (fold (t2.1 - 1)) (decide (3 ≤ t2.1)) m
              (profileOfTag t1.2).1 (profileOfTag t2.2).1
              (profileOfTag t1.2).2 (profileOfTag t2.2).2).1.image cStar ∧
          (classReduction (fold t1.1) (fold (t1.1 - 1)) (decide (3 ≤ t1.1))
              (fold t2.1) (fold (t2.1 - 1)) (decide (3 ≤ t2.1)) m
              (profileOfTag t1.2).1 (profileOfTag t2.2).1
              (profileOfTag t1.2).2 (profileOfTag t2.2).2).2 = ⊤) := by
  intro t1 h1 t2 h2 m hm hg
  have h := profileData_closureL t1 h1 t2 h2 m hm hg
  rw [closure_image, List.card_toFinset, List.mem_toFinset]
  exact closure_of_bits h

/-- `[CHECK]`: `c★` is valid at every level `5 ≤ r ≤ 14`, sharpened from
`≤ 22`. Rather than brute-forcing over
every tree with up to `16` leaves, this reduces `L`, `R`'s data to
`profileData` (`exists_mem_profileData`) and closes with a single bounded
`decide` (`profileData_closure`) — genuinely the same content as
checking the `621` constraints of `𝒞_{≤14}` (`lem:B`), just organised
around `classReduction`'s own finite input space instead of `CSet`'s
tree-indexed one. -/
lemma cStar_isValidAt_of_le_14 : ∀ r, 5 ≤ r → r ≤ 14 → IsValidAt cStarTree r := by
  intro r hr _hr14
  rw [isValidAt_treeColour_iff]
  rintro p ⟨T, hXlv, hXdegenerate, rfl⟩
  rcases hcx : T.core with _ | ⟨L, R⟩
  · simp [hcx] at hXdegenerate
  have hL2 : 2 ≤ #L := (two_le_of_core hcx).1
  have hR2 : 2 ≤ #R := (two_le_of_core hcx).2
  have hab_le : #L + #R ≤ #T := le_lv_of_core hcx
  have hkey := reduction_to_profiles r T L R hcx hXlv hXdegenerate
  obtain ⟨t1, ht1mem, ht1or, ht1a, ht1b, ht1c, ht1deg, ht1prof⟩ := exists_mem_profileData hL2
  obtain ⟨t2, ht2mem, ht2or, ht2a, ht2b, ht2c, ht2deg, ht2prof⟩ := exists_mem_profileData hR2
  have hmrange : min (r + 2 - #L - #R) 2 ∈ ({0, 1, 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hreach : min (r + 2 - #L - #R) 2 = 2 ∨
      7 ≤ t1.1 + t2.1 + min (r + 2 - #L - #R) 2 := by
    by_cases hm2 : 2 ≤ r + 2 - #L - #R
    · left; omega
    · right; omega
  have := profileData_closure t1 (ht1mem) t2
    (ht2mem) _ (by simpa using hmrange) hreach
  rw [ht1a, ht1b, ht1c, ht1deg, ht1prof, ht2a, ht2b, ht2c, ht2deg, ht2prof, hkey] at this
  exact this

/-- `thm:main`: `c★` is valid at every level `r ≥ 5`. -/
theorem cStar_isValidAt : ∀ r, 5 ≤ r → IsValidAt cStarTree r :=
  isValidAt_of_isValidAt_le_14 cStar cStar_isValidAt_of_le_14

end «The table and the main theorem»

end SteppingUp.Trees
