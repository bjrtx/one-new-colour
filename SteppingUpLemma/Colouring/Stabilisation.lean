/-
  `sec:stab` of the paper: the profile sets `Prof(p)` stabilise for `p ≥ 10`
  (`profSet_stabilises`), and the constraint set `𝒞_r` stabilises for
  `r ≥ 14` (`cSet_subset_cSetLe14`), reducing validity at every level
  `r ≥ 5` to the finitely many levels `5 ≤ r ≤ 14`
  (`isValidAt_of_isValidAt_le_14`).
-/
import Mathlib.Data.Set.Card
import SteppingUpLemma.Colouring.Basic

namespace SteppingUp.Trees
open BinaryTree

variable {T : Tree}

section «The profile sets stabilise»

/-- `lem:del-analysis`, first part: `false ∈ E(T)` (some deletion
of `T` is a proper) unless `T` is the specific `4`-leaf tree with
`M = 0`, `a = b = 2`; in particular this always holds for `T.numLeaves ≥ 5`. -/
lemma false_mem_delSet_of_five_le (hp : 5 ≤ #T) (hproper : T.core.isSome) :
    false ∈ ((∂T).map (·.core.isNone)) := by
  obtain ⟨a, _⟩ := exists_false_mem_dels hp (by simp_all)
  simp_all ; use a

/-- `lem:del-analysis`, second part: `true ∈ E(T)` iff one core
side has `2` leaves and the other is a degenerate tree. -/
lemma true_mem_delSet_iff {a b : ℕ} {lam rho : Bool}
    (h : T.signature = some ⟨a, b, lam, rho, d⟩) :
    true ∈ ((∂T).map (·.core.isNone)) ↔ (a = 2 ∧ rho) ∨ (b = 2 ∧ lam) := by
  unfold signature at h
  rw [List.mem_map, List.any_eq_true.symm]

  cases hcore : T.core with
  | none => simp_all
  | some p =>
    rw [hcore] at h
    injections h ; subst_eqs
    exact hasDegenerateDel_iff hcore

/-- A degenerate tree with `n + 1` leaves. -/
private abbrev mkDegenerate (n : ℕ) : Tree := peelN n .nil

/-- `lem:realise` (realisability): every well-formed `δ = 0`
class is realised by some proper tree of any large enough size. -/
lemma exists_of_isClass {a b : ℕ} {lam rho : Bool} (h : IsClass a b lam rho) (p : ℕ)
    (hp : a + b ≤ p) :
    ∃ T, #T = p ∧ T.core.isNone = false ∧
      T.signature = some ⟨a, b, lam, rho, decide (a + b = p)⟩ := by
  obtain ⟨ha, hb, haLam, hbRho⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  -- A tree of any size in `2..5`, degenerate exactly as `d` demands; sizes
  -- `≤ 3` force degeneracy, which is what `hd` records.
  have key (d : Bool) (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) (hd : n ≤ 3 → d) :
      ∃ T, #T = n ∧ T.core.isNone = d := by
    cases d
    · obtain rfl | rfl : n = 4 ∨ n = 5 := by rcases hn with rfl | rfl | rfl | rfl <;> simp_all
      · exists fourLeaves
      · exists fiveLeavesProper
    · exact ⟨mkDegenerate (n - 1), by simp; omega, by simp⟩
  obtain ⟨L, hLlv, hLdegenerate⟩ := key lam a ha haLam
  obtain ⟨R, hRlv, hRdegenerate⟩ := key rho b hb hbRho
  use peelN (p - (a + b)) (L △ R)
  have : (L △ R).core = some (L, R) := core_node_of_two_le
  rw [lv_peelN, numLeaves, hLlv, hRlv, signature]
  split_ands <;> simp_all


/-- `Prof(p)`: the set of extended profiles realised by trees with `p`
leaves (used in `thm:C` below). -/
def ProfSet (p : ℕ) : Set Prof := {π | ∃ T, #T = p ∧ prof T = π}

/-- The profile a well-formed class `(a, b, lam, rho)` induces
(`cor:E-determined`): `E` is `{false}`, plus `{true}` exactly when one side has
`2` leaves and the other is a degenerate tree. -/
def classProf (c : Signature) : Prof :=
  ⟨(c.a = 2 ∧ c.rho) ∨ (c.b = 2 ∧ c.lam),
    true,
    some ⟨fold c.a, fold c.b, c.lam, c.rho, false⟩⟩

/-- Membership in `allDelta0Classes` pins the `δ` coordinate to `false` (that
is what "delta 0" means), on top of well-formedness of the other four. -/
lemma mem_allDelta0Classes_iff {a b : ℕ} {lam rho d : Bool} :
    (⟨a, b, lam, rho, d⟩ : Signature) ∈ allDelta0Classes ↔ IsClass a b lam rho ∧ d = false := by
  unfold allDelta0Classes IsClass
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Signature.mk.injEq]
  constructor
  · rintro ⟨p, hp, hpa, hpb, hplam, hprho, hpd⟩
    simp_all
  · rintro ⟨⟨ha, hb, hlam, hrho⟩, rfl⟩
    refine ⟨(a, b, lam, rho), ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp_all

/-- If `T`'s core is exactly `(L, R)` with no extra peeling (`T.numLeaves = L.numLeaves +
R.numLeaves`), then `T` literally is `node L R`. Proved by the same induction as
`hasDegenerateDel_iff`/`sClasses_eq_of_core`: any peel step strictly increases `lv`
past `L.numLeaves + R.numLeaves` (via `le_lv_of_core`), contradicting the hypothesis. -/
lemma eq_node_of_core_of_lv_eq {L R : Tree} (hcore : T.core = some (L, R))
    (heq : #T = #L + #R) : T = L △ R := by
  induction T using BinaryTree.unitRecOn with
  | base => simp [core] at hcore
  | ind A B _ _ =>
    have hA1 := A.numLeaves_pos
    have hB1 := B.numLeaves_pos
    by_cases hA : #A = 1
    · simp at hA; subst A
      simp only [core] at hcore
      have := le_lv_of_core hcore
      simp only [numLeaves] at heq this; omega
    · by_cases hB : #B = 1
      · simp at hB; subst B
        rw [core_of_node_nil] at hcore
        have := le_lv_of_core hcore
        simp only [numLeaves] at heq this; omega
      · rw [show (A △ B).core = some (A, B) from core_node_of_two_le] at hcore
        injections hcore
        subst_vars; rfl

/-- Every degenerate tree (with `≥ 2` leaves, so it has at least one deletion)
has the single profile `({true}, none)`. -/
lemma prof_eq_degenerate_profile (hp2 : 2 ≤ #T)
    (hdegenerate : T.core = none) :
    prof T = degenerateProf := by
  have hlen : (∂T).length = #T := length_dels hp2
  have hall {Y} : Y ∈ ∂T → Y.core = none := core_isNone_of_mem_dels (by simp [hdegenerate])
  obtain ⟨Y, hY : Y ∈ ∂T⟩ := List.exists_mem_of_ne_nil ∂T (by grind only [= List.length_nil])
  have h1 : (∂T).any (·.core.isNone) := by grind only [List.any_eq, Option.isNone, core_isNone_of_mem_dels]
  have h2 : ¬ (∂T).any (·.core.isSome) := by simp_all
  simp [prof, degenerateProf, tau, signature, hdegenerate, h1, h2]

variable {x : ℕ}

private lemma fold_idem : fold (fold x) = fold x := by unfold fold; split_ifs <;> omega

lemma fold_le_self : fold x ≤ x := by unfold fold; split_ifs <;> omega

lemma fold_le_three_iff : fold x ≤ 3 ↔ x ≤ 3 := by unfold fold; split_ifs <;> omega

lemma fold_mem_of_two_le (hx : 2 ≤ x) : fold x ∈ ({2, 3, 4, 5} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold fold; split_ifs <;> omega

lemma fold_eq_self_of_mem (hx : x ∈ ({2, 3, 4, 5} : Finset ℕ)) : fold x = x := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  unfold fold; split_ifs <;> omega

/-- Every proper with `lv ≥ 5` has the profile `classProf` predicts
from its own (folded) class. -/
lemma prof_eq_classProf {a b : ℕ} {lam rho : Bool} (hp5 : 5 ≤ #T)
    (hdegenerate : T.core.isSome) (hk : T.signature = some ⟨a, b, lam, rho, d⟩) :
    prof T = classProf (⟨fold a, fold b, lam, rho, d⟩ : Signature) := by
  have hfalse := false_mem_delSet_of_five_le hp5 hdegenerate
  have htrue := true_mem_delSet_iff hk
  -- `anySome`: some deletion is proper, i.e. `false` is realised.
  have hAS : (prof T).anySome := by
    obtain ⟨Y, hY, hYn⟩ := List.mem_map.mp hfalse
    exact List.any_eq_true.mpr ⟨Y, hY, by cases hc : Y.core <;> simp_all⟩
  -- `anyNone`: `true` is realised exactly under `classProf`'s condition.
  have hAN : (prof T).anyNone =
      decide ((fold a = 2 ∧ rho) ∨ (fold b = 2 ∧ lam)) := by
    have h1 : (prof T).anyNone ↔ true ∈ ((∂T).map (·.core.isNone)) := by
      simp [prof, List.mem_map, List.any_eq_true]
    rw [Bool.eq_iff_iff, h1, htrue]
    simp [fold_eq_two_iff]
  have hcls : (prof T).cls = some (⟨fold a, fold b, lam, rho, false⟩ : CoreSignature) := by
    unfold prof tau; simp [hk, eraseDelta]
  have hRHS : classProf (⟨fold a, fold b, lam, rho, d⟩ : Signature) =
      ⟨decide ((fold a = 2 ∧ rho) ∨ (fold b = 2 ∧ lam)), true,
        some (⟨fold a, fold b, lam, rho, false⟩ : CoreSignature)⟩ := by
    unfold classProf; simp [fold_idem]
  rw [hRHS, ← hAN, ← hAS, ← hcls]

/-- The realised-profile set at any leaf-count `p ≥ 5`, expressed via the
finite set of well-formed classes realisable at that `p` (`thm:C`'s
proof): one degenerate tree profile, plus one `classProf` per class with
`a + b ≤ p` (`exists_of_isClass` for existence, `le_lv_of_core` for the
converse bound). -/
lemma profSet_eq_of_five_le {p : ℕ} (hp : 5 ≤ p) :
    ProfSet p = insert degenerateProf
      (classProf '' ↑(allDelta0Classes.filter (fun c ↦ c.a + c.b ≤ p))) := by
  ext π
  simp only [ProfSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe,
    Finset.mem_filter]
  constructor
  · show (∃ T, #T = p ∧ prof T = π) → π = degenerateProf
      ∨ ∃ x, (x ∈ allDelta0Classes ∧ x.a + x.b ≤ p) ∧ classProf x = π
    rintro ⟨T, hZlv, rfl⟩
    rcases hdegenerate : T.core with _ | ⟨L, R⟩
    · exact Or.inl (prof_eq_degenerate_profile (by omega) hdegenerate)
    · have hk : T.signature = some (⟨#L, #R, L.core.isNone, R.core.isNone, (#L + #R = #T)⟩ : Signature) := by
        unfold signature; simp [hdegenerate]
      obtain ⟨hL2, hR2⟩ := (two_le_of_kappa hk)
      obtain ⟨hlam3, hrho3⟩ := (core_isNone_of_kappa_le_three hk)
      have hab : #L + #R ≤ p := by have := le_lv_of_core hdegenerate; omega
      have hfoldab : fold (#L) + fold (#R) ≤ p := by
        have := fold_le_self (x := #L); have := fold_le_self (x := #R); omega
      have hmem :
          (⟨fold (#L), fold (#R), L.core.isNone, R.core.isNone, false⟩ : Signature) ∈
            allDelta0Classes := by
        rw [mem_allDelta0Classes_iff]
        exact ⟨⟨fold_mem_of_two_le hL2, fold_mem_of_two_le hR2,
          hlam3 ∘ fold_le_three_iff.mp, hrho3 ∘ fold_le_three_iff.mp⟩, rfl⟩
      exact Or.inr ⟨_, ⟨hmem, hfoldab⟩, (prof_eq_classProf (by omega) (by simp [hdegenerate]) hk).symm⟩
  · rintro (rfl | ⟨⟨a, b, lam, rho, dlt⟩, ⟨hcmem, hcle⟩, rfl⟩)
    · exact ⟨mkDegenerate (p - 1), by simp; omega,
        prof_eq_degenerate_profile (by simp; omega) (by simp)⟩
    · obtain ⟨⟨ha, hb, hlam, hrho⟩, -⟩ := mem_allDelta0Classes_iff.mp hcmem
      obtain ⟨T, hZlv, hZdegenerate, hZk⟩ := exists_of_isClass ⟨ha, hb, hlam, hrho⟩ p hcle
      have hpe := prof_eq_classProf (by omega) (by simpa using hZdegenerate) hZk
      rw [fold_eq_self_of_mem ha, fold_eq_self_of_mem hb] at hpe
      exact ⟨T, hZlv, hpe⟩

/-- `thm:C`, stabilisation part: `Prof(p)` is the
same set for every `p ≥ 10`. -/
theorem profSet_stabilises {p q : ℕ} (hp : 10 ≤ p) (hq : 10 ≤ q) :
    ProfSet p = ProfSet q := by
  have hfull : ∀ n, 10 ≤ n →
      allDelta0Classes.filter (fun c ↦ c.a + c.b ≤ n) = allDelta0Classes := by
    intro n hn
    apply Finset.filter_true_of_mem
    rintro ⟨a, b, lam, rho, dlt⟩ hc
    obtain ⟨⟨ha, hb, -, -⟩, -⟩ := mem_allDelta0Classes_iff.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    change a + b ≤ _
    omega
  rw [profSet_eq_of_five_le (by omega : 5 ≤ p), profSet_eq_of_five_le (by omega : 5 ≤ q),
    hfull p hp, hfull q hq]

end «The profile sets stabilise»

section «Stabilisation»

/-- `𝒞_r`, `𝒞_{≤n}`: the sets of `(sClasses T, cat(T))` pairs realised at
level `r`, and cumulatively up to level `n`. Colouring-independent, matching
the paper's `𝒞_r` of `sec:Ccount`. -/
def CSet (r : ℕ) : Set (Finset CoreSignature × Bool) :=
  {p | ∃ T, #T = r + 2 ∧ T.core.isSome ∧ p = (sClasses T, hasDegenerateDel T)}

/-- `𝒞_{≤n} = ⋃_{5 ≤ r ≤ n} 𝒞_r`. -/
def CSetLe (n : ℕ) : Set (Finset CoreSignature × Bool) :=
  ⋃ r ∈ Set.Icc 5 n, CSet r

/-- The stabilisation step used in `thm:stab`: every profile realised at
some leaf-count `a ≥ 2` is also realised at some `a' ≤ 11` with the same
fold-data `(fold a', fold (a' - 1), 3 ≤ a')` as `a` itself — either because
`a ≤ 11` already (`a' = a`), or (`a ≥ 12`) by repeatedly trading `a` for
`a - 2` via `profSet_stabilises` (valid once both sides are `≥ 10`) and
`fold_pred_of_five_le` (fold values depend only on parity once `≥ 5`), which
bottoms out at `a' ∈ {10, 11}`. -/
lemma exists_le_eleven_of_mem_profSet :
    ∀ a, 2 ≤ a → ∀ π : Prof,
      π ∈ ProfSet a →
      ∃ a', 2 ≤ a' ∧ a' ≤ 11 ∧ ((a ≤ 11 ∧ a' = a) ∨ 10 ≤ a') ∧ π ∈ ProfSet a' ∧
        fold a' = fold a ∧ fold (a' - 1) = fold (a - 1) ∧ (3 ≤ a' ↔ 3 ≤ a) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha2 π hπ
    by_cases ha11 : a ≤ 11
    · exact ⟨a, ha2, ha11, Or.inl ⟨ha11, rfl⟩, hπ, rfl, rfl, Iff.rfl⟩
    · have ha12 : 12 ≤ a := by omega
      have hstab : ProfSet a = ProfSet (a - 2) := profSet_stabilises (by omega) (by omega)
      have hπ' : π ∈ ProfSet (a - 2) := hstab ▸ hπ
      obtain ⟨a', ha'2, ha'11, ha'or, hπ'', hfold1, hfold2, htest⟩ :=
        ih (a - 2) (by omega) (by omega) π hπ'
      have h10 : 10 ≤ a' := by
        rcases ha'or with ⟨_, rfl⟩ | _ <;> omega

      have heq : (fold a, fold (a - 1)) = (fold (a - 2), fold (a - 3)) := by
        have h1 := fold_pred_of_five_le (p := a) (by omega)
        have h2 := fold_pred_of_five_le (p := a - 2) (by omega)
        rw [(by omega : (a - 2) % 2 = a % 2)] at h2
        exact h1.trans h2.symm
      injections
      have ha3 : a - 2 - 1 = a - 3 := by omega
      rw [ha3] at hfold2
      exact ⟨a', ha'2, ha'11, Or.inr h10, hπ'', by simp_all, by simp_all, by omega⟩

/-! ### Sharpening the stabilisation threshold from `22` to `14`

`classReduction`'s formula consults a core
side's *full* profile (`.2.2`, the folded class) only on the branch where
that side collapses (`testP`/`testQ` false, i.e. that side has exactly `2`
leaves); on the "main branch" (`3 ≤ L.numLeaves ∧ 3 ≤ R.numLeaves`) it consults only
`(Cat, E)` (`.1`, `.2.1`) for *each* side. `(Cat, E)` needs realising only up
to `7` leaves (not `11`), since — unlike the full folded class, which keeps
changing until `10` — it takes only finitely many values and every one of
them already appears by `7`. -/

/-- Realises a well-formed class at an exact target leaf-count `p`, reading
off `(Cat, E)` directly off `(a, b, lam, rho)` (via `prof_eq_classProf`,
`classProf`, `fold_eq_two_iff`) rather than the folded class itself. -/
private lemma exists_profile_witness {a b : ℕ} {lam rho : Bool} (h : IsClass a b lam rho)
    (p : ℕ) (hp : a + b ≤ p) (hp5 : 5 ≤ p) :
    ∃ T : Tree, #T = p ∧ T.core.isNone = false ∧
      (prof T).anyNone = decide ((a = 2 ∧ rho) ∨ (b = 2 ∧ lam)) ∧
      (prof T).anySome := by
  obtain ⟨T, hZlv, hZdegenerate, hZk⟩ := exists_of_isClass h p hp
  have hZdegenerate' : T.core.isSome := by
    cases hcZ : T.core with
    | none => rw [hcZ] at hZdegenerate; simp at hZdegenerate
    | some _ => rfl
  have hpc := prof_eq_classProf (hZlv ▸ hp5) hZdegenerate' hZk
  refine ⟨T, hZlv, hZdegenerate, ?_, ?_⟩ <;> rw [hpc] <;> unfold classProf <;>
    simp [fold_eq_two_iff]

/-- **The sharper reduction step**: for a tree `T` with `T.numLeaves ≥ 5`, some `T'`
with `5 ≤ T'.numLeaves ≤ 7`, of the same parity as `T.numLeaves`, has the same `(Cat, E)`
data as `T` — i.e. `prof T'` and `prof T` agree on `.1` and `.2.1` (though
generally not on `.2.2`, the folded class, which `classReduction`'s main
branch never reads). Two witness classes suffice for every case: `(2,2,⊤,⊤)`
(giving `E = {⊥,⊤}`, realised at `5` and `6`) and `(3,3,⊤,⊤)` (giving
`E = {⊥}`, realised at `6` and `7`); degenerate trees use `mkDegenerate` directly. -/
private lemma exists_le_seven_matching_degenerateE (hL5 : 5 ≤ #T) :
    ∃ T' : Tree, 5 ≤ #T' ∧ #T' ≤ 7 ∧ #T' % 2 = #T % 2 ∧
      T'.core.isNone = T.core.isNone ∧
      (prof T').anyNone = (prof T).anyNone ∧ (prof T').anySome = (prof T).anySome := by
  have hIsClass22 : IsClass 2 2 true true := by unfold IsClass; decide
  have hIsClass33 : IsClass 3 3 true true := by unfold IsClass; decide
  have hparity : #T % 2 = 0 ∨ #T % 2 = 1 := by omega
  rcases hdegenerate : T.core.isNone with _ | _
  · -- proper: read off `T`'s own core.
    rcases hc : T.core with _ | ⟨A, B⟩
    · simp [hc] at hdegenerate
    have hdegenerateS : T.core.isSome := by rw [hc]; rfl
    have hk : T.signature = some (⟨#A, #B, A.core.isNone, B.core.isNone, #A + #B = #T⟩ : Signature) := by
      unfold signature; rw [hc]; rfl
    -- The witness construction is the same in all four cases below: only the
    -- class, the size, and hence the `E`-value vary. `exists_profile_witness`
    -- already reports `E` as an `if` on the class, so that `if` is exactly the
    -- one fact each case has to supply.
    have hTsome : (prof T).anySome := by
      rw [prof_eq_classProf (by omega) hdegenerateS hk]; rfl
    have mk {a b : ℕ} (hc : IsClass a b true true) (N : ℕ)
        (hE : decide ((a = 2 ∧ (true : Bool)) ∨ (b = 2 ∧ (true : Bool)))
            = (prof T).anyNone)
        (hab : a + b ≤ N := by omega) (h5 : 5 ≤ N := by omega) (h7 : N ≤ 7 := by omega)
        (hpar : N % 2 = #T % 2 := by omega) :
        ∃ T' : Tree, 5 ≤ #T' ∧ #T' ≤ 7 ∧ #T' % 2 = #T % 2 ∧
          T'.core.isNone = false ∧
          (prof T').anyNone = (prof T).anyNone ∧ (prof T').anySome = (prof T).anySome := by
      obtain ⟨T', hlv, hdeg, hZN, hZS⟩ := exists_profile_witness hc N hab h5
      exact ⟨T', by omega, by omega, by omega, hdeg, by rw [hZN, hE], by rw [hZS, hTsome]⟩
    by_cases hTrue :
        (#A = 2 ∧ B.core.isNone) ∨ (#B = 2 ∧ A.core.isNone)
    · have hprofNone : (prof T).anyNone := by
        rw [prof_eq_classProf (by omega) hdegenerateS hk]
        unfold classProf
        simp only [fold_eq_two_iff, decide_eq_true_eq, hTrue]
      rcases hparity with hev | hod
      · exact mk hIsClass22 6 (by simp [hprofNone])
      · exact mk hIsClass22 5 (by simp [hprofNone])
    · have hprofNone : (prof T).anyNone = false := by
        rw [prof_eq_classProf (by omega) hdegenerateS hk]
        unfold classProf
        simp only [fold_eq_two_iff, hTrue]
        rfl
      rcases hparity with hev | hod
      · exact mk hIsClass33 6 (by simp [hprofNone])
      · exact mk hIsClass33 7 (by simp [hprofNone])
  · -- degenerate tree: `prof` is `({true}, none)` at every size (`≥ 2`).
    rcases hparity with h | h
    all_goals
      have hprof5 : prof (mkDegenerate (4 + (1 - #T % 2))) = degenerateProf :=
        prof_eq_degenerate_profile (by simp [h]) (by simp [h])
      have hprofL : prof T = degenerateProf :=
        prof_eq_degenerate_profile (by omega) (by simpa using hdegenerate)
      exact ⟨mkDegenerate (4 + (1 - #T % 2)), by simp, by simp [h], by simp; omega,
        by simp, by simp [hprof5, hprofL], by simp [hprof5, hprofL]⟩


/-- Wraps `exists_le_seven_matching_degenerateE` with the "already small" case
(`T.numLeaves ≤ 7`, `T' = T`), and adds the `fold`/`3 ≤ ·`-matching facts needed to
substitute `T'` for `T` inside `classReduction`'s explicit `foldP`/`foldPm1`/
`testP` arguments (mirroring `exists_le_eleven_of_mem_profSet`'s own
"either already small, or reduced and `≥ 5`" disjunction, which the
final-bound `omega` calls below need). -/
private lemma exists_le_seven_matching_degenerateE' (hL3 : 3 ≤ #T) :
    ∃ T' : Tree, 3 ≤ #T' ∧ #T' ≤ 7 ∧ ((#T ≤ 7 ∧ T' = T) ∨ 5 ≤ #T') ∧
      fold (#T') = fold (#T) ∧ fold (#T' - 1) = fold (#T - 1) ∧
      decide (3 ≤ #T') = decide (3 ≤ #T) ∧
      T'.core.isNone = T.core.isNone ∧
      (prof T').anyNone = (prof T).anyNone ∧ (prof T').anySome = (prof T).anySome := by
  by_cases h7 : #T ≤ 7
  · exact ⟨T, hL3, h7, Or.inl ⟨h7, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨T', h1, h2, h3, h4, h5, h6⟩ := exists_le_seven_matching_degenerateE (T := T) (by omega)
    have : (fold (#T'), fold (#T' - 1)) = (fold (#T), fold (#T - 1)) := by
      have hf1 := fold_pred_of_five_le (p := #T') h1
      have hf2 := fold_pred_of_five_le (p := #T) (by omega)
      exact (h3 ▸ hf1).trans hf2.symm
    injection this
    exact ⟨T', by omega, h2, Or.inr h1, by assumption, by assumption,
      by rw [decide_eq_decide]; omega, h4, h5, h6⟩

/-- `classReduction`'s formula, on the "main branch" `testP = testQ = true`
(both core sides `≥ 3` leaves), depends on `profL`/`profR` only through `.1`
(`.2`, the folded class, is never read there) — the fact that lets the
reduction on that branch bottom out at `7` leaves instead of `11`. `degL`/
`degR` are shared verbatim between both sides of the equation (they no
longer come from `profL`/`profR` at all), so no hypothesis about them is
needed here. -/
private lemma classReduction_eq_of_degenerateE
    {foldP foldPm1 foldQ foldQm1 m : ℕ} {testP testQ : Bool}
    (htP : testP) (htQ : testQ)
    {degL degR : Bool}
    {profL profR profL2 profR2 : Prof}
    (h1 : profL2.anyNone = profL.anyNone) (h1s : profL2.anySome = profL.anySome)
    (h2 : profR2.anyNone = profR.anyNone) (h2s : profR2.anySome = profR.anySome) :
    classReduction foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL2 profR2 =
    classReduction foldP foldPm1 testP foldQ foldQm1 testQ m degL degR profL profR := by
  simp only [classReduction, htP, htQ, if_true, h1, h1s, h2, h2s]

/-- The peel count carrying a collapsed configuration back into `5 ≤ r' ≤ 14`.
`p` is the side being reduced, to `s ≤ 11` leaves; `q` is the side pinned at
`2`; `D` is the original peel count, taken as a parameter so that either
argument order of `r + 2 - #L - #R` matches. Both branches of
`cSet_subset_cSetLe14_collapse` need this, with the same arithmetic. -/
private lemma exists_peel_count {r p q s D : ℕ} (hr : 5 ≤ r) (hq : q = 2)
    (hpq : p + q ≤ r + 2) (hD : D = r + 2 - p - q) (hs2 : 2 ≤ s) (hs11 : s ≤ 11)
    (hsor : (p ≤ 11 ∧ s = p) ∨ 10 ≤ s) :
    ∃ M', min M' 2 = min D 2 ∧ 7 ≤ s + q + M' ∧ s + q + M' ≤ 15 := by
  subst hD
  by_cases hM2 : 2 ≤ r + 2 - p - q
  · have hmeq : min (r + 2 - p - q) 2 = 2 := min_eq_right hM2
    by_cases h5 : 5 ≤ s + q
    · exact ⟨2, by rw [hmeq]; decide, by omega, by omega⟩
    · exact ⟨3, by rw [hmeq]; decide, by omega, by omega⟩
  · refine ⟨r + 2 - p - q, rfl, ?_, by omega⟩
    rcases hsor with ⟨_, rfl⟩ | hs10 <;> omega

/-- Both collapse branches finish alike. A reduced pair `(A, B)` and a peel
count `M'` placing the level in `[5, 14]` assemble into a tree whose own
`classReduction` data is the constraint under consideration, so that
constraint lies in `CSetLe 14`. -/
private lemma mem_cSetLe14_of_reduction {T A B : Tree} {M' : ℕ}
    (hA2 : 2 ≤ #A) (hB2 : 2 ≤ #B)
    (h7 : 7 ≤ #A + #B + M') (h15 : #A + #B + M' ≤ 15)
    (hGeq : classReduction (fold (#A)) (fold (#A - 1)) (decide (3 ≤ #A))
        (fold (#B)) (fold (#B - 1)) (decide (3 ≤ #B))
        (min M' 2) (A.core.isNone) (B.core.isNone) (prof A) (prof B) =
      (sClasses T, hasDegenerateDel T)) :
    (sClasses T, hasDegenerateDel T) ∈ CSetLe 14 := by
  have hZcore : core (.node A B) = some (A, B) := core_node_of_two_le hA2 hB2
  have hcoreX : (peelN M' (.node A B)).core = some (A, B) := by
    rw [core_peelN, hZcore]
  have hXlv : #(peelN M' (.node A B)) = (#A + #B + M' - 2) + 2 := by
    rw [lv_peelN]; simp only [numLeaves]; omega
  set r' := #A + #B + M' - 2 with hr'def
  set X := peelN M' (.node A B) with hXdef
  have hXsome : X.core.isSome := by rw [hcoreX]; rfl
  have hrange : r' ∈ Set.Icc 5 14 := by rw [Set.mem_Icc, hr'def]; omega
  have hkey := reduction_to_profiles r' X A B hcoreX hXlv hXsome
  have hM : min (r' + 2 - #A - #B) 2 = min M' 2 := by rw [hr'def]; congr 1; omega
  rw [hM, hGeq] at hkey
  rw [hkey]
  exact Set.mem_iUnion₂.mpr ⟨r', hrange, ⟨X, hXlv, hXsome, rfl⟩⟩

/-- The two "collapse" branches of `cSet_subset_cSetLe14` (one side of `core T`
exactly at level `2`, the other reduced fully to `≤ 11` via
`exists_le_eleven_of_mem_profSet`) — mirror images of one another under
`β = true` (`R` is the fixed side) vs `β = false` (`L` is the fixed side). -/
private lemma cSet_subset_cSetLe14_collapse {r : ℕ} {T L R : Tree} (hr : 5 ≤ r)
    (ha2 : 2 ≤ #L) (hb2 : 2 ≤ #R)
    (hab : #L + #R ≤ r + 2)
    (hkey1 : classReduction (fold (#L)) (fold (#L - 1)) (decide (3 ≤ #L))
        (fold (#R)) (fold (#R - 1)) (decide (3 ≤ #R))
        (min (r + 2 - #L - #R) 2) (L.core.isNone) (R.core.isNone)
        (prof L) (prof R) = (sClasses T, hasDegenerateDel T))
    (β : Bool) (hβ : if β then #R = 2 else #L = 2) :
    (sClasses T, hasDegenerateDel T) ∈ CSetLe 14 := by
  cases β with
  | true =>
    have hR2 : #R = 2 := hβ
    have : R = .nil △ .nil := by simp at hR2; exact hR2
    rw [this] at *
    have hprofL : prof L ∈ ProfSet (#L) := ⟨L, rfl, rfl⟩
    obtain ⟨a', ha'2, ha'11, ha'or, hprofL', hfoldA1, hfoldA2, htestA⟩ :=
      exists_le_eleven_of_mem_profSet (#L) ha2 (prof L) hprofL
    obtain ⟨L', hL'lv, hL'prof⟩ := hprofL'
    have hdegA : L'.core = none ↔ L.core = none := core_isNone_eq_of_prof_eq hL'prof
    have hL'2 : 2 ≤ #L' := by rw [hL'lv]; exact ha'2
    obtain ⟨M', hMmin, hr'7, hr'15⟩ :=
      exists_peel_count (p := #L) (q := #R) (s := a') (D := r + 2 - #L - #R)
        hr hR2 hab rfl ha'2 ha'11 ha'or

    refine mem_cSetLe14_of_reduction (M' := M') hL'2 hb2 (by omega) (by omega) (Eq.trans ?_ hkey1)
    have hargA1 : fold (#L') = fold (#L) := by rw [hL'lv]; exact hfoldA1
    have hargA2 : fold (#L' - 1) = fold (#L - 1) := by rw [hL'lv]; exact hfoldA2
    have hargA3 : decide (3 ≤ #L') = decide (3 ≤ #L) := by
      rw [decide_eq_decide, hL'lv]; exact htestA
    rw [hargA1, hargA2, hargA3, hMmin, hL'prof]
    have hdegA' : L'.core.isNone = L.core.isNone := by
      rw [Bool.eq_iff_iff]; simp [Option.isNone_iff_eq_none, hdegA]
    rw [hdegA']
  | false =>
    have hL2 : #L = 2 := hβ
    have hprofR : prof R ∈ ProfSet (#R) := ⟨R, rfl, rfl⟩
    obtain ⟨b', hb'2, hb'11, hb'or, hprofR', hfoldB1, hfoldB2, htestB⟩ :=
      exists_le_eleven_of_mem_profSet (#R) hb2 (prof R) hprofR
    obtain ⟨R', hR'lv, hR'prof⟩ := hprofR'
    have hdegB : R'.core.isNone = R.core.isNone := by
      unfold prof at hR'prof
      have hdegB' := core_isNone_eq_of_prof_eq hR'prof
      rcases hR' : R'.core with _ | p
      · rw [hdegB'.mp hR']
      · rcases hR : R.core with _ | q
        · exact absurd (hdegB'.mpr hR) (by rw [hR']; simp)
        · rfl
    have hR'2 : 2 ≤ #R' := by rw [hR'lv]; exact hb'2
    obtain ⟨M', hMmin, hr'7, hr'15⟩ :=
      exists_peel_count (p := #R) (q := #L) (s := b') (D := r + 2 - #L - #R)
        hr hL2 (by omega) (by omega) hb'2 hb'11 hb'or
    refine mem_cSetLe14_of_reduction (M' := M') ha2 hR'2 (by omega) (by omega) (Eq.trans ?_ hkey1)
    have hargB1 : fold (#R') = fold (#R) := by rw [hR'lv]; exact hfoldB1
    have hargB2 : fold (#R' - 1) = fold (#R - 1) := by rw [hR'lv]; exact hfoldB2
    have hargB3 : decide (3 ≤ #R') = decide (3 ≤ #R) := by
      rw [decide_eq_decide, hR'lv]; exact htestB
    rw [hargB1, hargB2, hargB3, hMmin, hdegB, hR'prof]

/-- `thm:stab`. Splits on
`classReduction`'s own branching (`3 ≤ L.numLeaves`, `3 ≤ R.numLeaves`): on the main
branch both sides reduce to `≤ 7` leaves (`exists_le_seven_matching_degenerateE'`,
via `classReduction_eq_of_degenerateE`); on each collapse branch (`L.numLeaves = 2` or
`R.numLeaves = 2`) the fixed side needs no reduction and the other side still needs
the full `≤ 11` profile reduction (`exists_le_eleven_of_mem_profSet`), since
`classReduction` there reads that side's folded class in full. -/
theorem cSet_subset_cSetLe14 {r : ℕ} (hr : 5 ≤ r) : CSet r ⊆ CSetLe 14 := by
  rintro p ⟨T, hXlv, hXdegenerate, hp2⟩
  cases hcx : T.core with
  | none =>
    simp [hcx] at hXdegenerate
  | some LR =>
    obtain ⟨L, R⟩ := LR
    have ha2 : 2 ≤ #L := (two_le_of_core hcx).1
    have hb2 : 2 ≤ #R := (two_le_of_core hcx).2
    have hab_le : #L + #R ≤ #T := le_lv_of_core hcx
    have hkey1 := reduction_to_profiles r T L R hcx hXlv hXdegenerate
    by_cases htestP : 3 ≤ #L
    · by_cases htestQ : 3 ≤ #R
      · -- Main branch: `3 ≤ L.numLeaves`, `3 ≤ R.numLeaves`. Reduce both sides to `≤ 7`.
        obtain ⟨L', hL'3, hL'7, hL'or, hfoldA1, hfoldA2, htestA, hprofA1, hprofA2⟩ :=
          exists_le_seven_matching_degenerateE' htestP
        obtain ⟨R', hR'3, hR'7, hR'or, hfoldB1, hfoldB2, htestB, hprofB1, hprofB2⟩ :=
          exists_le_seven_matching_degenerateE' htestQ
        obtain ⟨M', hMmin, hr'7, hr'16⟩ :
            ∃ M', min M' 2 = min (r + 2 - #L - #R) 2 ∧
              7 ≤ #L' + #R' + M' ∧ #L' + #R' + M' ≤ 16 := by
          by_cases hM2 : 2 ≤ r + 2 - #L - #R
          · have hmeq : min (r + 2 - #L - #R) 2 = 2 := min_eq_right hM2
            exact ⟨2, by rw [hmeq]; decide, by omega, by omega⟩
          · refine ⟨r + 2 - #L - #R, rfl, ?_, ?_⟩
            <;> rcases hL'or with ⟨_, rfl⟩ | _
            <;> rcases hR'or with ⟨_, rfl⟩ | _
            <;> omega
        have hZ'core : core (.node L' R') = some (L', R') := by
          rw [core_eq_ite, if_pos ⟨by omega, by omega⟩]
        have hcoreX' : (peelN M' (.node L' R')).core = some (L', R') := by
          rw [core_peelN, hZ'core]
        have hX'lv : #(peelN M' (.node L' R')) = #L' + #R' + M' := by
          rw [lv_peelN]; simp only [numLeaves]; omega
        set X' := peelN M' (.node L' R') with hX'def
        set r' := #L' + #R' + M' - 2 with hr'def
        have hr'lv : #X' = r' + 2 := by rw [hX'lv, hr'def]; omega
        have hX'degenerate : X'.core.isSome := by rw [hcoreX']; rfl
        have hX'range : r' ∈ Set.Icc 5 14 := by rw [Set.mem_Icc, hr'def]; omega
        have hkey2 := reduction_to_profiles r' X' L' R' hcoreX' hr'lv hX'degenerate
        have hargM0 : r' + 2 - #L' - #R' = M' := by rw [hr'def]; omega
        have hargM : min (r' + 2 - #L' - #R') 2 = min (r + 2 - #L - #R) 2 := by
          rw [hargM0, hMmin]
        have hkey2' : classReduction (fold (#L)) (fold (#L - 1)) (decide (3 ≤ #L))
            (fold (#R)) (fold (#R - 1)) (decide (3 ≤ #R))
            (min (r + 2 - #L - #R) 2) (L.core.isNone) (R.core.isNone)
            (prof L') (prof R') =
            (sClasses X', hasDegenerateDel X') := by
          rw [← hfoldA1, ← hfoldA2, ← htestA, ← hfoldB1, ← hfoldB2, ← htestB, ← hargM,
            ← hprofA1, ← hprofB1]
          exact hkey2
        have htPtrue : decide (3 ≤ #L) := by rw [decide_eq_true_iff]; exact htestP
        have htQtrue : decide (3 ≤ #R) := by rw [decide_eq_true_iff]; exact htestQ
        have hGeq := classReduction_eq_of_degenerateE
          (foldP := fold (#L)) (foldPm1 := fold (#L - 1))
          (foldQ := fold (#R)) (foldQm1 := fold (#R - 1))
          (m := min (r + 2 - #L - #R) 2)
          (degL := L.core.isNone) (degR := R.core.isNone) htPtrue htQtrue
          hprofA2.1 hprofA2.2 hprofB2.1 hprofB2.2
        rw [hkey1, hkey2'] at hGeq
        rw [hp2, ← hGeq]
        exact Set.mem_iUnion₂.mpr ⟨r', hX'range, ⟨X', hr'lv, hX'degenerate, rfl⟩⟩
      · -- Collapse branch: `R.numLeaves = 2`. Reduce `L` fully to `≤ 11`; `R' = R`.
        rw [hp2]
        exact cSet_subset_cSetLe14_collapse hr ha2 hb2 (hXlv ▸ hab_le) hkey1 true
          (show #R = 2 by omega)
    · -- Collapse branch: `L.numLeaves = 2`. Reduce `R` fully to `≤ 11`; `L' = L`.
      rw [hp2]
      exact cSet_subset_cSetLe14_collapse hr ha2 hb2 (hXlv ▸ hab_le) hkey1 false
        (show #L = 2 by omega)


/-- Validity of the induced tree-colouring `treeColour c` at level `r`,
restated over `𝒞_r` via `sSet_eq_image_sClasses`. -/
lemma isValidAt_treeColour_iff (c : CoreSignature → EtaColour) (r : ℕ) :
    IsValidAt (treeColour c) r ↔
      ∀ p ∈ CSet r, 2 ≤ (p.1.image c).card ∨ (EtaColour.cN ∈ p.1.image c ∧ p.2) := by
  unfold IsValidAt CSet
  constructor
  · rintro h p ⟨T, hX, hd, rfl⟩
    rw [← sSet_eq_image_sClasses]
    exact h T hX hd
  · intro h T hXlv hXdeg
    have := h (sClasses T, hasDegenerateDel T) ⟨T, hXlv, hXdeg, rfl⟩
    rwa [sSet_eq_image_sClasses]

/-- `thm:stab`, consequence, sharpened: a table `c` valid at every level
`5 ≤ r ≤ 14` is valid at every level `r ≥ 5`. -/
theorem isValidAt_of_isValidAt_le_14 (c : CoreSignature → EtaColour)
    (hc : ∀ r, 5 ≤ r → r ≤ 14 → IsValidAt (treeColour c) r) :
    ∀ r, 5 ≤ r → IsValidAt (treeColour c) r := by
  intro r hr
  rw [isValidAt_treeColour_iff]
  intro p hp
  obtain ⟨r', hr', hpS⟩ := Set.mem_iUnion₂.mp (cSet_subset_cSetLe14 hr hp)
  rw [Set.mem_Icc] at hr'
  exact (isValidAt_treeColour_iff c r').mp (hc r' hr'.1 hr'.2) p hpS

end «Stabilisation»

end SteppingUp.Trees
