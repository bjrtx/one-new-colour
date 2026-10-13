/-
  Counts quoted in the paper, machine-checked.
  Stand-alone: no other module depends on this one.
-/
import SteppingUpLemma.Colouring.Stabilisation

namespace SteppingUp.Trees.Counts
open BinaryTree


private lemma classProf_injOn : Set.InjOn classProf ↑allDelta0Classes := by
  -- destructure both classes up front: once `fold c.a` (a `Decidable.rec`)
  -- appears in the context, `cases c` can no longer eliminate dependently.
  rintro ⟨a1, b1, l1, r1, d1⟩ hc1 ⟨a2, b2, l2, r2, d2⟩ hc2 heq
  obtain ⟨⟨ha1, hb1, -, -⟩, rfl⟩ := mem_allDelta0Classes_iff.mp (Finset.mem_coe.mp hc1)
  obtain ⟨⟨ha2, hb2, -, -⟩, rfl⟩ := mem_allDelta0Classes_iff.mp (Finset.mem_coe.mp hc2)
  unfold classProf at heq
  simp_all [fold_eq_self_of_mem]

private lemma classProf_injOn_filter {p : ℕ} :
    Set.InjOn classProf ↑(allDelta0Classes.filter (fun c ↦ c.a + c.b ≤ p)) := by
  apply Set.InjOn.mono _ classProf_injOn
  grind only [= Set.subset_def, = Finset.mem_coe, = Finset.mem_filter]

private lemma card_profSet_eq {p : ℕ} (hp5 : 5 ≤ p := by omega) :
    (ProfSet p).ncard =
      1 + (allDelta0Classes.filter (fun c ↦ c.a + c.b ≤ p)).card := by
  -- `classProf` never returns `degenerateProf`: it reports `anySome = true`.
  rw [profSet_eq_of_five_le hp5,
    Set.ncard_insert_of_notMem (by simp [degenerateProf, classProf]),
    classProf_injOn_filter.ncard_image, Set.ncard_coe_finset, Nat.add_comm]

/-- `|Prof(p)| = 37` for `p ≥ 10`. -/
theorem card_profSet_of_ten_le {p : ℕ} (hp : 10 ≤ p) : (ProfSet p).ncard = 37 := by
  rw [profSet_stabilises hp (le_refl 10), card_profSet_eq,
    show allDelta0Classes.filter (fun c ↦ c.a + c.b ≤ 10) = allDelta0Classes by decide,
    card_allDelta0Classes]

private lemma fold_add_ge_six_iff {A B : ℕ} (hA2 : 2 ≤ A) (hB2 : 2 ≤ B) :
    6 ≤ fold A + fold B ↔ 6 ≤ A + B := by
  unfold fold
  split_ifs <;> omega

/-- Hard half of the count of classes in `sec:classes`: of the `72`
classes, `69` are realised — `36` with `δ = 0` (any class is realisable with
δ = false, taking `r` far from `a + b - 1`), plus the `33` (of `36`) classes
with `a + b ≥ 6` also realisable with `δ = true` (taking `r = a + b - 1 ≥ 5`;
the other `3` classes, with `a + b < 6`, force `a + b - 1 < 5`, so `δ = true`
is unreachable for them). -/
private def realisedClassesFinset : Finset CoreSignature :=
  (allDelta0Classes.image (fun c ↦ ⟨c.a, c.b, c.lam, c.rho, false⟩)) ∪
  ((allDelta0Classes.filter (fun c ↦ 6 ≤ c.a + c.b)).image
    (fun c ↦ ⟨c.a, c.b, c.lam, c.rho, true⟩))

/-- The classes realised over `r ≥ 5`. -/
def RealisedClasses : Set CoreSignature := {cls | ∃ T, 6 ≤ #T ∧ tau T = some cls}

private lemma realisedClasses_eq : RealisedClasses = ↑realisedClassesFinset := by
  ext cls
  simp only [RealisedClasses, Set.mem_ofPred_eq, realisedClassesFinset, Finset.coe_union,
    Set.mem_union, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨T, hr, htau⟩
    rcases hc : T.signature with _ | ⟨A, B, lam, rho, dd⟩
    · exfalso; unfold tau at htau; rw [hc] at htau; simp at htau
    have hk : T.signature = some (⟨A, B, lam, rho, dd⟩ : Signature) := hc
    unfold tau at htau
    rw [hk] at htau
    injections htau
    subst htau
    have hA2 : 2 ≤ A := (two_le_of_kappa hk).1
    have hB2 : 2 ≤ B := (two_le_of_kappa hk).2
    have hlam3 : A ≤ 3 → lam = true := (core_isNone_of_kappa_le_three hk).1
    have hrho3 : B ≤ 3 → rho = true := (core_isNone_of_kappa_le_three hk).2
    have hmem : ⟨fold A, fold B, lam, rho, false⟩ ∈ allDelta0Classes := by
      rw [mem_allDelta0Classes_iff]
      exact ⟨⟨fold_mem_of_two_le hA2, fold_mem_of_two_le hB2,
        hlam3 ∘ fold_le_three_iff.mp, hrho3 ∘ fold_le_three_iff.mp⟩, rfl⟩
    have hdd : dd = decide (A + B = #T) := delta_of_signature hk
    by_cases hd : A + B = #T
    · exact .inr ⟨⟨fold A, fold B, lam, rho, false⟩,
        ⟨hmem, by rw [fold_add_ge_six_iff hA2 hB2]; omega⟩, by simp [hd, hdd]⟩
    · exact .inl ⟨⟨fold A, fold B, lam, rho, false⟩, hmem, by simp [hd, hdd]⟩
  · rintro (⟨⟨a, b, lam, rho, dlt⟩, hcmem, rfl⟩ | ⟨⟨a, b, lam, rho, dlt⟩, ⟨hcmem, hcge⟩, rfl⟩) <;>
      obtain ⟨⟨ha, hb, hlam, hrho⟩, -⟩ := mem_allDelta0Classes_iff.mp hcmem
    -- `δ = false`: take a witness strictly bigger than its own core, so
    -- `a + b ≠ #T` and the peel depth is positive.
    · obtain ⟨T, hlv, -, hk⟩ := exists_of_isClass ⟨ha, hb, hlam, hrho⟩ (a + b + 6) (by omega)
      exact ⟨T, by omega, by simp [tau, hk, fold_eq_self_of_mem ha, fold_eq_self_of_mem hb]⟩
    -- `δ = true`: take the witness to be its own core, `#T = a + b ≥ 6`.
    · obtain ⟨T, hlv, -, hk⟩ := exists_of_isClass ⟨ha, hb, hlam, hrho⟩ (a + b) le_rfl
      exact ⟨T, by rw [hlv]; exact hcge,
        by simp [tau, hk, fold_eq_self_of_mem ha, fold_eq_self_of_mem hb]⟩

lemma card_realisedClasses : RealisedClasses.ncard = 69 := by
  rw [realisedClasses_eq, Set.ncard_coe_finset]
  unfold realisedClassesFinset
  have hinj1 : Set.InjOn (fun (c : Signature) ↦ (⟨c.a, c.b, c.lam, c.rho, false⟩ :
      CoreSignature)) ↑allDelta0Classes := by
    rintro ⟨x1, y1, z1, w1, d1⟩ _ ⟨x2, y2, z2, w2, d2⟩
    simp_all [mem_allDelta0Classes_iff]
  have hinj2 : Set.InjOn (fun (c : Signature) ↦ (⟨c.a, c.b, c.lam, c.rho, true⟩ :
      CoreSignature)) ↑(allDelta0Classes.filter (fun c ↦ 6 ≤ c.a + c.b)) := by
    rintro ⟨x1, y1, z1, w1, d1⟩ hm1 ⟨x2, y2, z2, w2, d2⟩
    simp_all [mem_allDelta0Classes_iff]
  have : Disjoint (allDelta0Classes.image (fun c ↦
      (⟨c.a, c.b, c.lam, c.rho, false⟩ : CoreSignature)))
      ((allDelta0Classes.filter (fun c ↦ 6 ≤ c.a + c.b)).image
        (fun c ↦ (⟨c.a, c.b, c.lam, c.rho, true⟩ : CoreSignature))) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra! ⟨⟨_, _, _, _, b⟩, hx⟩
    cases b <;> simp at hx
  rw [Finset.card_union_of_disjoint this,
    Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2, card_allDelta0Classes,
    (by decide : (allDelta0Classes.filter (fun c ↦ 6 ≤ c.a + c.b)).card = 33)]

end SteppingUp.Trees.Counts
