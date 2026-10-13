/-
  The finite partition relation `Arrow`, and the three finitary stepping-up
  theorems about it.

  Colourings are total functions `Finset ℕ → Fin k`. Nothing
  is claimed about the values on sets that are not `r`-subsets of the ground
  set, so totality costs nothing.

  The theorems are not proved here from a finitary construction; they are
  transported from their infinitary counterparts in `Infinitary.lean`.
  `Arrow n r k s` quantifies over `X ⊆ range n`: it is a statement about a
  ground set of that *size* and nothing else, so it is invariant under any
  bijection of the ground set, and the linear order the splitting machinery
  relies on never appears in it. That is what makes the transport possible,
  and it is what retired the separate finitary development (`Splitting`,
  `Delta` and `EtaOneBridge`, which proved these from their own
  `ℕ`-as-bitset construction).
-/
import SteppingUpLemma.Infinitary

namespace SteppingUp

open Finset

section «The arrow relation»

/-- Erdős–Rado arrow relation `n → (s 0, …, s (k-1))^r`. -/
def Arrow (n r k : ℕ) (s : Fin k → ℕ) : Prop :=
  -- Under every colouring with colours in {0, ... , k - 1} ...
  ∀ f : Finset ℕ → Fin k,
  -- there is a colour `i` and a subset of {0, ... , n - 1} of cardinality
  -- `s i`, every `r`-subset of which gets colour `i`.
    ∃ i : Fin k, ∃ X ⊆ range n, #X = s i ∧ ∀ T ⊆ X, #T = r → f T = i

end «The arrow relation»

section «Stepped-up target sizes»

/-! These are the goals in the negative stepping-up lemma, depending on the
uniformity `r` -/

/-- The target sizes for the `η = 1` stepped-up relation at `r = 3`: `s i + 1`
in the old colours, `5` in the single new one. -/
def stepSizesR3 {k : ℕ} (s : Fin k → ℕ) (j : Fin (k + 1)) : ℕ :=
  if h : j < k then s ⟨j, h⟩ + 1 else 5

/-- The target sizes for the `η = 2` stepped-up relation at `r = 4`: `s i + 1`
in the old colours, `6` in either of the two new ones. -/
def stepSizesR4 {k : ℕ} (s : Fin k → ℕ) (j : Fin (k + 2)) : ℕ :=
  if h : j < k then s ⟨j, h⟩ + 1 else 6

/-- The target sizes for the `η = 1` stepped-up relation  at any `r ≥ 5`: `s i + 1`
in the old colours, `r + 2` in the single new one. -/
def stepSizesEtaOne (r : ℕ) {k : ℕ} (s : Fin k → ℕ) (j : Fin (k + 1)) : ℕ :=
  if h : j < k then s ⟨j, h⟩ + 1 else r + 2

end «Stepped-up target sizes»

/-! ### Transport to and from the infinitary relation -/

namespace Transport

open Cardinal

section «Naturals inside the ordinals»

/-- The natural number that a `< ω` ordinal names. Junk (`0`) above `ω`; every
use below is guarded by a `< (k : Ordinal)` hypothesis with `k : ℕ`. -/
noncomputable def onat (o : Ordinal) : ℕ := o.card.toNat

/-- Tagged `norm_cast`, so that `onat` behaves like any other cast: once an
ordinal is known to be a natural cast, `push_cast`/`exact_mod_cast` discharge
the round trips without naming a lemma. -/
@[simp, norm_cast] lemma onat_natCast (m : ℕ) : onat (m : Ordinal) = m := by
  simp [onat]

/-- An ordinal below a natural bound *is* a natural cast. Substituting with
this is what puts a goal in range of the cast machinery. -/
lemma exists_natCast_eq {o : Ordinal} {n : ℕ} (h : o < n) :
    ∃ m : ℕ, o = (m : Ordinal) :=
  Ordinal.lt_omega0.1 (h.trans (Ordinal.natCast_lt_omega0 n))

/-- Below a natural bound, `onat` is a genuine inverse to `Nat.cast`. -/
lemma natCast_onat {o : Ordinal} {n : ℕ} (h : o < n) :
    (onat o : Ordinal) = o := by
  obtain ⟨m, rfl⟩ := exists_natCast_eq h; norm_cast

lemma onat_lt {o : Ordinal} {n : ℕ} (h : o < n) : onat o < n := by
  obtain ⟨m, rfl⟩ := exists_natCast_eq h; exact_mod_cast h

end «Naturals inside the ordinals»

section «Enumerating a finite set of vertices»

/-! Everything below is driven by a single map `σ : ℕ → V` that sends `range n`
bijectively onto the ambient set and is junk elsewhere. -/

variable {V : Type*} {n : ℕ} {Vfull : Set V}

/-- A set of vertices of natural cardinality is finite, with that many
elements. -/
lemma exists_finset_of_mk_eq (hVfull : #Vfull = n) :
    ∃ Vf : Finset V, Vf = Vfull ∧ Vf.card = n := by
  have hVf : Vfull.Finite :=
    Cardinal.lt_aleph0_iff_set_finite.1 (by rw [hVfull]; exact Cardinal.natCast_lt_aleph0)
  refine ⟨hVf.toFinset, hVf.coe_toFinset, ?_⟩
  have h1 : #(hVf.toFinset : Set V) = (hVf.toFinset.card : Cardinal) := Cardinal.mk_coe_finset
  rw [hVf.coe_toFinset, hVfull] at h1
  exact_mod_cast h1.symm

/-- The enumeration itself: `σ` restricted to `range n` is a bijection onto
`Vf`. Stated as an explicit `∃` rather than a definition so that no
`Nonempty V` instance has to be carried around; the junk value comes from
`hn : 0 < n`. -/
lemma exists_enumeration (hn : 0 < n) {Vf : Finset V} (hVfcard : Vf.card = n) :
    ∃ σ : ℕ → V, (∀ m, m < n → σ m ∈ Vf) ∧ Set.InjOn σ {m | m < n} ∧
      ∀ v ∈ Vf, ∃ m, m < n ∧ σ m = v := by
  classical
  let e : Vf ≃ Fin n := Vf.equivFin.trans (finCongr hVfcard)
  have hne : Nonempty V := ⟨(e.symm ⟨0, hn⟩ : V)⟩
  refine ⟨fun m ↦ if h : m < n then (e.symm ⟨m, h⟩ : V) else Classical.arbitrary V,
    fun m hm ↦ by simp only [dif_pos hm]; exact (e.symm ⟨m, hm⟩).2, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [dif_pos ha, dif_pos hb] at hab
    exact congrArg Fin.val (e.symm.injective (Subtype.coe_injective hab))
  · intro v hv
    refine ⟨(e ⟨v, hv⟩ : Fin n), (e ⟨v, hv⟩).2, ?_⟩
    simp only [dif_pos (e ⟨v, hv⟩).2]
    rw [show (⟨(e ⟨v, hv⟩ : Fin n).val, (e ⟨v, hv⟩).2⟩ : Fin n) = e ⟨v, hv⟩ from rfl,
      Equiv.symm_apply_apply]

end «Enumerating a finite set of vertices»

section «The transport»

open SteppingUp.Infinitary in
/-- **Transport, forwards.** A finitary arrow relation gives the abstract one
over *any* vertex type: the ambient `Vfull` is enumerated by `range n`, and a
colouring of `Finset V` pulls back to a colouring of `Finset ℕ`.

`s'` is not required to be any particular function of `s` — only to agree with
it on the colours below `k`, which is all either relation looks at. -/
theorem arrowsTo_of_arrow {V : Type*} {n r k : ℕ} {s : Fin k → ℕ}
    {s' : Ordinal → Cardinal} (hn : 0 < n)
    (hs' : ∀ (m : ℕ) (hm : m < k), s' m = s ⟨m, hm⟩)
    (h : Arrow n r k s) :
    ArrowsTo V (n : Cardinal) r (k : Ordinal) s' := by
  classical
  intro Vfull hVfull f
  obtain ⟨Vf, hVfcoe, hVfcard⟩ := exists_finset_of_mk_eq hVfull
  obtain ⟨σ, hσmem, hσinj, hσsurj⟩ := exists_enumeration hn hVfcard
  -- `σ` is injective on any subset of `range n`.
  have hinjOn {U : Finset ℕ} (hU : U ⊆ Finset.range n) : Set.InjOn σ U :=
    fun _ ha _ hb => hσinj (Finset.mem_range.1 (hU ha)) (Finset.mem_range.1 (hU hb))
  -- Pull `f` back along `σ`.
  set f' : Finset ℕ → Fin k := fun U ↦ ⟨onat ↑(f (U.image σ)), onat_lt (f (U.image σ)).2⟩
    with hf'def
  obtain ⟨i, X, hXsub, hXcard, hXmono⟩ := h f'
  refine ⟨⟨(i : ℕ), Set.mem_Iio.2 (by exact_mod_cast i.isLt)⟩, ↑(X.image σ), ?_, ?_, ?_⟩
  · -- the image lands inside `Vfull`
    rw [← hVfcoe]
    intro v hv
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hv
    exact hσmem m (Finset.mem_range.1 (hXsub hm))
  · -- and has the right cardinality
    have hmk : #(↑(X.image σ) : Set V) = ((X.image σ).card : Cardinal) :=
      Cardinal.mk_coe_finset
    rw [hmk, Finset.card_image_of_injOn (hinjOn hXsub), hXcard, hs' (i : ℕ) i.isLt]
  · -- monochromaticity transports back along the same enumeration
    intro T hT hTcard
    set U : Finset ℕ := X.filter (σ · ∈ T) with hUdef
    have hUX : U ⊆ X := Finset.filter_subset _ _
    have hUT : U.image σ = T := by
      ext v
      constructor
      · intro hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hv
        exact (Finset.mem_filter.1 hm).2
      · intro hv
        obtain ⟨m, hm, hmv⟩ := Finset.mem_image.1 (by simpa using hT hv)
        exact Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨hm, hmv ▸ hv⟩, hmv⟩
    have : U.card = r := by
      rw [← hTcard, ← hUT, Finset.card_image_of_injOn (hinjOn (hUX.trans hXsub))]
    have := congrArg Fin.val (hXmono U hUX this)
    simp only [hf'def, hUT] at this
    exact Subtype.ext (by rw [← natCast_onat (f T).2, this])


open SteppingUp.Infinitary in
/-- **Transport, backwards.** Conversely, the abstract relation over a vertex
type with at least `n` elements gives the finitary one. The extra hypothesis
is unavoidable: `ArrowsTo V κ …` quantifies over subsets of `V` of size `κ`
and is vacuously true when there are none. -/
theorem arrow_of_arrowsTo {V : Type*} {n r k : ℕ} {s : Fin k → ℕ}
    {s' : Ordinal → Cardinal} (hn : 0 < n) (hV : n ≤ #V)
    (hs' : ∀ m (hm : m < k), s' m = s ⟨m, hm⟩)
    (h : ArrowsTo V (n : Cardinal) r (k : Ordinal) s') :
    Arrow n r k s := by
  classical
  intro f'
  obtain ⟨Vfull, hVfull⟩ := Cardinal.le_mk_iff_exists_set.1 hV
  obtain ⟨Vf, hVfcoe, hVfcard⟩ := exists_finset_of_mk_eq hVfull
  obtain ⟨σ, hσmem, hσinj, hσsurj⟩ := exists_enumeration hn hVfcard
  have hinjOn {U : Finset ℕ} (hU : U ⊆ Finset.range n) : Set.InjOn σ ↑U :=
    fun a ha b hb ↦ hσinj (Finset.mem_range.1 (hU ha)) (Finset.mem_range.1 (hU hb))
  -- Push `f'` forward along `σ`: a set of vertices is coloured by the set of
  -- indices naming it.
  set τ : Finset V → Finset ℕ := fun T ↦ (Finset.range n).filter (σ · ∈ T) with hτdef
  set f : Finset V → Set.Iio (k : Ordinal) :=
    fun T ↦ ⟨((f' (τ T) : ℕ) : Ordinal), Set.mem_Iio.2 (by exact_mod_cast (f' (τ T)).isLt)⟩ with hfdef
  obtain ⟨i, Y, hYsub, hYcard, hYmono⟩ := h Vfull hVfull f
  have hik : (i : Ordinal) < k := i.2
  -- The colour `i` lies below the natural bound `k`, so it *is* a natural cast;
  -- substituting for it here is what keeps `onat` out of the rest of the proof.
  obtain ⟨j, hj⟩ := exists_natCast_eq hik
  have hjk : j < k := by exact_mod_cast hj ▸ hik
  -- `Y` is a subset of `Vfull`, hence the `σ`-image of a subset of `range n`.
  have hYVf : Y ⊆ Vf := hVfcoe ▸ hYsub
  set X : Finset ℕ := (Finset.range n).filter (σ · ∈ Y) with hXdef
  have hXsub : X ⊆ Finset.range n := Finset.filter_subset _ _
  have hXimage : (X.image σ) = Y := by
    ext v
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hXdef, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨m, ⟨-, hmY⟩, rfl⟩; exact hmY
    · intro hv
      obtain ⟨m, hm, hmv⟩ := hσsurj v (by simpa using hYVf hv)
      exact ⟨m, ⟨hm, hmv ▸ hv⟩, hmv⟩
  -- Cardinalities match, so `X.card = s j`.
  have hXcard : X.card = s ⟨j, hjk⟩ := by
    have h1 : #((X.image σ) : Set V) = ((X.image σ).card : Cardinal) := Cardinal.mk_coe_finset
    rw [hXimage, Finset.card_image_of_injOn (hinjOn hXsub)] at h1
    exact_mod_cast h1.symm.trans (hYcard.trans (hj ▸ hs' j hjk))
  refine ⟨⟨j, hjk⟩, X, hXsub, hXcard, ?_⟩
  -- Monochromaticity transports back.
  intro U hUX hUcard
  have hUn : U ⊆ Finset.range n := hUX.trans hXsub
  have hτU : τ (U.image σ) = U := by
    ext m
    simp only [hτdef, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hmn, m', hm', hm'eq⟩
      rwa [← hσinj (Finset.mem_range.1 (hUn hm')) hmn hm'eq]
    · intro hm
      exact ⟨Finset.mem_range.1 (hUn hm), m, hm, rfl⟩
  have hsub : ↑(U.image σ) ⊆ Y := by
    rw [← hXimage]
    exact_mod_cast Finset.image_subset_image hUX
  have hcard : (U.image σ).card = r := by
    rw [Finset.card_image_of_injOn (hinjOn hUn), hUcard]
  have := congrArg Subtype.val (hYmono (U.image σ) hsub hcard)
  simp only [hfdef, hτU] at this
  exact Fin.val_injective (by exact_mod_cast hj ▸ this)


end «The transport»

section «Target sizes as an ordinal-indexed family»

/-- The `Fin k`-indexed target sizes, as the `Ordinal`-indexed family of
`Cardinal`s that `ArrowsTo` expects. Junk (`0`) at and above `k`. -/
noncomputable def ordSizes {k : ℕ} (s : Fin k → ℕ) (j : Ordinal) : Cardinal :=
  if h : j < (k : Ordinal) then (s ⟨onat j, onat_lt h⟩ : Cardinal) else 0

lemma ordSizes_natCast {k : ℕ} (s : Fin k → ℕ) (m : ℕ) (hm : m < k) :
    ordSizes s (m : Ordinal) = (s ⟨m, hm⟩ : Cardinal) := by
  simp [ordSizes, hm]

/-- Any finitary size family of `stepSizes` shape matches `stepSizes` under
`ordSizes`. All three cases below are instances, differing only in the colour
count `K` and the value taken on the new colours. -/
lemma stepSizes_ordSizes_of {r k K : ℕ} (s : Fin k → ℕ) {t : Fin K → ℕ}
    (ht : ∀ (m : ℕ) (hm : m < K), t ⟨m, hm⟩ = if h : m < k then s ⟨m, h⟩ + 1 else r + 2)
    (m : ℕ) (hm : m < K) :
    Infinitary.stepSizes r (k : Ordinal) (ordSizes s) (m : Ordinal)
      = (t ⟨m, hm⟩ : Cardinal) := by
  rw [ht m hm]
  by_cases hmk : m < k <;>
    simp [Infinitary.stepSizes, ordSizes, hmk]

lemma stepSizes_ordSizes {r k : ℕ} (s : Fin k → ℕ) (m : ℕ) (hm : m < k + 1) :
    Infinitary.stepSizes r k (ordSizes s) m = stepSizesEtaOne r s ⟨m, hm⟩ :=
  stepSizes_ordSizes_of s (fun _ _ ↦ rfl) m hm

lemma stepSizes_ordSizes_r4 {k : ℕ} (s : Fin k → ℕ) (m : ℕ) (hm : m < k + 2) :
    Infinitary.stepSizes 4 k (ordSizes s) m = stepSizesR4 s ⟨m, hm⟩ :=
  stepSizes_ordSizes_of s (fun _ _ ↦ rfl) m hm

lemma stepSizes_ordSizes_r3 {k : ℕ} (s : Fin k → ℕ) (m : ℕ) (hm : m < k + 1) :
    Infinitary.stepSizes 3 k (ordSizes s) m = stepSizesR3 s ⟨m, hm⟩ :=
  stepSizes_ordSizes_of s (fun _ _ ↦ rfl) m hm

end «Target sizes as an ordinal-indexed family»

end Transport

section «The finitary stepping-up lemmas»

/-! These carry the names the rest of the development and the paper use. Their
statements are unchanged from the superseded finitary constructions; only the
proofs are different, and their axiom footprints are identical. -/

open Transport

/-- The transport shell shared by the three theorems below. They differ only in
the uniformity `r`, the stepped colour count `K`, the size family `t`, and which
infinitary theorem is applied; everything here — the round trip through
`ArrowsTo`, the `ℕ`-to-`Cardinal`/`Ordinal` bookkeeping, and the fact that the
ordinals are large enough to host the base relation — is common to all three.

The infinitary theorem is a parameter rather than a fixed reference because the
three have different signatures: `r` is a variable in one and fixed in the other
two. `kO` is the stepped colour count as an *ordinal*, supplied by that
theorem's conclusion; `hK` is the one cast that depends on how many new colours
the case introduces. -/
private lemma of_infinitary {k n r K : ℕ} {kO : Ordinal.{0}} {s : Fin k → ℕ} {t : Fin K → ℕ}
    (hn : r < n) (hK : ((K : ℕ) : Ordinal.{0}) = kO)
    (ht : ∀ (m : ℕ) (hm : m < K),
      SteppingUp.Infinitary.stepSizes r (k : Ordinal.{0}) (ordSizes s) (m : Ordinal.{0})
        = (t ⟨m, hm⟩ : Cardinal.{1}))
    (hinf : ¬ SteppingUp.Infinitary.ArrowsTo Ordinal.{0} (n : Cardinal.{1}) r (k : Ordinal.{0})
                (ordSizes s) →
            ¬ SteppingUp.Infinitary.ArrowsTo (Set Ordinal.{0}) (2 ^ n) (r + 1) kO
                (SteppingUp.Infinitary.stepSizes r (k : Ordinal.{0}) (ordSizes s)))
    (h : ¬ Arrow n r k s) :
    ¬ Arrow (2 ^ n) (r + 1) K t := by
  intro hcon
  -- Transport the stepped-up relation into the abstract setting.
  have hup := arrowsTo_of_arrow (V := Set Ordinal.{0}) (by positivity) ht hcon
  rw [show ((2 ^ n : ℕ) : Cardinal.{1}) = 2 ^ (n : Cardinal.{1}) by
      simp [Cardinal.power_natCast], hK] at hup
  -- The infinitary theorem, contrapositively, gives the abstract relation at
  -- the base level, which transports back down.
  refine h (arrow_of_arrowsTo (V := Ordinal.{0}) (by omega) ?_ (ordSizes_natCast s) ?_)
  · exact le_of_lt (Cardinal.natCast_lt_aleph0.trans_le
      (Cardinal.aleph0_le_mk_iff.2 inferInstance))
  · exact by_contra (hinf · hup)

/-- **The finitary stepping-up lemma with `η(r) = 1` for `r ≥ 5`**, obtained
from `SteppingUp.Infinitary.stepping_up_eta_one` by transport rather than by a
separate finitary construction.

New here: for `r ≥ 5`, JKSY pay `η(r) = 2` for odd `r` and `3` for even `r`.

The universes are pinned to `Ordinal.{0}`: the finitary statement mentions no
universes, so one instance of the infinitary theorem is all that is needed,
and leaving them open only produces unsolvable universe metavariables. -/
theorem stepping_up_eta_one (k n r : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hr : 5 ≤ r) (hn : r < n)
    (hs : ∀ i, r + 1 ≤ s i)
    (h : ¬ Arrow n r k s) :
    ¬ Arrow (2 ^ n) (r + 1) (k + 1) (stepSizesEtaOne r s) :=
  of_infinitary hn (by simp) (stepSizes_ordSizes s)
    (SteppingUp.Infinitary.stepping_up_eta_one (n : Cardinal.{1}) r (k : Ordinal.{0})
      (ordSizes s) (by exact_mod_cast hk) hr
      (fun _ hi ↦ by simp [ordSizes, hi, Nat.lt_of_succ_le, hs])) h

/-- **The finitary stepping-up lemma with `η(4) = 2`**, by transport.

New here: JKSY pay `η(4) = 3`. -/
theorem stepping_up_eta_two_r4 (k n : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hn : 4 < n)
    (hs : ∀ i, 5 ≤ s i)
    (h : ¬ Arrow n 4 k s) :
    ¬ Arrow (2 ^ n) 5 (k + 2) (stepSizesR4 s) :=
  of_infinitary hn (by simp) (stepSizes_ordSizes_r4 s)
    (SteppingUp.Infinitary.stepping_up_eta_two_r4 (n : Cardinal.{1}) (k : Ordinal.{0})
      (ordSizes s) (by exact_mod_cast hk)
      (fun _ hi ↦ by simp [ordSizes, hi, hs])) h

/-- **The finitary stepping-up lemma with `η(3) = 1`**, by transport.

This one is JKSY's own result, not an improvement on it: they already have
`η(3) = 1`. It is reproved here by the same machinery as `r = 4` and
`r ≥ 5`, so that the three cases are established uniformly. -/
theorem stepping_up_eta_one_r3 (k n : ℕ) (s : Fin k → ℕ)
    (hk : 2 ≤ k) (hn : 3 < n)
    (hs : ∀ i, 4 ≤ s i)
    (h : ¬ Arrow n 3 k s) :
    ¬ Arrow (2 ^ n) 4 (k + 1) (stepSizesR3 s) :=
  of_infinitary hn (by simp) (stepSizes_ordSizes_r3 s)
    (SteppingUp.Infinitary.stepping_up_eta_one_r3 (n : Cardinal.{1}) (k : Ordinal.{0})
      (ordSizes s) (by exact_mod_cast hk)
      (fun _ hi ↦ by simp [ordSizes, hi, hs])) h

end «The finitary stepping-up lemmas»

end SteppingUp
