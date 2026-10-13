/-
  Enumerations backing the numbers the paper quotes.

  This module is deliberately **not** imported by `SteppingUpLemma.lean`:
  everything below is a `#eval`, which prints during elaboration, and nothing
  here is used by any proof. Run it on its own with

      lake env lean SteppingUpLemma/Colouring/Enumerations.lean

  It backs three of the paper's computational claims.

  * The proof of `thm:stab` claims every value of the pair `([core T ≟ ∅], E(T))` is
    already realised by `p = 7` leaves, "once parity is accounted for".
    `sigReport` prints the least `p ≥ 5` of *each parity* realising each
    value, and the values realised at each `p`. Its output is the table in
    the proof of `thm:stab`, including the entry that forces the threshold:
    `(⊥, {⊥})` first occurs at even `p = 6` but at odd `p = 7`, and
    the bound of `16 = 7 + 7 + 2` leaves is that odd entry doubled.

  * `thm:C` says `Prof(p)` stabilises at `37` elements from `p = 10`.
    `profCountReport` recomputes `|Prof(p)| = 2, 4, 9, 17, 25, 33, 37` for
    `p = 4, …, 10` from the trees themselves, and `profTable` prints
    `Prof(p)` in full for small `p`.

  * `sec:Ccount` quotes `|𝒞_{≤14}| = 621`. Two routes are here, side by side in
    `genConstraintReport`: `constraintsAt` reads the constraints straight off
    the proper trees, which runs out around `r = 9`, and is printed as the
    `tree` column; the report itself generates them from the bounded
    representatives through `classReduction`, which is `lem:B`'s formula, and
    reaches `r = 14`. The two agree on every level where both run
    (`|𝒞_r| = 20, 46, 94, 162, 239` for `r = 5..9`), and the generator gives
    `|𝒞_{≤13}| = 620` and `|𝒞_{≤14}| = 621`. `cSetUpTo` prints the 621
    constraints themselves, which is where the paper's appendix comes from.

  Enumeration here goes into a `List` rather than a `Finset`, which would be
  noncomputable; `treeCountCheck` confirms the counts are the Catalan
  numbers, i.e. that this enumeration is the same one.
-/
import SteppingUpLemma.Colouring.Basic

namespace SteppingUp.Trees.Enumerations

open SteppingUp.Trees BinaryTree

/-! ### A computable enumeration of trees -/

/-! `treeLevels` now lives in `SteppingUpLemma.Tree`, where the `r = 3, 4`
checks need it to be kernel-reducible; this module just reads it. -/
/-- The trees on `p` leaves, read off a precomputed `treeLevels`. -/
def treesAt (lv : List (List Tree)) (p : ℕ) : List Tree := lv.getD (p - 1) []

/-! ### Printable forms

`Prof` and `Signature` carry no `Repr`, and `Option` of a nested product will
not synthesise `DecidableEq`, so we render everything to `String` and
deduplicate there. -/

/-- An `Signature` as the tuple `(a, b, λ, ρ, δ)` the paper writes. -/
def clsStr (c : Signature) : String :=
  let b (x : Bool) := if x then "⊤" else "⊥"
  s!"({c.a}, {c.b}, {b c.lam}, {b c.rho}, {b c.delta})"

/-- A `Prof` as `(E, folded class)`. -/
def profStr (π : Prof) : String :=
  let e := match π.anyNone, π.anySome with
    | true,  true  => "{⊥,⊤}"
    | true,  false => "{⊤}"
    | false, true  => "{⊥}"
    | false, false => "{}"
  match π.cls with
  | none   => s!"({e}, ⊥)"
  | some c => s!"({e}, {clsStr c})"

/-! ### The pair `([core T ≟ ∅], E(T))`

`E(T)` collects `[core T' ≟ ∅]` over the one-leaf deletions `T'` of `T`, so
`⊤ ∈ E(T)` says some deletion is degenerate and `⊥ ∈ E(T)` says some deletion
is proper. -/

/-- The paper's `([core T ≟ ∅], E(T))`, rendered. -/
def sigStr (T : Tree) : String :=
  let π := prof T
  let e := match π.anyNone, π.anySome with
    | true,  true  => "{⊥,⊤}"
    | true,  false => "{⊤}"
    | false, true  => "{⊥}"
    | false, false => "{}"
  s!"({if T.core.isNone then "⊤" else "⊥"}, {e})"

/-- The distinct values of `sigStr` over all trees on `p` leaves. -/
def sigsAt (lv : List (List Tree)) (p : ℕ) : List String :=
  ((treesAt lv p).map sigStr).dedup

/-- Every value realised on at most `n` leaves. -/
def sigsUpTo (lv : List (List Tree)) (n : ℕ) : List String :=
  (((List.range (n + 1)).filter (2 <= ·)).flatMap (sigsAt lv)).dedup

/-- The least number of leaves `p ≥ 5` of a given parity realising a given
value.

`(fold p, fold (p-1))` depends only on the parity of `p` once `p ≥ 5`, so the
reduction of a configuration to a smaller one moves `p` down by two at a time
and cannot go below `5`. What bounds the reduction is therefore the least
`p ≥ 5` of *each* parity realising a value, not the least `p` outright. -/
def leastLeaves (lv : List (List Tree)) (s : String) (par bound : ℕ) : Option ℕ :=
  ((List.range (bound + 1)).filter fun p => 5 ≤ p ∧ p % 2 = par).find?
    (sigsAt lv · |>.contains s)

/-- `Prof(p)`, deduplicated. -/
def profsAt (lv : List (List Tree)) (p : ℕ) : List String :=
  ((treesAt lv p).map (profStr ∘ prof)).dedup

/-! ### The constraint set `𝒞_r`

`𝒞_r = {(S(T), ad(T)) : T a proper (r+2)-tree}` and
`𝒞_{≤R} = ⋃_{5 ≤ r ≤ R} 𝒞_r`. The paper quotes `|𝒞_{≤14}| = 621`.

`sClasses` is a `Finset`, so to render it we filter the (finite) universe of
folded classes by membership rather than converting it to a list. -/

/-- Every conceivable folded class: `a, b ∈ {2,3,4,5}` and three Booleans. -/
def allClasses : List Signature :=
  (List.range 4).flatMap fun a => (List.range 4).flatMap fun b =>
    [true, false].flatMap fun l => [true, false].flatMap fun r =>
      [true, false].map fun d => ⟨a + 2, b + 2, l, r, d⟩

/-- The constraint `(S(T), ad(T))` a single proper tree imposes, rendered. -/
def constraintStr (T : Tree) : String :=
  let sc := sClasses T
  let s := (allClasses.filter (· ∈ sc)).map clsStr
  s!"({String.intercalate " " s}, {if hasDegenerateDel T then "⊤" else "⊥"})"

/-- `𝒞_r`, deduplicated: the proper trees on `r + 2` leaves. -/
def constraintsAt (lv : List (List Tree)) (r : ℕ) : List String :=
  (((treesAt lv (r + 2)).filter (·.core.isSome)).map constraintStr).dedup

/-! ### `𝒞_r` from bounded representatives

Generating from trees stops around `r = 9`. But `reduction_to_profiles` says

    classReduction (fold P) (fold (P-1)) [3 ≤ P] (fold Q) (fold (Q-1)) [3 ≤ Q]
                   (min M 2) (core L).isNone (core R).isNone (prof L) (prof R)
      = (S(T), ad(T))

whenever `core T = some (L, R)`, `#L = P`, `#R = Q` and `#T = P + Q + M`. So
`𝒞_r` is the image of that formula over `P, Q ≥ 2` with `P + Q ≤ r + 2`,
`M = r + 2 - P - Q`, and `π_L, π_R` ranging independently over `Prof(P)` and
`Prof(Q)` — a computation that does not touch a single tree above `11` leaves,
since `Prof(p) = Prof(10)` for every `p ≥ 10` (`profSet_stabilises`).

`genConstraintReport` checks this against the tree-derived counts before
trusting it. -/

/-- `Prof(p)` as values rather than strings, deduplicated on the rendering. -/
def profValsAt (lv : List (List Tree)) (p : ℕ) : List Prof :=
  ((treesAt lv p).map prof).foldl
    (fun acc π => if acc.any (fun q => profStr q == profStr π) then acc else acc ++ [π]) []

/-- `Prof(p)`, using stabilisation for `p ≥ 10` so no large level is needed. -/
def profFor (lv : List (List Tree)) (p : ℕ) : List Prof :=
  profValsAt lv (min 10 p)

/-- A constraint, rendered exactly as `constraintStr` renders a tree's. -/
def redStr (c : Finset CoreSignature × Bool) : String :=
  let s := (allClasses.filter (· ∈ c.1)).map clsStr
  s!"({String.intercalate " " s}, {if c.2 then "⊤" else "⊥"})"

/-- `𝒞_r`, generated from the representatives rather than from trees. -/
def genConstraintsAt (lv : List (List Tree)) (r : ℕ) : List String :=
  (((List.range (r + 3)).filter (2 ≤ ·)).flatMap fun P =>
    ((List.range (r + 3 - P)).filter (2 ≤ ·)).flatMap fun Q =>
      (profFor lv P).flatMap fun pl =>
        (profFor lv Q).map fun pr =>
          redStr (classReduction (fold P) (fold (P - 1)) (decide (3 ≤ P))
            (fold Q) (fold (Q - 1)) (decide (3 ≤ Q))
            (min (r + 2 - P - Q) 2) pl.cls.isNone pr.cls.isNone pl pr)).dedup

def genConstraintReport (lv : List (List Tree)) (check bound : ℕ) : IO Unit := do
  IO.println "-- 𝒞_r from representatives; `tree` column is the direct count --"
  let mut acc : List String := []
  for r in [5:bound + 1] do
    let cr := genConstraintsAt lv r
    acc := (acc ++ cr).dedup
    let tree := if r ≤ check then s!"{(constraintsAt lv r).length}" else "--"
    IO.println s!"  r = {r}: |𝒞_r| = {cr.length} (tree: {tree}), |𝒞_(≤{r})| = {acc.length}"

/-- The constraints of `𝒞_{≤bound}`, sorted, for printing as an appendix. -/
def cSetUpTo (lv : List (List Tree)) (bound : ℕ) : List String :=
  ((List.range (bound + 1)).filter (5 ≤ ·)).flatMap (genConstraintsAt lv) |>.dedup
    |>.mergeSort (· ≤ ·)

/-! ### Reports -/

def treeCountCheck (lv : List (List Tree)) (bound : ℕ) : IO Unit := do
  IO.println "-- number of trees on p leaves (should be Catalan (p-1)) --"
  for p in [1:bound + 1] do
    IO.println s!"  p = {p}: {(treesAt lv p).length}"

def sigReport (lv : List (List Tree)) (bound : ℕ) : IO Unit := do
  IO.println s!"-- ([core T ≟ ∅], E(T)) over trees on 2..{bound} leaves --"
  IO.println ""
  IO.println "value | least even p ≥ 5 | least odd p ≥ 5"
  for s in sigsUpTo lv bound do
    let fmt : Option ℕ → String := fun
      | some p => toString p
      | none   => "--"
    IO.println s!"  {s} | {fmt (leastLeaves lv s 0 bound)} | {fmt (leastLeaves lv s 1 bound)}"
  IO.println ""
  IO.println "values realised at each p:"
  for p in [2:bound + 1] do
    IO.println s!"  p = {p}: {String.intercalate ", " (sigsAt lv p)}"

def profCountReport (lv : List (List Tree)) (bound : ℕ) : IO Unit := do
  IO.println "-- |Prof(p)| recomputed from the trees on p leaves --"
  for p in [2:bound + 1] do
    IO.println s!"  |Prof({p})| = {(profsAt lv p).length}"

def profTable (lv : List (List Tree)) (p : ℕ) : IO Unit := do
  IO.println s!"-- Prof({p}), as (E, (a, b, λ, ρ, δ)) --"
  for π in (profsAt lv p).mergeSort (· ≤ ·) do
    IO.println s!"  {π}"

/-- Everything, against one shared enumeration. -/
def report (bound : ℕ) : IO Unit := do
  let lv := treeLevels bound
  treeCountCheck lv bound
  IO.println ""
  sigReport lv bound
  IO.println ""
  profCountReport lv bound
  IO.println ""
  profTable lv 6
  IO.println ""
  profTable lv 7

end SteppingUp.Trees.Enumerations

section «Run»
open SteppingUp.Trees SteppingUp.Trees.Enumerations
#eval report 11
#eval do
  let lv := treeLevels 11
  genConstraintReport lv 9 14
  IO.println ""
  IO.println "-- 𝒞_{≤14}, the paper's appendix --"
  for c in cSetUpTo lv 14 do IO.println s!"  {c}"
end «Run»
