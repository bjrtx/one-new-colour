/-
  The cases `r = 3` and `r = 4`: valid colourings `c3` (`isValidAt_c3`, one
  new colour) and `c4` (`isValidAt4_c4`, two new colours; the paper's
  `prop:r4`), each checked by `decide` over the structurally recursive
  enumeration `treesL`. Only the `r = 4` half is new; `η(3) = 1` is JKSY's.
  `Bridge.lean` and
  `Infinitary.lean` turn them into `stepping_up_eta_two_r4` and
  `stepping_up_eta_one_r3`.
-/
import SteppingUpLemma.Colouring.Basic

namespace SteppingUp.Trees
open BinaryTree

section «The exceptional case r = 4»

/-! Unlike `r ≥ 5`, the colouring here does *not* factor through folded classes
(as a table does in `def:valid`): the two trees `«🤚» = .nil △ fourLeaves` and
`«🖖» = fourLeaves △ .nil` share the same core-derived class
`(2, 2, false, true, true)` (their core is `fourLeaves`'s own, reached
by peeling the lone extra leaf) but must receive *different* colours in the
two-new-colour construction below. Everything in this section therefore
works directly with `Tree → EtaColour`-valued functions (already exactly
what `sSet`/`IsValidAt` accept) or with a dedicated `4`-colour type, never
through a class-valued table/`treeColour`. -/


/-! #### The trees used in `prop:r4` -/

@[match_pattern] private abbrev «🍒» := .nil △ .nil
@[match_pattern] private abbrev «🍁🍒» := .nil △ «🍒»
@[match_pattern] private def «🍒🍁» := «🍒» △ .nil
@[match_pattern] private abbrev «🍒🍒» := «🍒» △ «🍒»
@[match_pattern] private abbrev «🤚» := .nil △ «🍒🍒»
@[match_pattern] private abbrev «🖖» := «🍒🍒» △ .nil
@[match_pattern] private def «🍒(🍁🍒)» := «🍒» △ «🍁🍒»
@[match_pattern] private def «🍒(🍒🍁)» := «🍒» △ «🍒🍁»
@[match_pattern] private def «(🍁🍒)🍒» := «🍁🍒» △ «🍒»
@[match_pattern] private def «(🍒🍁)🍒» := «🍒🍁» △ «🍒»


inductive Colour4 where
  | c0 | c1 | n0 | n1
  deriving DecidableEq

/-- The colours seen among `T`'s proper one-deletions. -/
def sSet4 (c : Tree → Colour4) (T : Tree) : Finset Colour4 :=
  ∂T |>.filter (·.core.isSome) |>.toFinset.image c

/-- The `Colour4` analogue of `IsValidAt`, for the two-new-colour case
`r = 4`: every proper tree sees `≥ 2` proper colours, or exactly one of
the two new colours together with a degenerate tree deletion. -/
def IsValidAt4 (c : Tree → Colour4) (r : ℕ) : Prop :=
  ∀ T, #T = r + 2 → T.core.isSome →
    2 ≤ (sSet4 c T).card ∨
      ((Colour4.n0 ∈ sSet4 c T ∨ Colour4.n1 ∈ sSet4 c T) ∧ hasDegenerateDel T)

def c4 : Tree → Colour4
  | «🤚» | «(🍁🍒)🍒» | «(🍒🍁)🍒» => .n0
  | «🖖» | «🍒(🍁🍒)» | «🍒(🍒🍁)» => .n1
  | _ => .c0

/-- `prop:r4`: `c4` is valid at level `4`, using two
colours outside `{c0, c1}`. -/
theorem isValidAt4_c4 : IsValidAt4 c4 4 := by
  have hcheck : ∀ {T}, T ∈ treesL 6 → T.core.isSome →
      2 ≤ (sSet4 c4 T).card ∨
        ((.n0 ∈ sSet4 c4 T ∨ .n1 ∈ sSet4 c4 T) ∧ hasDegenerateDel T) := by
    decide
  exact fun T _ ↦ hcheck ((by omega : #T = 6) ▸ mem_treesL T)


/-! #### `r = 3`: `η(3) = 1` -/

def c3 : Tree → EtaColour | «🍒🍒» => .cN | _ => .c0

theorem isValidAt_c3 : IsValidAt c3 3 := by
  have hcheck : ∀ {T} , T ∈ treesL 5 → T.core.isSome →
      2 ≤ (sSet c3 T).card ∨ (EtaColour.cN ∈ sSet c3 T ∧ hasDegenerateDel T) := by
    decide
  exact fun T _  ↦ hcheck ((by omega : #T = 5) ▸ mem_treesL T)

end «The exceptional case r = 4»

end SteppingUp.Trees
