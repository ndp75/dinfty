import Dinfty.Assembly

open GluingTowerLibrary SierpinskiApplication

/-!
# The rest of pillar B's chain, compiled

`Dinfty/Assembly.lean` formalized handoff §3: `StageDefinable` implies
`Subsingleton (DInfty ≃o DInfty)`.  This module writes down what `StageDefinable`
itself reduces to — Angle A's sub-problems — as named `Prop`s, and proves the
reduction.

**Correction to `Assembly.lean`'s docstring.**  It asserts that
`NoCrossFiberTie` "has no Lean statement".  **That is false.**
`S5Invariant.lean:586` carries

    def NoCrossFiberTie : Prop :=
      ∀ x x' : {x : P // JoinIrred P x}, x ≠ x' → ∀ q' : P, q' ≠ ⊥ →
        sig3 (⊥ : P) x ≠ sig3 q' x'

deliberately as a `def` rather than a `theorem`, because it is *known false for
arbitrary `P`* and open for `P := D_k`.  The claim was produced by a truncated
grep and should not have been made.  What is genuinely missing is not the
statement but the **route**: nothing connects `NoCrossFiberTie` to
`StageDefinable`.  This module supplies the shape of that route.

## The chain

    NoCrossFiberTie (all k)          -- S5Invariant.lean:586, OPEN for D_k
        ⟹  JoinIrredStagePreserved   -- NOT written; the intended use of #1
        together with
           StageJoinRecoverable      -- sub-problem #3, clauses (3a)+(3c)
           StageSupClosed            -- stage suprema stay in the stage
        ⟹  StageDefinable            -- proved below
        ⟹  Subsingleton (DInfty ≃o DInfty)   -- Assembly.lean
        ⟹  Subsingleton (DBilimit ≃o DBilimit)

`stageDefinable_of` is the middle implication, and it is short: an automorphism
transports the supremum witnessing recoverability, sends stage join-irreducibles
to stage join-irreducibles, and stage-closure puts the result back in the stage.

## What each remaining `Prop` costs

* **`JoinIrredStagePreserved`** — the real work, and the intended consumer of
  `NoCrossFiberTie`: the `(down, up, rank)` signature is order-invariant, so if
  it separates stage-`k` join-irreducibles from later ones, an automorphism
  cannot move one to the other.  Writing that implication is the next task; it
  needs `sig3`'s components to be shown order-invariant *as computed in
  `DInfty`*, which is where `JoinIrredLevelStable` and the missing
  `DInfty`-level half of clause (3b) enter.
* **`StageJoinRecoverable`** — sub-problem #3.  Should follow from `D k` being a
  finite lattice plus `iotaD_sup`; not attempted here.
* **`StageSupClosed`** — should follow from `DInftySupRep_atLevel` plus
  finiteness of `D k`; not attempted here.

The last two were expected to be routine.  **They are: both are PROVED in
`Dinfty/ColimitCompatPipe.lean` (2026-08-28), so `JoinIrredStagePreserved` is
now the single open link between the library and `colimit_compat`.**  The first
is where the mathematics is.
-/

open scoped Classical

namespace AssemblyChain

open Assembly

/-- **What sub-problem #1 is for.**  An automorphism of `DInfty` carries each
stage's join-irreducibles to join-irreducibles of that same stage.

`NoCrossFiberTie` (`S5Invariant.lean:586`) is the intended route: its
`(down, up, rank)` signature is order-invariant, so separating stage-`k`
join-irreducibles from later ones prevents an automorphism from mixing them. -/
def JoinIrredStagePreserved : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), JoinIrred (D k) x →
    ∃ y : D k, JoinIrred (D k) y ∧ θ (toD k x) = toD k y

/-- **Sub-problem #3, clauses (3a)+(3c).**  Every stage element is the
`DInfty`-supremum of the stage join-irreducibles beneath it. -/
def StageJoinRecoverable : Prop :=
  ∀ (k : ℕ) (x : D k),
    IsLUB {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z ∧ z ≤ toD k x}
      (toD k x)

/-- **Stage suprema stay in the stage.**  Expected to follow from
`DInftySupRep_atLevel` and finiteness of `D k`. -/
def StageSupClosed : Prop :=
  ∀ (k : ℕ) (S : Set DInfty) (z : DInfty),
    (∀ w ∈ S, ∃ y : D k, toD k y = w) → IsLUB S z → ∃ y : D k, toD k y = z

/-- **The middle implication of pillar B's chain.**

Transport the recoverability supremum through `θ` (`OrderIso.isLUB_image'`),
observe that every member of the transported set is again a stage-`k` point
(that is exactly `JoinIrredStagePreserved`), and close under stage suprema. -/
theorem stageDefinable_of (h1 : JoinIrredStagePreserved)
    (h3 : StageJoinRecoverable) (hc : StageSupClosed) : StageDefinable := by
  intro θ k x
  have hlub : IsLUB {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z
      ∧ z ≤ toD k x} (toD k x) := h3 k x
  have himg : IsLUB (θ '' {z : DInfty | ∃ y : D k, JoinIrred (D k) y ∧ toD k y = z
      ∧ z ≤ toD k x}) (θ (toD k x)) := (OrderIso.isLUB_image' θ).mpr hlub
  obtain ⟨y, hy⟩ := hc k _ (θ (toD k x)) (by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨y0, hy0, hy0z, -⟩ := hz
    obtain ⟨y', -, hy'eq⟩ := h1 θ k y0 hy0
    exact ⟨y', by rw [← hy0z]; exact hy'eq.symm⟩) himg
  exact ⟨y, hy.symm⟩

/-- **Pillar B, fully assembled modulo three named `Prop`s.** -/
theorem DBilimit_rigid_of_chain (h1 : JoinIrredStagePreserved)
    (h3 : StageJoinRecoverable) (hc : StageSupClosed) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_stageDefinable (stageDefinable_of h1 h3 hc)

end AssemblyChain
