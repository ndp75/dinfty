import Dinfty.AssemblyChain

open GluingTowerLibrary SierpinskiApplication

/-!
# Piping `colimit_compat`: two of the three open `Prop`s discharged

`Dinfty/AssemblyChain.lean` reduced pillar B to three named `Prop`s and called
two of them "expected to be routine". That was an untested claim. This module
tests it: **`StageJoinRecoverable` and `StageSupClosed` are both proved here**,
outright, leaving `JoinIrredStagePreserved` as the *single* remaining gap
between the library and `colimit_compat`.

## What the chain looks like now

    JoinIrredStagePreserved            -- the ONLY open link; NoCrossFiberTie's consumer
      ⟹ StageDefinable                 -- AssemblyChain.stageDefinable_of
      ⟹ Subsingleton (DInfty ≃o DInfty)-- Assembly.colimit_rigid_of_stageDefinable
      ⟹ Subsingleton (DBilimit ≃o DBilimit)

and `colimit_compat` itself — the biconditional
`Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k)` — follows,
since its forward direction is `D_all_rigid`, already unconditional.

## What made the two `Prop`s routine after all

Three facts that were already on file and had not been put together:

* `finite_lattice_eq_sup_joinIrreds` (`GluingTowerLibrary.lean:2339`) — every
  element of a finite lattice is the join of the join-irreducibles below it.
  `StageJoinRecoverable` is that statement transported along `toD k`.
* `toD_sup'` — `toD k` preserves binary joins, so it preserves finite ones by
  `Finset` induction.
* `glueA_bot` — `glueA m ⊥ = ⊥` by `rfl`, which gives `iotaD_bot`, hence
  `iotaLe_bot`, hence `toD_bot_le`: **`toD k ⊥` is a least element of `DInfty`**.
  That last one is what makes the empty-`Finset` base case go through, and
  `DInfty` carries no `OrderBot` instance, so it had to be proved by hand.

## The residue, stated exactly

`JoinIrredStagePreserved` says an automorphism of `DInfty` carries each stage's
join-irreducibles to join-irreducibles *of that same stage*. That is where
`NoCrossFiberTie` is meant to enter, and it is open — known **false** for
arbitrary `P` (handoff §7a's 12-element counterexample), open for `P := D_k`.

Nothing here narrows that gap. What it does is remove every other obstacle
between it and pillar B's conclusion, so a future session can work on one thing.

**And the shape of that one thing is now sharper.** The naive route — "apply
`NoCrossFiberTie` to `DInfty`" — is not merely unproven, it does not typecheck:
`sig3` and `NoCrossFiberTie` live under `variable [Fintype P]`
(`S5Invariant.lean:482`), and `DInfty` carries no `Fintype` instance. So the
route has to transfer a *finite-level* invariant to a statement about a `DInfty`
automorphism. Each stage is finite (`stage_finite` below), so signatures are
computable *on a stage*; what is not available is computing down-sets and
up-sets in `DInfty` itself. That is the same wall the handoff records as
"bottoms out in the values `up_EndP(D_1)` achieves", now located precisely.
-/

open scoped Classical

namespace ColimitCompatPipe

open Assembly AssemblyChain

/-! ## `toD k ⊥` is a least element of `DInfty` -/

/-- `iotaD` preserves `⊥`.  `⊥ : EndP (D k)` is the constant-`⊥` map, and
`glueA m ⊥ = ⊥` by `rfl` (`glueA_bot`). -/
theorem iotaD_bot (k : ℕ) : iotaD k (⊥ : D k) = (⊥ : D (k + 1)) := by
  first
    | rfl
    | (apply Subtype.ext; rfl)
    | (apply Subtype.ext
       show (Sum.inl (constHom (⊥ : D k)) : GlueBase (EndP (D k)))
         = Sum.inl (⊥ : EndP (D k))
       congr 1
       ext x
       rfl)

theorem iotaLe_bot {k n : ℕ} (h : k ≤ n) : iotaLe h (⊥ : D k) = (⊥ : D n) := by
  induction n, h using Nat.le_induction with
  | base => exact iotaLe_self _ _
  | succ m hm ih =>
      rw [iotaLe_succ hm (Nat.le_succ_of_le hm), ih, iotaD_bot]

/-- **`DInfty` has a least element after all** — it just carries no `OrderBot`
instance.  Needed for the empty-`Finset` base case below. -/
theorem toD_bot_le (k : ℕ) (z : DInfty) : toD k (⊥ : D k) ≤ z := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨n, y⟩ := p
    show toD k (⊥ : D k) ≤ toD n y
    rw [toD_le_iff k n (⊥ : D k) y (le_max_left k n) (le_max_right k n), iotaLe_bot]
    exact bot_le

/-! ## `toD k` preserves finite joins -/

/-- Finite-join transport, in the form the two `Prop`s need. -/
theorem toD_sup_le (k : ℕ) (w : DInfty) :
    ∀ T : Finset (D k), (∀ y ∈ T, toD k y ≤ w) → toD k (T.sup id) ≤ w := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using toD_bot_le k w
  | @insert a T _ha ih =>
      intro hw
      have h1 : toD k a ≤ w := hw a (Finset.mem_insert_self a T)
      have h2 : toD k (T.sup id) ≤ w := ih (fun y hy => hw y (Finset.mem_insert_of_mem hy))
      rw [Finset.sup_insert, show (id a ⊔ T.sup id) = a ⊔ T.sup id from rfl, ← toD_sup']
      exact sup_le h1 h2

/-! ## The two `Prop`s -/

/-- **`StageJoinRecoverable`, proved.**  It is
`finite_lattice_eq_sup_joinIrreds` transported along `toD k`. -/
theorem stageJoinRecoverable : StageJoinRecoverable := by
  intro k x
  have hx : x = (Finset.univ.filter (fun q : D k => JoinIrred (D k) q ∧ q ≤ x)).sup id :=
    finite_lattice_eq_sup_joinIrreds x
  constructor
  · rintro z ⟨y, _hy, _hyz, hle⟩
    exact hle
  · intro w hw
    rw [hx]
    refine toD_sup_le k w _ ?_
    intro y hy
    have hy' : JoinIrred (D k) y ∧ y ≤ x := (Finset.mem_filter.mp hy).2
    exact hw ⟨y, hy'.1, rfl, (toD_le_iff' k y x).mpr hy'.2⟩

/-- **`StageSupClosed`, proved.**  The stage is the image of a `Fintype`, so the
supremum of any sub-collection is computed by a `Finset.sup` inside `D k`. -/
theorem stageSupClosed : StageSupClosed := by
  intro k S z hS hz
  refine ⟨(Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id, ?_⟩
  have hle : toD k ((Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id) ≤ z :=
    toD_sup_le k z _ (fun y hy => hz.1 (Finset.mem_filter.mp hy).2)
  have hub : ∀ w ∈ S, w ≤ toD k ((Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id) := by
    intro w hw
    obtain ⟨y, rfl⟩ := hS w hw
    refine (toD_le_iff' k y _).mpr ?_
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hw⟩)
  exact le_antisymm hle (hz.2 hub)

/-- Each stage is a finite subset of `DInfty` — so a signature *can* be computed
on a stage.  What is unavailable is computing one in `DInfty`. -/
theorem stage_finite (k : ℕ) : (Set.range (toD k)).Finite := Set.finite_range _

/-! ## The chain, with one link left -/

/-- **Pillar B, modulo a single `Prop`.** -/
theorem colimit_rigid_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_rigid_of_stageDefinable
    (stageDefinable_of h1 stageJoinRecoverable stageSupClosed)

theorem DBilimit_rigid_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_chain h1 stageJoinRecoverable stageSupClosed

/-- **`colimit_compat` itself**, reduced to `JoinIrredStagePreserved`.  The
forward direction is `D_all_rigid` and needs no hypothesis at all. -/
theorem colimit_compat_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k) :=
  ⟨fun _ _ => D_all_rigid _, fun _ => colimit_rigid_of_joinIrredStagePreserved h1⟩

/-- And the headline, with `DBilimit_rigid_of_colimit_compat`'s hypothesis
discharged from the same single `Prop`. -/
theorem DBilimit_rigid_of_joinIrredStagePreserved' (h1 : JoinIrredStagePreserved) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_colimit_compat (colimit_compat_of_joinIrredStagePreserved h1)

end ColimitCompatPipe
