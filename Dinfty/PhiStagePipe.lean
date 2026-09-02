import Dinfty.StageRigidity

open GluingTowerLibrary SierpinskiApplication

/-!
# Cleaning the residue: `PhiStageDefinable` down to one level-local `Prop`

§108 left `PhiStageDefinable` — *every automorphism of `B` carries each stage
into itself* — as the single open statement on pillar A's rigidity side.  This
module does to it what `ColimitCompatPipe` did to pillar B's chain: it discharges
everything except the one place where the mathematics is.

## The tool: `ins k` is a left adjoint

```lean
StageRigidity.ins_le_iff' (k) (a) (u) :  T.ins k a ≤ u  ↔  a ≤ u.1 k
```

One line in each direction (`ins_self`; `ins_monotone` then `ins_le_self`), and
it is the whole engine below: it turns every question about a stage point and an
arbitrary bilimit point into a question inside the *finite* level `k`.

## What it discharges

* **`stageSupClosed`** — a supremum of stage-`k` points is a stage-`k` point.
  The candidate is `ins k` of a `Finset.sup` inside `D (k+1)`; leastness is the
  adjunction.
* **`stageJoinRecoverable`** — every stage point is the supremum of the stage
  join-irreducibles below it: `finite_lattice_eq_sup_joinIrreds` transported by
  the adjunction.

Both are the `B`-side analogues of `ColimitCompatPipe.stageSupClosed` and
`stageJoinRecoverable`, and both were *harder* there — `toD` needed
`toD_bot_le` proved by hand because `DInfty` carries no `OrderBot`.  Here the
adjunction gives the empty case for free.

## What is unconditional, and what is left

The stages of `B` are exactly its compact elements:

```lean
omegaCompact_iff_stage (z) : OmegaCompact z ↔ ∃ k y, insD k y = z
```

(`←` is `BilimitGap.topB_omegaCompact`'s argument run at an arbitrary stage point
rather than only at `topB`; `→` is `chainSet_isLUB` plus antisymmetry.)
Compactness is order-theoretic, so **every automorphism of `B` already maps
stages into stages** (`stages_union_preserved`), with no hypothesis at all.

So the residue is not *whether* `θ` respects the filtration but **whether it
moves the index**, and that is all that is left:

```lean
PhiJoinIrredStagePreserved → PhiStageDefinable → Subsingleton (B ≃o B)
```

`PhiJoinIrredStagePreserved` is the exact mirror of pillar B's
`AssemblyChain.JoinIrredStagePreserved`, and it is level-local.
-/

open Set

open scoped Classical

namespace PhiStagePipe

open PhiIterateTower PhiBilimit EpPairTower StageRigidity BilimitGap

/-! ## 0.  The stage inclusion, with its domain spelled as a level

`phiTowerEP.carrier k` and `D (k + 1)` are definitionally equal, but instance
search does not unfold the projection, so `Finset.sup` and friends fail on the
first spelling.  `insD` fixes the spelling once. -/

/-- The stage-`k` inclusion `D (k+1) ↪ B`. -/
noncomputable def insD (k : ℕ) (y : D (k + 1)) : B := phiTowerEP.ins k y

theorem insD_le_iff (k : ℕ) (a : D (k + 1)) (u : B) : insD k a ≤ u ↔ a ≤ u.1 k :=
  StageRigidity.ins_le_iff' (T := phiTowerEP) k a u

theorem insD_monotone (k : ℕ) : Monotone (insD k) :=
  EpPairTower.ins_monotone (T := phiTowerEP) k

theorem insD_le_self (y : B) (k : ℕ) : insD k (y.1 k) ≤ y :=
  EpPairTower.ins_le_self (T := phiTowerEP) y k

/-! ## 1.  The two routine `Prop`s, discharged -/

/-- **Stage suprema stay in the stage.**  The `B`-side `StageSupClosed`. -/
theorem stageSupClosed (k : ℕ) (S : Set B) (z : B)
    (hS : ∀ w ∈ S, ∃ y : D (k + 1), insD k y = w) (hz : IsLUB S z) :
    ∃ y : D (k + 1), insD k y = z := by
  classical
  set T₀ : Finset (D (k + 1)) :=
    Finset.univ.filter (fun y : D (k + 1) => insD k y ∈ S) with hT₀
  refine ⟨T₀.sup id, ?_⟩
  have hlub : IsLUB S (insD k (T₀.sup id)) := by
    constructor
    · intro w hw
      obtain ⟨y, rfl⟩ := hS w hw
      exact insD_monotone k (Finset.le_sup (f := id)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hw⟩))
    · intro u hu
      refine (insD_le_iff k _ u).mpr (Finset.sup_le ?_)
      intro y hy
      have hyS : insD k y ∈ S := (Finset.mem_filter.mp hy).2
      exact (insD_le_iff k y u).mp (hu hyS)
  exact hlub.unique hz

/-- The set the recoverability statement is about: the stage join-irreducibles
below a stage point. -/
def stageJI (k : ℕ) (x : D (k + 1)) : Set B :=
  {z : B | ∃ y : D (k + 1), JoinIrred (D (k + 1)) y ∧ insD k y = z ∧ z ≤ insD k x}

/-- **Every stage point is the supremum of the stage join-irreducibles below
it.**  The `B`-side `StageJoinRecoverable`. -/
theorem stageJoinRecoverable (k : ℕ) (x : D (k + 1)) :
    IsLUB (stageJI k x) (insD k x) := by
  classical
  constructor
  · rintro z ⟨_, _, _, hle⟩
    exact hle
  · intro u hu
    refine (insD_le_iff k x u).mpr ?_
    have hx : x = (Finset.univ.filter (fun q : D (k + 1) =>
        JoinIrred (D (k + 1)) q ∧ q ≤ x)).sup id := finite_lattice_eq_sup_joinIrreds x
    rw [hx]
    refine Finset.sup_le ?_
    intro y hy
    obtain ⟨hji, hyx⟩ := (Finset.mem_filter.mp hy).2
    exact (insD_le_iff k y u).mp (hu ⟨y, hji, rfl, insD_monotone k hyx⟩)

/-! ## 2.  The stages are exactly the compact elements -/

-- `isLUB_bilim_apply` unfolds the tower's dcpo structure; the default budget is
-- not enough at a general level index.
set_option maxHeartbeats 1000000 in
/-- Every stage point is `ω`-compact — `BilimitGap.topB_omegaCompact`'s argument
at an arbitrary stage point.  The level is finite, so a monotone chain there
stabilises, and the adjunction moves the question to that level. -/
theorem insD_omegaCompact (k : ℕ) (x : D (k + 1)) : OmegaCompact (insD k x) := by
  intro c hc s hs hle
  have hdir : DirectedOn (· ≤ ·) (Set.range c) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨c (max a b), ⟨max a b, rfl⟩, hc (le_max_left a b), hc (le_max_right a b)⟩
  have hlvl := EpPairTower.isLUB_bilim_apply phiTowerEP_isDcpo hs ⟨c 0, 0, rfl⟩ hdir k
  have himg : ((fun z : B => z.1 k) '' Set.range c) = Set.range fun n => (c n).1 k := by
    rw [← Set.range_comp]
    rfl
  rw [himg] at hlvl
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => (c n).1 k, fun a b hab => (hc hab) k⟩ : ℕ →o D (k + 1))
  have hub : ∀ b ∈ Set.range fun n => (c n).1 k, b ≤ (c N).1 k := by
    rintro _ ⟨m, rfl⟩
    rcases le_total N m with hle' | hle'
    · exact le_of_eq (hN m hle').symm
    · exact (hc hle') k
  have hsk : s.1 k ≤ (c N).1 k := hlvl.2 hub
  exact ⟨N, (insD_le_iff k x (c N)).mpr (((insD_le_iff k x s).mp hle).trans hsk)⟩

/-- Conversely, a compact element is a stage point: it dominates a member of its
own approximating chain, and that member is below it. -/
theorem exists_stage_of_omegaCompact {z : B} (hz : OmegaCompact z) :
    ∃ (k : ℕ) (y : D (k + 1)), insD k y = z := by
  have hmono : Monotone (fun n => insD n (z.1 n)) :=
    fun a b h => EpPairTower.ins_chain_mono (T := phiTowerEP) z h
  have hlub : IsLUB (Set.range fun n => insD n (z.1 n)) z :=
    EpPairTower.chainSet_isLUB (T := phiTowerEP) z
  obtain ⟨n, hn⟩ := hz _ hmono z hlub le_rfl
  exact ⟨n, z.1 n, le_antisymm (insD_le_self z n) hn⟩

/-- **The stages of `B` are exactly its compact elements.** -/
theorem omegaCompact_iff_stage (z : B) :
    OmegaCompact z ↔ ∃ (k : ℕ) (y : D (k + 1)), insD k y = z :=
  ⟨exists_stage_of_omegaCompact, fun ⟨k, y, hy⟩ => hy ▸ insD_omegaCompact k y⟩

/-- **Unconditional: every automorphism of `B` maps stages into stages.**  What
it does *not* say — and what the residue is — is that the index cannot move. -/
theorem stages_union_preserved (θ : B ≃o B) (k : ℕ) (x : D (k + 1)) :
    ∃ (n : ℕ) (y : D (n + 1)), θ (insD k x) = insD n y := by
  obtain ⟨n, y, hy⟩ := exists_stage_of_omegaCompact ((insD_omegaCompact k x).map θ)
  exact ⟨n, y, hy.symm⟩

/-! ## 3.  RETIRED: the join-irreducible route

This module originally reduced `PhiStageDefinable` to a
`PhiJoinIrredStagePreserved`, mirroring `AssemblyChain.JoinIrredStagePreserved`.
`StageEmbedding.stage_map_exists` then reduced `PhiStageDefinable` to a
**finite** statement directly, routing around it, and nothing ever consumed the
join-irreducible Prop.  It has been deleted rather than left standing: an open
`Prop` with no consumer is debt, not progress.

`stageSupClosed` and `stageJoinRecoverable` above are kept — they are proved,
cheap, and are the `B`-side analogues of `ColimitCompatPipe`'s two lemmas — but
the live chain does not use them either.  What the live chain does use from this
module is `omegaCompact_iff_stage` and `stages_union_preserved`. -/

/-! ## 4.  What the residue is already pinned at

`stages_union_preserved` says `θ` cannot leave the filtration; these two say it
cannot move the two ends of any stage.  So the residue lives strictly in the
*interior* of the stages. -/

theorem apply_insD_bot (θ : B ≃o B) (k : ℕ) : θ (insD k ⊥) = insD k ⊥ := by
  rw [show insD k (⊥ : D (k + 1)) = (⊥ : B) from PhiBilimit.ins_bot k]
  exact θ.map_bot

theorem apply_insD_top (θ : B ≃o B) (k : ℕ) : θ (insD k ⊤) = insD k ⊤ := by
  rw [show insD k (⊤ : D (k + 1)) = (⊤ : B) from PhiBilimit.ins_top k]
  exact θ.map_top

end PhiStagePipe
