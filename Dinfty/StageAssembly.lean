import Dinfty.TwoPointAssembly

open GluingTowerLibrary SierpinskiApplication

/-!
# `StageFixed`, reduced from an arbitrary base stage

`TwoPointFixed` is only the `k = 0` slice of `StageFixed`, and `StageFixed` is
what `colimit_compat` actually needs (`StageFixed → JoinIrredStagePreserved →
colimit_compat`).  This module carries the `TwoPointAssembly` reduction from base
stage `0` to an arbitrary base stage `n`, and runs it at every point.

## What generalises for free

`TwoPointAssembly`'s copy-`A` exclusion compares `WeakProd (Fam 0) × T` with
`WeakProd (Fam (k+1)) × S_y` at the index `j = k`, so that `Fam 0 j` is `D k` and
the two finite pieces — an up-set and a level seed — are both strictly smaller
than it (`card_upSet_lt_D`, `card_levelSeed_lt`).  From base stage `n` the same
argument wants `Fam n j = D k`, i.e. `j = k - n`, available exactly when `n ≤ k`.
That is no restriction: the competitor sits at stage `k+1` and only stages
**above** the base are ever compared.

So `copyA_forces_bot_at` and `copyA_step_at` are the old proofs with `j = k`
replaced by `j = k - n`.

## `StageFixed` does not need the point pinned — only the stage

The first draft of this module asked for `BaseSeparation`: distinct
join-irreducibles of `D k` have non-isomorphic seeds.  **That is false**, already
at `k = 1`: among the sixteen join-irreducibles of `D 1` the seeds of

```
tag_A 2 ≅ tag_A 3      tag_B 2 ≅ tag_B 3      tag_C 2 ≅ tag_C 3
```

are genuinely isomorphic — verified by a backtracking isomorphism search, not
merely by an invariant (`_archive/check_base_separation_level1.py`).  `midInf`
and `topJ` are *not* involved, so `base_midInf` / `base_topJ` are unaffected.

The right observation is that `StageFixed` never needed it.  It asks only that
`θ (toD k x)` **lie in stage `k`**, not that it equal `toD k x`; and the copy-`A`
step already descends one stage at a time, so iterating it from `N` down to `k`
lands the competitor inside stage `k` whoever it is.  Hence

```lean
stageFixed_of : (∀ k x, JoinIrred x → CopyBCExcludedAt k (toD k x)) → StageFixed
```

— **one** hypothesis family, and no base case at all.

## What is left

`CopyBCExcludedAt k (toD k x)` is the copy-`B`/`C` exclusion demanded at every
stage-`k` join-irreducible rather than at the two special points.  It is strictly
stronger than `TwoPointAssembly.CopyBCExcludedFor` (`copyBCExcludedAt_zero_iff`
identifies the `k = 0` slice) and it is not proved.  What this module buys is
that `StageFixed` now has the *same shape* as `TwoPointFixed` with one family
instead of two, so the `PairFactor` / `TripleFactor` criteria — already stated
for an arbitrary left-hand piece — apply to it verbatim.

The stage comparison itself is free: `exists_stage` puts `θ (toD k x)` at some
stage `N`; if `N ≤ k` it is already inside stage `k` (`toD_iotaLe`), and if
`N > k` the descent brings it back.
-/

open scoped Classical

namespace StageAssembly

open TwoPointAssembly CopyAClassification SeedShapeProof SeedLevelStep
open WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis TowerNoAbsorption
open TowerCardGrowth JoinIrredDInfty JSeedRecursion

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## The copy-`A` exclusion from an arbitrary base stage -/

theorem copyA_forces_bot_at {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (n k : ℕ) (hnk : n ≤ k) {p : D k} (hp : p ≠ ⊥)
    (q : {x : D k // JoinIrred (D k) x})
    (e : (WeakProd (Fam n) × T) ≃o (WeakProd (Fam (k + 1)) ×
      ((LevelSeed (k + 1) (glueA (markedPt k)
        (jiOrderIso (OrderDual.toDual p, q)).1))ᵒᵈ))) : False := by
  haveI : OrderBot (UpSet k p) :=
    { bot := ⟨p, le_refl p⟩
      bot_le := fun a => a.2 }
  haveI : IsAtomic (UpSet k p) := GluingTowerLibrary.isAtomic_of_finite
  haveI := levelSeedDualBot q.2
  haveI : IsAtomic ((LevelSeed k q.1)ᵒᵈ) := GluingTowerLibrary.isAtomic_of_finite
  have e' : (WeakProd (Fam n) × T)
      ≃o (WeakProd (Fam (k + 1)) × (UpSet k p × (LevelSeed k q.1)ᵒᵈ)) :=
    e.trans (prodCongrIso (OrderIso.refl _) (copyASeedDualIso k p q))
  have hidx : n + (k - n) = k := by omega
  have hsmall : ∀ i, Fintype.card (Fam n (k - n)) < Fintype.card (Fam (k + 1) i) := by
    intro i
    show Fintype.card (D (n + (k - n))) < Fintype.card (D (k + 1 + i))
    exact card_D_strictMono (by omega)
  have hA : Fintype.card (UpSet k p) < Fintype.card (Fam n (k - n)) := by
    show Fintype.card (UpSet k p) < Fintype.card (D (n + (k - n)))
    rw [hidx]
    exact card_upSet_lt_D k hp
  have hB : Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (Fam n (k - n)) := by
    show Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (D (n + (k - n)))
    rw [hidx]
    exact card_levelSeed_lt k q.1
  have hempty := no_iso_of_small_piecesL (D := Fam n) (E := Fam (k + 1)) (T := T)
    (A := UpSet k p) (B := (LevelSeed k q.1)ᵒᵈ)
    (fun j => lamD (n + j)) (fun j => lamD (k + 1 + j))
    (fun j => lamD_ne_bot (n + j)) (fun j => lamD_le (n + j))
    (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
    (k - n) hsmall hA hB
  exact hempty.elim e'

/-! ## The induction step from an arbitrary base stage -/

theorem copyA_step_at (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (k : ℕ) (hnk : n ≤ k) (F : EndP (D k)) (hF : JoinIrred (EndP (D k)) F)
    (e : JBelow (toD (k + 1) (glueA (markedPt k) F)) ≃o JBelow z) :
    ∃ q : D k, JoinIrred (D k) q ∧ glueA (markedPt k) F = iotaD k q
      ∧ Nonempty (JBelow (toD k q) ≃o JBelow z) := by
  letI := realUniqueAtomCoatom k
  set aq := jiOrderIso.symm (⟨F, hF⟩ : {f : EndP (D k) // JoinIrred (EndP (D k)) f})
    with haq
  have hFval : F = (jiOrderIso aq).1 := by
    rw [haq, OrderIso.apply_symm_apply]
  have hyji : JoinIrred (D (k + 1)) (glueA (markedPt k) F) :=
    (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mpr hF
  have ecmp : (WeakProd (Fam n) × T)
      ≃o (WeakProd (Fam (k + 1)) × (LevelSeed (k + 1) (glueA (markedPt k) F))ᵒᵈ) :=
    hz.symm.trans (e.dual.symm.trans (seedShape (k + 1) (glueA (markedPt k) F) hyji))
  rw [hFval] at ecmp
  have hp : OrderDual.ofDual aq.1 = (⊥ : D k) := by
    by_contra hne
    exact copyA_forces_bot_at (T := T) n k hnk hne aq.2 ecmp
  have haq1 : aq.1 = OrderDual.toDual (⊥ : D k) := hp
  have hFc : F = constHom aq.2.1 := by
    rw [hFval]
    have hswap : (jiOrderIso aq).1
        = (jiOrderIso (OrderDual.toDual (⊥ : D k), aq.2)).1 := by
      rw [← haq1]
    rw [hswap, jiOrderIso_bot_val (P := D k) aq.2]
  have hiota : glueA (markedPt k) F = iotaD k aq.2.1 := by
    rw [hFc]
    rfl
  have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k aq.2.1 := by
    rw [hiota]
    have h2 := toD_iotaLe (Nat.le_succ k) aq.2.1
    rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) aq.2.1,
         iotaLe_self (le_refl k) aq.2.1] at h2
  exact ⟨aq.2.1, aq.2.2, hiota, ⟨hstep ▸ e⟩⟩

/-! ## The two hypothesis families -/

/-- The copy-`B`/`C` obligation, at base stage `n`. -/
def CopyBCExcludedAt (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ y : D (k + 1), JoinIrred (D (k + 1)) y →
    (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow z)

/-- **Distinct join-irreducibles of a level have distinct seeds.**

**This is FALSE**, already at `k = 1` — `tag_A 2`/`tag_A 3`, `tag_B 2`/`tag_B 3`
and `tag_C 2`/`tag_C 3` have isomorphic seeds
(`_archive/check_base_separation_level1.py`).  It is kept here only to record
that the "pin the point" route is the wrong one for `StageFixed`, which needs
the stage and not the point.  Nothing below uses it. -/
def BaseSeparation : Prop :=
  ∀ (k : ℕ) (x y : D k), JoinIrred (D k) x → JoinIrred (D k) y →
    Nonempty (JBelow (toD k y) ≃o JBelow (toD k x)) → toD k y = toD k x

/-! ## The descent, from an arbitrary base stage -/

/-- **A competitor with the same seed descends to the base stage.**  Not to the
*point* — that is `BaseSeparation`, which is false — but into the stage, which is
all `StageFixed` asks. -/
theorem stage_of_seed_iso (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (h : CopyBCExcludedAt n z) :
    ∀ (N : ℕ), n ≤ N → ∀ y : D N, JoinIrred (D N) y →
      Nonempty (JBelow (toD N y) ≃o JBelow z) → ∃ q : D n, toD N y = toD n q := by
  intro N
  induction N with
  | zero =>
      intro hn y _ _
      have hn0 : n = 0 := Nat.le_zero.mp hn
      subst hn0
      exact ⟨y, rfl⟩
  | succ k ih =>
      intro hn y hy he
      rcases Nat.lt_or_ge k n with hlt | hge
      · have hnk : n = k + 1 := by omega
        subst hnk
        exact ⟨y, rfl⟩
      · by_cases hA : ∃ F : EndP (D k), y = glueA (markedPt k) F
        · obtain ⟨F, rfl⟩ := hA
          have hF : JoinIrred (EndP (D k)) F :=
            (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mp hy
          obtain ⟨q, hq, hiota, hqe⟩ := copyA_step_at n z hz k hge F hF he.some
          have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k q := by
            rw [hiota]
            have h2 := toD_iotaLe (Nat.le_succ k) q
            rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) q,
                 iotaLe_self (le_refl k) q] at h2
          obtain ⟨r, hr⟩ := ih hge q hq hqe
          exact ⟨r, hstep.trans hr⟩
        · exact absurd he (h k hge y hy hA)

/-! ## `StageFixed` -/

/-- **`StageFixed` from the copy-`B`/`C` family alone.**  `θ (toD k x)` lands at
some stage `N`; if `N ≤ k` it is already inside stage `k`, and if `N > k` the
descent brings it back. -/
theorem stageFixed_of
    (hc : ∀ (k : ℕ) (x : D k), JoinIrred (D k) x → CopyBCExcludedAt k (toD k x)) :
    StageFixed := by
  intro θ k x hx
  letI : OrderBot (Base k x) := levelSeedDualBot hx
  haveI : IsAtomic (Base k x) := GluingTowerLibrary.isAtomic_of_finite
  have hji : JoinIrred DInfty (toD k x) := (joinIrred_toD_iff k x).mpr hx
  have hjt : JoinIrred DInfty (θ (toD k x)) := GluingTowerLibrary.joinIrred_orderIso θ hji
  obtain ⟨N, y, hNy⟩ := exists_stage (θ (toD k x))
  have hyji : JoinIrred (D N) y := by
    refine (joinIrred_toD_iff N y).mp ?_
    rw [← hNy]
    exact hjt
  rcases Nat.le_total N k with hNk | hkN
  · exact ⟨iotaLe hNk y, hNy.trans (toD_iotaLe hNk y).symm⟩
  · have hiso : Nonempty (JBelow (toD N y) ≃o JBelow (toD k x)) := by
      rw [← hNy]
      exact ⟨(JBelow.map θ (toD k x)).symm⟩
    obtain ⟨q, hq⟩ := stage_of_seed_iso k (toD k x) (seedShape k x hx) (hc k x hx)
      N hkN y hyji hiso
    exact ⟨q, hNy.trans hq⟩

/-- …and hence the whole pipe: `colimit_compat`. -/
theorem colimit_compat_of
    (hc : ∀ (k : ℕ) (x : D k), JoinIrred (D k) x → CopyBCExcludedAt k (toD k x)) :
    Subsingleton (DInfty ≃o DInfty) :=
  ColimitCompatPipe.colimit_rigid_of_joinIrredStagePreserved
    (joinIrredStagePreserved_of_stageFixed (stageFixed_of hc))

/-! ## The `k = 0` slice is the old statement -/

theorem copyBCExcludedAt_zero_iff (z : DInfty) :
    CopyBCExcludedAt 0 z ↔ TwoPointAssembly.CopyBCExcludedFor z := by
  constructor
  · intro h k y hy hA
    exact h k (Nat.zero_le k) y hy hA
  · intro h k _ y hy hA
    exact h k y hy hA

end StageAssembly
