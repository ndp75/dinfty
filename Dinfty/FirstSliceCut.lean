import Dinfty.CutObstruction
import Dinfty.FinishLine
import Dinfty.CopyBAtoms
import Dinfty.SeedCardBound
import Dinfty.FirstSliceToColimit

open GluingTowerLibrary SierpinskiApplication

/-!
# `FirstSliceB` for every level, by the cut obstruction

The first slice asks whether a non-copy-`A` join-irreducible of `D (n+1)` can
carry the seed `D n × Base n x` of a stage-`n` point.  For copy `B` the answer is
**no, uniformly in `n`**, and the argument needs no enumeration at all.

## The shape of a copy-`B` seed

Write `Y = glueB (markedPt n) b` and `S = (LevelSeed (n+1) Y)ᵒᵈ`.  Two facts about
the gluing decide everything:

* every seed element is copy `A` or copy `B` (`seed_cases`, using `copyB_ne_top`);
* a copy-`A` seed element lies below **every** copy-`B` one (`copyA_le_copyB`).

So `S` is an **ordinal sum** — a *cut* — with the copy-`B` part below the copy-`A`
part.  Stated order-theoretically, the cut is

```lean
cutB : Set S := {u | ¬ (u ≤ dMid (n+1))}
```

and its complement is literally `LevelSeed (n+1) (dMid (n+1))`, because
`dMid (n+1) = glueA (markedPt n) (markedPt n)` by `rfl`.

## Why the upper part is a product

`copyAIsoGen` identifies that complement with
`{f : EndP (D n) // JoinIrred f ∧ f ≤ markedPt n}`, and by
`SeedParametrisation.stepMap_le_markedPt` the condition `stepMap q p ≤ markedPt n`
is `q ≤ dMid n` — **it does not mention the threshold `p`**.  So the threshold
coordinate is free and

```
card (Aᶜ) = card (D n) * card (JMid n).
```

## The contradiction

`CutObstruction.no_iso_of_cut_bounds` now runs: a product of two bounded
nondegenerate posets has only trivial cuts, the upper part is far too big to be
the trivial one, so the *lower* part collapses to a single element and
`card S = 1 + card (D n) * card (JMid n)`.  But an isomorphism
`S ≃o D n × Base n x` makes `card (D n)` divide `card S`, hence divide `1`.

The one degenerate case — `Base n x` a single point, i.e. `x = lamD n` — is
disposed of by the existing bound `card_D_lt_card_seed_B`.

Nothing here is special to any level, and nothing enumerates `J (D (n+1))`.
-/

open scoped Classical

namespace FirstSliceCut

open CutObstruction FinishLine SeedLevelStep JSeedRecursion
open WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open TowerCardGrowth CopyAClassification CopyBCStructure CopyBAtoms CopyBExclusion
open TowerNoAbsorption SeedParametrisation SeedCardBound

variable (k : ℕ)

private theorem hmk' : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk' : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk' : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## Two small `Equiv` combinators -/

private def subInter {α : Type*} (p q : α → Prop) :
    {x : {a : α // p a} // q x.1} ≃ {a : α // p a ∧ q a} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def sndSub {α β : Type*} (p : β → Prop) :
    {s : α × β // p s.2} ≃ α × {b : β // p b} where
  toFun s := (s.1.1, ⟨s.1.2, s.2⟩)
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## `lamD` is join-irreducible -/

theorem joinIrred_lamD : JoinIrred (D k) (lamD k) := by
  refine ⟨lamD_ne_bot k, fun b c hbc => ?_⟩
  by_cases hb : b = (⊥ : D k)
  · subst hb; right; simpa using hbc
  · left
    have hble : b ≤ lamD k := hbc ▸ le_sup_left
    exact le_antisymm (lamD_le k b hb) hble |>.symm ▸ rfl

/-! ## The copy-`A` part below the marked point is a product -/

/-- The join-irreducibles of `D k` below the marked value. -/
abbrev JMid : Type := {q : D k // JoinIrred (D k) q ∧ q ≤ dMid k}

theorem jMid_nonempty : Nonempty (JMid k) :=
  ⟨⟨lamD k, joinIrred_lamD k, lamD_le k (dMid k) (dMid_ne_bot k)⟩⟩

/-- **The membership condition is threshold-free.** -/
theorem jiOrderIso_le_markedPt (z : (D k)ᵒᵈ × {q : D k // JoinIrred (D k) q}) :
    (jiOrderIso z).1 ≤ markedPt k ↔ z.2.1 ≤ dMid k := by
  have hz : (jiOrderIso z).1 = stepMap z.2.1 (OrderDual.ofDual z.1) := rfl
  rw [hz]
  exact stepMap_le_markedPt z.2.2.1

/-- **So the copy-`A` part below the marked point is a product**: the threshold
coordinate is free. -/
noncomputable def markedSeedEquiv :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ markedPt k}
      ≃ ((D k)ᵒᵈ × JMid k) :=
  (subInter (fun f : EndP (D k) => JoinIrred (EndP (D k)) f)
      (fun f => f ≤ markedPt k)).symm.trans
    (((Equiv.subtypeEquiv (jiOrderIso (P := D k)).toEquiv (fun _ => Iff.rfl)).symm.trans
      ((Equiv.subtypeEquivRight (jiOrderIso_le_markedPt k)).trans
        ((sndSub _).trans
          (Equiv.prodCongr (Equiv.refl _)
            (subInter (fun q : D k => JoinIrred (D k) q) (fun q => q ≤ dMid k)))))))

theorem card_markedSeed :
    Fintype.card {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ markedPt k}
      = Fintype.card (D k) * Fintype.card (JMid k) := by
  rw [Fintype.card_congr (markedSeedEquiv k), Fintype.card_prod]
  congr 1

/-! ## The cut -/

variable {k}
variable {x : EndP (D k)} (hx : x ≠ ⊥)

/-- The copy-`B` part of a copy-`B` seed, stated order-theoretically: the seed
elements that the marked point does **not** bound. -/
def cutB (hx : x ≠ ⊥) : Set ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) :=
  {u | ¬ ((OrderDual.ofDual u).1 ≤ dMid (k + 1))}

include hx in
theorem cutB_isCut (hxt : x ≠ ⊤) : IsCut (cutB hx) := by
  intro a ha u hu
  simp only [cutB, Set.mem_setOf_eq, not_not] at hu
  show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual a).1
  rcases seed_cases hx hxt (OrderDual.ofDual a).1 (OrderDual.ofDual a).2.2 with
    ⟨v, hvm, hv⟩ | ⟨b, hb, hv⟩
  · exact absurd (hv ▸ (glueA_le_iff (markedPt k) (hmk' k) v (markedPt k)).mpr hvm) ha
  · obtain ⟨w, hw⟩ := le_glueA_imp_glueA_shaped (markedPt k) (hmk' k) (hbtk' k)
      (OrderDual.ofDual u).1 (markedPt k) hu
    have hwu : (OrderDual.ofDual u).1 = glueA (markedPt k) w := Subtype.ext hw
    have hwm : w ≤ markedPt k := by
      rw [hwu] at hu
      exact (glueA_le_iff (markedPt k) (hmk' k) w (markedPt k)).mp hu
    rw [hwu, hv]
    exact copyA_le_copyB hwm hb

include hx in
theorem cutB_nonempty (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) :
    (cutB hx).Nonempty := by
  refine ⟨OrderDual.toDual (⟨glueB (markedPt k) x hx, hy, le_refl _⟩ :
    LevelSeed (k + 1) (glueB (markedPt k) x hx)), ?_⟩
  show ¬ ((glueB (markedPt k) x hx : D (k + 1)) ≤ dMid (k + 1))
  intro hcon
  exact dMid_ne_copyB hx (le_antisymm (dMid_le_glueB k hx) hcon)

/-- **The complement of the cut is the seed of the marked point.** -/
def cutBComplEquiv (hx : x ≠ ⊥) :
    ↥((cutB hx)ᶜ) ≃ LevelSeed (k + 1) (dMid (k + 1)) where
  toFun u := ⟨(OrderDual.ofDual u.1).1, (OrderDual.ofDual u.1).2.1, not_not.mp u.2⟩
  invFun w := ⟨OrderDual.toDual (⟨w.1, w.2.1, w.2.2.trans (dMid_le_glueB k hx)⟩ :
    LevelSeed (k + 1) (glueB (markedPt k) x hx)), by
      show ¬ ¬ (w.1 ≤ dMid (k + 1))
      exact not_not.mpr w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cutBCompl (hx : x ≠ ⊥) :
    Fintype.card ↥((cutB hx)ᶜ) = Fintype.card (D k) * Fintype.card (JMid k) := by
  rw [Fintype.card_congr (cutBComplEquiv hx)]
  rw [← card_markedSeed k]
  exact (Fintype.card_congr (copyAIsoGen k (markedPt k)).toEquiv).symm

/-! ## The theorem -/

-- the `no_iso_of_cut_bounds` application carries large implicit tower types
set_option maxHeartbeats 1000000 in
/-- **`FirstSliceB` holds at every level.**

No copy-`B` join-irreducible of `D (n+1)` carries the seed of a stage-`n` point,
for any `n`.  The proof is the cut obstruction plus one degenerate case. -/
theorem firstSliceB (n : ℕ) : FirstSliceB n := by
  intro x hx b hb hy
  refine ⟨fun e => ?_⟩
  have hbt : b ≠ ⊤ := copyB_ne_top n hb hy
  by_cases hxl : x = lamD n
  · -- degenerate: the base seed is a single point, so the comparison is a count
    have hsub : Subsingleton (LevelSeed n x) := by
      refine ⟨fun u v => Subtype.ext ?_⟩
      have hu : u.1 = lamD n := le_antisymm (hxl ▸ u.2.2) (lamD_le n u.1 u.2.1.1)
      have hv : v.1 = lamD n := le_antisymm (hxl ▸ v.2.2) (lamD_le n v.1 v.2.1.1)
      rw [hu, hv]
    have hone : Fintype.card (LevelSeed n x) = 1 := by
      have hpos : 0 < Fintype.card (LevelSeed n x) :=
        Fintype.card_pos_iff.mpr ⟨⟨x, hx, le_refl x⟩⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    have hcard : Fintype.card
        (LevelSeed (n + 1) (glueB (markedPt n) b hb : D (n + 1)))
          = Fintype.card (D n) * Fintype.card (LevelSeed n x) := by
      have h := Fintype.card_congr e.toEquiv
      rw [Fintype.card_prod] at h
      exact h
    have hlt := card_D_lt_card_seed_B n hb hy
    rw [hone, Nat.mul_one] at hcard
    omega
  · -- main case: the cut obstruction
    have hcut : IsCut (cutB hb) := cutB_isCut hb hbt
    have hAne : (cutB hb).Nonempty := cutB_nonempty hb hy
    have hc : Fintype.card ↥((cutB hb)ᶜ)
        = Fintype.card (D n) * Fintype.card (JMid n) := card_cutBCompl hb
    have hcpos : 0 < Fintype.card ↥((cutB hb)ᶜ) := by
      rw [hc]
      exact mul_pos Fintype.card_pos (Fintype.card_pos_iff.mpr (jMid_nonempty n))
    have hcne : ((cutB hb)ᶜ).Nonempty := by
      obtain ⟨w⟩ := Fintype.card_pos_iff.mp hcpos
      exact ⟨w.1, w.2⟩
    have hdvd : Fintype.card (D n) ∣ Fintype.card ↥((cutB hb)ᶜ) := ⟨_, hc⟩
    have hQne : (OrderDual.toDual (⟨x, hx, le_refl x⟩ : LevelSeed n x))
        ≠ OrderDual.toDual
            (⟨lamD n, joinIrred_lamD n, lamD_le n x hx.1⟩ : LevelSeed n x) := by
      intro hcon
      exact hxl (congrArg (fun w => (OrderDual.ofDual w).1) hcon)
    exact no_iso_of_cut_bounds (fun _ => bot_le) (fun _ => le_top)
      (fun q => q.2.2)
      (fun q => lamD_le n (OrderDual.ofDual q).1 (OrderDual.ofDual q).2.1.1)
      (Ne.symm (top_ne_bot_D n)) hQne hcut hAne hcne hdvd e

/-! ## Copy `C` below the marked point

`CopyCLow.seedC_cases` says that when `markedPt k ≰ c` there is **no copy-`B`
element** in the seed, so the same argument runs with the boundary moved from
`dMid (k+1) = glueA m m` up to `glueA m ⊤` — copy `A` reaches copy `C`
unconditionally (`copyA_le_copyC`), so the whole of copy `A` is the upper part of
the cut, and its size is `card (D k) * card (J (D k))`.

For `markedPt k ≤ c` the copy-`B` elements *are* in the seed and no copy-`A`
element above the marked point bounds them (`not_iotaD_top_le_glueB`): the cut
does not exist, and that half is left open below. -/

section CopyC

open CopyCLow

/-- All join-irreducibles of `D k`. -/
abbrev JAll (k : ℕ) : Type := {q : D k // JoinIrred (D k) q}

theorem jAll_nonempty (k : ℕ) : Nonempty (JAll k) := ⟨⟨lamD k, joinIrred_lamD k⟩⟩

/-- The copy-`A` part of a copy-`C` seed is **all** of copy `A`, and that is a
product. -/
noncomputable def topSeedEquiv (k : ℕ) :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (⊤ : EndP (D k))}
      ≃ ((D k)ᵒᵈ × JAll k) :=
  (Equiv.subtypeEquivRight (fun _ => ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩)).trans
    (jiOrderIso (P := D k)).toEquiv.symm

theorem card_topSeed (k : ℕ) :
    Fintype.card {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (⊤ : EndP (D k))}
      = Fintype.card (D k) * Fintype.card (JAll k) := by
  rw [Fintype.card_congr (topSeedEquiv k), Fintype.card_prod]
  congr 1

variable {k : ℕ} {c : EndP (D k)}

/-- The cut for a copy-`C` point: the seed elements that the copy-`A` top does
not bound.

The boundary is written `iotaD k ⊤`, not `glueA (markedPt k) ⊤`: the two are
equal (`iotaD_top_eq_glueA`) but only the former elaborates at `D (k+1)` rather
than at the raw `GlueCar`, and `le_antisymm` needs the `D (k+1)` order. -/
def cutC (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    Set ((LevelSeed (k + 1) (glueC (markedPt k) c hc hcm))ᵒᵈ) :=
  {u | ¬ ((OrderDual.ofDual u).1 ≤ iotaD k (⊤ : D k))}

theorem cutC_isCut (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : ¬ (markedPt k ≤ c)) : IsCut (cutC hc hcm) := by
  intro a ha u hu
  simp only [cutC, Set.mem_setOf_eq, not_not] at hu
  rw [iotaD_top_eq_glueA k] at hu
  show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual a).1
  rcases seedC_cases hc hcm hmc (OrderDual.ofDual a).1 (OrderDual.ofDual a).2.2 with
    ⟨v, hv⟩ | ⟨c', hc', hcm', hv⟩
  · refine absurd ?_ ha
    rw [iotaD_top_eq_glueA k, hv]
    exact (glueA_le_iff (markedPt k) (hmk' k) v (⊤ : EndP (D k))).mpr le_top
  · obtain ⟨w, hw⟩ := le_glueA_imp_glueA_shaped (markedPt k) (hmk' k) (hbtk' k)
      (OrderDual.ofDual u).1 (⊤ : EndP (D k)) hu
    have hwu : (OrderDual.ofDual u).1 = glueA (markedPt k) w := Subtype.ext hw
    rw [hwu, hv]
    exact copyA_le_copyC w hc' hcm'

theorem cutC_nonempty (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) c hc hcm)) :
    (cutC hc hcm).Nonempty := by
  refine ⟨OrderDual.toDual (⟨glueC (markedPt k) c hc hcm, hy, le_refl _⟩ :
    LevelSeed (k + 1) (glueC (markedPt k) c hc hcm)), ?_⟩
  intro hcon
  have heq : iotaD k (⊤ : D k) = glueC (markedPt k) c hc hcm :=
    le_antisymm (iotaD_top_le_glueC k hc hcm) hcon
  rw [iotaD_top_eq_glueA k] at heq
  exact glueA_ne_copyC hc hcm (⊤ : EndP (D k)) heq

/-- The complement of the cut is the seed of the copy-`A` top. -/
def cutCComplEquiv (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    ↥((cutC hc hcm)ᶜ) ≃ LevelSeed (k + 1) (iotaD k (⊤ : D k)) where
  toFun u := ⟨(OrderDual.ofDual u.1).1, (OrderDual.ofDual u.1).2.1, not_not.mp u.2⟩
  invFun w := ⟨OrderDual.toDual (⟨w.1, w.2.1,
    w.2.2.trans (iotaD_top_le_glueC k hc hcm)⟩ :
      LevelSeed (k + 1) (glueC (markedPt k) c hc hcm)), not_not.mpr w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cutCCompl (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    Fintype.card ↥((cutC hc hcm)ᶜ) = Fintype.card (D k) * Fintype.card (JAll k) := by
  rw [Fintype.card_congr (cutCComplEquiv hc hcm), iotaD_top_eq_glueA k,
    ← card_topSeed k]
  exact (Fintype.card_congr (copyAIsoGen k (⊤ : EndP (D k))).toEquiv).symm

end CopyC

-- the `no_iso_of_cut_bounds` application carries large implicit tower types
set_option maxHeartbeats 1000000 in
/-- **Copy `C` below the marked point is excluded at every level.** -/
theorem firstSliceC_low (n : ℕ) (x : D n) (hx : JoinIrred (D n) x)
    (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n)
    (hmc : ¬ (markedPt n ≤ c))
    (hy : JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm)) :
    IsEmpty ((LevelSeed (n + 1) (glueC (markedPt n) c hc hcm))ᵒᵈ
      ≃o (D n × (LevelSeed n x)ᵒᵈ)) := by
  refine ⟨fun e => ?_⟩
  by_cases hxl : x = lamD n
  · have hsub : Subsingleton (LevelSeed n x) := by
      refine ⟨fun u v => Subtype.ext ?_⟩
      have hu : u.1 = lamD n := le_antisymm (hxl ▸ u.2.2) (lamD_le n u.1 u.2.1.1)
      have hv : v.1 = lamD n := le_antisymm (hxl ▸ v.2.2) (lamD_le n v.1 v.2.1.1)
      rw [hu, hv]
    have hone : Fintype.card (LevelSeed n x) = 1 := by
      have hpos : 0 < Fintype.card (LevelSeed n x) :=
        Fintype.card_pos_iff.mpr ⟨⟨x, hx, le_refl x⟩⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    have hcard : Fintype.card
        (LevelSeed (n + 1) (glueC (markedPt n) c hc hcm : D (n + 1)))
          = Fintype.card (D n) * Fintype.card (LevelSeed n x) := by
      have h := Fintype.card_congr e.toEquiv
      rw [Fintype.card_prod] at h
      exact h
    have hlt := card_D_lt_card_seed_C n hc hcm hy
    rw [hone, Nat.mul_one] at hcard
    omega
  · have hcut : IsCut (cutC hc hcm) := cutC_isCut hc hcm hmc
    have hAne : (cutC hc hcm).Nonempty := cutC_nonempty hc hcm hy
    have hcc : Fintype.card ↥((cutC hc hcm)ᶜ)
        = Fintype.card (D n) * Fintype.card (JAll n) := card_cutCCompl hc hcm
    have hcpos : 0 < Fintype.card ↥((cutC hc hcm)ᶜ) := by
      rw [hcc]
      exact mul_pos Fintype.card_pos (Fintype.card_pos_iff.mpr (jAll_nonempty n))
    have hcne : ((cutC hc hcm)ᶜ).Nonempty := by
      obtain ⟨w⟩ := Fintype.card_pos_iff.mp hcpos
      exact ⟨w.1, w.2⟩
    have hdvd : Fintype.card (D n) ∣ Fintype.card ↥((cutC hc hcm)ᶜ) := ⟨_, hcc⟩
    have hQne : (OrderDual.toDual (⟨x, hx, le_refl x⟩ : LevelSeed n x))
        ≠ OrderDual.toDual
            (⟨lamD n, joinIrred_lamD n, lamD_le n x hx.1⟩ : LevelSeed n x) := by
      intro hcon
      exact hxl (congrArg (fun w => (OrderDual.ofDual w).1) hcon)
    exact no_iso_of_cut_bounds (fun _ => bot_le) (fun _ => le_top)
      (fun q => q.2.2)
      (fun q => lamD_le n (OrderDual.ofDual q).1 (OrderDual.ofDual q).2.1.1)
      (Ne.symm (top_ne_bot_D n)) hQne hcut hAne hcne hdvd e

/-! ## What is left: copy `C` above the marked point -/

/-- The copy-`C`-high half — the one case the cut does not reach.

When `markedPt n ≤ c` the copy-`B` elements are in the seed too, and no copy-`A`
element above the marked point bounds them (`not_iotaD_top_le_glueB`), so the
seed is not an ordinal sum at either boundary. -/
def FirstSliceCHigh (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n), markedPt n ≤ c →
      JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm) →
        IsEmpty ((LevelSeed (n + 1) (glueC (markedPt n) c hc hcm))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

theorem firstSliceC (n : ℕ) (h : FirstSliceCHigh n) : FirstSliceC n := by
  intro x hx c hc hcm hy
  by_cases hmc : markedPt n ≤ c
  · exact h x hx c hc hcm hmc hy
  · exact firstSliceC_low n x hx c hc hcm hmc hy

/-- **The first slice, at every level, modulo copy-`C`-high.** -/
theorem firstSlice (n : ℕ) (h : FirstSliceCHigh n) : FirstSlice n :=
  firstSlice_of (firstSliceB n) (firstSliceC n h)

/-- **Pillar B now rests on copy-`C`-high alone.**

Every other arrow from the first slice to `Subsingleton (DInfty ≃o DInfty)` is
machine-checked: copy `B` and copy-`C`-low by the cut obstruction above, the
first-slice reduction by `BaseShift`, and the restatement by
`FirstSliceToColimit`. -/
theorem colimit_compat_of_firstSliceCHigh (h : ∀ n, FirstSliceCHigh n) :
    Subsingleton (DInfty ≃o DInfty) :=
  FirstSliceToColimit.colimit_compat_of_firstSlice (fun n => firstSlice n (h n))

end FirstSliceCut
