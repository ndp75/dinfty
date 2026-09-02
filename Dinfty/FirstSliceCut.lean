import Dinfty.CutObstruction
import Dinfty.FinishLine
import Dinfty.CopyBAtoms
import Dinfty.SeedCardBound
import Dinfty.FirstSliceToColimit

open GluingTowerLibrary SierpinskiApplication

-- [D-3173] §FirstSliceB-for-every-level-by-the-cut
open scoped Classical

namespace FirstSliceCut

open CutObstruction FinishLine SeedLevelStep JSeedRecursion
open WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open TowerCardGrowth CopyAClassification CopyBCStructure CopyBAtoms CopyBExclusion
open TowerNoAbsorption SeedParametrisation SeedCardBound

variable (k : ℕ)

-- [D-3174] hmk'
private theorem hmk' : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-3175] hmtk'
private theorem hmtk' : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-3176] hbtk'
private theorem hbtk' : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-3177] §Two-small-Equiv-combinators
-- [D-3178] subInter
private def subInter {α : Type*} (p q : α → Prop) :
    {x : {a : α // p a} // q x.1} ≃ {a : α // p a ∧ q a} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-3179] sndSub
private def sndSub {α β : Type*} (p : β → Prop) :
    {s : α × β // p s.2} ≃ α × {b : β // p b} where
  toFun s := (s.1.1, ⟨s.1.2, s.2⟩)
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-3180] §lamD-is-join-irreducible
-- [D-3181] joinIrred_lamD
theorem joinIrred_lamD : JoinIrred (D k) (lamD k) := by
  refine ⟨lamD_ne_bot k, fun b c hbc => ?_⟩
  by_cases hb : b = (⊥ : D k)
  · subst hb; right; simpa using hbc
  · left
    have hble : b ≤ lamD k := hbc ▸ le_sup_left
    exact le_antisymm (lamD_le k b hb) hble |>.symm ▸ rfl

-- [D-3182] §The-copy-A-part-below-the-marked-point
-- [D-3183] JMid
abbrev JMid : Type := {q : D k // JoinIrred (D k) q ∧ q ≤ dMid k}

-- [D-3184] jMid_nonempty
theorem jMid_nonempty : Nonempty (JMid k) :=
  ⟨⟨lamD k, joinIrred_lamD k, lamD_le k (dMid k) (dMid_ne_bot k)⟩⟩

-- [D-3185] jiOrderIso_le_markedPt
theorem jiOrderIso_le_markedPt (z : (D k)ᵒᵈ × {q : D k // JoinIrred (D k) q}) :
    (jiOrderIso z).1 ≤ markedPt k ↔ z.2.1 ≤ dMid k := by
  have hz : (jiOrderIso z).1 = stepMap z.2.1 (OrderDual.ofDual z.1) := rfl
  rw [hz]
  exact stepMap_le_markedPt z.2.2.1

-- [D-3186] markedSeedEquiv
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

-- [D-3187] card_markedSeed
theorem card_markedSeed :
    Fintype.card {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ markedPt k}
      = Fintype.card (D k) * Fintype.card (JMid k) := by
  rw [Fintype.card_congr (markedSeedEquiv k), Fintype.card_prod]
  congr 1

-- [D-3188] §The-cut
variable {k}
variable {x : EndP (D k)} (hx : x ≠ ⊥)

-- [D-3189] cutB
def cutB (hx : x ≠ ⊥) : Set ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) :=
  {u | ¬ ((OrderDual.ofDual u).1 ≤ dMid (k + 1))}

-- [D-3190] cutB_isCut
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

-- [D-3191] cutB_nonempty
include hx in
theorem cutB_nonempty (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) :
    (cutB hx).Nonempty := by
  refine ⟨OrderDual.toDual (⟨glueB (markedPt k) x hx, hy, le_refl _⟩ :
    LevelSeed (k + 1) (glueB (markedPt k) x hx)), ?_⟩
  show ¬ ((glueB (markedPt k) x hx : D (k + 1)) ≤ dMid (k + 1))
  intro hcon
  exact dMid_ne_copyB hx (le_antisymm (dMid_le_glueB k hx) hcon)

-- [D-3192] cutBComplEquiv
def cutBComplEquiv (hx : x ≠ ⊥) :
    ↥((cutB hx)ᶜ) ≃ LevelSeed (k + 1) (dMid (k + 1)) where
  toFun u := ⟨(OrderDual.ofDual u.1).1, (OrderDual.ofDual u.1).2.1, not_not.mp u.2⟩
  invFun w := ⟨OrderDual.toDual (⟨w.1, w.2.1, w.2.2.trans (dMid_le_glueB k hx)⟩ :
    LevelSeed (k + 1) (glueB (markedPt k) x hx)), by
      show ¬ ¬ (w.1 ≤ dMid (k + 1))
      exact not_not.mpr w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-3193] card_cutBCompl
theorem card_cutBCompl (hx : x ≠ ⊥) :
    Fintype.card ↥((cutB hx)ᶜ) = Fintype.card (D k) * Fintype.card (JMid k) := by
  rw [Fintype.card_congr (cutBComplEquiv hx)]
  rw [← card_markedSeed k]
  exact (Fintype.card_congr (copyAIsoGen k (markedPt k)).toEquiv).symm

-- [D-3194] §The-theorem
-- [D-3195] firstSliceB
set_option maxHeartbeats 1000000 in

theorem firstSliceB (n : ℕ) : FirstSliceB n := by
  intro x hx b hb hy
  refine ⟨fun e => ?_⟩
  have hbt : b ≠ ⊤ := copyB_ne_top n hb hy
  by_cases hxl : x = lamD n
  ·
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
  ·
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

-- [D-3196] §Copy-C-below-the-marked-point
section CopyC

open CopyCLow

-- [D-3197] JAll
abbrev JAll (k : ℕ) : Type := {q : D k // JoinIrred (D k) q}

-- [D-3198] jAll_nonempty
theorem jAll_nonempty (k : ℕ) : Nonempty (JAll k) := ⟨⟨lamD k, joinIrred_lamD k⟩⟩

-- [D-3199] topSeedEquiv
noncomputable def topSeedEquiv (k : ℕ) :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (⊤ : EndP (D k))}
      ≃ ((D k)ᵒᵈ × JAll k) :=
  (Equiv.subtypeEquivRight (fun _ => ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩)).trans
    (jiOrderIso (P := D k)).toEquiv.symm

-- [D-3200] card_topSeed
theorem card_topSeed (k : ℕ) :
    Fintype.card {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (⊤ : EndP (D k))}
      = Fintype.card (D k) * Fintype.card (JAll k) := by
  rw [Fintype.card_congr (topSeedEquiv k), Fintype.card_prod]
  congr 1

variable {k : ℕ} {c : EndP (D k)}

-- [D-3201] cutC
def cutC (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    Set ((LevelSeed (k + 1) (glueC (markedPt k) c hc hcm))ᵒᵈ) :=
  {u | ¬ ((OrderDual.ofDual u).1 ≤ iotaD k (⊤ : D k))}

-- [D-3202] cutC_isCut
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

-- [D-3203] cutC_nonempty
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

-- [D-3204] cutCComplEquiv
def cutCComplEquiv (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    ↥((cutC hc hcm)ᶜ) ≃ LevelSeed (k + 1) (iotaD k (⊤ : D k)) where
  toFun u := ⟨(OrderDual.ofDual u.1).1, (OrderDual.ofDual u.1).2.1, not_not.mp u.2⟩
  invFun w := ⟨OrderDual.toDual (⟨w.1, w.2.1,
    w.2.2.trans (iotaD_top_le_glueC k hc hcm)⟩ :
      LevelSeed (k + 1) (glueC (markedPt k) c hc hcm)), not_not.mpr w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-3205] card_cutCCompl
theorem card_cutCCompl (hc : c ≠ ⊥) (hcm : c ≠ markedPt k) :
    Fintype.card ↥((cutC hc hcm)ᶜ) = Fintype.card (D k) * Fintype.card (JAll k) := by
  rw [Fintype.card_congr (cutCComplEquiv hc hcm), iotaD_top_eq_glueA k,
    ← card_topSeed k]
  exact (Fintype.card_congr (copyAIsoGen k (⊤ : EndP (D k))).toEquiv).symm

end CopyC

-- [D-3206] firstSliceC_low
set_option maxHeartbeats 1000000 in
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

-- [D-3207] §What-is-left-copy-C-above-the-marked-point
-- [D-3208] FirstSliceCHigh
def FirstSliceCHigh (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n), markedPt n ≤ c →
      JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm) →
        IsEmpty ((LevelSeed (n + 1) (glueC (markedPt n) c hc hcm))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

-- [D-3209] firstSliceC
theorem firstSliceC (n : ℕ) (h : FirstSliceCHigh n) : FirstSliceC n := by
  intro x hx c hc hcm hy
  by_cases hmc : markedPt n ≤ c
  · exact h x hx c hc hcm hmc hy
  · exact firstSliceC_low n x hx c hc hcm hmc hy

-- [D-3210] firstSlice
theorem firstSlice (n : ℕ) (h : FirstSliceCHigh n) : FirstSlice n :=
  firstSlice_of (firstSliceB n) (firstSliceC n h)

-- [D-3211] colimit_compat_of_firstSliceCHigh
theorem colimit_compat_of_firstSliceCHigh (h : ∀ n, FirstSliceCHigh n) :
    Subsingleton (DInfty ≃o DInfty) :=
  FirstSliceToColimit.colimit_compat_of_firstSlice (fun n => firstSlice n (h n))

end FirstSliceCut
