import Dinfty.JSeedRecursion
import Dinfty.ChainUnion
import Dinfty.JoinIrredLevelStable

open GluingTowerLibrary SierpinskiApplication

-- [D-1581] §The-seed-s-level-step-at-the-tower
open scoped Classical

universe u

namespace SeedLevelStep

open JSeedRecursion

-- [D-1582] §constHom-is-the-step-map-at-threshold
-- [D-1583] stepMap_bot
theorem stepMap_bot {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
    (x : P) : stepMap x (⊥ : P) = constHom x := by
  apply OrderHom.ext
  funext y
  exact stepMap_apply_of_ge x (⊥ : P) bot_le

-- [D-1584] jiOrderIso_bot_val
theorem jiOrderIso_bot_val {P : Type u} [Fintype P] [DecidableEq P] [Lattice P]
    [BoundedOrder P] (q : {x : P // JoinIrred P x}) :
    (jiOrderIso (OrderDual.toDual (⊥ : P), q)).1 = constHom q.1 := by
  show (jiEquiv ((⊥ : P), q)).1 = constHom q.1
  exact stepMap_bot q.1

-- [D-1585] §The-seed-at-a-level
-- [D-1586] LevelSeed
abbrev LevelSeed (k : ℕ) (v : D k) : Type := {u : D k // JoinIrred (D k) u ∧ u ≤ v}

-- [D-1587] subtypeShuffle
def subtypeShuffle {X : Type u} [PartialOrder X] (Q : X → Prop) (x0 : {x : X // Q x}) :
    {x : X // Q x ∧ x ≤ x0.1} ≃o {g : {x : X // Q x} // g ≤ x0} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

-- [D-1588] §Copy-A-carries-the-seed-up-a-level
section CopyA

variable (k : ℕ) (v : D k) (hv : JoinIrred (D k) v)

-- [D-1589] hm_k
private theorem hm_k : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-1590] hmt_k
private theorem hmt_k : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-1591] hbt_k
private theorem hbt_k : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-1592] jiBot
noncomputable abbrev jiBot : {f : EndP (D k) // JoinIrred (EndP (D k)) f} :=
  jiOrderIso (OrderDual.toDual (⊥ : D k), (⟨v, hv⟩ : {x : D k // JoinIrred (D k) x}))

-- [D-1593] copyAFun
noncomputable def copyAFun
    (f : {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (jiBot k v hv).1}) :
    LevelSeed (k + 1) (iotaD k v) :=
  ⟨glueA (markedPt k) f.1,
   (joinIrred_glueA_iff (markedPt k) (hm_k k) (hmt_k k) (hbt_k k) f.1).mpr f.2.1,
   (glueA_le_iff (markedPt k) (hm_k k) f.1 (constHom v)).mpr
     (le_of_le_of_eq f.2.2 (jiOrderIso_bot_val (P := D k) ⟨v, hv⟩))⟩

-- [D-1594] copyAFun_injective
theorem copyAFun_injective : Function.Injective (copyAFun k v hv) := by
  intro a b h
  apply Subtype.ext
  exact glueA_injective (markedPt k) (congrArg Subtype.val h)

-- [D-1595] copyAFun_surjective
theorem copyAFun_surjective : Function.Surjective (copyAFun k v hv) := by
  intro w
  obtain ⟨f, hf⟩ := le_glueA_imp_glueA_shaped (markedPt k) (hm_k k) (hbt_k k)
    w.1 (constHom v) w.2.2
  have hw : w.1 = glueA (markedPt k) f := Subtype.ext hf
  refine ⟨⟨f, ?_, ?_⟩, ?_⟩
  · exact (joinIrred_glueA_iff (markedPt k) (hm_k k) (hmt_k k) (hbt_k k) f).mp (hw ▸ w.2.1)
  · rw [jiOrderIso_bot_val (P := D k) ⟨v, hv⟩]
    exact (glueA_le_iff (markedPt k) (hm_k k) f (constHom v)).mp (hw ▸ w.2.2)
  · exact Subtype.ext hw.symm

-- [D-1596] copyAIso
noncomputable def copyAIso :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (jiBot k v hv).1}
      ≃o LevelSeed (k + 1) (iotaD k v) where
  toEquiv := Equiv.ofBijective (copyAFun k v hv)
    ⟨copyAFun_injective k v hv, copyAFun_surjective k v hv⟩
  map_rel_iff' := by
    intro a b
    show (copyAFun k v hv a) ≤ (copyAFun k v hv b) ↔ a ≤ b
    exact glueA_le_iff (markedPt k) (hm_k k) a.1 b.1

-- [D-1597] copyAIso_apply
@[simp] theorem copyAIso_apply
    (f : {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (jiBot k v hv).1}) :
    ((copyAIso k v hv f) : D (k + 1)) = glueA (markedPt k) f.1 := rfl

end CopyA

-- [D-1598] §The-level-step
-- [D-1599] levelStepIso
noncomputable def levelStepIso (k : ℕ) (v : D k) (hv : JoinIrred (D k) v) :
    LevelSeed (k + 1) (iotaD k v) ≃o ((D k)ᵒᵈ × LevelSeed k v) :=
  letI := realUniqueAtomCoatom k
  (copyAIso k v hv).symm.trans
    ((subtypeShuffle (fun f : EndP (D k) => JoinIrred (EndP (D k)) f) (jiBot k v hv)).trans
      ((jSeedIso_bot (P := D k) ⟨v, hv⟩).trans
        (prodCongrIso (OrderIso.refl _)
          (subtypeShuffle (fun x : D k => JoinIrred (D k) x)
            (⟨v, hv⟩ : {x : D k // JoinIrred (D k) x})).symm)))

-- [D-1600] §and-the-tower-s-own-embedding-is-the-insertion
-- [D-1601] levelStepIso_symm_bot
theorem levelStepIso_symm_bot (k : ℕ) (v : D k) (hv : JoinIrred (D k) v)
    (u : LevelSeed k v) :
    ((levelStepIso k v hv).symm (OrderDual.toDual (⊥ : D k), u) : D (k + 1))
      = iotaD k u.1 := by
  letI := realUniqueAtomCoatom k
  show glueA (markedPt k) (jiOrderIso (OrderDual.toDual (⊥ : D k),
      (⟨u.1, u.2.1⟩ : {x : D k // JoinIrred (D k) x}))).1 = iotaD k u.1
  rw [jiOrderIso_bot_val (P := D k) ⟨u.1, u.2.1⟩]
  rfl

end SeedLevelStep
