import Dinfty.CopyHierarchy

open GluingTowerLibrary SierpinskiApplication

-- [D-3440] §Copy-A-is-a-principal-ideal
open Set

open scoped Classical

namespace SeamFixed

universe u

-- [D-3441] §1-Every-point-occurs-among-its-own-occurrences
section Generic

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-3442] leGlueGen_tagA_top
theorem leGlueGen_tagA_top (m a : P) : leGlueGen m (Sum.inl a) (Sum.inl ⊤) :=
  ⟨Sum.inl a, self_mem_occsGen m _, Sum.inl ⊤, self_mem_occsGen m _, le_top⟩

end Generic

-- [D-3443] §2-The-seam-point-of-a-level-and-copy
open CopyHierarchy

-- [D-3444] cSeam
noncomputable def cSeam (k : ℕ) : D (k + 1) := glueA (markedPt k) (⊤ : EndP (D k))

-- [D-3445] cSeam_val
@[simp] theorem cSeam_val (k : ℕ) : (cSeam k).1 = Sum.inl (⊤ : EndP (D k)) := rfl

-- [D-3446] le_cSeam_of_tagA
theorem le_cSeam_of_tagA (k : ℕ) {x : D (k + 1)} {a : EndP (D k)}
    (hx : x.1 = Sum.inl a) : x ≤ cSeam k := by
  show leGlueGen (markedPt k) x.1 (cSeam k).1
  rw [hx, cSeam_val]
  exact leGlueGen_tagA_top _ a

-- [D-3447] tagA_of_le_cSeam
theorem tagA_of_le_cSeam (k : ℕ) {x : D (k + 1)} (h : x ≤ cSeam k) :
    ∃ a : EndP (D k), x.1 = Sum.inl a := by
  have hle : leGlueGen (markedPt k) x.1 (Sum.inl (⊤ : EndP (D k))) := h
  exact tagA_source (markedPt k) (D_marked_point_nondegenerate k).1
    (D_marked_point_nondegenerate k).2.2 x.2 hle

-- [D-3448] mem_copyA_iff_le_cSeam
theorem mem_copyA_iff_le_cSeam (k : ℕ) (x : D (k + 1)) :
    (∃ a : EndP (D k), x.1 = Sum.inl a) ↔ x ≤ cSeam k :=
  ⟨fun ⟨a, ha⟩ => le_cSeam_of_tagA k ha, fun h => tagA_of_le_cSeam k h⟩

-- [D-3449] §3-One-point-pins-the-copy-A-split
-- [D-3450] copyA_preserved
theorem copyA_preserved {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) (hseam : f (cSeam k) = cSeam m)
    (x : D (k + 1)) :
    (∃ a : EndP (D m), (f x).1 = Sum.inl a) ↔ (∃ a : EndP (D k), x.1 = Sum.inl a) := by
  rw [mem_copyA_iff_le_cSeam, mem_copyA_iff_le_cSeam]
  constructor
  · intro h
    refine hrefl x (cSeam k) ?_
    rw [hseam]
    exact h
  · intro h
    rw [← hseam]
    exact hmono h

-- [D-3451] copyA_mapsTo
theorem copyA_mapsTo {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hseam : f (cSeam k) ≤ cSeam m) (x : D (k + 1))
    (hx : ∃ a : EndP (D k), x.1 = Sum.inl a) :
    ∃ a : EndP (D m), (f x).1 = Sum.inl a := by
  rw [mem_copyA_iff_le_cSeam] at hx ⊢
  exact le_trans (hmono hx) hseam

end SeamFixed
