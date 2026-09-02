import Dinfty.PhiTri

open GluingTowerLibrary SierpinskiApplication

-- [D-2949] §The-copy-hierarchy-the-glued-order-s-edge
open scoped Classical

universe u

namespace CopyHierarchy

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-2950] copyIdx
def copyIdx : GlueBaseGen P → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

-- [D-2951] copyIdx_inl
@[simp] theorem copyIdx_inl (x : P) : copyIdx (Sum.inl x) = 0 := rfl
-- [D-2952] copyIdx_inr_inl
@[simp] theorem copyIdx_inr_inl (x : P) : copyIdx (Sum.inr (Sum.inl x)) = 1 := rfl
-- [D-2953] copyIdx_inr_inr
@[simp] theorem copyIdx_inr_inr (x : P) : copyIdx (Sum.inr (Sum.inr x)) = 2 := rfl

-- [D-2954] copyIdx_mono
theorem copyIdx_mono (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (hx : canonGen m x = x)
    (hgen : ∀ b : P, y = Sum.inr (Sum.inl b) → b ≠ ⊤)
    (h : leGlueGen m x y) : copyIdx x ≤ copyIdx y := by
  cases x with
  | inl a =>
    cases y with
    | inl _ => exact le_rfl
    | inr y => cases y with
      | inl _ => exact by simp only [copyIdx]; decide
      | inr _ => exact by simp only [copyIdx]; decide
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagB_tagAGen m b a' hm hbt hbne)
      | inr y => cases y with
        | inl _ => exact le_rfl
        | inr _ => exact by simp only [copyIdx]; decide
    | inr c =>
      have hcne : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagC_tagAGen m c a' hcne)
      | inr y => cases y with
        | inl b' => exact absurd h (not_leGlue_tagC_tagBGen m c b' (hgen b' rfl))
        | inr _ => exact le_rfl

-- [D-2955] tagC_sink
theorem tagC_sink (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {c : P} {y : GlueBaseGen P}
    (hx : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c))
    (hgen : ∀ b : P, y = Sum.inr (Sum.inl b) → b ≠ ⊤)
    (h : leGlueGen m (Sum.inr (Sum.inr c)) y) : ∃ c' : P, y = Sum.inr (Sum.inr c') := by
  have hmono := copyIdx_mono m hm hbt hx hgen h
  cases y with
  | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
  | inr y => cases y with
    | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
    | inr c' => exact ⟨c', rfl⟩

-- [D-2956] tagA_source
theorem tagA_source (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {a : P} {x : GlueBaseGen P}
    (hx : canonGen m x = x)
    (h : leGlueGen m x (Sum.inl a)) : ∃ a' : P, x = Sum.inl a' := by
  have hmono := copyIdx_mono m hm hbt hx (by rintro b ⟨⟩) h
  cases x with
  | inl a' => exact ⟨a', rfl⟩
  | inr x => cases x with
    | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
    | inr _ => exact absurd hmono (by simp only [copyIdx]; decide)

end CopyHierarchy
