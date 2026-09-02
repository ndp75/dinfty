import Dinfty.GenContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-1400] §Gap-1-of-GenContinuity-transport-of-the-copy-B-C
open scoped Classical

universe u v

namespace GenContinuity

section Transport

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-1401] occsGen_subset_canonGen
theorem occsGen_subset_canonGen (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : GlueBaseGen P) {w : GlueBaseGen P} (hw : w ∈ occsGen m x) :
    w ∈ occsGen m (canonGen m x) := by
  cases x with
  | inl a => simpa [canonGen] using hw
  | inr x =>
    cases x with
    | inl b =>
      by_cases hb : b = ⊥
      · subst hb
        have hwv : w = Sum.inr (Sum.inl (⊥ : P)) := by
          simp only [occsGen] at hw
          rw [if_neg hbt] at hw
          simpa using hw
        subst hwv
        show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inl (⊥ : P))))
        simp only [canonGen, if_pos rfl, occsGen]
        simp
      · show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inl b)))
        simp only [canonGen]
        rw [if_neg hb]
        exact hw
    | inr c =>
      have hwv : w = Sum.inr (Sum.inr c) := by simpa [occsGen] using hw
      subst hwv
      show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inr c)))
      simp only [canonGen]
      by_cases hc : c = ⊥
      · subst hc
        rw [if_pos rfl]
        simp [occsGen, Ne.symm hmt]
      · rw [if_neg hc]
        by_cases hcm : c = m
        · subst hcm
          rw [if_pos rfl]
          simp only [occsGen, if_pos rfl]
          simp
        · rw [if_neg hcm]
          simp [occsGen]

-- [D-1402] leGlueGen_canonGen
theorem leGlueGen_canonGen (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (h : leGlueGen m x y) :
    leGlueGen m (canonGen m x) (canonGen m y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨u, occsGen_subset_canonGen m hmt hbt x hu,
         v, occsGen_subset_canonGen m hmt hbt y hv, huv⟩

-- [D-1403] tagBGen
noncomputable def tagBGen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (b : P) :
    GlueCarGen (P := P) m :=
  ⟨canonGen m (Sum.inr (Sum.inl b)), canonGen_idem m hm hbt _⟩

-- [D-1404] tagBGen_val_of_ne_bot
theorem tagBGen_val_of_ne_bot (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {b : P}
    (hb : b ≠ ⊥) : (tagBGen m hm hbt b).1 = Sum.inr (Sum.inl b) := by
  show canonGen m (Sum.inr (Sum.inl b)) = Sum.inr (Sum.inl b)
  simp only [canonGen]; rw [if_neg hb]

-- [D-1405] tagCGen_marked_eq_skelG3Gen
theorem tagCGen_marked_eq_skelG3Gen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    tagCGen m hm hbt m = skelG3Gen m hm hbt := by
  apply Subtype.ext
  show canonGen m (Sum.inr (Sum.inr m)) = canonGen m (Sum.inr (Sum.inl (⊤ : P)))
  simp only [canonGen]
  rw [if_neg hm]
  simp [Ne.symm hbt]

-- [D-1406] tagBGen_isLUB
theorem tagBGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagBGen m hm hbt '' S) (tagBGen m hm hbt c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hraw_ub, hraw_least⟩ := tagB_isLUB_raw m hm hbt hS ⟨s0, hs0⟩ hSb
  have hcb : c ≠ ⊥ := fun h => hSb s0 hs0 (le_bot_iff.mp (h ▸ hS.1 hs0))
  have hcval : (tagBGen m hm hbt c).1 = Sum.inr (Sum.inl c) :=
    tagBGen_val_of_ne_bot m hm hbt hcb
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (tagBGen m hm hbt s).1 (tagBGen m hm hbt c).1
    rw [tagBGen_val_of_ne_bot m hm hbt (hSb s hs), hcval]
    exact hraw_ub s hs
  · intro w hw
    show leGlueGen m (tagBGen m hm hbt c).1 w.1
    rw [hcval]
    refine hraw_least w.1 (fun s hs => ?_)
    have hle : leGlueGen m (tagBGen m hm hbt s).1 w.1 := hw ⟨s, hs, rfl⟩
    rwa [show ((tagBGen m hm hbt s).1) = Sum.inr (Sum.inl s) from
      tagBGen_val_of_ne_bot m hm hbt (hSb s hs)] at hle

-- [D-1407] tagCGen_isLUB
theorem tagCGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty)
    (hSb : ∀ s ∈ S, s ≠ ⊥) (hSm : ∀ s ∈ S, s ≠ m) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagCGen m hm hbt '' S) (tagCGen m hm hbt c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hraw_ub, hraw_least⟩ := tagC_isLUB_raw m hS ⟨s0, hs0⟩ hSb
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (tagCGen m hm hbt s).1 (tagCGen m hm hbt c).1
    exact leGlueGen_canonGen m hmt hbt (hraw_ub s hs)
  · intro w hw
    show leGlueGen m (tagCGen m hm hbt c).1 w.1
    have hraw : leGlueGen m (Sum.inr (Sum.inr c)) w.1 := by
      refine hraw_least w.1 (fun s hs => ?_)
      have hle : leGlueGen m (tagCGen m hm hbt s).1 w.1 := hw ⟨s, hs, rfl⟩
      rwa [show ((tagCGen m hm hbt s).1) = Sum.inr (Sum.inr s) from
        tagCGen_val_of_generic m hm hbt (hSb s hs) (hSm s hs)] at hle
    have hcan := leGlueGen_canonGen m hmt hbt hraw
    rwa [w.2] at hcan

end Transport

end GenContinuity
