import Dinfty.EndLocalContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-1534] §How-rigid-is-the-Gen-layer-morphism-action
open scoped Classical

universe u v

namespace BaseMapGenRigidity

open GenContinuity EndLocalContinuity

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

-- [D-1535] §The-positive-half-copy-wise-agreement
-- [D-1536] baseMapGen_unique
theorem baseMapGen_unique (g : P →o P') (H : GlueBaseGen P → GlueBaseGen P')
    (hA : ∀ x, H (Sum.inl x) = Sum.inl (g x))
    (hB : ∀ x, H (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl (g x)))
    (hC : ∀ x, H (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr (g x))) :
    H = baseMapGen g := by
  funext x
  cases x with
  | inl a => exact hA a
  | inr x =>
    cases x with
    | inl b => exact hB b
    | inr c => exact hC c

-- [D-1537] §The-negative-half-copy-A-and-even-copy-C-is-not
-- [D-1538] collapseB
def collapseB (g : P →o P') : GlueBaseGen P → GlueBaseGen P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl (⊤ : P'))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

-- [D-1539] collapseB_inl
@[simp] theorem collapseB_inl (g : P →o P') (a : P) :
    collapseB g (Sum.inl a) = Sum.inl (g a) := rfl

-- [D-1540] collapseB_inr_inr
@[simp] theorem collapseB_inr_inr (g : P →o P') (c : P) :
    collapseB g (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr (g c)) := rfl

-- [D-1541] collapseB_eq_on_tagA
theorem collapseB_eq_on_tagA (g : P →o P') (a : P) :
    collapseB g (Sum.inl a) = baseMapGen g (Sum.inl a) := rfl

-- [D-1542] collapseB_eq_on_tagC
theorem collapseB_eq_on_tagC (g : P →o P') (c : P) :
    collapseB g (Sum.inr (Sum.inr c)) = baseMapGen g (Sum.inr (Sum.inr c)) := rfl

-- [D-1543] collapseB_canonGen_fixed
theorem collapseB_canonGen_fixed (m : P) (m' : P') (g : P →o P')
    (hgb : g ⊥ = ⊥) (hgm : g m = m') (hginj : Function.Injective g)
    (hbt' : (⊥ : P') ≠ ⊤) {x : GlueBaseGen P} (hx : canonGen m x = x) :
    canonGen m' (collapseB g x) = collapseB g x := by
  cases x with
  | inl a => rfl
  | inr x =>
    cases x with
    | inl b =>
      show canonGen m' (Sum.inr (Sum.inl (⊤ : P'))) = Sum.inr (Sum.inl (⊤ : P'))
      simp only [canonGen]; rw [if_neg (Ne.symm hbt')]
    | inr c =>
      have hcb : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      have hcm : c ≠ m := by
        intro hcon
        have hval : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inl (⊤ : P)) := by
          simp only [canonGen]; rw [if_neg hcb, if_pos hcon]
        rw [hx] at hval
        exact absurd hval (by simp)
      show canonGen m' (Sum.inr (Sum.inr (g c))) = Sum.inr (Sum.inr (g c))
      simp only [canonGen]
      rw [if_neg (fun h => hcb (hginj (h.trans hgb.symm))),
          if_neg (fun h => hcm (hginj (h.trans hgm.symm)))]

-- [D-1544] collapseB_monotone
theorem collapseB_monotone (m : P) (m' : P') (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt : (⊥ : P) ≠ ⊤) (g : P →o P')
    (hgm : g m = m') {x y : GlueBaseGen P}
    (hx : canonGen m x = x) (hy : canonGen m y = y)
    (h : leGlueGen m x y) :
    leGlueGen m' (collapseB g x) (collapseB g y) := by
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      have : a ≤ a' := (leGlueGen_tagA_tagA_iff m hm a a').mp h
      exact (leGlueGen_tagA_tagA_iff m' hm' (g a) (g a')).mpr (g.monotone this)
    | inr y =>
      cases y with
      | inl _ => exact leGlue_tagA_tagB_topGen m' (g a)
      | inr c' => exact leGlueGen_tagA_tagC m' (g a) (g c')
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      cases y with
      | inl a' =>
        exact absurd h (not_leGlue_tagB_tagAGen m b a' hm hbt hbne)
      | inr y =>
        cases y with
        | inl _ => exact leGlueGen_refl m' _
        | inr c' =>
          have hmc : m ≤ c' := marked_le_of_leGlueGen_tagB_tagC m b c' h
          exact ⟨Sum.inr (Sum.inl (⊤ : P')), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr (g c')), self_mem_occsGen _ _,
                 hgm ▸ g.monotone hmc⟩
    | inr c =>
      have hcne : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagC_tagAGen m c a' hcne)
      | inr y =>
        cases y with
        | inl b' =>
          have hb'top : b' = ⊤ := by
            by_contra hcon
            exact not_leGlue_tagC_tagBGen m c b' hcon h
          subst hb'top
          have hcm : c ≤ m := by
            obtain ⟨u, hu, v, hv, huv⟩ := h
            have hu' : u = Sum.inr (Sum.inr c) := occsGen_tagC m c u hu
            subst hu'
            rcases occsGen_tagB m (⊤ : P) v hv with hv' | ⟨_, hv'⟩
            · subst hv'; exact huv.elim
            · subst hv'; exact huv
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr m'), by simp [collapseB, occsGen],
                 hgm ▸ g.monotone hcm⟩
        | inr c' =>
          obtain ⟨u, hu, v, hv, huv⟩ := h
          have hu' : u = Sum.inr (Sum.inr c) := occsGen_tagC m c u hu
          have hv' : v = Sum.inr (Sum.inr c') := occsGen_tagC m c' v hv
          subst hu'; subst hv'
          exact ⟨Sum.inr (Sum.inr (g c)), self_mem_occsGen _ _,
                 Sum.inr (Sum.inr (g c')), self_mem_occsGen _ _, g.monotone huv⟩

-- [D-1545] collapseB_ne_baseMapGen
theorem collapseB_ne_baseMapGen (g : P →o P') {b : P} (hb : g b ≠ ⊤) :
    collapseB g (Sum.inr (Sum.inl b)) ≠ baseMapGen g (Sum.inr (Sum.inl b)) := by
  intro h
  exact hb (Sum.inl.inj (Sum.inr.inj h)).symm

end BaseMapGenRigidity
