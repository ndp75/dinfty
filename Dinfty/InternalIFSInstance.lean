import Dinfty.PhiSurjective
import Dinfty.CoreIFS

open GluingTowerLibrary SierpinskiApplication

-- [D-2535] §The-honest-internal-IFS-on-D
namespace InternalIFSInstance

open PhiIterateTower PhiBilimit GlueTag GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2536] sec
noncomputable def sec : PhiBilimit.phiB ≃o B := PhiSurjective.theoremA_orderIso

-- [D-2537] sec_injective
theorem sec_injective : Function.Injective sec := sec.injective

-- [D-2538] sec_surjective
theorem sec_surjective : Function.Surjective sec := sec.surjective

-- [D-2539] §Two-small-injectivity-inputs
-- [D-2540] constS_injective
theorem constS_injective : Function.Injective (constS : B → ScottEndP B) := by
  intro x y h
  exact congrArg (fun F : ScottEndP B => F.1 botB) h

-- [D-2541] constS_bot
theorem constS_bot : constS (⊥ : B) = (⊥ : ScottEndP B) := rfl

-- [D-2542] §The-glue-bottom
-- [D-2543] tagA_bot_le_raw
theorem tagA_bot_le_raw (v : GlueBaseGen (ScottEndP B)) :
    leGlueGen markedB (Sum.inl (⊥ : ScottEndP B)) v := by
  refine ⟨Sum.inl (⊥ : ScottEndP B), self_mem_occsGen _ _, v, self_mem_occsGen _ _, ?_⟩
  cases v with
  | inl _ => exact bot_le
  | inr w => cases w with
    | inl _ => exact bot_le
    | inr _ => trivial

-- [D-2544] tagA_bot_le
theorem tagA_bot_le (z : PhiBilimit.phiB) :
    tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B) ≤ z :=
  tagA_bot_le_raw z.1

-- [D-2545] §The-internal-IFS
-- [D-2546] ifsB
noncomputable def ifsB : InternalIFS B where
  sigmaA x := sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (constS x))
  sigmaB x := sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS x))
  sigmaC x := sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (constS x))

-- [D-2547] sigmaA_apply
@[simp] theorem sigmaA_apply (x : B) :
    ifsB.sigmaA x = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

-- [D-2548] sigmaB_apply
@[simp] theorem sigmaB_apply (x : B) :
    ifsB.sigmaB x = sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

-- [D-2549] sigmaC_apply
@[simp] theorem sigmaC_apply (x : B) :
    ifsB.sigmaC x = sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

-- [D-2550] §Injectivity-on-all-of-B-for-all-three-copies
-- [D-2551] sigma_inj
private theorem sigma_inj (t : ℕ) {x y : B}
    (h : sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (constS x))
       = sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (constS y))) : x = y :=
  constS_injective
    (tagPt_injective t markedB markedB_ne_bot endPB_bot_ne_top (sec_injective h))

-- [D-2552] sigmaA_injective
theorem sigmaA_injective : Function.Injective ifsB.sigmaA := fun _ _ h => sigma_inj 0 h
-- [D-2553] sigmaB_injective
theorem sigmaB_injective : Function.Injective ifsB.sigmaB := fun _ _ h => sigma_inj 1 h
-- [D-2554] sigmaC_injective
theorem sigmaC_injective : Function.Injective ifsB.sigmaC := fun _ _ h => sigma_inj 2 h

-- [D-2555] §is-fixed-by-copy
-- [D-2556] sigmaA_bot
theorem sigmaA_bot : ifsB.sigmaA (⊥ : B) = ⊥ := by
  refine le_antisymm ?_ bot_le
  obtain ⟨z, hz⟩ := sec_surjective (⊥ : B)
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) ≤ (⊥ : B)
  rw [← hz]
  exact sec.monotone (tagA_bot_le z)

-- [D-2557] bot_mem_fix_sigmaA
theorem bot_mem_fix_sigmaA : (⊥ : B) ∈ Fix ifsB.sigmaA := sigmaA_bot

-- [D-2558] §sec-s-coordinates-are-the-projection-legs
-- [D-2559] sec_apply_succ
theorem sec_apply_succ (z : PhiBilimit.phiB) (n : ℕ) :
    (sec z).1 (n + 1) = PhiCocone.pLeg n z := rfl

-- [D-2560] sec_apply_zero
theorem sec_apply_zero (z : PhiBilimit.phiB) :
    (sec z).1 0 = phiTowerEP.prj 0 (PhiCocone.pLeg 0 z) := rfl

-- [D-2561] projEndDown_markedB
theorem projEndDown_markedB (j : ℕ) :
    (PhiCocone.projEndDown j).toFun markedB = markedPt (j + 1) := rfl

-- [D-2562] pLeg_val
theorem pLeg_val (j : ℕ) (H : ScottEndP B) :
    (PhiCocone.pLeg j (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top H)).1
      = Sum.inl ((PhiCocone.projEndDown j).toFun H) :=
  congrArg Subtype.val (PhiSurjective.pLeg_tagPt j 0 H)

-- [D-2563] §Self-similarity-named
-- [D-2564] selfSimilar
theorem selfSimilar : Nonempty (B ≃o PhiBilimit.phiB) := ⟨sec.symm⟩

end InternalIFSInstance
