import Dinfty.BaseShift
import Dinfty.CopyBCAtBase

open GluingTowerLibrary SierpinskiApplication

-- [D-3169] §Closing-the-wiring-FirstSlice-implies-colimit
open scoped Classical

namespace FirstSliceToColimit

open SeedLevelStep SeedShapeProof FinishLine CopyBCAtBase
open BaseShift

-- [D-3170] multiAtomExcluded_of_firstSlice
theorem multiAtomExcluded_of_firstSlice (n : ℕ) (x : D n) (hx : JoinIrred (D n) x)
    (hFS : ∀ k, FirstSlice k) :
    CopyBCMultiAtomExcludedAt n (toD n x) := by
  intro k hnk y hy hnotA _hmulti
  rintro ⟨e0⟩
  exact (no_comparison_of_firstSlice n k hnk x hx y hy hnotA (hFS k)).elim
    ((seedShape n x hx).symm.trans (e0.dual.symm.trans (seedShape (k + 1) y hy)))

-- [D-3171] colimit_compat_of_firstSlice
theorem colimit_compat_of_firstSlice (hFS : ∀ k, FirstSlice k) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_compat_of_multiAtom
    (fun k x hx => multiAtomExcluded_of_firstSlice k x hx hFS)

-- [D-3172] colimit_compat_of_firstSlice_parts
theorem colimit_compat_of_firstSlice_parts
    (hB : ∀ n, FirstSliceB n) (hC : ∀ n, FirstSliceC n) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_compat_of_firstSlice (fun n => firstSlice_of (hB n) (hC n))

end FirstSliceToColimit
