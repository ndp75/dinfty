import Dinfty.BaseShift
import Dinfty.CopyBCAtBase

open GluingTowerLibrary SierpinskiApplication

/-!
# Closing the wiring: `FirstSlice` implies `colimit_compat`

Section 69 proved the base shift
(`BaseShift.no_comparison_of_firstSlice`): a `FirstSlice k` hypothesis
kills every seed comparison at every base `n <= k`, in the *product* form

```
IsEmpty ((WeakProd (Fam n) x Base n x) ≃o (WeakProd (Fam (k+1)) x Base (k+1) y))
```

`CopyBCAtBase.CopyBCMultiAtomExcludedAt` states the same exclusion in the
*`JBelow`* form.  This file is the restatement between them -- no argument, just
`seedShape` on both sides -- and then the end-to-end chain.

The translation is the one already used inside `copyBCExcludedAt_of_multiAtom`:
given `e0 : JBelow (toD (k+1) y) ≃o JBelow (toD n x)`, dualise and paste
`seedShape` at each end.

Note the direction of strength: `CopyBCMultiAtomExcludedAt` *supplies* a
two-distinct-atoms hypothesis on the competitor seed, and the proof below never
uses it.  So what `FirstSlice` gives is strictly stronger than what the reduction
needs.
-/

open scoped Classical

namespace FirstSliceToColimit

open SeedLevelStep SeedShapeProof FinishLine CopyBCAtBase
open BaseShift

/-- **The restatement.**  `FirstSlice` at every level excludes the copy-`B` /
copy-`C` competitors against the stage-`n` point `toD n x`, in the form
`CopyBCMultiAtomExcludedAt` asks for. -/
theorem multiAtomExcluded_of_firstSlice (n : ℕ) (x : D n) (hx : JoinIrred (D n) x)
    (hFS : ∀ k, FirstSlice k) :
    CopyBCMultiAtomExcludedAt n (toD n x) := by
  intro k hnk y hy hnotA _hmulti
  rintro ⟨e0⟩
  exact (no_comparison_of_firstSlice n k hnk x hx y hy hnotA (hFS k)).elim
    ((seedShape n x hx).symm.trans (e0.dual.symm.trans (seedShape (k + 1) y hy)))

/-- **The chain, end to end.**  `FirstSlice` at every level is enough for
`colimit_compat`. -/
theorem colimit_compat_of_firstSlice (hFS : ∀ k, FirstSlice k) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_compat_of_multiAtom
    (fun k x hx => multiAtomExcluded_of_firstSlice k x hx hFS)

/-- The same, phrased against the two halves of `FirstSlice`, which is how the
remaining work is actually split. -/
theorem colimit_compat_of_firstSlice_parts
    (hB : ∀ n, FirstSliceB n) (hC : ∀ n, FirstSliceC n) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_compat_of_firstSlice (fun n => firstSlice_of (hB n) (hC n))

end FirstSliceToColimit
