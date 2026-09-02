import Dinfty.InternalIFSInstance

open GluingTowerLibrary SierpinskiApplication

/-!
# `Fix σ_A` is not a singleton — Theorem ESCAPE fails for the `constHom` IFS

§95 put Theorem ESCAPE (`Fix σ_A = {⊥}`) on the critical path: `CoreIFS.base_pin`
and `theoremA_unique_of_ingredients` need it for Theorem A's uniqueness clause.
This module does that analysis, and the answer is negative.

## The computation

`σ_A x = sec (tag_A (constS x))`, and `sec` is `toBilim` through `shiftIso`, so
its coordinates are the cocone's projection legs:

```
(sec z).1 (n+1) = pLeg n z          (sec z).1 0 = prj 0 (pLeg 0 z)
```

`PhiSurjective.pLeg_tagPt` pushes `pLeg` through a tag, and the payload computes:
`projEndDown j (constS x) = constHom (x.1 j)`.  So

```
(σ_A x).1 (n+1) = tag_A (constHom (x.1 n))    in  D (n+2)
```

Now take `x = midB`.  Then `constS midB` is *by definition* `markedB`, and
`midB.1 n = dMid (n+1)`, so `constHom (midB.1 n) = markedPt (n+1)` — and

```
tag_A (markedPt (n+1)) = ⟨Sum.inl (markedPt (n+1)), _⟩ = triMark (markedPt (n+1))
                       = dMid (n+2) = midB.1 (n+1)
```

by `PhiTriTower.dMid_succ_eq`, which is `rfl`.  The zeroth coordinate closes by
`TriEP.prj_mid`.  So **`σ_A` fixes the marked point**, not just `⊥`.

## What this means

`Fix σ_A ⊇ {⊥, midB}` and `midB ≠ ⊥`, so `Fix σ_A` is not a singleton
(`fix_sigmaA_not_singleton`).  Hence `CoreIFS.FixData`'s field
`fixA : Fix K.sigmaA = {P.botC}` **cannot be satisfied** by this internal IFS,
for any choice of `botC`, and `base_pin` is unavailable.

The diagnosis is not that Theorem A is wrong; it is that
`TheoremAPipe.internalIFSOfSection`'s modelling choice — sending `x` to the
**constant** endomorphism `constHom x` before including it into a copy — is not
the gasket contraction.  The marked point is a fixed point of that map for a
structural reason: `dMid (k+1)` *is* copy `A` at `markedPt k`, and `markedPt k`
*is* `constHom (dMid k)`, so the constant-inclusion recursion reproduces the
`dMid` tower exactly.  Any IFS whose copy-`A` map is built from `constHom` will
fix the marked point.

**So the σ's need to be rebuilt before the uniqueness clause can be attempted.**
Everything else in §95 stands: `ifsB` is a genuine `InternalIFS` with all three
maps injective, and `theoremA_orderIso` is unaffected.
-/

namespace EscapeAnalysis

open PhiIterateTower PhiBilimit GlueTag GenContinuity InternalIFSInstance

attribute [-instance] OrderHom.instDecidableEqOfForall

/-! ## `pLeg` of the marked tag-`A` point

`pLeg_val`, `projEndDown_markedB` and `sec`'s coordinates now live in
`InternalIFSInstance`, above the fork: they are generic, and keeping them here
would make live results import the refutation. -/

theorem pLeg_markedB (j : ℕ) :
    PhiCocone.pLeg j (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB)
      = dMid (j + 2) := by
  refine Subtype.ext ?_
  rw [pLeg_val j markedB, projEndDown_markedB j]
  rfl

/-! ## The marked point is fixed -/

theorem sigmaA_mid : ifsB.sigmaA midB = midB := by
  refine Subtype.ext (funext (fun n => ?_))
  cases n with
  | zero =>
      show phiTowerEP.prj 0
          (PhiCocone.pLeg 0 (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB))
        = dMid 1
      rw [pLeg_markedB 0]
      exact (iter 0).prj_mid
  | succ n =>
      show PhiCocone.pLeg n (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB)
        = dMid (n + 2)
      exact pLeg_markedB n

theorem mid_mem_fix : midB ∈ Fix ifsB.sigmaA := sigmaA_mid

/-! ## …and it is in the orbit of `⊥`

So the failure is not escapable by passing to the attractor: copy `B`'s redirect
`tag_B ⊥ ↦ tag_A m` sends `⊥` straight to the marked point, so `midB = σ_B ⊥`
lies in every set containing `⊥` and closed under the three maps. -/

theorem tagB_bot_eq_mark :
    tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
  rw [if_pos rfl]

theorem sigmaB_bot : ifsB.sigmaB (⊥ : B) = midB := by
  show sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS (⊥ : B))) = midB
  rw [constS_bot, tagB_bot_eq_mark]
  exact sigmaA_mid

/-! ## Theorem ESCAPE fails -/

/-- **`Fix σ_A` is not a singleton.**  It contains `⊥` and the marked point. -/
theorem fix_sigmaA_not_singleton (b : B) : Fix ifsB.sigmaA ≠ {b} := by
  intro h
  have hbot : (⊥ : B) ∈ Fix ifsB.sigmaA := bot_mem_fix_sigmaA
  have hmid : midB ∈ Fix ifsB.sigmaA := mid_mem_fix
  rw [h] at hbot hmid
  exact midB_ne_botB (hmid.trans hbot.symm)

/-- The same, phrased against `CoreIFS`'s field: no `botC` makes `fixA` true. -/
theorem no_fixA (botC : B) (hfixA : Fix ifsB.sigmaA = {botC}) : False :=
  fix_sigmaA_not_singleton botC hfixA

end EscapeAnalysis
