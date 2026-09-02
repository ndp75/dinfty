import Dinfty.InternalIFSInstance

open GluingTowerLibrary SierpinskiApplication

/-!
# Rebuilding `σ`, and a correction about what ESCAPE was needed for

§96 showed `Fix σ_A` is not a singleton for the `constHom`-built IFS, and I said
that blocked Theorem A's uniqueness clause.  **That was too strong**, and the
first half of this module retracts it.

## Correction: `base_pin` never needed the reverse inclusion

`CoreIFS.base_pin` takes `[FixData P]` and opens with
`have hbot : P.botC ∈ Fix K.sigmaA := by rw [FD.fixA]; rfl` — and then never
touches `FD` again.  Only **membership** is used, never `Fix K.sigmaA ⊆ {botC}`.
So `base_pin_of_mem` below asks for exactly `b ∈ Fix K.sigmaA` and needs no
`FixData` at all, and `theoremA_unique_of_mem` carries that through the whole
uniqueness argument.

`InternalIFSInstance.sigmaA_bot` already gives `⊥ ∈ Fix σ_A`.  **So Theorem A's
uniqueness clause is not blocked by ESCAPE's failure** — for either IFS.  What
ESCAPE's failure does block is the companion note's separate `G2` statement, the
`1/2/3` characterisation `fix_card`, which genuinely needs the exact sets.

## The rebuild

The defect was structural: `dMid (k+1)` *is* copy `A` at `markedPt k` and
`markedPt k` *is* `constHom (dMid k)`, so a copy-`A` map factoring through
`constHom` reproduces the `dMid` tower and fixes the marked point.  The repair is
to use the **strict** constant instead,

```
strictConst c : y ↦ if y = ⊥ then ⊥ else c
```

which is Scott-continuous (the only interesting case is a directed set whose
supremum is not `⊥`, where some member is already not `⊥`), and which kills the
coincidence at `⊥`: `strictConst c` sends `⊥ ↦ ⊥`, whereas `markedPt k` sends
`⊥ ↦ dMid k ≠ ⊥`.  `sigmaA_mid_ne` is exactly that evaluation.

## What is still open

`Fix ifsS.sigmaA = {⊥}` is **not** proved.  The fixed-point equation reduces,
levelwise, to the base ep-pair: `x ∈ Fix σ'_A` forces
`qAA 0 (tag_A (strictConstHom (x.1 0))) = x.1 0`, and `qAA 0` is obtained from
`EpFromJoin.exists_epPartner` by `Exists.choose`, so it is opaque.  The usable
necessary condition is the deflation one,
`glueAA 0 y ≤ tag_A (strictConstHom y)`, and `GlueAAJoin.glueAA_glueA` is the
handle: on copy-`A` points `glueAA` acts as `iotaEndP` on the payload, so the
condition reads `iotaEndP f ≤ strictConstHom (tag_A f)`, which at `⊥` says
`f ⊥ = ⊥`.  That excludes the marked point (`markedPt 1 ⊥ = dMid 1 ≠ ⊥`) but not
every non-`⊥` payload, so the exact fixed-point set needs the base ep-pair
pinned down.
-/

universe u

namespace SigmaRebuild

open PhiIterateTower PhiBilimit GlueTag GenContinuity InternalIFSInstance

attribute [-instance] OrderHom.instDecidableEqOfForall

/-! ## The correction, stated and proved -/

section Uniqueness

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma] {K : CoreIFS Dinf Gamma}

/-- **`base_pin` needs only membership.**  `CoreIFS.base_pin` asks for
`[FixData P]` but uses it solely to produce `P.botC ∈ Fix K.sigmaA`. -/
theorem base_pin_of_mem {b : K.Core} (hb : b ∈ Fix K.sigmaA)
    (hFixA : Subsingleton (Fix K.fA)) {rho1 rho2 : K.Core → Gamma}
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x)) :
    rho1 b = rho2 b := by
  have h1 : rho1 b ∈ Fix K.fA := equivariant_fixes_fix hA1 hb
  have h2 : rho2 b ∈ Fix K.fA := equivariant_fixes_fix hA2 hb
  exact congrArg Subtype.val (hFixA.elim (⟨rho1 b, h1⟩ : Fix K.fA) ⟨rho2 b, h2⟩)

/-- **Uniqueness, with `FixData` replaced by one membership.**  This is
`CoreIFS.theoremA_unique_of_ingredients` with its `[FixData P]` hypothesis
removed; `⊥ ∈ Fix σ_A` is all that was ever used. -/
theorem theoremA_unique_of_mem [T2Space Gamma] {b : K.Core} (hb : b ∈ Fix K.sigmaA)
    (hFixA : Subsingleton (Fix K.fA)) (hDense : Dense (Orbit (K := K) b))
    {rho1 rho2 : K.Core → Gamma}
    (hc1 : Continuous rho1) (hc2 : Continuous rho2)
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hB1 : ∀ x, rho1 (K.sigmaB x) = K.fB (rho1 x))
    (hC1 : ∀ x, rho1 (K.sigmaC x) = K.fC (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x))
    (hB2 : ∀ x, rho2 (K.sigmaB x) = K.fB (rho2 x))
    (hC2 : ∀ x, rho2 (K.sigmaC x) = K.fC (rho2 x)) :
    rho1 = rho2 :=
  Continuous.ext_on hDense hc1 hc2
    (agree_on_orbit hA1 hB1 hC1 hA2 hB2 hC2 (base_pin_of_mem hb hFixA hA1 hA2))

end Uniqueness

/-! ## The strict constant -/

/-- `y ↦ if y = ⊥ then ⊥ else c`.  The strict constant: unlike `constS` it does
not send `⊥` to `c`, which is precisely the coincidence §96 exploited.  The
decidability instance is pinned in the term rather than opened, so that no
`Classical.propDecidable` competes with `PhiBilimit.decEqScottEndPB`. -/
noncomputable def strictFun (c : B) (y : B) : B := @ite B (y = ⊥) (Classical.dec _) ⊥ c

theorem strictFun_bot_case {c y : B} (hy : y = ⊥) : strictFun c y = ⊥ := by
  simp only [strictFun]
  rw [if_pos hy]

theorem strictFun_ne_case {c y : B} (hy : y ≠ ⊥) : strictFun c y = c := by
  simp only [strictFun]
  rw [if_neg hy]

theorem strictFun_mono (c : B) : Monotone (strictFun c) := by
  intro y y' h
  by_cases hy : y = ⊥
  · rw [strictFun_bot_case hy]
    exact bot_le
  · have hy' : y' ≠ ⊥ := fun hc => hy (le_antisymm (hc ▸ h) bot_le)
    rw [strictFun_ne_case hy, strictFun_ne_case hy']

theorem strictFun_scott (c : B) : ScottContinuous (strictFun c) := by
  intro S hne hdir a ha
  by_cases ha0 : a = ⊥
  · have hS : ∀ s ∈ S, s = ⊥ := fun s hs => le_antisymm (ha0 ▸ ha.1 hs) bot_le
    rw [strictFun_bot_case ha0]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      rw [strictFun_bot_case (hS s hs)]
    · intro w _
      exact bot_le
  · obtain ⟨s0, hs0, hs0b⟩ : ∃ s ∈ S, s ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact ha0 (le_antisymm (ha.2 (fun s hs => le_of_eq (hc s hs))) bot_le)
    rw [strictFun_ne_case ha0]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      by_cases hsb : s = ⊥
      · rw [strictFun_bot_case hsb]; exact bot_le
      · rw [strictFun_ne_case hsb]
    · intro w hw
      have hle := hw ⟨s0, hs0, rfl⟩
      rwa [strictFun_ne_case hs0b] at hle

/-- The strict constant, as a point of `ScottEndP B`. -/
noncomputable def strictConst (c : B) : ScottEndP B :=
  ⟨⟨strictFun c, strictFun_mono c⟩, strictFun_scott c⟩

@[simp] theorem strictConst_apply (c y : B) : (strictConst c).1 y = strictFun c y := rfl

theorem topB_ne_bot : topB ≠ (⊥ : B) := fun h => botB_ne_topB h.symm

theorem strictConst_injective : Function.Injective strictConst := by
  intro x y h
  have h1 : strictFun x topB = strictFun y topB :=
    congrArg (fun F : ScottEndP B => F.1 topB) h
  rwa [strictFun_ne_case (c := x) topB_ne_bot, strictFun_ne_case (c := y) topB_ne_bot] at h1

theorem strictConst_bot : strictConst (⊥ : B) = (⊥ : ScottEndP B) := by
  refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
  show strictFun (⊥ : B) y = (⊥ : ScottEndP B).1 y
  by_cases hy : y = ⊥
  · rw [strictFun_bot_case hy]; rfl
  · rw [strictFun_ne_case hy]; rfl

/-! ## The rebuilt internal IFS -/

/-- **`σ` rebuilt on the strict constant.**  Same shape as
`InternalIFSInstance.ifsB`, with `constS` replaced by `strictConst`. -/
noncomputable def ifsS : InternalIFS B where
  sigmaA x := sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
  sigmaB x := sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
  sigmaC x := sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))

private theorem sigmaS_inj (t : ℕ) {x y : B}
    (h : sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
       = sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst y))) : x = y :=
  strictConst_injective
    (tagPt_injective t markedB markedB_ne_bot endPB_bot_ne_top (sec_injective h))

theorem sigmaA_injective : Function.Injective ifsS.sigmaA := fun _ _ h => sigmaS_inj 0 h
theorem sigmaB_injective : Function.Injective ifsS.sigmaB := fun _ _ h => sigmaS_inj 1 h
theorem sigmaC_injective : Function.Injective ifsS.sigmaC := fun _ _ h => sigmaS_inj 2 h

/-! ## `⊥` is still fixed, and the marked point is not -/

theorem sigmaA_bot : ifsS.sigmaA (⊥ : B) = ⊥ := by
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = ⊥
  rw [strictConst_bot]
  exact InternalIFSInstance.sigmaA_bot

theorem bot_mem_fix : (⊥ : B) ∈ Fix ifsS.sigmaA := sigmaA_bot

/-- **The §96 defect is repaired.**  Evaluating the level-1 payload at `⊥`:
the strict constant gives `⊥`, while `markedPt 1` gives `dMid 1 ≠ ⊥`. -/
theorem sigmaA_mid_ne : ifsS.sigmaA midB ≠ midB := by
  intro h
  have h1 : (ifsS.sigmaA midB).1 1 = midB.1 1 := congrArg (fun z : B => z.1 1) h
  have hval : (Sum.inl ((PhiCocone.projEndDown 0).toFun (strictConst midB))
      : GlueBaseGen (EndP (D 1))) = Sum.inl (markedPt 1) := by
    rw [← InternalIFSInstance.pLeg_val 0 (strictConst midB)]
    exact congrArg Subtype.val h1
  have hpay : (PhiCocone.projEndDown 0).toFun (strictConst midB) = markedPt 1 :=
    Sum.inl.inj hval
  have hbot : ((PhiCocone.projEndDown 0).toFun (strictConst midB)) (⊥ : D 1)
      = (markedPt 1) (⊥ : D 1) := congrArg (fun f : EndP (D 1) => f (⊥ : D 1)) hpay
  have hlhs : ((PhiCocone.projEndDown 0).toFun (strictConst midB)) (⊥ : D 1) = (⊥ : D 1) := by
    show ((strictConst midB).1 (phiTowerEP.ins 0 (⊥ : D 1))).1 0 = (⊥ : D 1)
    rw [ins_bot 0]
    show (strictFun midB botB).1 0 = (⊥ : D 1)
    rw [strictFun_bot_case (rfl : botB = ⊥)]
    rfl
  rw [hlhs] at hbot
  exact dMid_ne_bot 1 hbot.symm

theorem mid_not_mem_fix : midB ∉ Fix ifsS.sigmaA := sigmaA_mid_ne

end SigmaRebuild
