import Dinfty.MidAnchor

open GluingTowerLibrary SierpinskiApplication

/-!
# The two-point hypothesis

`MidAnchor` observed that stage `0` is `{⊥, midInf, toD 0 ⊤}` and that `⊥` is
order-theoretically fixed already, so the base case of `StageFixed` is about two
points. This module states that as a `Prop` and proves the equivalence, so the
claim is a theorem rather than a remark.

```lean
def TwoPointFixed : Prop :=
  ∀ θ : DInfty ≃o DInfty, θ midInf = midInf ∧ θ (toD 0 ⊤) = toD 0 ⊤
```

`stageFixedZero_iff_twoPointFixed` : `StageFixedZero ↔ TwoPointFixed`.

Forward is `MidAnchor.fixes_stage_of_maps_into` — "maps into" already forces
"identity on", by `D_monotone_injection_eq_id`. Backward is immediate once `⊥`
is handled, which `OrderIso.map_bot` does.

## Why it is worth having as a named `Prop`

`stageFixed_imp_twoPointFixed` shows **`TwoPointFixed` is necessary for pillar
B**: it follows from `StageFixed`, which `colimit_compat`'s open half needs. So
it is a *falsifiable* target, not merely a sub-goal —

* exhibit one automorphism of `DInfty` moving `midInf` or `toD 0 ⊤`, and pillar
  B's rigidity claim is **dead**;
* prove it, and the base case of the induction is closed.

Either outcome is progress, which is not true of `StageFixed` in general.

## What the two points look like from below, for whoever attacks this

Copy `A` is downward closed in `GlueCar` (`rawRule` sends neither `tag_B` nor
`tag_C` below a `tag_A`), and both points are copy-`A` all the way up:

* `↓ midInf` is the colimit of `↓(constHom (dMid k))` inside `EndP (D k)` — the
  monotone maps `D k → [⊥, dMid k]`.
* `↓ (toD 0 ⊤)` is the colimit of `↓(⊤ : EndP (D k))` — *all* of `EndP (D k)`,
  since `⊤ : EndP L` is `constHom ⊤`.

Both are join-irreducible in `DInfty` (`joinIrred_toD_iff` applied to `1` and `2`
in `Fin 3`) and comparable (`midInf < toD 0 ⊤`). Distinguishing them from the
rest of `J∞` by an order-theoretic property is exactly the open question, and
the second description above is the concrete handle: `↓(toD 0 ⊤)` is the colimit
of the *full* endomorphism posets, `↓midInf` of a proper interval-restricted
sub-family.
-/

open scoped Classical

namespace TwoPointHypothesis

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor

/-! ## The two `Prop`s -/

/-- `StageFixed` restricted to level `0`, with the join-irreducibility
hypothesis dropped (it is free there: `⊥` is handled by `OrderIso.map_bot`). -/
def StageFixedZero : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (x : D 0), ∃ y : D 0, θ (toD 0 x) = toD 0 y

/-- **The two-point hypothesis.**  Every order-automorphism of `DInfty` fixes
the seam and the top of stage `0`. -/
def TwoPointFixed : Prop :=
  ∀ θ : DInfty ≃o DInfty,
    θ midInf = midInf ∧ θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0)

/-! ## The equivalence -/

theorem orderIso_map_bot (θ : DInfty ≃o DInfty) : θ (⊥ : DInfty) = (⊥ : DInfty) :=
  θ.map_bot

theorem stageFixedZero_iff_twoPointFixed : StageFixedZero ↔ TwoPointFixed := by
  constructor
  · intro h θ
    exact ⟨fixes_midInf_of_maps_into θ (h θ),
           fixes_toD_zero_top_of_maps_into θ (h θ)⟩
  · intro h θ x
    have hx : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
      show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
      revert x; decide
    rcases hx with rfl | rfl | rfl
    · refine ⟨(⊥ : D 0), ?_⟩
      rw [← bot_eq_toD 0, orderIso_map_bot]
    · exact ⟨dMid 0, (h θ).1⟩
    · exact ⟨(⊤ : D 0), (h θ).2⟩

/-! ## Necessity — so the hypothesis is falsifiable -/

theorem joinIrred_D0_top : JoinIrred (D 0) (⊤ : D 0) := by
  show JoinIrred (Fin 3) (2 : Fin 3)
  exact ⟨by decide, by decide⟩

/-- **`StageFixed` implies the two-point hypothesis**, so refuting the latter
kills pillar B outright. -/
theorem stageFixed_imp_stageFixedZero (h : StageFixed) : StageFixedZero := by
  intro θ x
  have hx : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
    show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
    revert x; decide
  rcases hx with rfl | rfl | rfl
  · refine ⟨(⊥ : D 0), ?_⟩
    rw [← bot_eq_toD 0, orderIso_map_bot]
  · exact h θ 0 (dMid 0) (D_mid_joinIrred 0)
  · exact h θ 0 (⊤ : D 0) joinIrred_D0_top

theorem stageFixed_imp_twoPointFixed (h : StageFixed) : TwoPointFixed :=
  stageFixedZero_iff_twoPointFixed.mp (stageFixed_imp_stageFixedZero h)

/-- Contrapositive, spelled out: a single automorphism moving either point
refutes pillar B's rigidity claim. -/
theorem not_stageFixed_of_not_twoPointFixed (h : ¬ TwoPointFixed) : ¬ StageFixed :=
  fun hs => h (stageFixed_imp_twoPointFixed hs)

/-! ## Both points are join-irreducible in the colimit -/

theorem joinIrred_midInf : JoinIrred DInfty midInf := by
  rw [midInf]
  exact (joinIrred_toD_iff 0 (dMid 0)).mpr (D_mid_joinIrred 0)

theorem joinIrred_toD_zero_top : JoinIrred DInfty (toD 0 (⊤ : D 0)) :=
  (joinIrred_toD_iff 0 (⊤ : D 0)).mpr joinIrred_D0_top

/-- The two points are distinct and comparable, so an automorphism preserving
the pair setwise fixes each — the two-point hypothesis is genuinely about two
independent facts, not one. -/
theorem midInf_lt_top_zero : midInf < toD 0 (⊤ : D 0) := midInf_lt_toD_top 0

end TwoPointHypothesis
