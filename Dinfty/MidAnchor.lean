import Dinfty.DInftyNoFootholds

open GluingTowerLibrary SierpinskiApplication

/-!
# Where they cancel: the seam, and a canonical anchor at neither `⊥` nor `⊤`

`DInftyNoFootholds` showed both ends of `DInfty` are structureless, and closed
with the requirement that pillar B needs an invariant anchored at neither `⊥`
nor `⊤`.  There is a third place, and the gluing itself names it.

`canon`'s three rules are identifications of a *bottom* with something else:

```
tag_B ⊥  ↦  tag_A m        -- b.T ~ a.L : the bottom of copy B IS the marked point of copy A
tag_C ⊥  ↦  tag_A ⊤        -- c.T ~ a.R
tag_C m  ↦  tag_B ⊤        -- c.L ~ b.R
```

So the seams are exactly the places where a `⊥` of one copy and a `⊤`-or-marked
point of another are the same element — where the two ends cancel.  The first
seam is the marked point.

## The marked points are colimit-coherent — and that is new

Under the tag-`A` normalization (`midM mid = iotaGenM mid mid`),

```lean
dMid_succ_eq_iotaD : dMid (k + 1) = iotaD k (dMid k)      -- by rfl
```

The marked point of level `k+1` **is** the image of the marked point of level
`k`.  So the whole family collapses to a single element of the colimit:
`toD k (dMid k) = midInf` for every `k`, with `midInf := toD 0 (dMid 0)`.

This is a dividend of the 2026-08-28 basepoint decision and is **false under the
superseded tag-`B` convention**, where `dMid (k+1)` was `tag_B (markedPt k)` —
copy `B`, not in `iotaD`'s image at all.  Choosing tag `A` is what made the
tower's marked points assemble along the colimit, exactly as `pD_dMid_succ` made
them assemble along the bilimit (`PsiTargetTripointed.midSeq`).

`midInf` is interior on both sides (`bot_lt_midInf`, `midInf_lt_toD_top`), lives
at stage `0`, and is canonical.  It is the anchor the requirement asked for.

## What it does and does not settle

It does **not** make `lev` order-definable — that is still `StageFixed`.  What it
does is locate the base case exactly: stage `0` is `{⊥, midInf, toD 0 ⊤}`, `⊥` is
already order-theoretically fixed (it is the least element), and
`fixes_stage_of_maps_into` shows that an automorphism mapping a stage into
itself is the *identity* there.  So

> `StageFixed` at level `0` ⟺ every automorphism fixes `midInf` and `toD 0 ⊤`.

Two points. That is the smallest the base case can be made, and it says what to
attack: not "is level definable", but "is the seam definable".
-/

open scoped Classical

namespace MidAnchor

open Assembly ColimitCompatPipe JoinIrredDInfty

/-! ## The marked points are colimit-coherent -/

/-- **`dMid (k+1)` is `iotaD k (dMid k)` — on the nose.**  `midM mid` is
`iotaGenM mid mid = glueA (constHom mid) (constHom mid)`, and `iotaD k x` is
`glueA (markedPt k) (constHom x)` with `markedPt k = constHom (dMid k)`.  The
two are the same term. -/
theorem dMid_succ_eq_iotaD (k : ℕ) : dMid (k + 1) = iotaD k (dMid k) := rfl

theorem iotaLe_dMid {k n : ℕ} (h : k ≤ n) : iotaLe h (dMid k) = dMid n := by
  induction n, h using Nat.le_induction with
  | base => exact iotaLe_self _ _
  | succ m hm ih =>
      rw [iotaLe_succ hm (Nat.le_succ_of_le hm), ih, ← dMid_succ_eq_iotaD]

/-- **The seam, as a single point of the colimit.** -/
noncomputable def midInf : DInfty := toD 0 (dMid 0)

/-- Every level's marked point names the same element of `DInfty`. -/
theorem toD_dMid (k : ℕ) : toD k (dMid k) = midInf := by
  rw [midInf, ← toD_iotaLe (Nat.zero_le k) (dMid 0), iotaLe_dMid]

/-! ## `midInf` is interior on both sides -/

theorem midInf_ne_bot : midInf ≠ (⊥ : DInfty) := fun h =>
  dMid_ne_bot 0 ((toD_eq_bot_iff 0 (dMid 0)).mp h)

theorem bot_lt_midInf : (⊥ : DInfty) < midInf :=
  lt_of_le_of_ne bot_le (Ne.symm midInf_ne_bot)

theorem midInf_lt_toD_top (k : ℕ) : midInf < toD k (⊤ : D k) := by
  rw [← toD_dMid k]
  refine lt_of_le_of_ne ((toD_le_iff' k _ _).mpr le_top) ?_
  intro h
  exact dMid_ne_top k (toD_inj k h)

/-! ## An automorphism that maps a stage into itself is the identity there -/

/-- The per-level core of `Assembly.eq_refl_of_stageDefinable`, extracted: on a
single stage, "maps into" already forces "is the identity on".  It uses
`TowerRigidity.D_monotone_injection_eq_id`, so it needs no surjectivity. -/
theorem fixes_stage_of_maps_into (θ : DInfty ≃o DInfty) (k : ℕ)
    (h : ∀ x : D k, ∃ y : D k, θ (toD k x) = toD k y) (x : D k) :
    θ (toD k x) = toD k x := by
  choose f hf using h
  have hmono : Monotone f := by
    intro a b hab
    have h2 : θ (toD k a) ≤ θ (toD k b) := θ.monotone ((toD_le_iff' k a b).mpr hab)
    rw [hf a, hf b] at h2
    exact (toD_le_iff' k (f a) (f b)).mp h2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : θ (toD k a) = θ (toD k b) := by rw [hf a, hf b, hab]
    exact toD_inj k (θ.injective h1)
  have hid : f = id := TowerRigidity.D_monotone_injection_eq_id k hmono hinj
  rw [hf x, congrFun hid x]
  rfl

/-- **Base case of the residue, at its smallest.**  If `θ` keeps stage `0`
inside itself then it fixes the seam. -/
theorem fixes_midInf_of_maps_into (θ : DInfty ≃o DInfty)
    (h : ∀ x : D 0, ∃ y : D 0, θ (toD 0 x) = toD 0 y) : θ midInf = midInf := by
  rw [midInf]
  exact fixes_stage_of_maps_into θ 0 h (dMid 0)

/-- …and the top of stage `0` too.  Together with `⊥` — already fixed, being the
least element — those are all three points of stage `0`. -/
theorem fixes_toD_zero_top_of_maps_into (θ : DInfty ≃o DInfty)
    (h : ∀ x : D 0, ∃ y : D 0, θ (toD 0 x) = toD 0 y) :
    θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0) :=
  fixes_stage_of_maps_into θ 0 h (⊤ : D 0)

/-- **Stage `0` has exactly three points**, and `⊥` is one of them — so the
base case of `StageFixed` really is two points, `midInf` and `toD 0 ⊤`. -/
theorem stage_zero_eq :
    Set.range (toD 0) = {(⊥ : DInfty), midInf, toD 0 (⊤ : D 0)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
      show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
      revert x; decide
    rcases this with h | h | h
    · left; rw [h, ← bot_eq_toD 0]
    · right; left; rw [h, midInf]
    · right; right; rw [h]; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨(⊥ : D 0), (bot_eq_toD 0).symm⟩
    · exact ⟨dMid 0, rfl⟩
    · exact ⟨(⊤ : D 0), rfl⟩

end MidAnchor
