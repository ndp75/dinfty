import Dinfty.EmbDImage
import Dinfty.CopyHierarchy

open GluingTowerLibrary SierpinskiApplication

/-!
# The tower's embeddings are tagwise, and so is their image

§111 left the residue as: *a bounded join-embedding `f : D (k+1) → D (m+1)`
sends join-irreducibles into `Set.range (embD h)`.*  This module unfolds
`Set.range (embD h)`, and the answer is as clean as it could be.

## `Φ` on morphisms never changes a copy

`phiFun g = canonGen ∘ baseMapGen g`, and `baseMapGen` is tagwise by definition.
The `canonGen` is *inert*: its three collapses are triggered by a tag-`B` payload
at `⊥` and a tag-`C` payload at `⊥` or at the mark, and an **injective tripointed**
`g` cannot produce any of those from a canonical point.  So

```lean
phiFun_val_tagwise (g) (hginj) (x) : (phiFun g … x).1 = baseMapGen g.toFun x.1
```

on the nose.  At the tower `(iter (n+1)).emb = phiTowerD (iter n).endUp` and
`endUp` is injective (it has `endDown` as a retraction), so

```lean
emb_succ_val (n) (x) : ((iter (n+1)).emb x).1 = baseMapGen (endUpFun) x.1
emb_succ_copyIdx (n) (x) : copyIdx ((iter (n+1)).emb x).1 = copyIdx x.1
```

**Every embedding of the `Φ`-tower preserves the copy index.**  That is the fact
the remaining analysis has to match.

## The image, tagwise

```lean
mem_range_emb_succ_iff (n) (z) :
  z ∈ Set.range ((iter (n+1)).emb) ↔ ∃ w, baseMapGen endUpFun w.1 = z.1
```

and copy by copy the condition is membership in `Set.range endUpFun`
(`mem_range_emb_succ_inl` for tag `A`).  Since
`endUpFun E h = E.emb ∘ h ∘ E.prj`, that range is the endomorphisms fixed by
conjugation with the deflation `E.emb ∘ E.prj` — the same shape as
`EmbDImage.mem_range_embD_iff`, one level down in `EndP`.  **The image condition
is recursive**, and it bottoms out at `emb 0 = glueAA 0`, whose copies are
`iotaEndPGen` (tag `A`) and `liftGen` (tags `B`, `C`) — both with a full
`_eq_bot_iff` / `_eq_id_iff` / `_eq_top_iff` API already in the library.

## What this makes of the residue

The residue is now an **inductive step**.  If a bounded join-embedding
`f : D (k+1) → D (m+1)` is forced to be tagwise, then `f` is `Φ` of a map one
level down with the same properties, and the recursion runs.  So the open
question is exactly:

> must such an `f` preserve the copy index?

`CopyHierarchy.copyIdx_mono`, `tagA_source` and `tagC_sink` are the tools aimed
at it, `f ⊥ = ⊥` and `f ⊤ = ⊤` are the boundary conditions (`⊥` is in copy `A`,
`⊤` in copy `C`), and the join-irreducibles of `D (k+1)` are already classified
by copy (`dSuccCases`, `joinIrred_glueA_iff`).  This module does not answer it.
-/

open Set

open scoped Classical

namespace EmbTagwise

open PhiTriFunctor GenContinuity

universe u

/-! ## 1.  `canonGen` is inert on the image of an injective tripointed map -/

section Generic

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

/-- The tag-`C` companion of `ne_bot_of_canon_tagCGen`: a canonical tag-`C`
payload is not the mark either. -/
theorem ne_mark_of_canon_tagC (c : P) (hc : c ≠ ⊥)
    (hw : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c)) : c ≠ m := by
  intro hcm
  rw [canonGen, if_neg hc, if_pos hcm] at hw
  exact Sum.inl_ne_inr (Sum.inr_injective hw)

/-- **`canonGen` is inert.**  An injective tripointed `g` cannot send a canonical
point onto one of the three collapse sites. -/
theorem canonGen_baseMapGen (g : TriHom m m') (hginj : Function.Injective g.toFun)
    {w : GlueBaseGen P} (hw : canonGen m w = w) :
    canonGen m' (baseMapGen g.toFun w) = baseMapGen g.toFun w := by
  cases w with
  | inl a => rfl
  | inr w =>
    cases w with
    | inl b =>
        have hb : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hw
        have hgb : g.toFun b ≠ ⊥ := fun hc => hb (hginj (hc.trans g.map_bot.symm))
        change canonGen m' (Sum.inr (Sum.inl (g.toFun b))) = _
        rw [canonGen, if_neg hgb]
        rfl
    | inr c =>
        have hc : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hw
        have hcm : c ≠ m := ne_mark_of_canon_tagC c hc hw
        have hgc : g.toFun c ≠ ⊥ := fun hcon => hc (hginj (hcon.trans g.map_bot.symm))
        have hgcm : g.toFun c ≠ m' := fun hcon => hcm (hginj (hcon.trans g.map_mark.symm))
        change canonGen m' (Sum.inr (Sum.inr (g.toFun c))) = _
        rw [canonGen, if_neg hgc, if_neg hgcm]
        rfl

/-- **`Φ` on morphisms is tagwise on the nose.** -/
theorem phiFun_val_tagwise (g : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (hginj : Function.Injective g.toFun) (x : GlueCarGen (P := P) m) :
    (phiFun g hm' hbt' x).1 = baseMapGen g.toFun x.1 :=
  canonGen_baseMapGen g hginj x.2

/-- `baseMapGen` never changes a copy. -/
theorem baseMapGen_copyIdx (g : P →o P') (w : GlueBaseGen P) :
    CopyHierarchy.copyIdx (baseMapGen g w) = CopyHierarchy.copyIdx w := by
  cases w with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

end Generic

/-! ## 2.  At the `Φ`-iterate tower -/

open PhiIterateTower PhiTriTower

private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

theorem endDownFun_endUpFun (n : ℕ) (h : EndP (D (n + 1))) :
    (iter n).endDownFun ((iter n).endUpFun h) = h := by
  ext x
  show (iter n).prj ((iter n).emb (h ((iter n).prj ((iter n).emb x)))) = h x
  rw [(iter n).retraction, (iter n).retraction]

theorem endUpFun_injective (n : ℕ) : Function.Injective (iter n).endUpFun := by
  intro h h' hh
  rw [← endDownFun_endUpFun n h, ← endDownFun_endUpFun n h', hh]

/-- **The tower's embeddings are tagwise on the nose.** -/
theorem emb_succ_val (n : ℕ) (x : D (n + 2)) :
    ((iter (n + 1)).emb x).1 = baseMapGen (iter n).endUp.toFun x.1 :=
  phiFun_val_tagwise (iter n).endUp (hmk' (n + 2)) (hbtk' (n + 2))
    (endUpFun_injective n) x

/-- **…so they preserve the copy index.**  This is the shape the remaining
analysis has to match. -/
theorem emb_succ_copyIdx (n : ℕ) (x : D (n + 2)) :
    CopyHierarchy.copyIdx ((iter (n + 1)).emb x).1 = CopyHierarchy.copyIdx x.1 := by
  rw [emb_succ_val]
  exact baseMapGen_copyIdx _ _

/-! ## 3.  The image, tagwise -/

theorem mem_range_emb_succ_iff (n : ℕ) (z : D (n + 3)) :
    z ∈ Set.range ((iter (n + 1)).emb) ↔
      ∃ w : D (n + 2), baseMapGen (iter n).endUp.toFun w.1 = z.1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (emb_succ_val n w).symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext ((emb_succ_val n w).trans hw)⟩

/-- **The tag-`A` slot of the image is `Set.range endUpFun`.**  Tags `B` and `C`
are the same computation with the canonical-payload side conditions. -/
theorem range_val_emb_succ_inl (n : ℕ) (z : D (n + 3)) (a : EndP (D (n + 2)))
    (hz : z.1 = Sum.inl a) :
    z ∈ Set.range ((iter (n + 1)).emb) ↔ a ∈ Set.range (iter n).endUpFun := by
  constructor
  · rintro ⟨w, rfl⟩
    have hv := emb_succ_val n w
    rw [hz] at hv
    cases hwv : w.1 with
    | inl b =>
        rw [hwv] at hv
        exact ⟨b, (Sum.inl_injective hv).symm⟩
    | inr v =>
        exfalso
        rw [hwv] at hv
        cases v with
        | inl _ => exact Sum.inl_ne_inr hv
        | inr _ => exact Sum.inl_ne_inr hv
  · rintro ⟨b, hb⟩
    refine ⟨glueA (markedPt (n + 1)) b, Subtype.ext ?_⟩
    rw [emb_succ_val, hz, ← hb]
    rfl

end EmbTagwise
