import Dinfty.PhiTriTower

open GluingTowerLibrary SierpinskiApplication

/-!
# The obstruction is one-directional: `Φ` acts on the tower's **projections**

Obstruction (T) (`Dinfty/TripointedObstruction.lean`) says a tagwise action of
`Φ` must be tripointed, and `PhiLimitContinuity` records the consequence for
ingredient 3: `δₙ = ιₙ ∘ pₙ` is not tripointed, so `Φ(δₙ)` is not an element of
the hom-poset and the hom-poset form of local continuity is unavailable.  Both
readings stopped at "the tower's ep-pair is not tripointed".

**That is only half true, and the half that fails is the embedding.**

* `pEndP k : EndP (D (k+1)) → EndP (D k)`, `g ↦ pD k ∘ g ∘ iotaD k`, **is
  tripointed** — `pTri` below.  `map_bot` and `map_top` were already on file
  (`pEndP_bot`, `pEndP_top`); `map_mark` is `pD_dMid_succ`, also on file.
* `iotaEndP k : EndP (D k) → EndP (D (k+1))`, `f ↦ iotaD k ∘ f ∘ pD k`, is
  **not** — `iotaEndP_top_ne_top`, and the reason is exactly `iotaD_ne_top`.

So the failure is entirely on the embedding side, and it is the *same* one line
(`iotaD k ⊤ ≠ ⊤`) that obstruction (T) turns on.

## Why the asymmetry matters

`EpPairTower.Bilim` is `{x : ∀ k, carrier k // ∀ k, prj k (x (k+1)) = x k}` — it
mentions `prj` and never `emb`.  The bilimit sees only the projection system.
`Φ` acts on the projection system.  So `Φ` acts on everything the bilimit sees,
even though it does not act on the tower's ep-pairs.

`phiP k := Φ (pTri k) : D (k+2) → D (k+1)` is that action written down.  It is
**not** `pD (k+1)`: `pD` reads a copy-`A` point by evaluating at `⊥`, while
`phiP` is tagwise.  That difference is exactly the `D∞` / `D∞^F` distinction the
`PsiIso` refutation turned on (`Meta/Finding - PsiIso tower mismatch`), now
visible as two projection systems on the same carriers rather than as a defect.
-/

universe u

namespace ProjectionTripointed

open PhiTriFunctor PhiTriTower GenContinuity

attribute [local instance 2000] endPDecidableEq

/-! ## The projection is tripointed -/

-- `pEndP_monotone` is `SierpinskiApplication.pEndP_monotone`; the re-proof that used to sit here was removed 2026-09-01 (identical statement).

/-- `pEndP k` bundled as an `OrderHom`, the shape `TriHom` wants. -/
noncomputable def pEndPHom (k : ℕ) : EndP (D (k + 1)) →o EndP (D k) :=
  ⟨pEndP k, pEndP_monotone k⟩

@[simp] theorem pEndPHom_apply (k : ℕ) (g : EndP (D (k + 1))) :
    pEndPHom k g = pEndP k g := rfl

/-- **The marked point is preserved.**  `markedPt` is a constant map, so this is
`pD k (dMid (k+1)) = dMid k`, i.e. `pD_dMid_succ`. -/
theorem pEndP_markedPt (k : ℕ) : pEndP k (markedPt (k + 1)) = markedPt k := by
  ext x
  show pD k ((markedPt (k + 1)) (iotaD k x)) = dMid k
  rw [markedPt_apply]
  exact pD_dMid_succ k

/-- **The tower's projection is a tripointed morphism.** -/
noncomputable def pTri (k : ℕ) : TowerHom (k + 1) k where
  toFun := pEndPHom k
  map_bot := pEndP_bot k
  map_mark := pEndP_markedPt k
  map_top := pEndP_top k

@[simp] theorem pTri_toFun (k : ℕ) (g : EndP (D (k + 1))) :
    (pTri k).toFun g = pEndP k g := rfl

/-! ## The embedding is not -/

/-- **`iotaEndP k` fails `map_top`.**  Its value at `⊤` is the constant
`iotaD k ⊤`, and `iotaD` never hits the top (`iotaD_ne_top`). -/
theorem iotaEndP_top_ne_top (k : ℕ) :
    iotaEndP k (⊤ : EndP (D k)) ≠ (⊤ : EndP (D (k + 1))) := by
  intro h
  have h1 := congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h
  exact iotaD_ne_top k _ h1

/-- **No tripointed morphism has `iotaEndP k` as its underlying map** — so the
tower's embedding is not a morphism of the category `Φ` is a functor on.  This
is obstruction (T) located precisely: on the embedding, not the ep-pair. -/
theorem no_towerHom_iotaEndP (k : ℕ) (f : TowerHom k (k + 1)) :
    (f.toFun : EndP (D k) → EndP (D (k + 1))) ≠ iotaEndP k := by
  intro h
  exact iotaEndP_top_ne_top k (h ▸ f.map_top)

/-! ## `Φ` applied to the projection -/

/-- **`Φ(p)`** — the F-tower's projection `D (k+2) → D (k+1)`. -/
noncomputable def phiP (k : ℕ) : D (k + 2) → D (k + 1) := phiTowerD (pTri k)

@[simp] theorem phiP_val (k : ℕ) (x : D (k + 2)) :
    (phiP k x).1 = canonGen (markedPt k) (baseMapGen (pEndPHom k) x.1) := rfl

theorem phiP_monotone (k : ℕ) : Monotone (phiP k) := fun _ _ h =>
  phiTower_monotone (pTri k) h

/-! ### Values on the three copies -/

theorem phiP_tagA (k : ℕ) (g : EndP (D (k + 1))) (h) :
    phiP k ⟨Sum.inl g, h⟩ = ⟨Sum.inl (pEndP k g), rfl⟩ :=
  Subtype.ext rfl

theorem phiP_bot (k : ℕ) : phiP k (⊥ : D (k + 2)) = (⊥ : D (k + 1)) := by
  rw [bot_succ_eq (k + 1), bot_succ_eq k]
  exact phiTower_triBot (pTri k)

theorem phiP_mid (k : ℕ) : phiP k (dMid (k + 2)) = dMid (k + 1) := by
  rw [dMid_succ_eq (k + 1), dMid_succ_eq k]
  exact phiTower_triMark (pTri k)

theorem phiP_top (k : ℕ) : phiP k (⊤ : D (k + 2)) = (⊤ : D (k + 1)) := by
  rw [top_succ_eq (k + 1), top_succ_eq k]
  exact phiTower_triTop (pTri k)

/-! ## The retraction: `Φ(p) ∘ glueAA = id`

`glueAA k` is the F-tower's embedding — `Φ` applied to the tower's ep-pair, with
the two correction terms `liftGenM` adds precisely because `iotaEndP` is *not*
tripointed.  `phiP k` is `Φ` applied to the projection, which needs no
correction.  They form a section/retraction pair. -/

set_option maxHeartbeats 4000000 in
/-- **`pEndP` undoes `liftGenM`.**  The correction terms vanish under
`pD k ∘ · ∘ iotaD k`: away from `f = ⊤` this is
`liftGenM_apply_iotaGenM_of_not_top` plus `pD_iotaD`, and at `f = ⊤` both sides
are `⊤`.  Stated in `Gen` names throughout — `pD k` *is* `pGenM (dMid k)` and
`iotaD k` *is* `iotaGenM (dMid k)`, but `rw` needs the syntactic form the
`GlueAAGenReflectM` lemmas use. -/
theorem pEndP_liftGenM (k : ℕ) (f : EndP (D k)) :
    pEndP k (liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial f) = f := by
  ext x
  show pGenM (dMid k) ((liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial f) (iotaGenM (dMid k) x)) = f x
  by_cases hft : (⊤ : EndP (D k)) ≤ f
  · have hf : f = (⊤ : EndP (D k)) := top_le_iff.mp hft
    subst hf
    rw [liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial]
    simp only [endPTop_apply]
    exact pGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial
  · rw [liftGenM_apply_iotaGenM_of_not_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial hft x]
    exact pGenM_section (dMid k) (f x)

/-- **`pEndP` undoes `iotaEndP`** — the tower's own section, restated at the
`Gen`-layer name `glueAAGenM` uses on copy `A`. -/
theorem pEndP_iotaEndPGenM (k : ℕ) (f : EndP (D k)) :
    pEndP k (iotaEndPGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial f) = f :=
  pEndP_iotaEndP k f

set_option maxHeartbeats 4000000 in
/-- **The F-tower's embedding and `Φ`'s projection form a section/retraction
pair.**  Copy `A` is `pEndP_iotaEndP`; copies `B` and `C` are `pEndP_liftGenM`
after the descent lemma `canonGen_baseMapGen_canon` strips `glueAA`'s
canonicalisation — the one place where `Φ` being a *descent* rather than a
restriction is what makes the computation go through. -/
theorem phiP_glueAA (k : ℕ) (x : D (k + 1)) : phiP k (glueAA k x) = x := by
  refine Subtype.ext ?_
  obtain ⟨xv, hxv⟩ := x
  have hstrip : ∀ v : GlueBaseGen (EndP (D (k + 1))),
      canonGen (markedPt k) (baseMapGen (pTri k).toFun (canonGen (markedPt (k + 1)) v))
        = canonGen (markedPt k) (baseMapGen (pTri k).toFun v) :=
    fun v => canonGen_baseMapGen_canon (pTri k) (markedPt_ne_bot (k + 1))
      (markedPt_ne_bot k) (D_marked_point_nondegenerate k).2.2 v
  rcases xv with f | f | f
  · show Sum.inl (pEndP k (iotaEndPGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f)) = Sum.inl f
    rw [pEndP_iotaEndPGenM k f]
  · show canonGen (markedPt k) (baseMapGen (pTri k).toFun
      (canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl (liftGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f))))) = Sum.inr (Sum.inl f)
    rw [hstrip]
    show canonGen (markedPt k) (Sum.inr (Sum.inl (pEndP k (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f))))
        = Sum.inr (Sum.inl f)
    rw [pEndP_liftGenM k f]
    exact hxv
  · show canonGen (markedPt k) (baseMapGen (pTri k).toFun
      (canonGen (markedPt (k + 1)) (Sum.inr (Sum.inr (liftGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f))))) = Sum.inr (Sum.inr f)
    rw [hstrip]
    show canonGen (markedPt k) (Sum.inr (Sum.inr (pEndP k (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f))))
        = Sum.inr (Sum.inr f)
    rw [pEndP_liftGenM k f]
    exact hxv

/-! ## But it is **not** an ep-pair: the deflation fails

A section/retraction pair is not an ep-pair.  `EpPairTower` also asks for
`emb (prj z) ≤ z`, and that fails — with a witness that is exactly the one line
obstruction (T) turns on, `iotaD k ⊤ ≠ ⊤`, showing up a third time.

The bad point is `tag_B (constHom (iotaD k ⊤))`: a copy-`B` point of `D (k+2)`
whose tag is the constant at the *image of the top*.  `pEndP` cannot tell that
apart from the constant at `⊤` — `pD k (iotaD k ⊤) = ⊤` — so `Φ(p)` sends it to
`tag_B ⊤`, `glueAA` sends that to `tag_B ⊤` one level up, and `tag_B ⊤` is not
below where we started. -/

theorem constHom_iotaD_top_ne_bot (k : ℕ) :
    (constHom (iotaD k (⊤ : D k)) : EndP (D (k + 1))) ≠ ⊥ := by
  intro h
  have h2 : iotaD k (⊤ : D k) = (⊥ : D (k + 1)) :=
    congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h
  have h3 : iotaD k (dMid k) ≤ iotaD k (⊤ : D k) := iotaD_monotone k le_top
  rw [h2] at h3
  exact dMid_ne_bot (k + 1) (le_bot_iff.mp h3)

theorem constHom_iotaD_top_ne_top (k : ℕ) :
    (constHom (iotaD k (⊤ : D k)) : EndP (D (k + 1))) ≠ ⊤ := fun h =>
  iotaD_ne_top k (⊤ : D k)
    (congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h)

/-- `pEndP` collapses `constHom (iotaD k ⊤)` to `⊤`, because `pD k (iotaD k ⊤) = ⊤`. -/
theorem pEndP_constHom_iotaD_top (k : ℕ) :
    pEndP k (constHom (iotaD k (⊤ : D k))) = (⊤ : EndP (D k)) := by
  ext x
  show pD k (iotaD k (⊤ : D k)) = (⊤ : EndP (D k)) x
  rw [pD_iotaD, endPTop_apply]

set_option maxHeartbeats 4000000 in
/-- **The deflation fails.**  `(glueAA k, phiP k)` is a section/retraction pair
but **not** an embedding/projection pair, so the F-iterate tower is not an
`EpPairTower` when its projection is `Φ`'s own.  The witness is a copy-`B`
point.

The bad tag is bound as an opaque local `c` on purpose: writing
`constHom (iotaD k ⊤)` inside a `D (k+2)`-typed anonymous constructor forces the
elaborator to unfold `D (k+2)` and then it cannot find `Lattice (D (k+1))`
again. -/
theorem not_glueAA_phiP_deflation (k : ℕ) :
    ¬ ∀ z : D (k + 2), glueAA k (phiP k z) ≤ z := by
  intro hdefl
  obtain ⟨c, hc⟩ : ∃ c : EndP (D (k + 1)), c = constHom (iotaD k (⊤ : D k)) := ⟨_, rfl⟩
  have hne : c ≠ ⊥ := by rw [hc]; exact constHom_iotaD_top_ne_bot k
  have hct : c ≠ ⊤ := by rw [hc]; exact constHom_iotaD_top_ne_top k
  have hpc : pEndP k c = (⊤ : EndP (D k)) := by rw [hc]; exact pEndP_constHom_iotaD_top k
  have hbt : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2
  have hbt1 : (⊥ : EndP (D (k + 1))) ≠ ⊤ := (D_marked_point_nondegenerate (k + 1)).2.2
  have hz : canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl c)) = Sum.inr (Sum.inl c) := by
    simp only [canonGen]
    rw [if_neg hne]
  have hzt : canonGen (markedPt k) (Sum.inr (Sum.inl (⊤ : EndP (D k))))
      = Sum.inr (Sum.inl (⊤ : EndP (D k))) := by
    simp only [canonGen]
    rw [if_neg (Ne.symm hbt)]
  -- `Φ(p)` cannot tell the bad point from `tag_B ⊤`
  have hphi : phiP k ⟨Sum.inr (Sum.inl c), hz⟩
      = (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1)) := by
    refine Subtype.ext ?_
    show canonGen (markedPt k) (Sum.inr (Sum.inl (pEndP k c))) = _
    rw [hpc]
    exact hzt
  -- and `glueAA` sends `tag_B ⊤` to `tag_B ⊤` one level up
  have hglue : (glueAA k (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1))).1
      = Sum.inr (Sum.inl (⊤ : EndP (D (k + 1)))) := by
    show canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial (⊤ : EndP (D k))))) = _
    rw [liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial]
    simp only [canonGen]
    split_ifs with hcon
    · exact absurd hcon.symm hbt1
    · rfl
  have hle := hdefl ⟨Sum.inr (Sum.inl c), hz⟩
  rw [hphi] at hle
  -- `≤` at `D (k+2)` IS `leGlueGen` on the values (`le_succ_eq`, `rfl`), so the
  -- conversion is `exact`; only then can `hglue` be rewritten in.
  have hraw : leGlueGen (markedPt (k + 1))
      ((glueAA k (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1))).1)
      (Sum.inr (Sum.inl c)) := hle
  rw [hglue] at hraw
  have hle2 : (⊤ : EndP (D (k + 1))) ≤ c :=
    (leGlue_tagB_tagB_iffGen (markedPt (k + 1)) _ _ hct (Ne.symm hbt1)).mp hraw
  rw [hc] at hle2
  exact iotaD_ne_top k (⊤ : D k)
    (top_le_iff.mp (OrderHom.le_def.mp hle2 (⊥ : D (k + 1))))

end ProjectionTripointed
