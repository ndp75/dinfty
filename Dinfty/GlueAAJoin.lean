import Dinfty.GlueAAEpPartner

open GluingTowerLibrary SierpinskiApplication

/-!
# `glueAA` preserves binary joins — the tag lemmas

§80 left pillar A resting on one identity per level,
`GlueAAEpPartner.GlueAAJoinPreserving k`.  This module builds the pieces; the
nine-case verification follows.

`glueAA k` is `iotaEndP k` on copy `A` and `liftGenM` on copies `B` and `C`.
Everything below is stated through wrappers **declared** at `EndP (D (k+1))` and
`D (k+1)` rather than at the raw `GlueCar (constHom (dMid k))`, because `⊔`,
`⊥` and `⊤` do not resolve on the latter (§80's gotcha).

## The two facts that are not bookkeeping

The join formula `glueJoinRaw` has four guarded branches, and the identity turns
on those guards being *preserved*:

```lean
iotaEndP_le_marked_iff : iotaEndP k f ≤ markedPt (k+1) ↔ f ≤ markedPt k
marked_le_liftT_iff    : markedPt (k+1) ≤ liftT k f    ↔ markedPt k ≤ f
```

Both go through `pD_iotaD`: the projection has the copy-`A` inclusion as a
section, so a pointwise statement over `D (k+1)` restricted along `iotaD k`
recovers the statement over `D k`.  The second also needs
`liftGenM_apply_iotaGenM_of_not_top` — away from `f = ⊤` the two correction
terms vanish on the image of `iotaD k`.
-/

open scoped Classical

namespace GlueAAJoin

open JoinPrimality GlueAAEpPartner

/-! ## `liftGenM`, declared at the tower -/

/-- `liftGenM` with its result type **declared** at `EndP (D (k+1))`. -/
noncomputable def liftT (k : ℕ) (f : EndP (D k)) : EndP (D (k + 1)) :=
  liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f

theorem liftT_apply (k : ℕ) (f : EndP (D k)) (w : D (k + 1)) :
    liftT k f w = liftVal k f w := rfl

theorem liftT_bot (k : ℕ) : liftT k (⊥ : EndP (D k)) = (⊥ : EndP (D (k + 1))) :=
  liftGenM_bot (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem liftT_mid (k : ℕ) : liftT k (markedPt k) = markedPt (k + 1) :=
  liftGenM_mid (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem liftT_top (k : ℕ) : liftT k (⊤ : EndP (D k)) = (⊤ : EndP (D (k + 1))) :=
  liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem liftT_eq_bot_iff (k : ℕ) {f : EndP (D k)} :
    liftT k f = (⊥ : EndP (D (k + 1))) ↔ f = ⊥ :=
  liftGenM_eq_bot_iff (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem liftT_eq_mid_iff (k : ℕ) {f : EndP (D k)} :
    liftT k f = markedPt (k + 1) ↔ f = markedPt k :=
  liftGenM_eq_mid_iff (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

theorem liftT_monotone (k : ℕ) {f g : EndP (D k)} (h : f ≤ g) : liftT k f ≤ liftT k g :=
  liftGenM_monotone (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial h

theorem liftT_ne_bot (k : ℕ) {f : EndP (D k)} (hf : f ≠ ⊥) :
    liftT k f ≠ (⊥ : EndP (D (k + 1))) := fun h => hf ((liftT_eq_bot_iff k).mp h)

theorem liftT_ne_mid (k : ℕ) {f : EndP (D k)} (hf : f ≠ markedPt k) :
    liftT k f ≠ markedPt (k + 1) := fun h => hf ((liftT_eq_mid_iff k).mp h)

/-- **`liftT` preserves binary joins** — round 49's `liftVal_sup`, bundled. -/
theorem liftT_sup (k : ℕ) (f g : EndP (D k)) :
    liftT k (f ⊔ g) = liftT k f ⊔ liftT k g := by
  ext w
  show liftVal k (f ⊔ g) w = (liftT k f ⊔ liftT k g) w
  simp only [OrderHom.coe_sup, Pi.sup_apply]
  exact liftVal_sup k f g w

/-! ## The two guards -/

/-- **Copy `A`'s guard is preserved.**  `pD_iotaD` gives the reverse direction:
testing at `iotaD k z` recovers the statement over `D k`. -/
theorem iotaEndP_le_marked_iff (k : ℕ) (f : EndP (D k)) :
    iotaEndP k f ≤ markedPt (k + 1) ↔ f ≤ markedPt k := by
  constructor
  · intro h
    rw [OrderHom.le_def]
    intro z
    have h1 : iotaD k (f (pD k (iotaD k z))) ≤ dMid (k + 1) :=
      OrderHom.le_def.mp h (iotaD k z)
    rw [pD_iotaD k z] at h1
    exact (iotaD_le_iff k (f z) (dMid k)).mp h1
  · intro h
    rw [OrderHom.le_def]
    intro w
    show iotaD k (f (pD k w)) ≤ dMid (k + 1)
    exact iotaD_monotone k (OrderHom.le_def.mp h (pD k w))

/-- **Copy `C`'s guard is preserved.**  Away from `f = ⊤` the two correction
terms in `liftGenM` vanish on the image of `iotaD k`
(`liftGenM_apply_iotaGenM_of_not_top`), and at `f = ⊤` both sides hold. -/
theorem marked_le_liftT_iff (k : ℕ) (f : EndP (D k)) :
    markedPt (k + 1) ≤ liftT k f ↔ markedPt k ≤ f := by
  constructor
  · intro h
    by_cases hft : f = (⊤ : EndP (D k))
    · rw [hft]; exact le_top
    · have hnt : ¬ (⊤ : EndP (D k)) ≤ f := fun hc => hft (top_le_iff.mp hc)
      rw [OrderHom.le_def]
      intro z
      have e : liftT k f (iotaD k z) = iotaD k (f z) :=
        liftGenM_apply_iotaGenM_of_not_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
          bot_ne_top_of_nontrivial hnt z
      have h1 : dMid (k + 1) ≤ liftT k f (iotaD k z) := OrderHom.le_def.mp h (iotaD k z)
      rw [e] at h1
      exact (iotaD_le_iff k (dMid k) (f z)).mp h1
  · intro h
    have h1 := liftT_monotone k h
    rwa [liftT_mid k] at h1

/-! ## `glueAA` on the three copies, canon-free -/

theorem glueAA_glueA (k : ℕ) (f : EndP (D k)) :
    glueAA k (glueA (markedPt k) f) = glueA (markedPt (k + 1)) (iotaEndP k f) :=
  Subtype.ext rfl

set_option maxHeartbeats 4000000 in
theorem glueAA_glueB (k : ℕ) (f : EndP (D k)) (hf : f ≠ ⊥) :
    glueAA k (glueB (markedPt k) f hf)
      = glueB (markedPt (k + 1)) (liftT k f) (liftT_ne_bot k hf) := by
  refine Subtype.ext ?_
  show canon (markedPt (k + 1)) (Sum.inr (Sum.inl (liftT k f)))
    = Sum.inr (Sum.inl (liftT k f))
  simp only [canon]
  rw [if_neg (liftT_ne_bot k hf)]

set_option maxHeartbeats 4000000 in
theorem glueAA_glueC (k : ℕ) (f : EndP (D k)) (hf : f ≠ ⊥) (hfm : f ≠ markedPt k) :
    glueAA k (glueC (markedPt k) f hf hfm)
      = glueC (markedPt (k + 1)) (liftT k f) (liftT_ne_bot k hf) (liftT_ne_mid k hfm) := by
  refine Subtype.ext ?_
  show canon (markedPt (k + 1)) (Sum.inr (Sum.inr (liftT k f)))
    = Sum.inr (Sum.inr (liftT k f))
  simp only [canon]
  rw [if_neg (liftT_ne_bot k hf), if_neg (liftT_ne_mid k hfm)]

/-! ## The join, read on values -/

theorem sup_val (k : ℕ) (x y : D (k + 1)) :
    (x ⊔ y).1 = canon (markedPt k) (glueJoinRaw (markedPt k) x.1 y.1) := rfl

/-! ## `canon` and `glueJoinRaw`, one branch at a time

Generic in `P`, so each is used twice — once at `EndP (D k)` and once at
`EndP (D (k+1))`.  The conditional branches are stated as `_pos` / `_neg` pairs
rather than with an `if`, because `glueJoinRaw`'s guards carry `latticeDecLE`
and an `if` written at the use site would carry the ambient classical instance
instead. -/

section Branches

variable {P : Type} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

@[simp] theorem canon_inl (m a : P) : canon m (Sum.inl a) = Sum.inl a := rfl

theorem canon_inrl_of_ne (m : P) {a : P} (ha : a ≠ ⊥) :
    canon m (Sum.inr (Sum.inl a)) = Sum.inr (Sum.inl a) := by
  simp only [canon]
  rw [if_neg ha]

theorem canon_inrr_of_ne (m : P) {a : P} (ha : a ≠ ⊥) (ham : a ≠ m) :
    canon m (Sum.inr (Sum.inr a)) = Sum.inr (Sum.inr a) := by
  simp only [canon]
  rw [if_neg ha, if_neg ham]

theorem canon_inrr_mid {m : P} (hm : m ≠ ⊥) :
    canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤) := by
  simp only [canon]
  rw [if_neg hm]
  simp

@[simp] theorem gjr_AA (m f g : P) :
    glueJoinRaw m (Sum.inl f) (Sum.inl g) = Sum.inl (f ⊔ g) := rfl

@[simp] theorem gjr_BB (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inl (f ⊔ g)) := rfl

@[simp] theorem gjr_CC (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr (f ⊔ g)) := rfl

@[simp] theorem gjr_AC (m f g : P) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inr g)) = Sum.inr (Sum.inr g) := rfl

@[simp] theorem gjr_CA (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inl g) = Sum.inr (Sum.inr f) := rfl

theorem gjr_AB_pos (m f g : P) (h : f ≤ m) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inl g)) = Sum.inr (Sum.inl g) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

theorem gjr_AB_neg (m f g : P) (h : ¬ f ≤ m) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inl g)) = Sum.inr (Sum.inr m) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

theorem gjr_BA_pos (m f g : P) (h : g ≤ m) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inl g) = Sum.inr (Sum.inl f) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

theorem gjr_BA_neg (m f g : P) (h : ¬ g ≤ m) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inl g) = Sum.inr (Sum.inr m) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

theorem gjr_BC_pos (m f g : P) (h : m ≤ g) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr g) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

theorem gjr_BC_neg (m f g : P) (h : ¬ m ≤ g) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr (g ⊔ m)) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

theorem gjr_CB_pos (m f g : P) (h : m ≤ f) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inr f) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

theorem gjr_CB_neg (m f g : P) (h : ¬ m ≤ f) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inr (f ⊔ m)) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

theorem canonC_ne_mid {m w : P}
    (h : canon m (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w)) : w ≠ m := by
  intro hw
  rw [hw] at h
  simp only [canon] at h
  split_ifs at h <;> simp at h

theorem sup_ne_bot_of_left {f g : P} (hf : f ≠ ⊥) : f ⊔ g ≠ ⊥ := fun h =>
  hf (le_bot_iff.mp (le_trans le_sup_left h.le))

end Branches

/-! ## The tagwise payload map -/

/-- `glueAA`'s payload action, before canonicalisation. -/
noncomputable def tagMap (k : ℕ) :
    GlueBase (EndP (D k)) → GlueBase (EndP (D (k + 1)))
  | Sum.inl f => Sum.inl (iotaEndP k f)
  | Sum.inr (Sum.inl f) => Sum.inr (Sum.inl (liftT k f))
  | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr (liftT k f))

@[simp] theorem tagMap_inl (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inl f) = Sum.inl (iotaEndP k f) := rfl

@[simp] theorem tagMap_inrl (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl (liftT k f)) := rfl

@[simp] theorem tagMap_inrr (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr (liftT k f)) := rfl

set_option maxHeartbeats 4000000 in
theorem glueAA_val (k : ℕ) (z : D (k + 1)) :
    (glueAA k z).1 = canon (markedPt (k + 1)) (tagMap k z.1) := by
  obtain ⟨zv, hzv⟩ := z
  rcases zv with f | f | f <;> rfl

set_option maxHeartbeats 4000000 in
theorem canon_tagMap (k : ℕ) (u : GlueBase (EndP (D k)))
    (hu : canon (markedPt k) u = u) :
    canon (markedPt (k + 1)) (tagMap k u) = tagMap k u := by
  rcases u with f | f | f
  · rfl
  · rw [tagMap_inrl]
    exact canon_inrl_of_ne _ (liftT_ne_bot k (ne_bot_of_canon_tagB (markedPt k) f hu))
  · rw [tagMap_inrr]
    exact canon_inrr_of_ne _
      (liftT_ne_bot k (CopyBExclusion.canonCFixBot hu))
      (liftT_ne_mid k (canonC_ne_mid hu))

/-! ## The nine cases

`glueAA z = canon m' (T z)` for canon-fixed `z`, so the whole identity is one
equation on raw values.  Having `canon m'` on **both** sides is what keeps the
cases short: the four places where the base join leaves the tag it started in
all end as `canon m' (tag_C m') = tag_B ⊤` on the right and `tag_B (liftT ⊤)` on
the left, which `liftT_top` closes. -/

set_option maxHeartbeats 4000000 in
/-- **The core identity**, on raw canon-fixed values. -/
theorem core (k : ℕ) (u v : GlueBase (EndP (D k)))
    (hu : canon (markedPt k) u = u) (hv : canon (markedPt k) v = v) :
    canon (markedPt (k + 1))
        (tagMap k (canon (markedPt k) (glueJoinRaw (markedPt k) u v)))
      = canon (markedPt (k + 1))
        (glueJoinRaw (markedPt (k + 1)) (tagMap k u) (tagMap k v)) := by
  have hm : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
  have hm' : (markedPt (k + 1)) ≠ ⊥ := (D_marked_point_nondegenerate (k + 1)).1
  have hbt' : (⊥ : EndP (D (k + 1))) ≠ ⊤ := (D_marked_point_nondegenerate (k + 1)).2.2
  rcases u with f | f | f
  · rcases v with g | g | g
    · -- A, A
      simp only [gjr_AA, canon_inl, tagMap_inl]
      rw [iotaEndP_sup]
    · -- A, B
      have hg : g ≠ ⊥ := ne_bot_of_canon_tagB (markedPt k) g hv
      by_cases hfm : f ≤ markedPt k
      · rw [gjr_AB_pos _ _ _ hfm, canon_inrl_of_ne _ hg]
        simp only [tagMap_inl, tagMap_inrl]
        rw [gjr_AB_pos _ _ _ ((iotaEndP_le_marked_iff k f).mpr hfm)]
      · rw [gjr_AB_neg _ _ _ hfm, canon_inrr_mid hm]
        simp only [tagMap_inl, tagMap_inrl]
        rw [liftT_top, canon_inrl_of_ne _ (Ne.symm hbt'),
          gjr_AB_neg _ _ _ (fun hc => hfm ((iotaEndP_le_marked_iff k f).mp hc)),
          canon_inrr_mid hm']
    · -- A, C
      have hg : g ≠ ⊥ := CopyBExclusion.canonCFixBot hv
      have hgm : g ≠ markedPt k := canonC_ne_mid hv
      simp only [gjr_AC, tagMap_inl, tagMap_inrr]
      rw [canon_inrr_of_ne _ hg hgm, tagMap_inrr]
  · rcases v with g | g | g
    · -- B, A
      have hf : f ≠ ⊥ := ne_bot_of_canon_tagB (markedPt k) f hu
      by_cases hgm : g ≤ markedPt k
      · rw [gjr_BA_pos _ _ _ hgm, canon_inrl_of_ne _ hf]
        simp only [tagMap_inrl, tagMap_inl]
        rw [gjr_BA_pos _ _ _ ((iotaEndP_le_marked_iff k g).mpr hgm)]
      · rw [gjr_BA_neg _ _ _ hgm, canon_inrr_mid hm]
        simp only [tagMap_inrl, tagMap_inl]
        rw [liftT_top, canon_inrl_of_ne _ (Ne.symm hbt'),
          gjr_BA_neg _ _ _ (fun hc => hgm ((iotaEndP_le_marked_iff k g).mp hc)),
          canon_inrr_mid hm']
    · -- B, B
      have hf : f ≠ ⊥ := ne_bot_of_canon_tagB (markedPt k) f hu
      simp only [gjr_BB, tagMap_inrl]
      rw [canon_inrl_of_ne _ (sup_ne_bot_of_left hf), tagMap_inrl, liftT_sup]
    · -- B, C
      have hg : g ≠ ⊥ := CopyBExclusion.canonCFixBot hv
      have hgm : g ≠ markedPt k := canonC_ne_mid hv
      by_cases hmg : markedPt k ≤ g
      · rw [gjr_BC_pos _ _ _ hmg, canon_inrr_of_ne _ hg hgm]
        simp only [tagMap_inrl, tagMap_inrr]
        rw [gjr_BC_pos _ _ _ ((marked_le_liftT_iff k g).mpr hmg)]
      · rw [gjr_BC_neg _ _ _ hmg]
        simp only [tagMap_inrl, tagMap_inrr]
        rw [gjr_BC_neg _ _ _ (fun hc => hmg ((marked_le_liftT_iff k g).mp hc)),
          ← liftT_mid k, ← liftT_sup]
        by_cases hsm : g ⊔ markedPt k = markedPt k
        · rw [hsm, canon_inrr_mid hm, tagMap_inrl, liftT_top,
            canon_inrl_of_ne _ (Ne.symm hbt'), liftT_mid k, canon_inrr_mid hm']
        · rw [canon_inrr_of_ne _ (sup_ne_bot_of_left hg) hsm, tagMap_inrr]
  · rcases v with g | g | g
    · -- C, A
      have hf : f ≠ ⊥ := CopyBExclusion.canonCFixBot hu
      have hfm : f ≠ markedPt k := canonC_ne_mid hu
      simp only [gjr_CA, tagMap_inrr, tagMap_inl]
      rw [canon_inrr_of_ne _ hf hfm, tagMap_inrr]
    · -- C, B
      have hf : f ≠ ⊥ := CopyBExclusion.canonCFixBot hu
      have hfm : f ≠ markedPt k := canonC_ne_mid hu
      by_cases hmf : markedPt k ≤ f
      · rw [gjr_CB_pos _ _ _ hmf, canon_inrr_of_ne _ hf hfm]
        simp only [tagMap_inrr, tagMap_inrl]
        rw [gjr_CB_pos _ _ _ ((marked_le_liftT_iff k f).mpr hmf)]
      · rw [gjr_CB_neg _ _ _ hmf]
        simp only [tagMap_inrr, tagMap_inrl]
        rw [gjr_CB_neg _ _ _ (fun hc => hmf ((marked_le_liftT_iff k f).mp hc)),
          ← liftT_mid k, ← liftT_sup]
        by_cases hsm : f ⊔ markedPt k = markedPt k
        · rw [hsm, canon_inrr_mid hm, tagMap_inrl, liftT_top,
            canon_inrl_of_ne _ (Ne.symm hbt'), liftT_mid k, canon_inrr_mid hm']
        · rw [canon_inrr_of_ne _ (sup_ne_bot_of_left hf) hsm, tagMap_inrr]
    · -- C, C
      have hf : f ≠ ⊥ := CopyBExclusion.canonCFixBot hu
      simp only [gjr_CC, tagMap_inrr]
      rw [← liftT_sup]
      by_cases hsm : f ⊔ g = markedPt k
      · rw [hsm, canon_inrr_mid hm, tagMap_inrl, liftT_top,
          canon_inrl_of_ne _ (Ne.symm hbt'), liftT_mid k, canon_inrr_mid hm']
      · rw [canon_inrr_of_ne _ (sup_ne_bot_of_left hf) hsm, tagMap_inrr]

set_option maxHeartbeats 4000000 in
/-- **`glueAA k` preserves binary joins.** -/
theorem glueAA_sup (k : ℕ) (x y : D (k + 1)) :
    glueAA k (x ⊔ y) = glueAA k x ⊔ glueAA k y := by
  refine Subtype.ext ?_
  have e1 : (glueAA k (x ⊔ y)).1
      = canon (markedPt (k + 1))
          (tagMap k (canon (markedPt k) (glueJoinRaw (markedPt k) x.1 y.1))) := by
    rw [glueAA_val, sup_val]
  have e2 : (glueAA k x ⊔ glueAA k y).1
      = canon (markedPt (k + 1))
          (glueJoinRaw (markedPt (k + 1)) (tagMap k x.1) (tagMap k y.1)) := by
    rw [sup_val (k + 1), glueAA_val, glueAA_val, canon_tagMap k x.1 x.2,
      canon_tagMap k y.1 y.2]
  rw [e1, e2]
  exact core k x.1 y.1 x.2 y.2

/-- **The hypothesis of §80 is a theorem.** -/
theorem glueAAJoinPreserving (k : ℕ) : GlueAAEpPartner.GlueAAJoinPreserving k :=
  glueAA_sup k

/-- **The F-iterate tower, unconditionally.**  This is the object
`Dinfty/EpPairTower.lean`'s header asked for: carriers `D (k+1)`, embeddings
`glueAA k`, projections the upper adjoints supplied by
`Dinfty/EpFromJoin.lean`. -/
noncomputable def fTowerReal : EpPairTower :=
  GlueAAEpPartner.fTower glueAAJoinPreserving

@[simp] theorem fTowerReal_carrier (k : ℕ) : fTowerReal.carrier k = D (k + 1) := rfl

@[simp] theorem fTowerReal_emb (k : ℕ) : fTowerReal.emb k = glueAA k := rfl

end GlueAAJoin
