import Dinfty.GlueAAEpPartner

open GluingTowerLibrary SierpinskiApplication

-- [D-2226] §glueAA-preserves-binary-joins-the-tag-lemmas
open scoped Classical

namespace GlueAAJoin

open JoinPrimality GlueAAEpPartner

-- [D-2227] §liftGenM-declared-at-the-tower
-- [D-2228] liftT
noncomputable def liftT (k : ℕ) (f : EndP (D k)) : EndP (D (k + 1)) :=
  liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f

-- [D-2229] liftT_apply
theorem liftT_apply (k : ℕ) (f : EndP (D k)) (w : D (k + 1)) :
    liftT k f w = liftVal k f w := rfl

-- [D-2230] liftT_bot
theorem liftT_bot (k : ℕ) : liftT k (⊥ : EndP (D k)) = (⊥ : EndP (D (k + 1))) :=
  liftGenM_bot (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2231] liftT_mid
theorem liftT_mid (k : ℕ) : liftT k (markedPt k) = markedPt (k + 1) :=
  liftGenM_mid (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2232] liftT_top
theorem liftT_top (k : ℕ) : liftT k (⊤ : EndP (D k)) = (⊤ : EndP (D (k + 1))) :=
  liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2233] liftT_eq_bot_iff
theorem liftT_eq_bot_iff (k : ℕ) {f : EndP (D k)} :
    liftT k f = (⊥ : EndP (D (k + 1))) ↔ f = ⊥ :=
  liftGenM_eq_bot_iff (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2234] liftT_eq_mid_iff
theorem liftT_eq_mid_iff (k : ℕ) {f : EndP (D k)} :
    liftT k f = markedPt (k + 1) ↔ f = markedPt k :=
  liftGenM_eq_mid_iff (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2235] liftT_monotone
theorem liftT_monotone (k : ℕ) {f g : EndP (D k)} (h : f ≤ g) : liftT k f ≤ liftT k g :=
  liftGenM_monotone (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial h

-- [D-2236] liftT_ne_bot
theorem liftT_ne_bot (k : ℕ) {f : EndP (D k)} (hf : f ≠ ⊥) :
    liftT k f ≠ (⊥ : EndP (D (k + 1))) := fun h => hf ((liftT_eq_bot_iff k).mp h)

-- [D-2237] liftT_ne_mid
theorem liftT_ne_mid (k : ℕ) {f : EndP (D k)} (hf : f ≠ markedPt k) :
    liftT k f ≠ markedPt (k + 1) := fun h => hf ((liftT_eq_mid_iff k).mp h)

-- [D-2238] liftT_sup
theorem liftT_sup (k : ℕ) (f g : EndP (D k)) :
    liftT k (f ⊔ g) = liftT k f ⊔ liftT k g := by
  ext w
  show liftVal k (f ⊔ g) w = (liftT k f ⊔ liftT k g) w
  simp only [OrderHom.coe_sup, Pi.sup_apply]
  exact liftVal_sup k f g w

-- [D-2239] §The-two-guards
-- [D-2240] iotaEndP_le_marked_iff
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

-- [D-2241] marked_le_liftT_iff
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

-- [D-2242] §glueAA-on-the-three-copies-canon-free
-- [D-2243] glueAA_glueA
theorem glueAA_glueA (k : ℕ) (f : EndP (D k)) :
    glueAA k (glueA (markedPt k) f) = glueA (markedPt (k + 1)) (iotaEndP k f) :=
  Subtype.ext rfl

-- [D-2244] glueAA_glueB
set_option maxHeartbeats 4000000 in
theorem glueAA_glueB (k : ℕ) (f : EndP (D k)) (hf : f ≠ ⊥) :
    glueAA k (glueB (markedPt k) f hf)
      = glueB (markedPt (k + 1)) (liftT k f) (liftT_ne_bot k hf) := by
  refine Subtype.ext ?_
  show canon (markedPt (k + 1)) (Sum.inr (Sum.inl (liftT k f)))
    = Sum.inr (Sum.inl (liftT k f))
  simp only [canon]
  rw [if_neg (liftT_ne_bot k hf)]

-- [D-2245] glueAA_glueC
set_option maxHeartbeats 4000000 in
theorem glueAA_glueC (k : ℕ) (f : EndP (D k)) (hf : f ≠ ⊥) (hfm : f ≠ markedPt k) :
    glueAA k (glueC (markedPt k) f hf hfm)
      = glueC (markedPt (k + 1)) (liftT k f) (liftT_ne_bot k hf) (liftT_ne_mid k hfm) := by
  refine Subtype.ext ?_
  show canon (markedPt (k + 1)) (Sum.inr (Sum.inr (liftT k f)))
    = Sum.inr (Sum.inr (liftT k f))
  simp only [canon]
  rw [if_neg (liftT_ne_bot k hf), if_neg (liftT_ne_mid k hfm)]

-- [D-2246] §The-join-read-on-values
-- [D-2247] sup_val
theorem sup_val (k : ℕ) (x y : D (k + 1)) :
    (x ⊔ y).1 = canon (markedPt k) (glueJoinRaw (markedPt k) x.1 y.1) := rfl

-- [D-2248] §canon-and-glueJoinRaw-one-branch-at-a-time
section Branches

variable {P : Type} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

-- [D-2249] canon_inl
@[simp] theorem canon_inl (m a : P) : canon m (Sum.inl a) = Sum.inl a := rfl

-- [D-2250] canon_inrl_of_ne
theorem canon_inrl_of_ne (m : P) {a : P} (ha : a ≠ ⊥) :
    canon m (Sum.inr (Sum.inl a)) = Sum.inr (Sum.inl a) := by
  simp only [canon]
  rw [if_neg ha]

-- [D-2251] canon_inrr_of_ne
theorem canon_inrr_of_ne (m : P) {a : P} (ha : a ≠ ⊥) (ham : a ≠ m) :
    canon m (Sum.inr (Sum.inr a)) = Sum.inr (Sum.inr a) := by
  simp only [canon]
  rw [if_neg ha, if_neg ham]

-- [D-2252] canon_inrr_mid
theorem canon_inrr_mid {m : P} (hm : m ≠ ⊥) :
    canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤) := by
  simp only [canon]
  rw [if_neg hm]
  simp

-- [D-2253] gjr_AA
@[simp] theorem gjr_AA (m f g : P) :
    glueJoinRaw m (Sum.inl f) (Sum.inl g) = Sum.inl (f ⊔ g) := rfl

-- [D-2254] gjr_BB
@[simp] theorem gjr_BB (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inl (f ⊔ g)) := rfl

-- [D-2255] gjr_CC
@[simp] theorem gjr_CC (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr (f ⊔ g)) := rfl

-- [D-2256] gjr_AC
@[simp] theorem gjr_AC (m f g : P) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inr g)) = Sum.inr (Sum.inr g) := rfl

-- [D-2257] gjr_CA
@[simp] theorem gjr_CA (m f g : P) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inl g) = Sum.inr (Sum.inr f) := rfl

-- [D-2258] gjr_AB_pos
theorem gjr_AB_pos (m f g : P) (h : f ≤ m) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inl g)) = Sum.inr (Sum.inl g) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

-- [D-2259] gjr_AB_neg
theorem gjr_AB_neg (m f g : P) (h : ¬ f ≤ m) :
    glueJoinRaw m (Sum.inl f) (Sum.inr (Sum.inl g)) = Sum.inr (Sum.inr m) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

-- [D-2260] gjr_BA_pos
theorem gjr_BA_pos (m f g : P) (h : g ≤ m) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inl g) = Sum.inr (Sum.inl f) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

-- [D-2261] gjr_BA_neg
theorem gjr_BA_neg (m f g : P) (h : ¬ g ≤ m) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inl g) = Sum.inr (Sum.inr m) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

-- [D-2262] gjr_BC_pos
theorem gjr_BC_pos (m f g : P) (h : m ≤ g) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr g) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

-- [D-2263] gjr_BC_neg
theorem gjr_BC_neg (m f g : P) (h : ¬ m ≤ g) :
    glueJoinRaw m (Sum.inr (Sum.inl f)) (Sum.inr (Sum.inr g))
      = Sum.inr (Sum.inr (g ⊔ m)) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

-- [D-2264] gjr_CB_pos
theorem gjr_CB_pos (m f g : P) (h : m ≤ f) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inr f) := by
  simp only [glueJoinRaw]
  rw [if_pos h]

-- [D-2265] gjr_CB_neg
theorem gjr_CB_neg (m f g : P) (h : ¬ m ≤ f) :
    glueJoinRaw m (Sum.inr (Sum.inr f)) (Sum.inr (Sum.inl g))
      = Sum.inr (Sum.inr (f ⊔ m)) := by
  simp only [glueJoinRaw]
  rw [if_neg h]

-- [D-2266] canonC_ne_mid
theorem canonC_ne_mid {m w : P}
    (h : canon m (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w)) : w ≠ m := by
  intro hw
  rw [hw] at h
  simp only [canon] at h
  split_ifs at h <;> simp at h

-- [D-2267] sup_ne_bot_of_left
theorem sup_ne_bot_of_left {f g : P} (hf : f ≠ ⊥) : f ⊔ g ≠ ⊥ := fun h =>
  hf (le_bot_iff.mp (le_trans le_sup_left h.le))

end Branches

-- [D-2268] §The-tagwise-payload-map
-- [D-2269] tagMap
noncomputable def tagMap (k : ℕ) :
    GlueBase (EndP (D k)) → GlueBase (EndP (D (k + 1)))
  | Sum.inl f => Sum.inl (iotaEndP k f)
  | Sum.inr (Sum.inl f) => Sum.inr (Sum.inl (liftT k f))
  | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr (liftT k f))

-- [D-2270] tagMap_inl
@[simp] theorem tagMap_inl (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inl f) = Sum.inl (iotaEndP k f) := rfl

-- [D-2271] tagMap_inrl
@[simp] theorem tagMap_inrl (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl (liftT k f)) := rfl

-- [D-2272] tagMap_inrr
@[simp] theorem tagMap_inrr (k : ℕ) (f : EndP (D k)) :
    tagMap k (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr (liftT k f)) := rfl

-- [D-2273] glueAA_val
set_option maxHeartbeats 4000000 in
theorem glueAA_val (k : ℕ) (z : D (k + 1)) :
    (glueAA k z).1 = canon (markedPt (k + 1)) (tagMap k z.1) := by
  obtain ⟨zv, hzv⟩ := z
  rcases zv with f | f | f <;> rfl

-- [D-2274] canon_tagMap
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

-- [D-2275] §The-nine-cases
-- [D-2276] core
set_option maxHeartbeats 4000000 in
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
    ·
      simp only [gjr_AA, canon_inl, tagMap_inl]
      rw [iotaEndP_sup]
    ·
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
    ·
      have hg : g ≠ ⊥ := CopyBExclusion.canonCFixBot hv
      have hgm : g ≠ markedPt k := canonC_ne_mid hv
      simp only [gjr_AC, tagMap_inl, tagMap_inrr]
      rw [canon_inrr_of_ne _ hg hgm, tagMap_inrr]
  · rcases v with g | g | g
    ·
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
    ·
      have hf : f ≠ ⊥ := ne_bot_of_canon_tagB (markedPt k) f hu
      simp only [gjr_BB, tagMap_inrl]
      rw [canon_inrl_of_ne _ (sup_ne_bot_of_left hf), tagMap_inrl, liftT_sup]
    ·
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
    ·
      have hf : f ≠ ⊥ := CopyBExclusion.canonCFixBot hu
      have hfm : f ≠ markedPt k := canonC_ne_mid hu
      simp only [gjr_CA, tagMap_inrr, tagMap_inl]
      rw [canon_inrr_of_ne _ hf hfm, tagMap_inrr]
    ·
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
    ·
      have hf : f ≠ ⊥ := CopyBExclusion.canonCFixBot hu
      simp only [gjr_CC, tagMap_inrr]
      rw [← liftT_sup]
      by_cases hsm : f ⊔ g = markedPt k
      · rw [hsm, canon_inrr_mid hm, tagMap_inrl, liftT_top,
          canon_inrl_of_ne _ (Ne.symm hbt'), liftT_mid k, canon_inrr_mid hm']
      · rw [canon_inrr_of_ne _ (sup_ne_bot_of_left hf) hsm, tagMap_inrr]

-- [D-2277] glueAA_sup
set_option maxHeartbeats 4000000 in
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

-- [D-2278] glueAAJoinPreserving
theorem glueAAJoinPreserving (k : ℕ) : GlueAAEpPartner.GlueAAJoinPreserving k :=
  glueAA_sup k

-- [D-2279] fTowerReal
noncomputable def fTowerReal : EpPairTower :=
  GlueAAEpPartner.fTower glueAAJoinPreserving

-- [D-2280] fTowerReal_carrier
@[simp] theorem fTowerReal_carrier (k : ℕ) : fTowerReal.carrier k = D (k + 1) := rfl

-- [D-2281] fTowerReal_emb
@[simp] theorem fTowerReal_emb (k : ℕ) : fTowerReal.emb k = glueAA k := rfl

end GlueAAJoin
