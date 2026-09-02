import Dinfty.GlueAAGenReflectM

open GluingTowerLibrary

-- [D-0763] §Closing-the-normalized-migration-the-lemmas
open scoped Classical

universe u

section MigrationCloseout

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0764] pGenM_top
theorem pGenM_top {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueOrderTop (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    pGenM mid (⊤ : GlueCar (P := EndP L) (constHom mid)) = (⊤ : L) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  letI := glueOrderTop (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  have hcanon : canon (constHom mid : EndP L) (Sum.inr (Sum.inr (⊤ : EndP L)))
      = Sum.inr (Sum.inr (⊤ : EndP L)) := by
    simp only [canon]
    split_ifs with h1 h2
    · exact absurd h1 hbt0.symm
    · exact absurd h2 hmt0.symm
    · rfl
  show pGenM mid ⟨_, _⟩ = _
  rw [pGenM]
  simp only [hcanon]

-- [D-0765] iotaEndPGenM_constHom
theorem iotaEndPGenM_constHom {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    iotaEndPGenM hmid0 hmidt hbt (constHom x) = constHom (iotaGenM mid x) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  ext w
  rw [iotaEndPGenM_apply, constHom_apply, constHom_apply]

-- [D-0766] glueAAGenM_iotaGenM
theorem glueAAGenM_iotaGenM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    glueAAGenM hmid0 hmidt hbt (iotaGenM mid x) = iotaGenM (midM mid) (iotaGenM mid x) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  apply Subtype.ext
  show (Sum.inl (iotaEndPGenM hmid0 hmidt hbt (constHom x))
      : GlueBase (EndP (GlueCar (P := EndP L) (constHom mid))))
    = Sum.inl (constHom (iotaGenM mid x))
  rw [iotaEndPGenM_constHom hmid0 hmidt hbt x]

-- [D-0767] glueAAGenM_pGenM_deflation_tagA
set_option maxHeartbeats 1000000 in
theorem glueAAGenM_pGenM_deflation_tagA {mid : L} (hmid0 : mid ≠ (⊥ : L))
    (hmidt : mid ≠ (⊤ : L)) (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    pGenM (L := GlueCar (P := EndP L) (constHom mid)) (midM mid)
      (glueAAGenM hmid0 hmidt hbt
        (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (constHom mid)))
      ≤ (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (constHom mid)) := by
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  have hb : pGenM mid (⊥ : GlueCar (P := EndP L) (constHom mid)) = (⊥ : L) := by
    rw [← iotaGenM_bot hmid0 hmidt hbt]
    exact pGenM_section mid (⊥ : L)
  have hval : pGenM (L := GlueCar (P := EndP L) (constHom mid)) (midM mid)
      (glueAAGenM hmid0 hmidt hbt
        (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (constHom mid)))
      = iotaGenM mid (f (⊥ : L)) := by
    show (iotaEndPGenM hmid0 hmidt hbt f) (⊥ : GlueCar (P := EndP L) (constHom mid))
      = iotaGenM mid (f (⊥ : L))
    rw [iotaEndPGenM_apply, hb]
  rw [hval, GlueCar.le_def]
  show leGlue (constHom mid : EndP L) (Sum.inl (constHom (f (⊥ : L)) : EndP L)) (Sum.inl f)
  exact (tagA_iso (constHom mid : EndP L) hm0 (constHom (f (⊥ : L))) f).mpr (by
    rw [OrderHom.le_def]; intro z; rw [constHom_apply]; exact f.monotone bot_le)

-- [D-0768] glueAAGenM_pGenM_deflation_tagB
set_option maxHeartbeats 1000000 in
theorem glueAAGenM_pGenM_deflation_tagB {mid : L} (hmid0 : mid ≠ (⊥ : L))
    (hmidt : mid ≠ (⊤ : L)) (hbt : (⊥ : L) ≠ ⊤) {f : EndP L}
    (hxv : canon (constHom mid : EndP L) (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl f))
    (hft : f ≠ (⊤ : EndP L)) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    pGenM (L := GlueCar (P := EndP L) (constHom mid)) (midM mid)
      (glueAAGenM hmid0 hmidt hbt
        (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (constHom mid)))
      ≤ (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (constHom mid)) := by
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv
  have hlt : liftGenM hmid0 hmidt hbt f ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
    fun hcon => hft ((liftGenM_eq_top_iff hmid0 hmidt hbt).mp hcon)
  have hlb : liftGenM hmid0 hmidt hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
    fun hcon => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hcon)
  have hcanonB : canon (constHom (midM mid))
      (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
      = Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)) := by
    simp only [canon]; rw [if_neg hlb]
  have hstep : glueAAGenM hmid0 hmidt hbt
      (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (constHom mid))
      = ⟨Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)), by
          rw [hcanonB]⟩ :=
    Subtype.ext hcanonB
  have hval : pGenM (L := GlueCar (P := EndP L) (constHom mid)) (midM mid)
      (glueAAGenM hmid0 hmidt hbt
        (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (constHom mid)))
      = midM mid := by
    rw [hstep]
    show (if liftGenM hmid0 hmidt hbt f
        = (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) then _ else midM mid) = midM mid
    rw [if_neg hlt]
  rw [hval, GlueCar.le_def]
  show leGlue (constHom mid : EndP L) (midM mid).1 (Sum.inr (Sum.inl f))
  show leGlue (constHom mid : EndP L) (Sum.inl (constHom mid : EndP L)) (Sum.inr (Sum.inl f))
  exact ⟨Sum.inl (constHom mid : EndP L), self_mem_occs _ _,
    Sum.inr (Sum.inl f), self_mem_occs _ _, le_rfl⟩

-- [D-0769] crossTag_CA_sufficientM
theorem crossTag_CA_sufficientM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (f : EndP L)
    (hfb : f ≠ (⊥ : EndP L)) (hfm : f ≠ (constHom mid : EndP L))
    (hidf : (constHom mid : EndP L) ≤ f)
    (Y : GlueCar (P := EndP L) (constHom mid))
    (hY : pGenM (L := L) mid Y = f (⊥ : L)) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    Y ≤ (incl (constHom mid : EndP L) (hmM_of hmid0) (hbtEL_of hbt)
      (Sum.inr (Sum.inr f))) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
    (hbtEL_of hbt)
  have hCfix : (incl (constHom mid : EndP L) (hmM_of hmid0) (hbtEL_of hbt)
      (Sum.inr (Sum.inr f))).1 = Sum.inr (Sum.inr f) := by
    show canon (constHom mid : EndP L) (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr f)
    rw [canon, if_neg hfb, if_neg hfm]
  rw [GlueCar.le_def]
  show leGlue (constHom mid : EndP L) Y.1
      (incl (constHom mid : EndP L) (hmM_of hmid0) (hbtEL_of hbt)
        (Sum.inr (Sum.inr f))).1
  rw [hCfix]
  rcases hY1 : Y.1 with v | v | v
  · show leGlue (constHom mid : EndP L) (Sum.inl v) (Sum.inr (Sum.inr f))
    exact leGlue_tagA_tagC (constHom mid : EndP L) v f
  · show leGlue (constHom mid : EndP L) (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr f))
    exact (leGlue_tagB_tagC_iff (constHom mid : EndP L) v f).mpr hidf
  · show leGlue (constHom mid : EndP L) (Sum.inr (Sum.inr v)) (Sum.inr (Sum.inr f))
    have hpg : pGenM (L := L) mid Y = (⊤ : L) := by
      show (match Y.1 with
        | Sum.inl f => f (⊥ : L)
        | Sum.inr (Sum.inl f) => if f = (⊤ : EndP L) then (⊤ : L) else mid
        | Sum.inr (Sum.inr _) => (⊤ : L)) = (⊤ : L)
      rw [hY1]
    have hftop : f (⊥ : L) = (⊤ : L) := hY.symm.trans hpg
    have hfeqtop : f = (⊤ : EndP L) := endP_eq_top_of_apply_bot_eq_top f hftop
    have hvf : v ≤ f := by rw [hfeqtop]; exact le_top
    exact (leGlue_tagC_tagC_iff (constHom mid : EndP L) v f).mpr hvf

end MigrationCloseout
