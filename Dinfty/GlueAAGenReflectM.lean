import Dinfty.GluingTowerLibrary

open GluingTowerLibrary

-- [D-0693] §GlueAAGenReflect-migrated-to-a-constant-marked
open scoped Classical

universe u

section MigratedEpPair

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0694] §The-marked-point-is-a-constant
-- [D-0695] hmM_of
theorem hmM_of {mid : L} (hmid0 : mid ≠ (⊥ : L)) : (constHom mid : EndP L) ≠ ⊥ := by
  intro h
  exact hmid0 (by simpa using congrArg (fun g : EndP L => g (⊥ : L)) h)

-- [D-0696] hmtM_of
theorem hmtM_of {mid : L} (hmidt : mid ≠ (⊤ : L)) : (constHom mid : EndP L) ≠ ⊤ := by
  intro h
  exact hmidt (by simpa using congrArg (fun g : EndP L => g (⊥ : L)) h)

-- [D-0697] §pGenM-the-ep-pair-projection-at-a-constant
-- [D-0698] pGenM
noncomputable def pGenM (mid : L) (w : GlueCar (P := EndP L) (constHom mid)) : L :=
  match w.1 with
  | Sum.inl f => f (⊥ : L)
  | Sum.inr (Sum.inl f) => if f = (⊤ : EndP L) then (⊤ : L) else mid
  | Sum.inr (Sum.inr _) => (⊤ : L)

-- [D-0699] iotaGenM
noncomputable def iotaGenM (mid : L) (x : L) : GlueCar (P := EndP L) (constHom mid) :=
  glueA (constHom mid : EndP L) (constHom x)

-- [D-0700] pGenM_section
theorem pGenM_section (mid x : L) : pGenM mid (iotaGenM mid x) = x := by
  show (constHom x : EndP L) (⊥ : L) = x
  rw [constHom_apply]

-- [D-0701] iotaGenM_le_iff
theorem iotaGenM_le_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (x y : L) :
    iotaGenM mid x ≤ iotaGenM mid y ↔ x ≤ y :=
  (glueA_le_iff (constHom mid : EndP L) (hmM_of hmid0) (constHom x) (constHom y)).trans
    (constHom_le_iff x y)

-- [D-0702] iotaGenM_injective
theorem iotaGenM_injective (mid : L) : Function.Injective (iotaGenM mid) := by
  intro x y h
  exact constHom_injective (glueA_injective (constHom mid : EndP L) h)

-- [D-0703] iotaGenM_monotone
theorem iotaGenM_monotone {mid : L} (hmid0 : mid ≠ (⊥ : L)) {x y : L} (hxy : x ≤ y) :
    iotaGenM mid x ≤ iotaGenM mid y :=
  (iotaGenM_le_iff hmid0 x y).mpr hxy

-- [D-0704] pGenM_deflation
theorem pGenM_deflation (mid : L) (w : GlueCar (P := EndP L) (constHom mid)) :
    leGlue (constHom mid : EndP L) (Sum.inl (constHom (pGenM mid w) : EndP L)) w.1 := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with f | f | f
  · show leGlue (constHom mid : EndP L) (Sum.inl (constHom (f (⊥ : L)) : EndP L)) (Sum.inl f)
    refine ⟨Sum.inl (constHom (f (⊥ : L))), self_mem_occs _ _, Sum.inl f, self_mem_occs _ _, ?_⟩
    show (constHom (f (⊥ : L)) : EndP L) ≤ f
    rw [OrderHom.le_def]
    intro z
    rw [constHom_apply]
    exact f.monotone bot_le
  · show leGlue (constHom mid : EndP L)
        (Sum.inl (constHom (if f = (⊤ : EndP L) then (⊤ : L) else mid) : EndP L))
        (Sum.inr (Sum.inl f))
    by_cases hft : f = (⊤ : EndP L)
    · rw [if_pos hft, hft]
      exact leGlue_tagA_tagB_top (constHom mid : EndP L) (constHom (⊤ : L))
    · rw [if_neg hft]
      exact (leGlue_tagA_tagB_iff (constHom mid : EndP L) (constHom mid) f hft).mpr le_rfl
  · show leGlue (constHom mid : EndP L) (Sum.inl (constHom (⊤ : L) : EndP L))
        (Sum.inr (Sum.inr f))
    exact ⟨Sum.inl (constHom (⊤ : L)), self_mem_occs _ _, Sum.inr (Sum.inr f),
      self_mem_occs _ _, trivial⟩

-- [D-0705] pGenM_monotone
theorem pGenM_monotone {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hbt : (⊥ : L) ≠ ⊤)
    (w w' : GlueCar (P := EndP L) (constHom mid)) (hle : w ≤ w') :
    pGenM mid w ≤ pGenM mid w' := by
  have hm : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hbtE : (⊥ : EndP L) ≠ (⊤ : EndP L) := endP_bot_ne_top hbt
  rw [GlueCar.le_def] at hle
  obtain ⟨wv, hwv⟩ := w
  obtain ⟨wv', hwv'⟩ := w'
  simp only at hle
  rcases wv with f | f | f <;> rcases wv' with f' | f' | f'
  · show f (⊥ : L) ≤ f' (⊥ : L)
    exact (OrderHom.le_def.mp ((tagA_iso (constHom mid : EndP L) hm f f').mp hle)) ⊥
  · show f (⊥ : L) ≤ (if f' = (⊤ : EndP L) then (⊤ : L) else mid)
    by_cases hf't : f' = (⊤ : EndP L)
    · rw [if_pos hf't]; exact le_top
    · rw [if_neg hf't]
      have hfm : f ≤ (constHom mid : EndP L) :=
        (leGlue_tagA_tagB_iff (constHom mid : EndP L) f f' hf't).mp hle
      simpa using OrderHom.le_def.mp hfm ⊥
  · show f (⊥ : L) ≤ (⊤ : L)
    exact le_top
  · exact absurd hle (not_leGlue_tagB_tagA (constHom mid : EndP L) f f' hm hbtE
      (ne_bot_of_canon_tagB (constHom mid : EndP L) f hwv))
  · show (if f = (⊤ : EndP L) then (⊤ : L) else mid) ≤
        (if f' = (⊤ : EndP L) then (⊤ : L) else mid)
    by_cases hf't : f' = (⊤ : EndP L)
    · rw [if_pos hf't]; exact le_top
    · have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB _ f hwv
      have hfle : f ≤ f' := (leGlue_tagB_tagB_iff (constHom mid : EndP L) f f' hf't hfb).mp hle
      have hfne : f ≠ (⊤ : EndP L) := fun hfT => hf't (top_le_iff.mp (hfT ▸ hfle))
      rw [if_neg hfne, if_neg hf't]
  · show (if f = (⊤ : EndP L) then (⊤ : L) else mid) ≤ (⊤ : L)
    exact le_top
  · exact absurd hle (not_leGlue_tagC_tagA (constHom mid : EndP L) f f'
      (ne_bot_of_canon_tagC (constHom mid : EndP L) f hwv))
  · by_cases hf't : f' = (⊤ : EndP L)
    · show (⊤ : L) ≤ (if f' = (⊤ : EndP L) then (⊤ : L) else mid)
      rw [if_pos hf't]
    · exact absurd hle (not_leGlue_tagC_tagB (constHom mid : EndP L) f f' hf't)
  · show (⊤ : L) ≤ (⊤ : L)
    exact le_refl _

end MigratedEpPair

section MigratedLift

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0706] §The-next-level-s-marked-point
-- [D-0707] midM
noncomputable def midM (mid : L) : GlueCar (P := EndP L) (constHom mid) :=
  iotaGenM mid mid

-- [D-0708] midM_ne_bot
theorem midM_ne_bot {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    midM mid ≠ (⊥ : GlueCar (P := EndP L) (constHom mid)) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  intro h
  have hv := congrArg Subtype.val h
  have h1 : (midM mid).1 = Sum.inl (constHom mid : EndP L) := rfl
  have h2 : (⊥ : GlueCar (P := EndP L) (constHom mid)).1 = Sum.inl (⊥ : EndP L) := rfl
  rw [h1, h2] at hv
  exact (hmM_of hmid0) (by simpa using hv)

-- [D-0709] iotaGenM_ne_top
theorem iotaGenM_ne_top {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    iotaGenM mid x ≠ (⊤ : GlueCar (P := EndP L) (constHom mid)) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  intro h
  have hv := congrArg Subtype.val h
  have h1 : (iotaGenM mid x).1 = Sum.inl (constHom x : EndP L) := rfl
  have h2 : (⊤ : GlueCar (P := EndP L) (constHom mid)).1 = Sum.inr (Sum.inr (⊤ : EndP L)) := by
    show canon (constHom mid : EndP L) (Sum.inr (Sum.inr (⊤ : EndP L)))
      = Sum.inr (Sum.inr (⊤ : EndP L))
    simp only [canon]
    rw [if_neg (hbtEL_of hbt).symm, if_neg (hmtM_of hmidt).symm]
  rw [h1, h2] at hv
  exact absurd hv (by simp)

-- [D-0710] midM_ne_top
theorem midM_ne_top {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    midM mid ≠ (⊤ : GlueCar (P := EndP L) (constHom mid)) :=
  iotaGenM_ne_top hmid0 hmidt hbt mid

-- [D-0711] §midM-is-the-ONLY-possible-next-marked-point
-- [D-0712] midM_unique
theorem midM_unique {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (mu : GlueCar (P := EndP L) (constHom mid))
    (hup : ∀ y : L, y ≤ mid → iotaGenM mid y ≤ mu)
    (hdown : ∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) :
    mu = midM mid := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  exact le_antisymm (hdown mid le_rfl) (hup mid le_rfl)

-- [D-0713] midM_ne_skelL
theorem midM_ne_skelL (mid : L) :
    (midM mid).1 ≠ skelL (constHom mid : EndP L) := by
  simp [midM, iotaGenM, glueA, skelL]

-- [D-0714] §iotaEndPGenM-and-liftGenM
-- [D-0715] iotaEndPGenM
noncomputable def iotaEndPGenM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    EndP (GlueCar (P := EndP L) (constHom mid)) :=
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  { toFun := fun w => iotaGenM mid (f (pGenM mid w))
    monotone' := fun w w' hle =>
      iotaGenM_monotone hmid0 (f.monotone (pGenM_monotone hmid0 hbt w w' hle)) }

-- [D-0716] iotaEndPGenM_apply
theorem iotaEndPGenM_apply {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    ∀ w : GlueCar (P := EndP L) (constHom mid),
      (iotaEndPGenM hmid0 hmidt hbt f) w = iotaGenM mid (f (pGenM mid w)) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  intro w
  rfl

-- [D-0717] iotaEndPGenM_monotone
theorem iotaEndPGenM_monotone {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} (hfg : f ≤ g) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    iotaEndPGenM hmid0 hmidt hbt f ≤ iotaEndPGenM hmid0 hmidt hbt g := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  rw [OrderHom.le_def]
  intro w
  show iotaGenM mid (f (pGenM mid w)) ≤ iotaGenM mid (g (pGenM mid w))
  exact iotaGenM_monotone hmid0 (OrderHom.le_def.mp hfg (pGenM mid w))

-- [D-0718] liftGenM
noncomputable def liftGenM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    EndP (GlueCar (P := EndP L) (constHom mid)) :=
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  iotaEndPGenM hmid0 hmidt hbt f
    ⊔ (if (constHom mid : EndP L) ≤ f
        then (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        else ⊥)
    ⊔ (if (⊤ : EndP L) ≤ f
        then (⊤ : EndP (GlueCar (P := EndP L) (constHom mid)))
        else ⊥)

-- [D-0719] liftGenM_monotone
theorem liftGenM_monotone {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} (hfg : f ≤ g) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    liftGenM hmid0 hmidt hbt f ≤ liftGenM hmid0 hmidt hbt g := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  unfold liftGenM
  exact sup_le_sup (sup_le_sup (iotaEndPGenM_monotone hmid0 hmidt hbt hfg)
    (ite_dominate_mono hfg _)) (ite_dominate_mono hfg _)

-- [D-0720] §Boundary-values
-- [D-0721] iotaGenM_bot
theorem iotaGenM_bot {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    iotaGenM mid (⊥ : L) = ⊥ := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  show glueA (constHom mid : EndP L) (constHom (⊥ : L)) = ⊥
  rw [constHom_bot_eq]
  rfl

-- [D-0722] iotaEndPGenM_bot
theorem iotaEndPGenM_bot {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    iotaEndPGenM hmid0 hmidt hbt (⊥ : EndP L) = ⊥ := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  ext w
  show iotaGenM mid ((⊥ : EndP L) (pGenM mid w))
    = (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) w
  rw [endPBot_apply]
  exact iotaGenM_bot hmid0 hmidt hbt

-- [D-0723] liftGenM_bot
theorem liftGenM_bot {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    liftGenM hmid0 hmidt hbt (⊥ : EndP L) = ⊥ := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  unfold liftGenM
  have h1 : ¬ (constHom mid : EndP L) ≤ (⊥ : EndP L) :=
    fun h => (hmM_of hmid0) (le_bot_iff.mp h)
  have h2 : ¬ (⊤ : EndP L) ≤ (⊥ : EndP L) := fun h => (hbtEL_of hbt) (le_bot_iff.mp h).symm
  rw [if_neg h1, if_neg h2, iotaEndPGenM_bot hmid0 hmidt hbt]
  exact le_antisymm (sup_le (sup_le le_rfl le_rfl) le_rfl) bot_le

-- [D-0724] liftGenM_mid
theorem liftGenM_mid {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    liftGenM hmid0 hmidt hbt (constHom mid : EndP L)
      = (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  unfold liftGenM
  have h1 : (constHom mid : EndP L) ≤ (constHom mid : EndP L) := le_refl _
  have h2 : ¬ (⊤ : EndP L) ≤ (constHom mid : EndP L) :=
    fun h => (hmtM_of hmidt) (top_le_iff.mp h)
  have hdefl : iotaEndPGenM hmid0 hmidt hbt (constHom mid : EndP L)
      ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) := by
    rw [OrderHom.le_def]
    intro w
    show iotaGenM mid ((constHom mid : EndP L) (pGenM mid w)) ≤ midM mid
    rw [constHom_apply]
    exact le_rfl
  rw [if_pos h1, if_neg h2]
  exact le_antisymm (sup_le (sup_le hdefl le_rfl) bot_le) (le_trans le_sup_right le_sup_left)

-- [D-0725] liftGenM_top
theorem liftGenM_top {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    liftGenM hmid0 hmidt hbt (⊤ : EndP L)
      = (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  unfold liftGenM
  rw [if_pos (le_refl (⊤ : EndP L))]
  exact le_antisymm le_top le_sup_right

end MigratedLift

section MigratedReflect

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0726] iotaEndPGenM_le_iff
theorem iotaEndPGenM_le_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    (iotaEndPGenM hmid0 hmidt hbt f ≤ iotaEndPGenM hmid0 hmidt hbt g ↔ f ≤ g) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  constructor
  · intro h
    rw [OrderHom.le_def]
    intro x
    have hw := OrderHom.le_def.mp h (iotaGenM mid x)
    rw [iotaEndPGenM_apply, iotaEndPGenM_apply] at hw
    rw [pGenM_section] at hw
    exact (iotaGenM_le_iff hmid0 _ _).mp hw
  · exact iotaEndPGenM_monotone hmid0 hmidt hbt

-- [D-0727] liftGenM_apply
theorem liftGenM_apply {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) (w : GlueCar (P := EndP L) (constHom mid)) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    (liftGenM hmid0 hmidt hbt f) w
      = iotaGenM mid (f (pGenM mid w))
          ⊔ (if (constHom mid : EndP L) ≤ f then midM mid else ⊥)
          ⊔ (if (⊤ : EndP L) ≤ f then (⊤ : GlueCar (P := EndP L) (constHom mid)) else ⊥) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  unfold liftGenM
  simp only [OrderHom.coe_sup, Pi.sup_apply, iotaEndPGenM_apply]
  congr 2
  · split_ifs with h1
    · exact constHom_apply _ w
    · exact endPBot_apply w
  · split_ifs with h2
    · exact endPTop_apply w
    · exact endPBot_apply w

-- [D-0728] liftGenM_eq_bot_iff
theorem liftGenM_eq_bot_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    (liftGenM hmid0 hmidt hbt f = ⊥ ↔ f = ⊥) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  constructor
  · intro h
    unfold liftGenM at h
    have hh := sup_eq_bot_iff.mp h
    have hh2 := sup_eq_bot_iff.mp hh.1
    have h1 : iotaEndPGenM hmid0 hmidt hbt f = ⊥ := hh2.1
    have h2 : iotaEndPGenM hmid0 hmidt hbt f = iotaEndPGenM hmid0 hmidt hbt (⊥ : EndP L) :=
      h1.trans (iotaEndPGenM_bot hmid0 hmidt hbt).symm
    have h4 : f ≤ (⊥ : EndP L) := (iotaEndPGenM_le_iff hmid0 hmidt hbt).mp (le_of_eq h2)
    exact le_bot_iff.mp h4
  · intro h; subst h; exact liftGenM_bot hmid0 hmidt hbt

-- [D-0729] liftGenM_eq_mid_iff
theorem liftGenM_eq_mid_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    (liftGenM hmid0 hmidt hbt f
        = (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
      ↔ f = (constHom mid : EndP L)) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  have hMt : midM mid ≠ (⊤ : GlueCar (P := EndP L) (constHom mid)) :=
    midM_ne_top hmid0 hmidt hbt
  constructor
  · intro h
    have hfnt : f ≠ (⊤ : EndP L) := by
      intro hfe; subst hfe
      rw [liftGenM_top] at h
      exact (hmtM_of hMt) h.symm
    have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hfnt (top_le_iff.mp hc)
    have key : ∀ z : L,
        iotaGenM mid (f z) ⊔ (if (constHom mid : EndP L) ≤ f then midM mid else ⊥)
          ⊔ (if (⊤ : EndP L) ≤ f then (⊤ : GlueCar (P := EndP L) (constHom mid)) else ⊥)
          = midM mid := by
      intro z
      have e1 := liftGenM_apply hmid0 hmidt hbt f (iotaGenM mid z)
      rw [h] at e1
      rw [pGenM_section] at e1
      rw [constHom_apply] at e1
      exact e1.symm
    have hle : f ≤ (constHom mid : EndP L) := by
      rw [OrderHom.le_def]
      intro z
      have hk := key z
      have hzz : iotaGenM mid (f z) ≤ midM mid := by
        rw [← hk]; exact le_trans le_sup_left le_sup_left
      have hzz2 : iotaGenM mid (f z) ≤ iotaGenM mid mid := hzz
      exact (iotaGenM_le_iff hmid0 _ _).mp hzz2
    by_cases hmf : (constHom mid : EndP L) ≤ f
    · exact le_antisymm hle hmf
    · exfalso
      have hcon : ∀ z : L, iotaGenM mid (f z) = iotaGenM mid mid := by
        intro z
        have hk := key z
        simp only [if_neg hmf, if_neg hnle, sup_bot_eq] at hk
        exact hk
      have hfeq : f = (constHom mid : EndP L) := by
        ext z; exact iotaGenM_injective mid (hcon z)
      exact hmf (hfeq ▸ le_refl _)
  · intro h; subst h; exact liftGenM_mid hmid0 hmidt hbt

-- [D-0730] liftGenM_eq_top_iff
theorem liftGenM_eq_top_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    (liftGenM hmid0 hmidt hbt f = ⊤ ↔ f = ⊤) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  constructor
  · intro h
    by_contra hne
    have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hne (top_le_iff.mp hc)
    have e1 := liftGenM_apply hmid0 hmidt hbt f (iotaGenM mid (⊥ : L))
    rw [h] at e1
    rw [pGenM_section, if_neg hnle, endPTop_apply] at e1
    by_cases hmf : (constHom mid : EndP L) ≤ f
    · rw [if_pos hmf, sup_bot_eq] at e1
      have hzz : mid ≤ f (⊥ : L) := by
        simpa using OrderHom.le_def.mp hmf (⊥ : L)
      have hle2 : midM mid ≤ iotaGenM mid (f (⊥ : L)) := iotaGenM_monotone hmid0 hzz
      have habs : iotaGenM mid (f (⊥ : L)) ⊔ midM mid = iotaGenM mid (f (⊥ : L)) :=
        sup_eq_left.mpr hle2
      rw [habs] at e1
      exact iotaGenM_ne_top hmid0 hmidt hbt _ e1.symm
    · rw [if_neg hmf, sup_bot_eq, sup_bot_eq] at e1
      exact iotaGenM_ne_top hmid0 hmidt hbt _ e1.symm
  · intro h; subst h; exact liftGenM_top hmid0 hmidt hbt

-- [D-0731] liftGenM_apply_iotaGenM_of_not_top
theorem liftGenM_apply_iotaGenM_of_not_top {mid : L} (hmid0 : mid ≠ (⊥ : L))
    (hmidt : mid ≠ (⊤ : L)) (hbt : (⊥ : L) ≠ ⊤) {g : EndP L}
    (hg : ¬ (⊤ : EndP L) ≤ g) (z : L) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    (liftGenM hmid0 hmidt hbt g) (iotaGenM mid z) = iotaGenM mid (g z) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  have e1 := liftGenM_apply hmid0 hmidt hbt g (iotaGenM mid z)
  rw [pGenM_section, if_neg hg] at e1
  by_cases hmg : (constHom mid : EndP L) ≤ g
  · rw [if_pos hmg, sup_bot_eq] at e1
    have hzz : mid ≤ g z := by simpa using OrderHom.le_def.mp hmg z
    have hle : midM mid ≤ iotaGenM mid (g z) := iotaGenM_monotone hmid0 hzz
    rw [sup_eq_left.mpr hle] at e1
    exact e1
  · rw [if_neg hmg, sup_bot_eq, sup_bot_eq] at e1
    exact e1

-- [D-0732] iotaEndPGenM_mid_le
theorem iotaEndPGenM_mid_le {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    iotaEndPGenM hmid0 hmidt hbt (constHom mid : EndP L)
      ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) := by
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  rw [OrderHom.le_def]
  intro w
  show iotaGenM mid ((constHom mid : EndP L) (pGenM mid w)) ≤ midM mid
  rw [constHom_apply]
  exact le_rfl

-- [D-0733] §glueAAGenM
-- [D-0734] glueAAGenM
noncomputable def glueAAGenM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (x : GlueCar (P := EndP L) (constHom mid)) :
    letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt)
      (hbtEL_of hbt)
    letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
    GlueCar (P := EndP (GlueCar (P := EndP L) (constHom mid))) (constHom (midM mid)) :=
  letI := glueCarPartialOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueLattice (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  letI := glueBoundedOrder (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (constHom mid)) :=
    glueCar_nontrivial (constHom mid : EndP L) (hmM_of hmid0) (hmtM_of hmidt) (hbtEL_of hbt)
  have hbtG : (⊥ : GlueCar (P := EndP L) (constHom mid)) ≠ ⊤ := bot_ne_top_of_nontrivial
  match x.1 with
  | Sum.inl f => ⟨Sum.inl (iotaEndPGenM hmid0 hmidt hbt f), rfl⟩
  | Sum.inr (Sum.inl f) =>
      incl (constHom (midM mid)) (hmM_of (midM_ne_bot hmid0 hmidt hbt)) (hbtEL_of hbtG)
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
  | Sum.inr (Sum.inr f) =>
      incl (constHom (midM mid)) (hmM_of (midM_ne_bot hmid0 hmidt hbt)) (hbtEL_of hbtG)
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))

-- [D-0735] glueAAGenM_monotone
set_option maxHeartbeats 4000000 in
theorem glueAAGenM_monotone {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (constHom mid)} (hxy : x ≤ y) :
    glueAAGenM hmid0 hmidt hbt x ≤ glueAAGenM hmid0 hmidt hbt y := by
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (constHom mid)) :=
    glueCar_nontrivial (constHom mid : EndP L) hm0 hmt0 hbt0
  have hbtG : (⊥ : GlueCar (P := EndP L) (constHom mid)) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm' : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) ≠ ⊥ :=
    hmM_of (midM_ne_bot hmid0 hmidt hbt)
  have hmt' : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) ≠ ⊤ :=
    hmtM_of (midM_ne_top hmid0 hmidt hbt)
  have hbtE' : (⊥ : EndP (GlueCar (P := EndP L) (constHom mid)))
      ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) := hbtEL_of hbtG
  obtain ⟨xv, hxv⟩ := x
  obtain ⟨yv, hyv⟩ := y
  have hxy' : leGlue (constHom mid : EndP L) xv yv := hxy
  rw [GlueCar.le_def]
  show leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
    (glueAAGenM hmid0 hmidt hbt (⟨xv, hxv⟩ : GlueCar (P := EndP L) (constHom mid))).1
    (glueAAGenM hmid0 hmidt hbt (⟨yv, hyv⟩ : GlueCar (P := EndP L) (constHom mid))).1
  rcases xv with f | f | f <;> rcases yv with f' | f' | f'
  ·
    show leGlue _ (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
      (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f'))
    have hff' : f ≤ f' := (tagA_iso (constHom mid : EndP L) hm0 f f').mp hxy'
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f)) (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f'))
      (iotaEndPGenM_monotone hmid0 hmidt hbt hff')
  ·
    show leGlue _ (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
      (canon _ (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid)))) := by
        simp only [canon]
        rw [if_neg (Ne.symm hbtE')]
      rw [liftGenM_top, hcanonB]
      exact leGlue_tagA_tagB_top _ _
    · have hfm : f ≤ (constHom mid : EndP L) :=
        (leGlue_tagA_tagB_iff (constHom mid : EndP L) f f' hft).mp hxy'
      have hle : iotaEndPGenM hmid0 hmidt hbt f
          ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        le_trans (iotaEndPGenM_monotone hmid0 hmidt hbt hfm)
          (iotaEndPGenM_mid_le hmid0 hmidt hbt)
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) hle
  ·
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
      (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) trivial
  ·
    exact absurd hxy' (not_leGlue_tagB_tagA (constHom mid : EndP L) f f' hm0 hbt0
      (ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv))
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f))))
      (canon _ (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      have hle : liftGenM hmid0 hmidt hbt f ≤ liftGenM hmid0 hmidt hbt (⊤ : EndP L) := by
        rw [liftGenM_top]; exact le_top
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt (⊤ : EndP L)))) hle
    · have hwb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv
      have hff' : f ≤ f' := (leGlue_tagB_tagB_iff (constHom mid : EndP L) f f' hft hwb).mp hxy'
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f')))
        (liftGenM_monotone hmid0 hmidt hbt hff')
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f))))
      (canon _ (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))))
    have hmf' : (constHom mid : EndP L) ≤ f' :=
      (leGlue_tagB_tagC_iff (constHom mid : EndP L) f f').mp hxy'
    have hle : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        ≤ liftGenM hmid0 hmidt hbt f' := by
      unfold liftGenM
      rw [if_pos hmf']
      exact le_trans le_sup_right le_sup_left
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
      (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) hle
  ·
    exact absurd hxy' (not_leGlue_tagC_tagA (constHom mid : EndP L) f f'
      (ne_bot_of_canon_tagC (constHom mid : EndP L) f hxv))
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f))))
      (canon _ (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      rw [liftGenM_top]
      have hfm : f ≤ (constHom mid : EndP L) :=
        (leGlue_tagC_tagB_top_iff (constHom mid : EndP L) f).mp hxy'
      have hle : liftGenM hmid0 hmidt hbt f
          ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) := by
        rw [← liftGenM_mid hmid0 hmidt hbt]
        exact liftGenM_monotone hmid0 hmidt hbt hfm
      have e1 : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (constHom (midM mid) :
            EndP (GlueCar (P := EndP L) (constHom mid))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid)))) := by
        simp only [canon]
        rw [if_neg hm']
        simp
      have e2 : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid)))) := by
        simp only [canon]
        rw [if_neg (Ne.symm hbtE')]
      have hcanon : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (constHom (midM mid) :
            EndP (GlueCar (P := EndP L) (constHom mid))))) =
          canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))))) := by
        rw [e1, e2]
      have hb := rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
        (Sum.inr (Sum.inr (constHom (midM mid) :
          EndP (GlueCar (P := EndP L) (constHom mid))))) hle
      rwa [hcanon] at hb
    · exact absurd hxy' (not_leGlue_tagC_tagB (constHom mid : EndP L) f f' hft)
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f))))
      (canon _ (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))))
    have hff' : f ≤ f' := (leGlue_tagC_tagC_iff (constHom mid : EndP L) f f').mp hxy'
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
      (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f')))
      (liftGenM_monotone hmid0 hmidt hbt hff')

-- [D-0736] glueAAGenM_reflect
set_option maxHeartbeats 4000000 in
theorem glueAAGenM_reflect {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (constHom mid)}
    (hxy : glueAAGenM hmid0 hmidt hbt x ≤ glueAAGenM hmid0 hmidt hbt y) : x ≤ y := by
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (constHom mid)) :=
    glueCar_nontrivial (constHom mid : EndP L) hm0 hmt0 hbt0
  have hbtG : (⊥ : GlueCar (P := EndP L) (constHom mid)) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm' : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) ≠ ⊥ :=
    hmM_of (midM_ne_bot hmid0 hmidt hbt)
  have hmt' : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) ≠ ⊤ :=
    hmtM_of (midM_ne_top hmid0 hmidt hbt)
  have hbtE' : (⊥ : EndP (GlueCar (P := EndP L) (constHom mid)))
      ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) := hbtEL_of hbtG
  obtain ⟨xv, hxv⟩ := x
  obtain ⟨yv, hyv⟩ := y
  rw [GlueCar.le_def] at hxy
  rw [GlueCar.le_def]
  show leGlue (constHom mid : EndP L) xv yv
  rcases xv with f | f | f <;> rcases yv with f' | f' | f'
  ·
    have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
        (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f')) := hxy
    have hff' : iotaEndPGenM hmid0 hmidt hbt f ≤ iotaEndPGenM hmid0 hmidt hbt f' :=
      (tagA_iso _ hm' _ _).mp hxy2
    exact (tagA_iso (constHom mid : EndP L) hm0 f f').mpr
      ((iotaEndPGenM_le_iff hmid0 hmidt hbt).mp hff')
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't; exact leGlue_tagA_tagB_top _ _
    · have hLnb : liftGenM hmid0 hmidt hbt f'
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => (ne_bot_of_canon_tagB (constHom mid : EndP L) f' hyv)
          ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) =
          Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f')) := by
        simp only [canon]; rw [if_neg hLnb]
      have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) := by
        rw [← hcanonB]; exact hxy
      have hLnt : liftGenM hmid0 hmidt hbt f'
          ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf't ((liftGenM_eq_top_iff hmid0 hmidt hbt).mp hc)
      have hle : iotaEndPGenM hmid0 hmidt hbt f
          ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        (leGlue_tagA_tagB_iff (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (iotaEndPGenM hmid0 hmidt hbt f) (liftGenM hmid0 hmidt hbt f') hLnt).mp hxy2
      have hfm : f ≤ (constHom mid : EndP L) := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hle (iotaGenM mid z)
        rw [iotaEndPGenM_apply] at hz
        rw [pGenM_section] at hz
        rw [constHom_apply] at hz
        have hz' : iotaGenM mid (f z) ≤ iotaGenM mid mid := hz
        exact (iotaGenM_le_iff hmid0 _ _).mp hz'
      exact (leGlue_tagA_tagB_iff (constHom mid : EndP L) f f' hf't).mpr hfm
  ·
    exact tagA_le_tagC (constHom mid : EndP L) f f'
  ·
    exfalso
    have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv
    have hLnb : liftGenM hmid0 hmidt hbt f
        ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
    have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f))) =
        Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)) := by
      simp only [canon]; rw [if_neg hLnb]
    have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
        (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f')) := by
      rw [← hcanonB]; exact hxy
    exact not_leGlue_tagB_tagA
      (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
      (liftGenM hmid0 hmidt hbt f) (iotaEndPGenM hmid0 hmidt hbt f') hm' hbtE' hLnb hxy2
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      exact ⟨Sum.inr (Sum.inl f), self_mem_occs _ _, Sum.inr (Sum.inl (⊤ : EndP L)),
        self_mem_occs _ _, le_top⟩
    · have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv
      have hf'b : f' ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f' hyv
      have hLnb : liftGenM hmid0 hmidt hbt f
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hL'nb : liftGenM hmid0 hmidt hbt f'
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf'b ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hL'nt : liftGenM hmid0 hmidt hbt f'
          ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf't ((liftGenM_eq_top_iff hmid0 hmidt hbt).mp hc)
      have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f))) =
          Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)) := by
        simp only [canon]; rw [if_neg hLnb]
      have hcanonB' : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) =
          Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f')) := by
        simp only [canon]; rw [if_neg hL'nb]
      have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) := by
        rw [← hcanonB, ← hcanonB']; exact hxy
      have hLle : liftGenM hmid0 hmidt hbt f ≤ liftGenM hmid0 hmidt hbt f' :=
        (leGlue_tagB_tagB_iff (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (liftGenM hmid0 hmidt hbt f) (liftGenM hmid0 hmidt hbt f') hL'nt hLnb).mp hxy2
      have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : f ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hLle (iotaGenM mid z)
        have heq : (liftGenM hmid0 hmidt hbt f') (iotaGenM mid z) = iotaGenM mid (f' z) :=
          liftGenM_apply_iotaGenM_of_not_top hmid0 hmidt hbt hnle z
        rw [heq] at hz
        have hlb : iotaGenM mid (f z) ≤ (liftGenM hmid0 hmidt hbt f) (iotaGenM mid z) := by
          have e1 := liftGenM_apply hmid0 hmidt hbt f (iotaGenM mid z)
          rw [pGenM_section] at e1
          rw [e1]
          exact le_trans le_sup_left le_sup_left
        exact (iotaGenM_le_iff hmid0 _ _).mp (le_trans hlb hz)
      exact (leGlue_tagB_tagB_iff (constHom mid : EndP L) f f' hf't hfb).mpr hfin
  ·
    have hf''b : f' ≠ (⊥ : EndP L) := (canon_inr_inr_ne (constHom mid : EndP L) f' hyv).1
    have hf''m : f' ≠ (constHom mid : EndP L) :=
      (canon_inr_inr_ne (constHom mid : EndP L) f' hyv).2
    have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f hxv
    have hLfnb : liftGenM hmid0 hmidt hbt f
        ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
    have hLf'nb : liftGenM hmid0 hmidt hbt f'
        ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hf''b ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
    have hLf'nm : liftGenM hmid0 hmidt hbt f'
        ≠ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hf''m ((liftGenM_eq_mid_iff hmid0 hmidt hbt).mp hc)
    have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f))) =
        Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)) := by
      simp only [canon]; rw [if_neg hLfnb]
    have hcanonC : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) =
        Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f')) := by
      simp only [canon]; rw [if_neg hLf'nb, if_neg hLf'nm]
    have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f)))
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) := by
      rw [← hcanonB, ← hcanonC]; exact hxy
    have hmL : (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        ≤ liftGenM hmid0 hmidt hbt f' :=
      (leGlue_tagB_tagC_iff (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (liftGenM hmid0 hmidt hbt f) (liftGenM hmid0 hmidt hbt f')).mp hxy2
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      exact (leGlue_tagB_tagC_iff (constHom mid : EndP L) f (⊤ : EndP L)).mpr le_top
    · have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : (constHom mid : EndP L) ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hmL (iotaGenM mid z)
        have heq : (liftGenM hmid0 hmidt hbt f') (iotaGenM mid z) = iotaGenM mid (f' z) :=
          liftGenM_apply_iotaGenM_of_not_top hmid0 hmidt hbt hnle z
        rw [heq] at hz
        rw [constHom_apply] at hz
        have hz' : iotaGenM mid mid ≤ iotaGenM mid (f' z) := hz
        exact (iotaGenM_le_iff hmid0 _ _).mp hz'
      exact (leGlue_tagB_tagC_iff (constHom mid : EndP L) f f').mpr hfin
  ·
    exfalso
    have hfb := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).1
    have hfm := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).2
    have hLfnb : liftGenM hmid0 hmidt hbt f
        ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
    have hLfnm : liftGenM hmid0 hmidt hbt f
        ≠ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfm ((liftGenM_eq_mid_iff hmid0 hmidt hbt).mp hc)
    have hcanonC : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f))) =
        Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)) := by
      simp only [canon]; rw [if_neg hLfnb, if_neg hLfnm]
    have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
        (Sum.inl (iotaEndPGenM hmid0 hmidt hbt f')) := by
      rw [← hcanonC]; exact hxy
    exact not_leGlue_tagC_tagA
      (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
      (liftGenM hmid0 hmidt hbt f) (iotaEndPGenM hmid0 hmidt hbt f') hLfnb hxy2
  ·
    have hfb := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).1
    have hfm := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).2
    have hLfnb : liftGenM hmid0 hmidt hbt f
        ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
    have hLfnm : liftGenM hmid0 hmidt hbt f
        ≠ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
      fun hc => hfm ((liftGenM_eq_mid_iff hmid0 hmidt hbt).mp hc)
    have hcanonC : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f))) =
        Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)) := by
      simp only [canon]; rw [if_neg hLfnb, if_neg hLfnm]
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      have hLtop_ne_bot : liftGenM hmid0 hmidt hbt (⊤ : EndP L)
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) := by
        rw [liftGenM_top]; exact Ne.symm hbtE'
      have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt (⊤ : EndP L)))) =
          Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt (⊤ : EndP L))) := by
        simp only [canon]
        rw [if_neg hLtop_ne_bot]
      have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt (⊤ : EndP L)))) := by
        rw [← hcanonC, ← hcanonB]; exact hxy
      rw [liftGenM_top] at hxy2
      have hle : liftGenM hmid0 hmidt hbt f
          ≤ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        (leGlue_tagC_tagB_top_iff
          (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (liftGenM hmid0 hmidt hbt f)).mp hxy2
      by_cases hft : f = (⊤ : EndP L)
      · exfalso
        subst hft
        rw [liftGenM_top] at hle
        exact hmt' (le_antisymm le_top hle)
      · have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hft (top_le_iff.mp hc)
        have hfin : f ≤ (constHom mid : EndP L) := by
          rw [OrderHom.le_def]
          intro z
          have hz := OrderHom.le_def.mp hle (iotaGenM mid z)
          have heq : (liftGenM hmid0 hmidt hbt f) (iotaGenM mid z) = iotaGenM mid (f z) :=
            liftGenM_apply_iotaGenM_of_not_top hmid0 hmidt hbt hnle z
          rw [heq] at hz
          rw [constHom_apply] at hz
          have hz' : iotaGenM mid (f z) ≤ iotaGenM mid mid := hz
          exact (iotaGenM_le_iff hmid0 _ _).mp hz'
        exact (leGlue_tagC_tagB_top_iff (constHom mid : EndP L) f).mpr hfin
    · exfalso
      have hf'b : f' ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (constHom mid : EndP L) f' hyv
      have hL'nb : liftGenM hmid0 hmidt hbt f'
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf'b ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hL'nt : liftGenM hmid0 hmidt hbt f'
          ≠ (⊤ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf't ((liftGenM_eq_top_iff hmid0 hmidt hbt).mp hc)
      have hcanonB : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) =
          Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f')) := by
        simp only [canon]; rw [if_neg hL'nb]
      have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
          (Sum.inr (Sum.inl (liftGenM hmid0 hmidt hbt f'))) := by
        rw [← hcanonC, ← hcanonB]; exact hxy
      exact not_leGlue_tagC_tagB
        (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
        (liftGenM hmid0 hmidt hbt f) (liftGenM hmid0 hmidt hbt f') hL'nt hxy2
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      exact (leGlue_tagC_tagC_iff (constHom mid : EndP L) f (⊤ : EndP L)).mpr le_top
    · have hfb := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).1
      have hfm := (canon_inr_inr_ne (constHom mid : EndP L) f hxv).2
      have hf'b := (canon_inr_inr_ne (constHom mid : EndP L) f' hyv).1
      have hf'm := (canon_inr_inr_ne (constHom mid : EndP L) f' hyv).2
      have hLfnb : liftGenM hmid0 hmidt hbt f
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hfb ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hLfnm : liftGenM hmid0 hmidt hbt f
          ≠ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hfm ((liftGenM_eq_mid_iff hmid0 hmidt hbt).mp hc)
      have hL'nb : liftGenM hmid0 hmidt hbt f'
          ≠ (⊥ : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf'b ((liftGenM_eq_bot_iff hmid0 hmidt hbt).mp hc)
      have hL'nm : liftGenM hmid0 hmidt hbt f'
          ≠ (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid))) :=
        fun hc => hf'm ((liftGenM_eq_mid_iff hmid0 hmidt hbt).mp hc)
      have hcanonCf : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f))) =
          Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)) := by
        simp only [canon]; rw [if_neg hLfnb, if_neg hLfnm]
      have hcanonCf' : canon (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) =
          Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f')) := by
        simp only [canon]; rw [if_neg hL'nb, if_neg hL'nm]
      have hxy2 : leGlue (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f)))
          (Sum.inr (Sum.inr (liftGenM hmid0 hmidt hbt f'))) := by
        rw [← hcanonCf, ← hcanonCf']; exact hxy
      have hLle : liftGenM hmid0 hmidt hbt f ≤ liftGenM hmid0 hmidt hbt f' :=
        (leGlue_tagC_tagC_iff _ _ _).mp hxy2
      have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : f ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hLle (iotaGenM mid z)
        have heq : (liftGenM hmid0 hmidt hbt f') (iotaGenM mid z) = iotaGenM mid (f' z) :=
          liftGenM_apply_iotaGenM_of_not_top hmid0 hmidt hbt hnle z
        rw [heq] at hz
        have hlb : iotaGenM mid (f z) ≤ (liftGenM hmid0 hmidt hbt f) (iotaGenM mid z) := by
          have e1 := liftGenM_apply hmid0 hmidt hbt f (iotaGenM mid z)
          rw [pGenM_section] at e1
          rw [e1]
          exact le_trans le_sup_left le_sup_left
        exact (iotaGenM_le_iff hmid0 _ _).mp (le_trans hlb hz)
      exact (leGlue_tagC_tagC_iff (constHom mid : EndP L) f f').mpr hfin

-- [D-0737] glueAAGenM_le_iff
theorem glueAAGenM_le_iff {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (constHom mid)} :
    glueAAGenM hmid0 hmidt hbt x ≤ glueAAGenM hmid0 hmidt hbt y ↔ x ≤ y :=
  ⟨glueAAGenM_reflect hmid0 hmidt hbt, glueAAGenM_monotone hmid0 hmidt hbt⟩

-- [D-0738] glueAAGenM_injective
theorem glueAAGenM_injective {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) : Function.Injective (glueAAGenM hmid0 hmidt hbt) := by
  have hm0 : (constHom mid : EndP L) ≠ ⊥ := hmM_of hmid0
  have hmt0 : (constHom mid : EndP L) ≠ ⊤ := hmtM_of hmidt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (constHom mid : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (constHom mid : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (constHom mid)) :=
    glueCar_nontrivial (constHom mid : EndP L) hm0 hmt0 hbt0
  have hbtG : (⊥ : GlueCar (P := EndP L) (constHom mid)) ≠ ⊤ := bot_ne_top_of_nontrivial
  letI := glueCarPartialOrder (constHom (midM mid) : EndP (GlueCar (P := EndP L) (constHom mid)))
    (hmM_of (midM_ne_bot hmid0 hmidt hbt)) (hmtM_of (midM_ne_top hmid0 hmidt hbt))
    (hbtEL_of hbtG)
  intro x y h
  exact le_antisymm ((glueAAGenM_le_iff hmid0 hmidt hbt).mp h.le)
    ((glueAAGenM_le_iff hmid0 hmidt hbt).mp h.ge)

end MigratedReflect

section MigrationObstructions

-- [D-0739] §Two-negative-checks
variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0740] pGenBad
noncomputable def pGenBad (mid : L) (w : GlueCar (P := EndP L) (constHom mid)) : L :=
  match w.1 with
  | Sum.inl f => f (⊥ : L)
  | Sum.inr (Sum.inl f) => if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)
  | Sum.inr (Sum.inr _) => (⊤ : L)

-- [D-0741] pGenBad_not_monotone
theorem pGenBad_not_monotone :
    ¬ (∀ w w' : GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3)),
        w ≤ w' → pGenBad (1 : Fin 3) w ≤ pGenBad (1 : Fin 3) w') := by
  intro h
  have hm0 : (constHom (1 : Fin 3) : EndP (Fin 3)) ≠ ⊥ := hmM_of (by decide)
  have hmt0 : (constHom (1 : Fin 3) : EndP (Fin 3)) ≠ ⊤ := hmtM_of (by decide)
  have hcw' : canon (constHom (1 : Fin 3) : EndP (Fin 3))
      (Sum.inr (Sum.inl (constHom (1 : Fin 3)))) =
      Sum.inr (Sum.inl (constHom (1 : Fin 3) : EndP (Fin 3))) := by
    simp only [canon]; rw [if_neg hm0]
  have hle : leGlue (constHom (1 : Fin 3) : EndP (Fin 3))
      (Sum.inl (constHom (1 : Fin 3) : EndP (Fin 3)))
      (Sum.inr (Sum.inl (constHom (1 : Fin 3) : EndP (Fin 3)))) :=
    (leGlue_tagA_tagB_iff (constHom (1 : Fin 3) : EndP (Fin 3)) (constHom (1 : Fin 3))
      (constHom (1 : Fin 3)) hmt0).mpr le_rfl
  have hb := h ⟨Sum.inl (constHom (1 : Fin 3)), rfl⟩
    ⟨Sum.inr (Sum.inl (constHom (1 : Fin 3))), hcw'⟩ hle
  have e2 : pGenBad (1 : Fin 3)
      (⟨Sum.inr (Sum.inl (constHom (1 : Fin 3))), hcw'⟩ :
        GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))) = (⊥ : Fin 3) := by
    show (if (constHom (1 : Fin 3) : EndP (Fin 3)) = ⊤ then (⊤ : Fin 3) else (⊥ : Fin 3))
      = (⊥ : Fin 3)
    rw [if_neg hmt0]
  rw [e2] at hb
  have e1 : pGenBad (1 : Fin 3)
      (⟨Sum.inl (constHom (1 : Fin 3)), rfl⟩ :
        GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))) = (1 : Fin 3) := rfl
  rw [e1] at hb
  exact absurd hb (by decide)

-- [D-0742] skelL_not_admissible
theorem skelL_not_admissible {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (mu : GlueCar (P := EndP L) (constHom mid))
    (hmu : mu.1 = skelL (constHom mid : EndP L))
    (h1 : ∀ y : L, y ≤ mid → iotaGenM mid y ≤ mu)
    (h2 : ∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) : False := by
  have heq := midM_unique hmid0 hmidt hbt mu h1 h2
  refine midM_ne_skelL mid ?_
  rw [← heq]
  exact hmu

end MigrationObstructions

section SkelLLocalisation

-- [D-0743] §Which-of-the-two-obligations-skelL-fails
variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0744] skelL_satisfies_hup
theorem skelL_satisfies_hup {mid : L} (hmidt : mid ≠ (⊤ : L))
    (mu : GlueCar (P := EndP L) (constHom mid))
    (hmu : mu.1 = skelL (constHom mid : EndP L)) (y : L) (hy : y ≤ mid) :
    iotaGenM mid y ≤ mu := by
  show leGlue (constHom mid : EndP L) (Sum.inl (constHom y : EndP L)) mu.1
  rw [hmu]
  exact (leGlue_tagA_tagB_iff (constHom mid : EndP L) (constHom y) (constHom mid)
    (hmtM_of hmidt)).mpr ((constHom_le_iff y mid).mpr hy)

-- [D-0745] skelL_fails_hdown
theorem skelL_fails_hdown {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hbt : (⊥ : L) ≠ ⊤)
    (mu : GlueCar (P := EndP L) (constHom mid))
    (hmu : mu.1 = skelL (constHom mid : EndP L)) :
    ¬ (∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) := by
  intro h
  have hb : leGlue (constHom mid : EndP L) mu.1 (Sum.inl (constHom mid : EndP L)) :=
    h mid le_rfl
  rw [hmu] at hb
  exact not_leGlue_tagB_tagA (constHom mid : EndP L) (constHom mid) (constHom mid)
    (hmM_of hmid0) (hbtEL_of hbt) (hmM_of hmid0) hb

end SkelLLocalisation

section NextBasepointUniqueGen

-- [D-0746] §The-three-way-fork-dissolves-hdown-alone-forces
variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

-- [D-0747] tagA_of_hdown_at_mid
theorem tagA_of_hdown_at_mid (m a : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCar (P := P) m) (hdown_mid : leGlue m mu.1 (Sum.inl a)) :
    ∃ x, mu.1 = Sum.inl x := by
  obtain ⟨v, hv⟩ := mu
  rcases v with x | y | z
  · exact ⟨x, rfl⟩
  · exact absurd hdown_mid
      (not_leGlue_tagB_tagA m y a hm hbt (ne_bot_of_canon_tagB m y hv))
  · exact absurd hdown_mid
      (not_leGlue_tagC_tagA m z a (ne_bot_of_canon_tagC m z hv))

-- [D-0748] not_hdown_of_tagB
theorem not_hdown_of_tagB (m a y : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCar (P := P) m) (hmu : mu.1 = Sum.inr (Sum.inl y)) :
    ¬ leGlue m mu.1 (Sum.inl a) := by
  intro h
  obtain ⟨x, hx⟩ := tagA_of_hdown_at_mid m a hm hbt mu h
  rw [hmu] at hx
  exact absurd hx (by simp)

-- [D-0749] not_hdown_of_tagC
theorem not_hdown_of_tagC (m a z : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCar (P := P) m) (hmu : mu.1 = Sum.inr (Sum.inr z)) :
    ¬ leGlue m mu.1 (Sum.inl a) := by
  intro h
  obtain ⟨x, hx⟩ := tagA_of_hdown_at_mid m a hm hbt mu h
  rw [hmu] at hx
  exact absurd hx (by simp)

-- [D-0750] canon_tagC_self
theorem canon_tagC_self (m : P) (hm : m ≠ ⊥) :
    canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P)) := by
  simp only [canon]
  rw [if_neg hm, if_pos trivial]

end NextBasepointUniqueGen

section NextBasepointUniqueM

-- [D-0751] §Specialised-to-the-migration-s-own-hdown
variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0752] tagA_of_hdownM
theorem tagA_of_hdownM {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hbt : (⊥ : L) ≠ ⊤)
    (mu : GlueCar (P := EndP L) (constHom mid))
    (hdown : ∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) :
    ∃ f : EndP L, mu.1 = Sum.inl f :=
  tagA_of_hdown_at_mid (constHom mid : EndP L) (constHom mid) (hmM_of hmid0)
    (hbtEL_of hbt) mu (hdown mid le_rfl)

-- [D-0753] skelL_fails_hdown_of_general
theorem skelL_fails_hdown_of_general {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hbt : (⊥ : L) ≠ ⊤)
    (mu : GlueCar (P := EndP L) (constHom mid))
    (hmu : mu.1 = skelL (constHom mid : EndP L)) :
    ¬ (∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) := by
  intro h
  exact not_hdown_of_tagB (constHom mid : EndP L) (constHom mid) (constHom mid)
    (hmM_of hmid0) (hbtEL_of hbt) mu hmu (h mid le_rfl)

-- [D-0754] muM_eq_tagA_mid
theorem muM_eq_tagA_mid {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (mu : GlueCar (P := EndP L) (constHom mid))
    (hup : ∀ y : L, y ≤ mid → iotaGenM mid y ≤ mu)
    (hdown : ∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) :
    ∃ f : EndP L, mu.1 = Sum.inl f ∧ f = (constHom mid : EndP L) := by
  refine ⟨constHom mid, ?_, rfl⟩
  rw [midM_unique hmid0 hmidt hbt mu hup hdown]
  rfl

-- [D-0755] muM_eq_skelG1
theorem muM_eq_skelG1 {mid : L} (hmid0 : mid ≠ (⊥ : L)) (hmidt : mid ≠ (⊤ : L))
    (hbt : (⊥ : L) ≠ ⊤) (mu : GlueCar (P := EndP L) (constHom mid))
    (hup : ∀ y : L, y ≤ mid → iotaGenM mid y ≤ mu)
    (hdown : ∀ y : L, mid ≤ y → mu ≤ iotaGenM mid y) :
    mu.1 = skelG1 (constHom mid : EndP L) := by
  obtain ⟨f, hf, hfv⟩ := muM_eq_tagA_mid hmid0 hmidt hbt mu hup hdown
  rw [hf, hfv]

end NextBasepointUniqueM

section NextBasepointNonVacuity

-- [D-0756] §Non-vacuity-of-the-two-excluded-branches
variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

-- [D-0757] canon_tagC_top
theorem canon_tagC_top (m : P) (hbt : (⊥ : P) ≠ ⊤) (hmt : m ≠ ⊤) :
    canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr (⊤ : P)) := by
  simp only [canon]
  rw [if_neg (Ne.symm hbt), if_neg (Ne.symm hmt)]

-- [D-0758] tagC_top_fails_hdown
theorem tagC_top_fails_hdown (m a : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (hmt : m ≠ ⊤) :
    ¬ leGlue m (Sum.inr (Sum.inr (⊤ : P))) (Sum.inl a) :=
  fun h =>
    not_hdown_of_tagC m a ⊤ hm hbt ⟨_, canon_tagC_top m hbt hmt⟩ rfl h

end NextBasepointNonVacuity

section NextBasepointUniqueGenMirror

-- [D-0759] §The-same-theorem-in-the-Gen-world-the-scoping
variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-0760] tagA_of_hdownGen_at_mid
theorem tagA_of_hdownGen_at_mid (m a : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCarGen (P := P) m) (hdown_mid : leGlueGen m mu.1 (Sum.inl a)) :
    ∃ x, mu.1 = Sum.inl x := by
  obtain ⟨v, hv⟩ := mu
  rcases v with x | y | z
  · exact ⟨x, rfl⟩
  · exact absurd hdown_mid
      (not_leGlue_tagB_tagAGen m y a hm hbt (ne_bot_of_canon_tagBGen m y hv))
  · exact absurd hdown_mid
      (not_leGlue_tagC_tagAGen m z a (ne_bot_of_canon_tagCGen m z hv))

-- [D-0761] not_hdownGen_of_tagB
theorem not_hdownGen_of_tagB (m a y : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCarGen (P := P) m) (hmu : mu.1 = Sum.inr (Sum.inl y)) :
    ¬ leGlueGen m mu.1 (Sum.inl a) := by
  intro h
  obtain ⟨x, hx⟩ := tagA_of_hdownGen_at_mid m a hm hbt mu h
  rw [hmu] at hx
  exact absurd hx (by simp)

-- [D-0762] not_hdownGen_of_tagC
theorem not_hdownGen_of_tagC (m a z : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (mu : GlueCarGen (P := P) m) (hmu : mu.1 = Sum.inr (Sum.inr z)) :
    ¬ leGlueGen m mu.1 (Sum.inl a) := by
  intro h
  obtain ⟨x, hx⟩ := tagA_of_hdownGen_at_mid m a hm hbt mu h
  rw [hmu] at hx
  exact absurd hx (by simp)

end NextBasepointUniqueGenMirror
