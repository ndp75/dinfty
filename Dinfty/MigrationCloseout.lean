import Dinfty.GlueAAGenReflectM

open GluingTowerLibrary

/-!
# Closing the normalized migration: the lemmas `GlueAAGenReflectM` does not have

`Dinfty/GlueAAGenReflectM.lean` is the `constHom mid` migration and carries the
hard part — `pGenM` (with the **correct** copy-`B` branch, returning `mid` and
not `⊥`), `pGenM_section`/`_deflation`/`_monotone`, `iotaGenM`, `midM`,
`glueAAGenM` and its monotone/reflect/le_iff/injective.

Integrating `SierpinskiApplication.lean.normalized_wip` leaves 16 errors, and
repointing its declarations at the `*M` versions covers all but four lemmas.
This module supplies what is missing.

**Read the warning in `GlueAAGenReflectM` first.** `pGenBad_not_monotone` refutes
the verbatim transplant of `pGen`'s body: its copy-`B` `⊥` is `(OrderHom.id) ⊥`
in disguise — a *use* of the marked point, not a constant. Anything ported here
has to respect that; the `mid` in `pGenM`'s copy-`B` branch is load-bearing.

Also note `midM mid = iotaGenM mid mid = tag_A (constHom mid)` — this module is
on the **tag-`A`** side, per the 2026-08-27 basepoint decision, not Ratnayake's
`tag_B`. The two differ, and `MarkedPointTranslator` records that no
automorphism reconciles them.
-/

open scoped Classical

universe u

section MigrationCloseout

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

/-- **`pGenM` sends the top to the top.**  The migrated `pGen_top`.

The top of the glued object is `tag_C ⊤`, and `pGenM`'s copy-`C` branch is the
constant `⊤` — the one branch where the `id` and `constHom mid` versions agree,
so the original proof transfers with only the marked point substituted. -/
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

/-- **`iotaEndPGenM` on a constant.**  The migrated `iotaEndPGen_constHom`.

This one transfers verbatim, and the reason is worth stating: `constHom x`
*discards* its argument, so the `pGenM` value never reaches the result and the
`mid`-versus-`⊥` difference in `pGenM`'s copy-`B` branch cannot bite. -/
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

/-- **Overlap agreement, migrated.**  `glueAAGenM` restricted to `iotaGenM`'s
image recovers the next level's `iotaGenM` — at the next marked point
`midM mid`, which is `tag_A (constHom mid)`. -/
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

-- **Tag-`A` deflation, migrated.**  `glueAAGenM` followed by the next level's
-- projection lands below the point it came from, on copy `A`.
--
-- This transfers because it only ever touches copy `A` and `⊥`, exactly where
-- `pGenM` and `pGen` agree — the divergent copy-`B` branch is never reached.
-- `iotaGenM_bot` and `pGenM_section` replace their `id` counterparts.
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

-- **Tag-`B` deflation, migrated — and this one is NOT a transfer.**
--
-- The `id` version concludes via `pGen`'s copy-`B` value `⊥`.  `pGenM`'s copy-`B`
-- value is `mid`, so the migrated statement lands at `midM mid` instead, and the
-- conclusion becomes `midM mid ≤ tag_B f`.  That holds for a different reason
-- than the original: `midM mid = tag_A (constHom mid)`, and copy `A` sits below
-- copy `B` exactly when the copy-`A` value is `≤` the marked point — here
-- `constHom mid ≤ constHom mid`, reflexively.  So the divergence that made
-- `pGenBad` non-monotone is what makes this case work.
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

-- **Cross-tag `C`–`A` sufficiency, migrated.**
--
-- This one IS a clean transfer: every step is stated over an arbitrary marked
-- point `m`, and the only place `pGen`'s value enters is the copy-`C` branch,
-- where `pGen` and `pGenM` agree (both `⊤`).  The copy-`B` branch — the sole
-- site where the two projections differ — is discharged by
-- `leGlue_tagB_tagC_iff`, whose condition `m ≤ f` is the hypothesis, not a
-- fact about the projection.  So the divergence never reaches this proof.
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
