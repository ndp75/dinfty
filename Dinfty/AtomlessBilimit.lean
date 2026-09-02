import Dinfty.EmbTagwise
import Dinfty.GlueAAJoin
import Dinfty.TowerNoAbsorption
import Dinfty.StageCofinal

open GluingTowerLibrary SierpinskiApplication

/-!
# The singular atom of an arbitrary slice — and why it does not reach `B`

Every level `D k` has a **least non-`⊥` element** `lamD k` (`UniqueAtomCoatom`,
carried at every level by `realUniqueAtomCoatom`).  That is the natural thing to
tie a witness level to: if the slices' atoms agreed, `B` would have a unique
atom, every automorphism would fix it, and every stage map would preserve it.

They do not agree.  This module computes the atom of every slice in closed form
and shows the tower's embeddings destroy it — so **`B` is atomless**, and the
atom cannot pin anything.

## The atom of a slice, in closed form

`atomOf (EndP P) = spikeHom (atomOf P)` (`endPUniqueAtomCoatom`) and the atom of
a glue is its copy-`A` image, so

```lean
lamD_succ : lamD (k+1) = glueA (markedPt k) (spikeHom (lamD k))
```

an iterated spike, all the way down to `atomOf (Fin 3) = 1`.

## The embeddings transport spikes — except at the base

For a **tripointed** ep-pair, `endUpFun` carries spikes to spikes:

```lean
endUpFun_spikeHom : E.endUpFun (spikeHom v) = spikeHom (E.emb v)
```

The proof needs `E.prj x = ⊤ → x = ⊤`, which is exactly `deflation` plus
`emb_top`.  So at every successor level the atom is preserved *if and only if*
it was preserved one level down: the question falls to the base.

And at the base it fails.  `(iter 0).emb` is `glueAA 0`, whose copy-`A` action is
`iotaEndP 0 f = fun w => iotaD 0 (f (pD 0 w))` — `endUpFun` for the **legacy**
pair `(iotaD, pD)`, which is *not* tripointed.  Evaluating at `⊤`:

* `iotaEndP 0 (spikeHom a) ⊤ = iotaD 0 a = glueA (markedPt 0) (constHom a)`,
* `spikeHom (lamD 1) ⊤ = lamD 1 = glueA (markedPt 0) (spikeHom a)`,

and `constHom a ≠ spikeHom a` for `a ≠ ⊥`.  The atom is **fattened from a spike
to a constant**, exactly once, by `iotaD`.

## Consequence

`emb_lamD_ne` at every level, so the stage atoms `insD k (lamD (k+1))` are a
strictly decreasing chain of non-`⊥` elements and none survives:

```lean
no_isAtom (a : B) : ¬ IsAtom a
```

`B` has a top (unlike `DInfty`, cf. `DInftyNoFootholds.no_top`) but no atoms.
So there is no "singular atom of `B`" for a witness level to be tied to, and any
height-from-the-bottom proxy for the stage index is unavailable here for the
same reason it was unavailable for the colimit.  Obstruction (T) — `iotaD`
missing the top — is once again the mechanism, injected at the base of the
`Φ`-tower and inherited by every level above it.
-/

open scoped Classical

namespace AtomlessBilimit

open PhiIterateTower PhiBilimit EpPairTower StageRigidity StageEmbedding
open TowerNoAbsorption GenContinuity GlueAAJoin PhiStagePipe

/-! ## 1.  Spikes -/

variable {P : Type} [Lattice P] [BoundedOrder P]

theorem spikeHom_ne_bot {v : P} (hv : v ≠ ⊥) : spikeHom v ≠ (⊥ : EndP P) := by
  intro h
  have h1 : spikeHom v (⊤ : P) = (⊥ : EndP P) ⊤ := congrArg (fun g : EndP P => g ⊤) h
  rw [spikeHom_apply_top, endPBot_apply] at h1
  exact hv h1

theorem spikeHom_injective : Function.Injective (spikeHom : P → EndP P) := by
  intro u v h
  have h1 : spikeHom u (⊤ : P) = spikeHom v (⊤ : P) := congrArg (fun g : EndP P => g ⊤) h
  rwa [spikeHom_apply_top, spikeHom_apply_top] at h1

theorem spikeHom_ne_constHom {v : P} (hv : v ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    spikeHom v ≠ constHom v := by
  intro h
  have h1 : spikeHom v (⊥ : P) = constHom v (⊥ : P) := congrArg (fun g : EndP P => g ⊥) h
  rw [spikeHom_apply_of_ne v hbt] at h1
  exact hv h1.symm

/-- A monotone endomorphism is `⊥` as soon as it is `⊥` at `⊤`. -/
theorem eq_bot_of_apply_top {f : EndP P} (h : f ⊤ = ⊥) : f = (⊥ : EndP P) := by
  apply OrderHom.ext
  funext x
  have hx : f x ≤ f ⊤ := f.monotone le_top
  rw [h, le_bot_iff] at hx
  rw [hx, endPBot_apply]

/-! ## 2.  The atom of a slice, in closed form -/

/-- `lamD` is pinned by its two defining properties, so nothing has to be
unfolded to identify it. -/
theorem eq_lamD {k : ℕ} {a : D k} (ha : a ≠ ⊥) (hle : ∀ z : D k, z ≠ ⊥ → a ≤ z) :
    a = lamD k :=
  le_antisymm (hle _ (lamD_ne_bot k)) (lamD_le k a ha)

theorem bot_val_succ (k : ℕ) : ((⊥ : D (k + 1))).1 = Sum.inl (⊥ : EndP (D k)) := rfl

theorem glueA_ne_bot_of_ne_bot (k : ℕ) {f : EndP (D k)} (hf : f ≠ ⊥) :
    glueA (markedPt k) f ≠ (⊥ : D (k + 1)) := by
  intro h
  have h1 : (glueA (markedPt k) f).1 = ((⊥ : D (k + 1))).1 := congrArg Subtype.val h
  rw [bot_val_succ k] at h1
  exact hf (Sum.inl_injective h1)

theorem ne_bot_of_tagA (k : ℕ) {b : D (k + 1)} {u : EndP (D k)} (hb : b.1 = Sum.inl u)
    (hbb : b ≠ ⊥) : u ≠ ⊥ := by
  intro hu
  apply hbb
  refine Subtype.ext ?_
  rw [hb, bot_val_succ k, hu]

/-- **The atom of every slice, in closed form: an iterated spike.** -/
theorem lamD_succ (k : ℕ) :
    lamD (k + 1) = glueA (markedPt k) (spikeHom (lamD k)) := by
  have hnd := D_marked_point_nondegenerate k
  have ha : lamD k ≠ (⊥ : D k) := lamD_ne_bot k
  have hbtD : (⊥ : D k) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hs : spikeHom (lamD k) ≠ (⊥ : EndP (D k)) := spikeHom_ne_bot ha
  refine (eq_lamD (glueA_ne_bot_of_ne_bot k hs) ?_).symm
  intro b hb
  obtain ⟨bv, hbc⟩ := b
  show leGlueGen (markedPt k) (Sum.inl (spikeHom (lamD k))) bv
  -- the spike is below every non-`⊥` endomorphism, and below the marked point
  have hspike : ∀ u : EndP (D k), u ≠ ⊥ → spikeHom (lamD k) ≤ u := by
    intro u hu
    have hut : u ⊤ ≠ (⊥ : D k) := fun hc => hu (eq_bot_of_apply_top hc)
    rw [OrderHom.le_def]
    intro x
    rcases eq_or_ne x (⊤ : D k) with hx | hx
    · subst hx
      rw [spikeHom_apply_top]
      exact lamD_le k _ hut
    · rw [spikeHom_apply_of_ne _ hx]
      exact bot_le
  have hmark : spikeHom (lamD k) ≤ markedPt k := by
    refine hspike (markedPt k) ?_
    intro hc
    refine dMid_ne_bot k ?_
    have h1 : (markedPt k) (⊤ : D k) = (⊥ : EndP (D k)) ⊤ :=
      congrArg (fun g : EndP (D k) => g ⊤) hc
    rwa [markedPt_apply, endPBot_apply] at h1
  cases bv with
  | inl u =>
      have hu : u ≠ ⊥ := ne_bot_of_tagA k (b := ⟨Sum.inl u, hbc⟩) rfl hb
      exact (leGlueGen_tagA_tagA_iff (markedPt k) hnd.1 _ u).mpr (hspike u hu)
  | inr w =>
      cases w with
      | inl y =>
          rcases eq_or_ne y (⊤ : EndP (D k)) with hy | hy
          · subst hy
            exact leGlue_tagA_tagB_topGen (markedPt k) (spikeHom (lamD k))
          · exact (leGlue_tagA_tagB_iffGen (markedPt k) _ y hy).mpr hmark
      | inr c => exact leGlueGen_tagA_tagC (markedPt k) _ c

/-! ## 3.  Tripointed ep-pairs transport spikes -/

theorem prj_eq_top_iff {k : ℕ} (E : TriEP k) (x : D (k + 1)) :
    E.prj x = ⊤ ↔ x = ⊤ := by
  constructor
  · intro h
    have h1 := E.deflation x
    rw [h, E.emb_top] at h1
    exact top_le_iff.mp h1
  · rintro rfl
    exact E.prj_top

/-- **`endUpFun` carries spikes to spikes** — the only place `deflation` and
`emb_top` are needed, and the reason the atom question falls to the base. -/
theorem endUpFun_spikeHom {k : ℕ} (E : TriEP k) (v : D k) :
    E.endUpFun (spikeHom v) = spikeHom (E.emb v) := by
  apply OrderHom.ext
  funext x
  show E.emb ((spikeHom v) (E.prj x)) = spikeHom (E.emb v) x
  rcases eq_or_ne x (⊤ : D (k + 1)) with hx | hx
  · subst hx
    rw [E.prj_top, spikeHom_apply_top, spikeHom_apply_top]
  · have hp : E.prj x ≠ ⊤ := fun hc => hx ((prj_eq_top_iff E x).mp hc)
    rw [spikeHom_apply_of_ne _ hp, spikeHom_apply_of_ne _ hx, E.emb_bot]

/-- The tower's embedding on copy `A`, at successor levels. -/
theorem emb_succ_glueA (n : ℕ) (h : EndP (D (n + 1))) :
    (iter (n + 1)).emb (glueA (markedPt (n + 1)) h)
      = glueA (markedPt (n + 2)) ((iter n).endUpFun h) := by
  refine Subtype.ext ?_
  rw [EmbTagwise.emb_succ_val]
  rfl

/-! ## 4.  The base fattens the spike -/

/-- `glueAA 0`'s copy-`A` action is `endUpFun` for the **legacy** pair
`(iotaD, pD)`, which misses `⊤`; so it sends the spike to a constant. -/
theorem base_emb_lamD_ne : (iter 0).emb (lamD 1) ≠ lamD 2 := by
  have ha : lamD 0 ≠ (⊥ : D 0) := lamD_ne_bot 0
  have hbt0 : (⊥ : D 0) ≠ ⊤ := bot_ne_top_of_nontrivial
  intro hcon
  rw [lamD_succ 0] at hcon
  have h1 : glueAA 0 (glueA (markedPt 0) (spikeHom (lamD 0)))
      = glueA (markedPt 1) (iotaEndP 0 (spikeHom (lamD 0))) :=
    glueAA_glueA 0 (spikeHom (lamD 0))
  rw [show (iter 0).emb = glueAA 0 from rfl, h1, lamD_succ 1] at hcon
  have h2 : iotaEndP 0 (spikeHom (lamD 0)) = spikeHom (lamD 1) :=
    glueA_injective (markedPt 1) hcon
  have h3 : (iotaEndP 0 (spikeHom (lamD 0))) (⊤ : D 1) = spikeHom (lamD 1) (⊤ : D 1) :=
    congrArg (fun g : EndP (D 1) => g ⊤) h2
  rw [spikeHom_apply_top] at h3
  have h4 : iotaD 0 ((spikeHom (lamD 0)) (pD 0 (⊤ : D 1))) = lamD 1 := h3
  rw [pD_top 0, spikeHom_apply_top] at h4
  -- `iotaD 0 (lamD 0)` is the *constant*, `lamD 1` is the *spike*
  rw [show iotaD 0 (lamD 0) = glueA (markedPt 0) (constHom (lamD 0)) from rfl,
    lamD_succ 0] at h4
  exact spikeHom_ne_constHom ha hbt0 (glueA_injective (markedPt 0) h4).symm

/-! ## 5.  …and every level inherits it -/

/-- **The tower's embedding never preserves the slice's atom.** -/
theorem emb_lamD_ne : ∀ k : ℕ, (iter k).emb (lamD (k + 1)) ≠ lamD (k + 2)
  | 0 => base_emb_lamD_ne
  | k + 1 => by
      intro hcon
      rw [lamD_succ (k + 1), emb_succ_glueA k (spikeHom (lamD (k + 1))),
        endUpFun_spikeHom (iter k) (lamD (k + 1)), lamD_succ (k + 2)] at hcon
      exact emb_lamD_ne k
        (spikeHom_injective (glueA_injective (markedPt (k + 2)) hcon))

/-! ## 6.  `B` is atomless -/

theorem botB_eq_bot : botB = (⊥ : B) := le_antisymm (botB_le ⊥) bot_le

theorem exists_ne_bot_component {z : B} (hz : z ≠ ⊥) :
    ∃ N : ℕ, (z.1 N : D (N + 1)) ≠ (⊥ : D (N + 1)) := by
  by_contra hc
  push_neg at hc
  refine hz ?_
  rw [← botB_eq_bot]
  exact Subtype.ext (funext fun n => hc n)

/-- The stage atoms strictly decrease. -/
theorem stage_atom_lt (N : ℕ) :
    insD (N + 1) (lamD (N + 2)) < insD N (lamD (N + 1)) := by
  have hembLe : phiTowerEP.embLe (Nat.le_succ N) (lamD (N + 1))
      = (iter N).emb (lamD (N + 1)) := by
    rw [EpPairTower.embLe_succ (T := phiTowerEP) (le_refl N) (Nat.le_succ N) (lamD (N + 1)),
      EpPairTower.embLe_self (T := phiTowerEP) (le_refl N) (lamD (N + 1))]
    rfl
  have hemb : insD (N + 1) ((iter N).emb (lamD (N + 1))) = insD N (lamD (N + 1)) := by
    show phiTowerEP.ins (N + 1) ((iter N).emb (lamD (N + 1))) = phiTowerEP.ins N (lamD (N + 1))
    rw [← hembLe]
    exact EpPairTower.ins_embLe (T := phiTowerEP) (Nat.le_succ N) (lamD (N + 1))
  have hne : (iter N).emb (lamD (N + 1)) ≠ (⊥ : D (N + 2)) := by
    intro hc
    refine lamD_ne_bot (N + 1) ?_
    have h1 : (iter N).emb (lamD (N + 1)) = (iter N).emb ⊥ := by rw [hc, (iter N).emb_bot]
    have h2 := congrArg (iter N).prj h1
    rwa [(iter N).retraction, (iter N).retraction] at h2
  refine lt_of_le_of_ne ?_ ?_
  · rw [← hemb]
    exact insD_monotone (N + 1) (lamD_le (N + 2) _ hne)
  · intro hc
    rw [← hemb] at hc
    exact emb_lamD_ne N (insD_injective (N + 1) hc).symm

/-- **`B` has no atoms.**  Every non-`⊥` element strictly dominates a non-`⊥`
element, so the atom of a slice never reaches the bilimit. -/
theorem exists_lt_lt_of_ne_bot {z : B} (hz : z ≠ ⊥) :
    ∃ w : B, (⊥ : B) < w ∧ w < z := by
  obtain ⟨N, hN⟩ := exists_ne_bot_component hz
  refine ⟨insD (N + 1) (lamD (N + 2)), ?_, ?_⟩
  · refine lt_of_le_of_ne bot_le ?_
    intro hc
    refine lamD_ne_bot (N + 2) (insD_injective (N + 1) ?_)
    rw [insD_bot (N + 1)]
    exact hc.symm
  · refine lt_of_lt_of_le (stage_atom_lt N) ?_
    refine le_trans (insD_monotone N (lamD_le (N + 1) _ hN)) ?_
    exact EpPairTower.ins_le_self (T := phiTowerEP) z N

theorem no_isAtom (a : B) : ¬ IsAtom a := by
  intro h
  obtain ⟨w, hw1, hw2⟩ := exists_lt_lt_of_ne_bot h.1
  exact (ne_of_gt hw1) (h.2 w hw2)

end AtomlessBilimit
