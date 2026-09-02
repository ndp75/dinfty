import Dinfty.HornBConjugation

open GluingTowerLibrary SierpinskiApplication

/-!
# `Φ`'s morphism action under the `const_L` normalization

`Meta/Finding - PsiIso tower mismatch (2026-08-26).md`, Updates 22–24.

The gluing functor `Φ(P) = GlueCar(P, m)` never had its action on *morphisms*
in Lean. `liftGen` was the attempt under the `m = id` convention and it failed:
conjugation is not `id`-exact, and the `⊔ id` / `⊔ ⊤` repair destroys
join-preservation (Finding Updates 2–3).

Under the normalization the vault actually uses — `m` a **marked point that a
tripointed map hits exactly** — the action is unproblematic. This file defines
it and proves it well-defined and monotone, from exactly three hypotheses on
`g`:

  `g ⊥ = ⊥`,  `g m = m'`,  `g ⊤ = ⊤`   (tripointedness)

plus injectivity of `g` (automatic for an ep-pair embedding, which is
order-reflecting). Nothing else: no distributivity, no join-preservation, no
finiteness beyond what `GlueCar` already assumes.

`glueMap_bot` / `glueMap_mid` / `glueMap_top` then say `Φ(g)` is *itself*
tripointed — which is the induction step

  `ι` tripointed ⟹ `conj ι p` tripointed (`HornB.conj_tripointed`)
                 ⟹ `Φ (conj ι p)` tripointed (here)

that carries tripointedness up the whole F-tower from a tripointed `ι₀`. This
was ingredient 4(c) of Claim 3(b)'s dependency chain (Update 23), previously
recorded as "definitional but unformalized".
-/

namespace NormalizedGlueMap

universe u

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

/-- The tagwise action on the raw three-copy base: apply `g` inside each copy,
leaving the tag alone. -/
def baseMap (g : P →o P') : GlueBase P → GlueBase P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (g x))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

section Reflect

variable (g : P →o P')

/-- `g a = ⊥ ↔ a = ⊥`, from `⊥`-exactness and injectivity. -/
theorem map_eq_bot (hginj : Function.Injective g) (hbot : g ⊥ = (⊥ : P')) (a : P) :
    g a = (⊥ : P') ↔ a = (⊥ : P) :=
  ⟨fun h => hginj (h.trans hbot.symm), fun h => h ▸ hbot⟩

/-- `g a = ⊤ ↔ a = ⊤`, from `⊤`-exactness and injectivity. -/
theorem map_eq_top (hginj : Function.Injective g) (htop : g ⊤ = (⊤ : P')) (a : P) :
    g a = (⊤ : P') ↔ a = (⊤ : P) :=
  ⟨fun h => hginj (h.trans htop.symm), fun h => h ▸ htop⟩

/-- `g a = m' ↔ a = m`, from marked-point exactness and injectivity. -/
theorem map_eq_mid (m : P) (m' : P') (hginj : Function.Injective g) (hmid : g m = m')
    (a : P) : g a = m' ↔ a = m :=
  ⟨fun h => hginj (h.trans hmid.symm), fun h => h ▸ hmid⟩

end Reflect

section Tripointed

variable (g : P →o P') (m : P) (m' : P')

/-- **The well-definedness lemma.** The tagwise action commutes with `canon`,
i.e. it respects all three glue identifications, exactly when `g` is
tripointed. -/
theorem canon_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueBase P) :
    canon m' (baseMap g x) = baseMap g (canon m x) := by
  have hm0' : m' ≠ (⊥ : P') := fun h => hm0 (hginj (hmid.trans (h.trans hbot.symm)))
  cases x with
  | inl a => rfl
  | inr y =>
    cases y with
    | inl a =>
      by_cases ha : a = (⊥ : P)
      · simp [baseMap, canon, ha, hbot, hmid]
      · simp [baseMap, canon, ha, (map_eq_bot g hginj hbot a).not.mpr ha]
    | inr a =>
      by_cases ha : a = (⊥ : P)
      · simp [baseMap, canon, ha, hbot, htop]
      · by_cases ham : a = m
        · simp [baseMap, canon, ham, hmid, htop, hm0, hm0',
            (map_eq_bot g hginj hbot a).not.mpr ha]
        · simp [baseMap, canon, ha, ham,
            (map_eq_bot g hginj hbot a).not.mpr ha,
            (map_eq_mid g m m' hginj hmid a).not.mpr ham]

/-- The tagwise action sends each point's occurrence list onto the image
point's occurrence list, exactly. -/
theorem occs_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) (x : GlueBase P) :
    (occs m x).map (baseMap g) = occs m' (baseMap g x) := by
  have hmt' : m' ≠ (⊤ : P') := fun h => hmt (hginj (hmid.trans (h.trans htop.symm)))
  have hb := map_eq_bot g hginj hbot
  have ht := map_eq_top g hginj htop
  have hm := map_eq_mid g m m' hginj hmid
  cases x with
  | inl a =>
    by_cases ham : a = m
    · simp [baseMap, occs, ham, hmid, hbot]
    · by_cases hat : a = (⊤ : P)
      · have : g a ≠ m' := fun h => hmt' (by rw [← h, hat, htop])
        simp [baseMap, occs, hat, htop, hbot, this, Ne.symm hmt, Ne.symm hmt']
      · simp [baseMap, occs, ham, hat, (hm a).not.mpr ham, (ht a).not.mpr hat]
  | inr y =>
    cases y with
    | inl a =>
      by_cases hat : a = (⊤ : P)
      · simp [baseMap, occs, hat, htop, hmid]
      · simp [baseMap, occs, hat, (ht a).not.mpr hat]
    | inr a => simp [baseMap, occs]

/-- The tagwise action preserves the raw comparison rule. -/
theorem rawRule_baseMap (hmid : g m = m') {u v : GlueBase P}
    (h : rawRule m u v) : rawRule m' (baseMap g u) (baseMap g v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact g.monotone h
    | inr w =>
      cases w with
      | inl b => exact hmid ▸ g.monotone h
      | inr b => trivial
  | inr u' =>
    cases u' with
    | inl a =>
      cases v with
      | inl b => exact h.elim
      | inr w =>
        cases w with
        | inl b => exact g.monotone h
        | inr b => exact hmid ▸ g.monotone h
    | inr a =>
      cases v with
      | inl b => exact h.elim
      | inr w =>
        cases w with
        | inl b => exact h.elim
        | inr b => exact g.monotone h

/-- **Monotonicity**, at the level of the raw glued order `leGlue`. -/
theorem leGlue_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) {x y : GlueBase P} (h : leGlue m x y) :
    leGlue m' (baseMap g x) (baseMap g y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  refine ⟨baseMap g u, ?_, baseMap g v, ?_, rawRule_baseMap g m m' hmid huv⟩
  · rw [← occs_baseMap g m m' hginj hbot hmid htop hmt]
    exact List.mem_map_of_mem hu
  · rw [← occs_baseMap g m m' hginj hbot hmid htop hmt]
    exact List.mem_map_of_mem hv

/-- **`Φ` on morphisms.**  The tagwise action, transported to the glued
carriers.  Well-defined by `canon_baseMap`. -/
def glueMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueCar (P := P) m) : GlueCar (P := P') m' :=
  ⟨baseMap g x.val, by
    rw [canon_baseMap g m m' hginj hbot hmid htop hm0, x.property]⟩

@[simp] theorem glueMap_val (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueCar (P := P) m) :
    (glueMap g m m' hginj hbot hmid htop hm0 x).val = baseMap g x.val := rfl

/-- `Φ(g)` is monotone. -/
theorem glueMap_monotone (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) (hm0 : m ≠ (⊥ : P))
    {x y : GlueCar (P := P) m} (h : leGlue m x.val y.val) :
    leGlue m' (glueMap g m m' hginj hbot hmid htop hm0 x).val
              (glueMap g m m' hginj hbot hmid htop hm0 y).val :=
  leGlue_baseMap g m m' hginj hbot hmid htop hmt h

section TripointedImage

variable (hginj : Function.Injective g)
  (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
  (hm0 : m ≠ (⊥ : P))

/-- `Φ(g)` sends `Φ(P)`'s bottom corner `tag_A ⊥` to `Φ(P')`'s. -/
theorem glueMap_bot :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelT m, rfl⟩ = ⟨skelT m', rfl⟩ := by
  apply Subtype.ext; simp [baseMap, skelT, hbot]

/-- `Φ(g)` sends `tag_B m` to `tag_B m'`.
**This is the step the `m = id` convention cannot supply** — it is exactly
`g m = m'`, which conjugation gives for free when `m` is a constant
(`HornB.conj_constHom`) and cannot give when `m` is `id`
(`HornB.conj_id_eq_id_iff`).

Since 2026-08-27 the tower's middle basepoint is `tag_A`, not `tag_B`, so the
tower's own tripointedness step is `glueMap_midA` below.  This theorem stays:
it is true, it is what `Φ_tri_v2`'s Ratnayake convention needs, and `baseMap`
is tagwise so both hold from the same hypothesis. -/
theorem glueMap_mid (hmb : canon m (skelL m) = skelL m)
    (hmb' : canon m' (skelL m') = skelL m') :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelL m, hmb⟩ = ⟨skelL m', hmb'⟩ := by
  apply Subtype.ext; simp [baseMap, skelL, hmid]

/-- **`tag_A m` is Ratnayake's `a.L ~ b.T` seam.**  `canon`'s first rule *is*
the source construction's glue relation identifying copy `a`'s `L`-corner with
copy `b`'s `T`-corner, so the tower's `tag_A` basepoint is not a point outside
the paper's scheme -- it is the seam between two of its copies.  This is why
moving from `tag_B` to `tag_A` is a change of *which named glue point* is
designated, not an abandonment of the construction's basepoint discipline. -/
theorem glueA_self_eq_glue_aL_bT (m : P) (hm0 : m ≠ (⊥ : P)) (hbt : (⊥ : P) ≠ ⊤) :
    glueA m m = incl m hm0 hbt (Sum.inr (Sum.inl (⊥ : P))) := by
  apply Subtype.ext
  show (Sum.inl m : GlueBase P) = canon m (Sum.inr (Sum.inl (⊥ : P)))
  rw [canon, if_pos rfl]

/-- `Φ(g)` sends `Φ(P)`'s top corner `tag_C ⊤` to `Φ(P')`'s. -/
theorem glueMap_top (hrt : canon m (skelR m) = skelR m)
    (hrt' : canon m' (skelR m') = skelR m') :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelR m, hrt⟩ = ⟨skelR m', hrt'⟩ := by
  apply Subtype.ext; simp [baseMap, skelR, htop]

/-- **`Φ(g)` sends `tag_A m` to `tag_A m'`** -- the tower's tripointedness step
under the `tag_A` convention.  Same hypothesis `hmid : g m = m'` as
`glueMap_mid`, and, unlike it, no `canon`-fixedness side-conditions: copy `A`
is unconditionally canonical. -/
theorem glueMap_midA :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelG1 m, rfl⟩ = ⟨skelG1 m', rfl⟩ := by
  apply Subtype.ext
  simp [baseMap, skelG1, hmid]

end TripointedImage

end Tripointed

/-! ## The normalized tower

`towerLevelSucc` (`SierpinskiApplication.lean`) glues at `m = id`. Obstruction
(T) (`Dinfty/TripointedObstruction.lean`) says that choice admits no tagwise
morphism action at all. The normalization is to glue at a marked point that is
a **constant** — `const_L`, the constant at the previous level's own middle
basepoint — which is what `Φ_tri_v2` does and what Claim 3(c)'s internal-IFS
route requires (all three glue points must lie in `η`'s image).

`TriLevel` carries that middle basepoint as data, so the marked point at each
step is `constHom prev.mid` and the next middle basepoint is `tag_A` of it.
Built in parallel with the live `TowerLevel` rather than replacing it, so the
existing spine is untouched.

**Basepoint convention: `tag_A`, changed from `tag_B` on 2026-08-27 (Noah).**
`Phi_tri_v2` takes `L' = b.L = tag_B (L_H)` from Ratnayake et al. 2021 SS2.2.
That choice is incompatible with the ep-pair layer: the reflection proof's
downward obligation `hdown` (`mid <= y -> mu <= iota y`) is satisfiable ONLY by
copy-`A` points, because copy `B` is never `<=` copy `A`
(`GlueAAGenReflectM.tagA_of_hdown_at_mid`; the old convention's failure is
recorded in `Dinfty/BasepointInvariant.lean`, which superseded the former
`NextBasepointConflict.lean`).

The change is smaller than it looks, and is not a departure from the source
construction: `canon`'s first rule IS Ratnayake's glue relation `a.L ~ b.T`, so
`tag_A m` is exactly the seam where copy `a`'s `L`-corner meets copy `b`'s
`T`-corner (`glueA_self_eq_glue_aL_bT` below).  Both candidates are points the
source gluing already names -- `b.L` and `a.L = b.T` -- and only the latter
supports the ep-pair route (`Dinfty/BasepointInvariant.lean`).

Tag-`A` is also cheaper everywhere tag-`B` was paid for: copy `A` is
unconditionally `canon`-fixed, so `glueA m m` needs no `!= bot` side-condition
to be a `GlueCar` point, and `glueMap_midA` needs none of `glueMap_mid`'s.

NOT re-checked under the new convention, and NOT to be inferred from the fact
that the mechanism generalises: Claim 3(b) ingredient 4 (`iota_0`'s
verification script sends `L |-> tag_B (const_L)`), Claim 3(c)'s internal-IFS
route, and any paper-side text quoting `L_(Phi H) = tag_B (L_H)`.
-/


/-! ## Theorem B's up-transfer survives the normalization

Update 25 flagged `D_deg_g2_ne_deg_l` as the migration's one blocker, on the
grounds that its down-cover-degree separation of the skeleton points collapses
when `m` is a constant. **That lemma has no consumers** — checked across every
live module — so it was never on the critical path.

The path that *is* load-bearing is `glue_rigid_of_incomparable`, and it is
already parametric in the marked point: it needs only `m ≠ ⊥`, `m ≠ ⊤`,
`⊥ ≠ ⊤`, rigidity of the base, and **one element incomparable to `m`**. Under
the `id` convention that witness is a constant `constHom v`; under the
normalization constants no longer work (two constants are comparable whenever
their values are, and `D 0` is a chain) — but `OrderHom.id` does, for free, at
every level. The two conventions simply swap roles.
-/

namespace UpTransfer

variable {X : Type u} [Lattice X] [BoundedOrder X]

/-- `id ≰ constHom mid` whenever `mid ≠ ⊤` — evaluate at `⊤`. -/
theorem id_not_le_constHom (mid : X) (hmt : mid ≠ (⊤ : X)) :
    ¬ (OrderHom.id : EndP X) ≤ constHom mid := fun h =>
  hmt (le_antisymm le_top (h ⊤))

/-- `constHom mid ≰ id` whenever `mid ≠ ⊥` — evaluate at `⊥`. -/
theorem constHom_not_le_id (mid : X) (hm0 : mid ≠ (⊥ : X)) :
    ¬ (constHom mid : EndP X) ≤ (OrderHom.id : EndP X) := fun h =>
  hm0 (le_bot_iff.mp (h ⊥))

end UpTransfer

open scoped Classical in
/-- **Theorem UP-TRANSFER, normalized.**  Rigidity of `EndP X` lifts to
rigidity of the *normalized* glued level `GlueCar (EndP X) (constHom mid)`,
for any `mid` strictly between `⊥` and `⊤`.

Same statement and same proof route as `D_up_transfer`
(`SierpinskiApplication.lean`), with the marked point `id` replaced by
`constHom mid` and the incomparability witness `constHom v` replaced by
`OrderHom.id`.  So Theorem B's up-transfer step costs nothing to migrate. -/
theorem tri_up_transfer {X : Type u} [DecidableEq X] [Lattice X] [BoundedOrder X]
    [Fintype X] (mid : X) (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X))
    (hbt : (⊥ : X) ≠ (⊤ : X))
    (hAut : Subsingleton (EndP X ≃o EndP X)) :
    Subsingleton (GlueCar (P := EndP X) (constHom mid)
      ≃o GlueCar (P := EndP X) (constHom mid)) := by
  have hMb : (constHom mid : EndP X) ≠ ⊥ := by
    intro h
    have hb : (⊥ : EndP X) = constHom (⊥ : X) := by ext x; rfl
    exact hm0 (constHom_injective (h.trans hb))
  have hMt : (constHom mid : EndP X) ≠ ⊤ := by
    intro h
    exact hmt (constHom_injective (h.trans endP_top_eq_constHom_top))
  exact glue_rigid_of_incomparable (P := EndP X) (constHom mid) hMb hMt
    (endP_bot_ne_top hbt) hAut OrderHom.id
    (UpTransfer.id_not_le_constHom mid hmt) (UpTransfer.constHom_not_le_id mid hm0)


open scoped Classical in
/-- **The normalized level 1 is rigid** — the analogue of `D1_rigid`, from the
same base fact `H0_rigid` through `tri_up_transfer`.  Confirms in Lean what
`_archive/check_normalized_tower_rigidity_and_invariant.py` found by directly
computing the 27-element automorphism group. -/
theorem tri_level1_rigid :
    Subsingleton (GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))
      ≃o GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))) :=
  tri_up_transfer (1 : Fin 3) (by decide) (by decide) (by decide) H0_rigid


/-! ## `D_down_transfer`'s inputs, normalized

`D_down_transfer`'s *statement* mentions no marked point, so it is
convention-agnostic by construction. What its proof consumes are level-`k`
facts: `realUniqueAtomCoatom`, `D_J_connected`, `D_top_hasUniqueDownCover`
(and `D_has_interior_point`, used by the first). This section re-establishes
each for a constant marked point.

Every one of them turns out to go through a library lemma that already takes
the marked point as a parameter, so the only genuinely new content is
`coatomOf_endP_ne_constHom` — and that is *easier* for a constant marked point
than for `id`, which needed a case split on whether `coatomOf X = ⊥`.
-/

namespace DownInputs

variable {X : Type u} [Lattice X] [BoundedOrder X]

/-- `constHom mid ≠ ⊥` in `EndP X`, from `mid ≠ ⊥`. -/
theorem constHom_ne_bot (mid : X) (hm0 : mid ≠ (⊥ : X)) :
    (constHom mid : EndP X) ≠ ⊥ := by
  intro h
  have hb : (⊥ : EndP X) = constHom (⊥ : X) := by ext x; rfl
  exact hm0 (constHom_injective (h.trans hb))

/-- `constHom mid ≠ ⊤` in `EndP X`, from `mid ≠ ⊤`. -/
theorem constHom_ne_top (mid : X) (hmt : mid ≠ (⊤ : X)) :
    (constHom mid : EndP X) ≠ ⊤ := fun h =>
  hmt (constHom_injective (h.trans endP_top_eq_constHom_top))

/-- `⊥ ≠ coatomOf (EndP X)` — the first hypothesis of `glueUniqueAtomCoatom`.
No marked point involved, so this is the existing argument verbatim. -/
theorem bot_ne_coatomOf_endP [UniqueAtomCoatom X] (hbt : (⊥ : X) ≠ ⊤) :
    (⊥ : EndP X) ≠ coatomOf (EndP X) := by
  rw [coatomOf_endP_eq_cospikeHom]
  intro hc
  have h1 : (⊥ : EndP X) (⊤ : X) = cospikeHom (coatomOf X) (⊤ : X) :=
    congrArg (· (⊤ : X)) hc
  rw [endPBot_apply, cospikeHom_apply_of_ne _ hbt.symm] at h1
  exact hbt h1

/-- **The one genuinely new input**: a *constant* marked point is never the
coatom of `EndP X`.  `coatomOf (EndP X) = cospikeHom (coatomOf X)` sends every
`x ≠ ⊥` to `⊤`, while `constHom mid` sends everything to `mid ≠ ⊤`; evaluating
at `⊤` separates them in one step.

Compare the `m = id` version (`realUniqueAtomCoatom`, `SierpinskiApplication`),
which needs a case split on whether `coatomOf X = ⊥` and an interior point of
`X` to handle one branch. The normalization makes this input *easier*, not
harder. -/
theorem coatomOf_endP_ne_constHom [UniqueAtomCoatom X] (mid : X)
    (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    coatomOf (EndP X) ≠ constHom mid := by
  rw [coatomOf_endP_eq_cospikeHom]
  intro hc
  have h1 : cospikeHom (coatomOf X) (⊤ : X) = (constHom mid : EndP X) (⊤ : X) :=
    congrArg (· (⊤ : X)) hc
  rw [cospikeHom_apply_of_ne _ hbt.symm, constHom_apply] at h1
  exact hmt h1.symm

end DownInputs

open scoped Classical in
/-- **Lemma UAC, normalized** — the successor step of `realUniqueAtomCoatom`
with a constant marked point. -/
noncomputable def tri_uniqueAtomCoatom {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := DownInputs.constHom_ne_bot mid hm0
    @UniqueAtomCoatom (GlueCar (P := EndP X) (constHom mid))
      (glueLattice (constHom mid) (DownInputs.constHom_ne_bot mid hm0)
        (DownInputs.constHom_ne_top mid hmt) (endP_bot_ne_top hbt))
      (glueBoundedOrder (constHom mid) (DownInputs.constHom_ne_bot mid hm0)
        (DownInputs.constHom_ne_top mid hmt) (endP_bot_ne_top hbt)) :=
  glueUniqueAtomCoatom (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
    (DownInputs.bot_ne_coatomOf_endP hbt)
    (DownInputs.coatomOf_endP_ne_constHom mid hmt hbt)

open scoped Classical in
/-- **Theorem J-CONN, normalized** — the successor step of `D_J_connected`.
`hasse_hasUniqueDownCover_glueCar_connected` already takes the marked point as
a parameter, so this costs nothing beyond `tri_uniqueAtomCoatom`. -/
theorem tri_J_connected {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueCarPartialOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    (Graph.Hasse {x : GlueCar (P := EndP X) (constHom mid) //
      HasUniqueDownCover x}).Connected :=
  hasse_hasUniqueDownCover_glueCar_connected (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)


section TriCovers

variable {X : Type u} [DecidableEq X] [Lattice X] [BoundedOrder X] [Fintype X]
  [UniqueAtomCoatom X] (mid : X) (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X))
  (hbt : (⊥ : X) ≠ ⊤)

/- `tri_top_hasUniqueDownCover` / `tri_bot_hasUniqueUpCover` are stated after
this section (Update 28).  Update 27 recorded them as attempted-and-abandoned
on instance alignment; the fix is simply to supply `glueLattice` /
`glueBoundedOrder` by `letI` in the *statement* as well as the proof, so that
the `top`/`bot` in the statement and the ones `hasUniqueDownCover_top` builds
from `tri_uniqueAtomCoatom` are the same instances.  Nothing mathematical
changed. -/

open scoped Classical in
/-- **`D_has_interior_point`, normalized**, and simpler: `tag_A` of the marked
point is interior at every level.  `glueA m ⊥ = ⊥` gives the lower half from
`m ≠ ⊥`, and `glueA_ne_top` (copy `A` is `Sum.inl`-shaped, `⊤` is not) gives
the upper half unconditionally. -/
theorem tri_has_interior_point :
    letI := glueCarPartialOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    glueA (P := EndP X) (constHom mid) (constHom mid) ≠ ⊥ ∧
    glueA (P := EndP X) (constHom mid) (constHom mid) ≠ ⊤ := by
  letI := glueCarPartialOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  refine ⟨fun h => DownInputs.constHom_ne_bot mid hm0 (glueA_injective _ h), ?_⟩
  exact glueA_ne_top (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt) (constHom mid)

end TriCovers

/-! ### The two cover corollaries, landed

Update 27 attempted `tri_top_hasUniqueDownCover` / `tri_bot_hasUniqueUpCover`
and recorded them as unproved: stated standalone, the `top`/`bot` elaborated
through instances that did not line up with the ones `hasUniqueDownCover_top`
builds from its `UniqueAtomCoatom` argument.  The fix is to `letI` the glue
`Lattice`/`BoundedOrder` in the *statement* as well as in the proof, so both
sides speak of the same instances.  Purely plumbing, as Update 27 said — but
now discharged rather than deferred.
-/

open scoped Classical in
/-- **`D_top_hasUniqueDownCover`, normalized.** -/
theorem tri_top_hasUniqueDownCover {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    HasUniqueDownCover (⊤ : GlueCar (P := EndP X) (constHom mid)) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  exact hasUniqueDownCover_top

open scoped Classical in
/-- **`D_bot_hasUniqueUpCover`, normalized** — the dual, same recipe. -/
theorem tri_bot_hasUniqueUpCover {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    HasUniqueUpCover (⊥ : GlueCar (P := EndP X) (constHom mid)) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  exact hasUniqueUpCover_bot


/-! ## `D_down_transfer` itself, level-parametric

`D_down_transfer`s statement mentions no marked point, and its *proof*
mentions the tower only through the three level-`k` facts re-established
above.  So the honest port is not a copy with `constHom mid` substituted in --
there is nothing to substitute -- but a restatement over an arbitrary finite
lattice carrying those facts as hypotheses.  `general_down_transfer` below is
`D_down_transfer`s proof verbatim, with `D k` replaced by the parameter `X`
and the three tower lookups (`realUniqueAtomCoatom k`,
`D_top_hasUniqueDownCover k`, `D_J_connected k`) turned into arguments.

Every step it uses -- `jh_product_order_level_full`, `jiEquiv`, `tauHat` and
its `_injective`/`_le_iff`/`_eq_of_joinIrred` lemmas,
`orderIso_eq_of_joinIrred_eq` -- is already stated for an arbitrary `P` in
`GluingTowerLibrary`, so the generalization costs nothing.

`D_down_transfer` is then literally this theorem applied at `X := D k`, and
the normalized tower gets its down-transfer step by applying it at the
normalized levels instead: the inputs are `tri_uniqueAtomCoatom`,
`tri_J_connected`, and the top-cover fact (see the `TriCovers` note above for
why the standalone form of the last one is not stated here).
-/

open scoped Classical in
/-- **Theorem DOWN-TRANSFER, level-parametric.**  For any finite lattice `X`
with a unique atom and coatom, whose top has a unique down-cover and whose
join-irreducible Hasse graph is connected: rigidity of `X` lifts to rigidity
of `EndP X`.

This is `D_down_transfer` (`SierpinskiApplication.lean`) with the tower
specialization removed.  It mentions no marked point, so it serves the `id`
tower and the normalized tower alike. -/
theorem general_down_transfer {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X]
    (hTop : HasUniqueDownCover (⊤ : X))
    (hJconn : (Graph.Hasse {x : X // JoinIrred X x}).Connected) :
    Subsingleton (X ≃o X) → Subsingleton (EndP X ≃o EndP X) := by
  intro hDk
  haveI : Nonempty {x : X // JoinIrred X x} :=
    ⟨⟨⊤, joinIrred_of_hasUniqueDownCover hTop⟩⟩
  suffices hall : ∀ φ₀ : EndP (X) ≃o EndP (X), φ₀ = OrderIso.refl _ by
    exact ⟨fun a b => (hall a).trans (hall b).symm⟩
  intro φ₀
  set φ : {f : EndP (X) // JoinIrred (EndP (X)) f} ≃
      {f : EndP (X) // JoinIrred (EndP (X)) f} :=
    { toFun := fun x => ⟨φ₀ x.1, joinIrred_orderIso φ₀ x.2⟩
      invFun := fun x => ⟨φ₀.symm x.1, joinIrred_orderIso φ₀.symm x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp } with hφdef
  have hφval : ∀ x : {f : EndP (X) // JoinIrred (EndP (X)) f}, (φ x).1 = φ₀ x.1 := fun x => rfl
  have hφord : ∀ v w, v ≤ w ↔ φ v ≤ φ w := by
    intro v w
    show (v : EndP (X)) ≤ w ↔ φ₀ v.1 ≤ φ₀ w.1
    exact φ₀.le_iff_le.symm
  let Φ : {f : EndP (X) // JoinIrred (EndP (X)) f} ≃o
      {f : EndP (X) // JoinIrred (EndP (X)) f} :=
    { toEquiv := φ, map_rel_iff' := fun {v w} => (hφord v w).symm }
  have hφadj : ∀ v w, (Graph.Hasse {f : EndP (X) // JoinIrred (EndP (X)) f}).adj v w ↔
      (Graph.Hasse {f : EndP (X) // JoinIrred (EndP (X)) f}).adj (φ v) (φ w) := by
    intro v w
    constructor
    · rintro (hc | hc)
      · exact Or.inl (covers_orderIso Φ hc)
      · exact Or.inr (covers_orderIso Φ hc)
    · rintro (hc | hc)
      · have hc' : Covers (Φ v) (Φ w) := hc
        have h2 := covers_orderIso Φ.symm hc'
        rw [Φ.symm_apply_apply, Φ.symm_apply_apply] at h2
        exact Or.inl h2
      · have hc' : Covers (Φ w) (Φ v) := hc
        have h2 := covers_orderIso Φ.symm hc'
        rw [Φ.symm_apply_apply, Φ.symm_apply_apply] at h2
        exact Or.inr h2
  obtain ⟨γA, γB, hγA_ord, hγB_ord, hdecomp⟩ := jh_product_order_level_full hJconn φ hφadj hφord
  have ΓA_map : ∀ a b : X, a ≤ b ↔ γA a ≤ γA b := hγA_ord
  let ΓA : X ≃o X := { toEquiv := γA, map_rel_iff' := fun {a b} => (ΓA_map a b).symm }
  have hΓA_id : ΓA = OrderIso.refl (X) := Subsingleton.elim _ _
  have hγA_id : ∀ q : X, γA q = q := fun q => DFunLike.congr_fun hΓA_id q
  have hvert : ∀ (x : X) (hx : JoinIrred (X) x) (q : X),
      φ₀ (stepMap x q) = stepMap (γB ⟨x, hx⟩).1 q := by
    intro x hx q
    have hd := hdecomp (q, ⟨x, hx⟩)
    have := congrArg Subtype.val hd
    simp only [hφdef, Equiv.coe_fn_mk, jiEquiv, Equiv.coe_fn_mk] at this
    rw [hγA_id q] at this
    exact this
  have hγB_ord' : ∀ b1 b2 : {x : X // JoinIrred (X) x}, b1 ≤ b2 ↔ γB b1 ≤ γB b2 := hγB_ord
  have ΓB_map : ∀ v v' : X, v ≤ v' ↔ tauHat γB v ≤ tauHat γB v' :=
    fun v v' => (tauHat_le_iff γB φ₀ hvert v v').symm
  have hΓB_bij : Function.Bijective (tauHat γB) :=
    Finite.injective_iff_bijective.mp (tauHat_injective γB φ₀ hvert)
  let ΓB : X ≃o X :=
    { toEquiv := Equiv.ofBijective (tauHat γB) hΓB_bij,
      map_rel_iff' := fun {a b} => (ΓB_map a b).symm }
  have hΓB_id : ΓB = OrderIso.refl (X) := Subsingleton.elim _ _
  have hγB_id : ∀ v : X, tauHat γB v = v := fun v => DFunLike.congr_fun hΓB_id v
  have hγB_fix : ∀ x : {x : X // JoinIrred (X) x}, γB x = x := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have := hγB_id x
    rw [tauHat_eq_of_joinIrred γB hγB_ord' x hx] at this
    exact this
  have hφ_fix : ∀ f : {f : EndP (X) // JoinIrred (EndP (X)) f}, φ₀ f.1 = f.1 := by
    intro f
    set q := (jiEquiv.symm f).1 with hqdef
    set x := (jiEquiv.symm f).2 with hxdef
    have hf : jiEquiv (q, x) = f := by rw [hqdef, hxdef]; exact jiEquiv.apply_symm_apply f
    have hd := hdecomp (q, x)
    rw [hf] at hd
    have hval := congrArg Subtype.val hd
    simp only [hφdef, Equiv.coe_fn_mk] at hval
    rw [hval, hγA_id, hγB_fix, hf]
  apply orderIso_eq_of_joinIrred_eq
  intro q hq
  show φ₀ q = q
  exact hφ_fix ⟨q, hq⟩


open scoped Classical in
/-- **`general_down_transfer` recovers `D_down_transfer` exactly.**  Kept as a
check that the generalization is faithful: the original theorem is this one
applied at `X := D k` with the three tower facts supplied. -/
theorem general_down_transfer_recovers_D_down_transfer (k : ℕ) :
    Subsingleton (D k ≃o D k) → Subsingleton (EndP (D k) ≃o EndP (D k)) := by
  letI := realUniqueAtomCoatom k
  exact general_down_transfer (D_top_hasUniqueDownCover k) (D_J_connected k)

open scoped Classical in
/-- **Theorem DOWN-TRANSFER, normalized.**  The successor step of
`D_down_transfer` for a constant marked point: rigidity of the glued level
`GlueCar (EndP X) (constHom mid)` lifts to rigidity of its own `EndP`.

Assembled from `general_down_transfer` and the normalized inputs —
`tri_uniqueAtomCoatom`, `tri_top_hasUniqueDownCover`, `tri_J_connected` (fed
through `connected_of_pointwise_iff`, exactly as `D_J_connected`'s successor
case does).  With `tri_up_transfer` this completes both transfer steps of
Theorem B for the normalized tower. -/
theorem tri_down_transfer {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    Subsingleton (GlueCar (P := EndP X) (constHom mid) ≃o GlueCar (P := EndP X) (constHom mid)) →
      Subsingleton (EndP (GlueCar (P := EndP X) (constHom mid))
        ≃o EndP (GlueCar (P := EndP X) (constHom mid))) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  refine general_down_transfer hasUniqueDownCover_top ?_
  exact connected_of_pointwise_iff HasUniqueDownCover
    (JoinIrred (GlueCar (P := EndP X) (constHom mid)))
    hasUniqueDownCover_iff_joinIrred (tri_J_connected (X := X) mid hm0 hmt hbt)

namespace NormalizedTower

/-- A tower level, carrying its **middle basepoint** as data alongside the
order structure — the tripointed `(⊥, mid, ⊤)` triple. -/
structure TriLevel : Type (u + 1) where
  carrier : Type u
  dec : DecidableEq carrier
  lat : Lattice carrier
  bdd : BoundedOrder carrier
  fin : Fintype carrier
  nontriv : Nontrivial carrier
  /-- the middle basepoint `L`, with its two nondegeneracy facts -/
  mid : carrier
  mid_ne_bot : letI := lat; letI := bdd; mid ≠ (⊥ : carrier)
  mid_ne_top : letI := lat; letI := bdd; mid ≠ (⊤ : carrier)

/-- Base level: the 3-chain `Fin 3`, middle basepoint `1`. -/
def triLevel0 : TriLevel where
  carrier := Fin 3
  dec := inferInstance
  lat := inferInstance
  bdd := inferInstance
  fin := inferInstance
  nontriv := ⟨0, 1, by decide⟩
  mid := 1
  mid_ne_bot := by decide
  mid_ne_top := by decide

section Succ

variable (prev : TriLevel)

/-- The marked point of the successor step: the **constant** at `prev`'s
middle basepoint. This is the normalization. -/
def markedPoint : letI := prev.lat; letI := prev.bdd; EndP prev.carrier :=
  letI := prev.lat; letI := prev.bdd; constHom prev.mid

theorem markedPoint_ne_bot :
    letI := prev.lat; letI := prev.bdd
    markedPoint prev ≠ (⊥ : EndP prev.carrier) := by
  letI := prev.lat; letI := prev.bdd
  intro h
  have hb : (⊥ : EndP prev.carrier) = constHom (⊥ : prev.carrier) := by ext x; rfl
  exact prev.mid_ne_bot (constHom_injective (h.trans hb))

theorem markedPoint_ne_top :
    letI := prev.lat; letI := prev.bdd
    markedPoint prev ≠ (⊤ : EndP prev.carrier) := by
  letI := prev.lat; letI := prev.bdd
  intro h
  exact prev.mid_ne_top (constHom_injective (h.trans endP_top_eq_constHom_top))

end Succ

open scoped Classical in
/-- **The normalized successor step.**  Glue `EndP prev` at the *constant*
`markedPoint prev = constHom prev.mid`, and take the next middle basepoint to
be `tag_B` of that marked point — the convention `L_(Phi H) = tag_B (L_H)`.

Contrast `towerLevelSucc` (`SierpinskiApplication.lean`), which glues at `id`
and is therefore obstructed by (T). -/
noncomputable def triLevelSucc (prev : TriLevel) : TriLevel :=
  letI := prev.dec
  letI := prev.lat
  letI := prev.bdd
  letI := prev.fin
  letI := prev.nontriv
  have hbtPrev : (⊥ : prev.carrier) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm : markedPoint prev ≠ (⊥ : EndP prev.carrier) := markedPoint_ne_bot prev
  have hmt : markedPoint prev ≠ (⊤ : EndP prev.carrier) := markedPoint_ne_top prev
  have hbt : (⊥ : EndP prev.carrier) ≠ (⊤ : EndP prev.carrier) := endP_bot_ne_top hbtPrev
  { carrier := GlueCar (P := EndP prev.carrier) (markedPoint prev)
    dec := inferInstance
    lat := glueLattice (markedPoint prev) hm hmt hbt
    bdd := glueBoundedOrder (markedPoint prev) hm hmt hbt
    fin := inferInstance
    nontriv := glueCar_nontrivial (markedPoint prev) hm hmt hbt
    mid := glueA (markedPoint prev) (markedPoint prev)
    mid_ne_bot := by
      letI := glueCarPartialOrder (markedPoint prev) hm hmt hbt
      letI := glueBoundedOrder (markedPoint prev) hm hmt hbt
      intro h
      have hb : (⊥ : GlueCar (P := EndP prev.carrier) (markedPoint prev))
          = incl (markedPoint prev) hm hbt (Sum.inl ⊥) := rfl
      rw [hb] at h
      have hv := congrArg Subtype.val h
      simp only [glueA, incl, canon] at hv
      exact hm (Sum.inl.inj hv)
    mid_ne_top := by
      letI := glueCarPartialOrder (markedPoint prev) hm hmt hbt
      letI := glueBoundedOrder (markedPoint prev) hm hmt hbt
      intro h
      have ht : (⊤ : GlueCar (P := EndP prev.carrier) (markedPoint prev))
          = incl (markedPoint prev) hm hbt (Sum.inr (Sum.inr ⊤)) := rfl
      rw [ht] at h
      have hv := congrArg Subtype.val h
      simp only [glueA, incl, canon] at hv
      rw [if_neg (Ne.symm hbt), if_neg (Ne.symm hmt)] at hv
      exact absurd hv (by simp) }

/-- The normalized tower. -/
noncomputable def triLevel : ℕ → TriLevel
  | 0 => triLevel0
  | k + 1 => triLevelSucc (triLevel k)

/-- **The basepoint convention, as a `rfl`-theorem.**  The successor's middle
basepoint is copy-`A`-shaped.  `Dinfty/BasepointInvariant.lean` depends on this
and will stop compiling if the convention is ever moved back. -/
theorem triLevelSucc_mid_val (prev : TriLevel) :
    letI := prev.dec; letI := prev.lat; letI := prev.bdd
    letI := prev.fin; letI := prev.nontriv
    ((triLevelSucc prev).mid : GlueCar (P := EndP prev.carrier) (markedPoint prev)).1
      = Sum.inl (markedPoint prev) := by
  letI := prev.dec; letI := prev.lat; letI := prev.bdd
  letI := prev.fin; letI := prev.nontriv
  rfl

end NormalizedTower

end NormalizedGlueMap
