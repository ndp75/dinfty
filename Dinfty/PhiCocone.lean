import Dinfty.PhiBilimit
import Dinfty.TowerShift
import Dinfty.CanonFixed

open GluingTowerLibrary SierpinskiApplication

/-!
# `Φ` of the colimit cocone — rebuilt on values

§85 wrote this module through `phiFun` and lost ten build cycles to competing
`DecidableEq` instances.  §86 diagnosed it: the carrier is cut out by a
condition that needs no decidability at all (`CanonFixed.Fixed`), so the
instance is an implementation detail of `canonGen`'s `if`s — and `phiFun` takes
*its own* copy of that instance, separately from the one inside its `TriHom`
argument's type, which is what could never be made to agree.

**So do not go through `phiFun`.**  `GlueBaseGen P = P ⊕ P ⊕ P` is instance-free,
and `baseMapGen` between such types is instance-free.  Build the legs as
subtype elements directly — value by `canonGen` at the *target*, proof by
`canonGen_idem` — and every instance in sight is the one the target type
already fixed.  Two `letI`s pin the tower side; dropping `open scoped Classical`
pins the `EndP B` side to the instance `phiB` was defined with.

Everything below is the same mathematics as §85; only the spelling changed.

* `eLeg k = Φ (ins k)` and `pLeg k = Φ (proj k)`, on values.
* `cocone_retraction` / `cocone_deflation` / `cocone_compat` — the three
  algebraic `IsColimitCocone` fields, each from `canonGen_baseMapGen_canon`
  (the descent lemma) plus `baseMapGen_comp` and the corresponding composite
  identity, exactly as in §84's `phiStep`.
* `PhiCoconeIsLUB` / `PhiSupExists` / `PhiProjContinuous` — the analysis, named.
* `theoremA_orderIso` — the assembly.
-/

namespace PhiCocone

-- One candidate per base: `endPDecidableEq` at `EndP (D k)` (which is what
-- `towerLevelSucc` baked into `D (k+1)`), and `PhiBilimit.decEqEndPB` at
-- `EndP B` (which is what `phiB` was defined with).  Erasing Mathlib's
-- competitor leaves no choice to get wrong, and no `Classical` is opened.
-- MERGE THE TWO SPELLINGS.  `D` is a regular `def`, so instance matching does
-- not unfold it, and `endPDecidableEq` — stated for `D k` — fails against a goal
-- presented as `EndP (towerLevel (k+1)).carrier`.  Now that D is reducible at the spine, the two
-- spellings are one; erasing Mathlib's competitor then leaves exactly one
-- candidate per base.  Neither attribute escapes this file, so the spine is
-- untouched.
attribute [-instance] OrderHom.instDecidableEqOfForall

open PhiIterateTower PhiBilimit EpPairTower PhiTriFunctor GenContinuity

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## The tower's cocone, as tripointed morphisms of glue bases

`TriHom` itself mentions no `DecidableEq` — it is `toFun` plus three equations —
so these two are instance-clean. -/

/-- `h ↦ ins k ∘ h ∘ proj k`.  The value is Scott-continuous: `ins k` is (its
domain is a finite level), `h` is (finite domain), and reading off level `k` is
(`phiTowerEP` is a dcpo). -/
noncomputable def insEndUp (k : ℕ) : TriHom (markedPt (k + 1)) markedB where
  toFun :=
    ⟨fun h => ⟨⟨fun y => phiTowerEP.ins k (h (y.1 k)),
          fun _ _ hyy => ins_monotone k (h.monotone (hyy k))⟩,
        by
          have h1 : ScottContinuous (fun y : B => y.1 k) := proj_scottContinuous k
          have h2 : ScottContinuous (fun x : D (k + 1) => h x) :=
            monotone_scottContinuous_of_finite_dom h.monotone
          have h3 : ScottContinuous (fun w : D (k + 1) => phiTowerEP.ins k w) :=
            ins_scottContinuous k
          -- ScottContinuous.comp (hf) (hg) : ScottContinuous (g . f) -- the
          -- RECEIVER is the INNER map.  Inner to outer: proj, then h, then ins.
          have hc := (h1.comp h2).comp h3
          simpa [Function.comp_def] using hc⟩,
      fun _ _ hh => by
        rw [scottEndP_le_def]
        intro y
        exact ins_monotone k (OrderHom.le_def.mp hh (y.1 k))⟩
  map_bot := by
    refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
    show phiTowerEP.ins k ((⊥ : EndP (D (k + 1))) (y.1 k)) = (⊥ : ScottEndP B).1 y
    rw [endPBot_apply]
    exact ins_bot k
  map_mark := by
    refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
    show phiTowerEP.ins k ((markedPt (k + 1)) (y.1 k)) = markedB.1 y
    rw [markedPt_apply]
    exact ins_mid k
  map_top := by
    refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
    show phiTowerEP.ins k ((⊤ : EndP (D (k + 1))) (y.1 k)) = (⊤ : ScottEndP B).1 y
    rw [endPTop_apply]
    exact ins_top k

/-- `H ↦ proj k ∘ H ∘ ins k`.  No continuity obligation: the target level is
finite. -/
noncomputable def projEndDown (k : ℕ) : TriHom markedB (markedPt (k + 1)) where
  toFun :=
    ⟨fun H => ⟨fun x => (H.1 (phiTowerEP.ins k x)).1 k,
        fun _ _ hxx => H.1.monotone (ins_monotone k hxx) k⟩,
      fun _ _ hh => by
        intro x
        exact (scottEndP_le_def.mp hh) (phiTowerEP.ins k x) k⟩
  map_bot := by
    ext x
    show ((⊥ : ScottEndP B).1 (phiTowerEP.ins k x)).1 k = (⊥ : EndP (D (k + 1))) x
    rfl
  map_mark := by
    ext x
    show (markedB.1 (phiTowerEP.ins k x)).1 k = (markedPt (k + 1)) x
    rw [markedPt_apply]
    rfl
  map_top := by
    ext x
    show ((⊤ : ScottEndP B).1 (phiTowerEP.ins k x)).1 k = (⊤ : EndP (D (k + 1))) x
    rfl

/-! ## The two composites, before `Φ`

Stated on the underlying `OrderHom`s, in the `f.toFun.comp g.toFun` spelling
that `baseMapGen_comp` produces. -/

theorem projEndDown_insEndUp (k : ℕ) :
    (projEndDown k).toFun.comp (insEndUp k).toFun
      = (OrderHom.id : EndP (D (k + 1)) →o EndP (D (k + 1))) := by
  refine OrderHom.ext _ _ (funext (fun h => ?_))
  refine OrderHom.ext _ _ (funext (fun x => ?_))
  show ((phiTowerEP.ins k (h ((phiTowerEP.ins k x).1 k))) : B).1 k = h x
  simp only [EpPairTower.ins_self]

theorem insEndUp_projEndDown_le (k : ℕ) :
    (insEndUp k).toFun.comp (projEndDown k).toFun
      ≤ (OrderHom.id : ScottEndP B →o ScottEndP B) := by
  intro H
  rw [scottEndP_le_def]
  intro y
  show phiTowerEP.ins k ((H.1 (phiTowerEP.ins k (y.1 k))).1 k) ≤ H.1 y
  refine le_trans (ins_monotone k ?_) (ins_le_self (H.1 y) k)
  exact H.1.monotone (ins_le_self y k) k

theorem insEndUp_comp_emb (k : ℕ) :
    (insEndUp (k + 1)).toFun.comp ((iter k).endUp).toFun = (insEndUp k).toFun := by
  refine OrderHom.ext _ _ (funext (fun h => ?_))
  refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
  show phiTowerEP.ins (k + 1) ((iter k).emb (h ((iter k).prj (y.1 (k + 1)))))
    = phiTowerEP.ins k (h (y.1 k))
  have hy : (iter k).prj (y.1 (k + 1)) = y.1 k := y.2 k
  have he : phiTowerEP.ins (k + 1) ((iter k).emb (h (y.1 k)))
      = phiTowerEP.ins k (h (y.1 k)) := ins_emb (T := phiTowerEP) k (h (y.1 k))
  rw [hy, he]

/-! ## The legs, built on values

`GlueBaseGen P = P ⊕ P ⊕ P` carries no instance, and neither does `baseMapGen`
between such types.  So the legs are built as subtype elements directly — value
by `canonGen` at the target, proof by `canonGen_idem` — and every instance in
sight is the one the target type already fixed.  That is what going through
`phiFun`, which takes its own copy of the instance, could not do (§85/§86). -/

/-- `Φ (ins k)`. -/
noncomputable def eLeg (k : ℕ) (x : D (k + 2)) : phiB :=
  ⟨canonGen markedB (baseMapGen (insEndUp k).toFun x.1),
    canonGen_idem markedB markedB_ne_bot endPB_bot_ne_top _⟩

/-- `Φ (proj k)`. -/
noncomputable def pLeg (k : ℕ) (z : phiB) : D (k + 2) :=
  ⟨canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun z.1),
    canonGen_idem (markedPt (k + 1)) (hmk (k + 1)) (hbtk (k + 1)) _⟩

theorem eLeg_monotone (k : ℕ) {x y : D (k + 2)} (h : x ≤ y) : eLeg k x ≤ eLeg k y := by
  show leGlueGen markedB (canonGen markedB (baseMapGen (insEndUp k).toFun x.1))
    (canonGen markedB (baseMapGen (insEndUp k).toFun y.1))
  exact leGlueGen_canon markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
    (leGlueGen_map (insEndUp k) markedB_ne_top h)

theorem pLeg_monotone (k : ℕ) {x y : phiB} (h : x ≤ y) : pLeg k x ≤ pLeg k y := by
  show leGlueGen (markedPt (k + 1))
    (canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun x.1))
    (canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun y.1))
  exact leGlueGen_canon (markedPt (k + 1)) (hmk (k + 1))
    ((D_marked_point_nondegenerate (k + 1)).2.1) (hbtk (k + 1))
    (leGlueGen_map (projEndDown k) ((D_marked_point_nondegenerate (k + 1)).2.1) h)

/-! ## Three of the four `IsColimitCocone` fields -/

set_option maxHeartbeats 1000000 in
theorem cocone_retraction (k : ℕ) (x : D (k + 2)) : pLeg k (eLeg k x) = x := by
  refine Subtype.ext ?_
  show canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun
      (canonGen markedB (baseMapGen (insEndUp k).toFun x.1))) = x.1
  rw [canonGen_baseMapGen_canon (projEndDown k) markedB_ne_bot (hmk (k + 1))
      (hbtk (k + 1)),
    ← baseMapGen_comp, projEndDown_insEndUp k, baseMapGen_id]
  exact x.2

set_option maxHeartbeats 1000000 in
theorem cocone_deflation (k : ℕ) (z : phiB) : eLeg k (pLeg k z) ≤ z := by
  have hle : (insEndUp k).toFun.comp (projEndDown k).toFun
      ≤ (OrderHom.id : ScottEndP B →o ScottEndP B) := insEndUp_projEndDown_le k
  have h2 : leGlueGen markedB
      (canonGen markedB (baseMapGen ((insEndUp k).toFun.comp (projEndDown k).toFun) z.1))
      (canonGen markedB (baseMapGen (OrderHom.id : ScottEndP B →o ScottEndP B) z.1)) :=
    leGlueGen_canon markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
      (baseMapGen_leGlueGen_of_le markedB hle z.1)
  rw [baseMapGen_id, z.2] at h2
  show leGlueGen markedB (canonGen markedB (baseMapGen (insEndUp k).toFun
      (canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun z.1)))) z.1
  rw [canonGen_baseMapGen_canon (insEndUp k) (hmk (k + 1)) markedB_ne_bot
      endPB_bot_ne_top,
    ← baseMapGen_comp]
  exact h2

set_option maxHeartbeats 1000000 in
theorem cocone_compat (k : ℕ) (w : D (k + 2)) :
    eLeg (k + 1) (phiTowerEP.emb (k + 1) w) = eLeg k w := by
  refine Subtype.ext ?_
  have hemb : (phiTowerEP.emb (k + 1) w).1
      = canonGen (markedPt (k + 2)) (baseMapGen ((iter k).endUp).toFun w.1) := rfl
  show canonGen markedB (baseMapGen (insEndUp (k + 1)).toFun
      (phiTowerEP.emb (k + 1) w).1)
    = canonGen markedB (baseMapGen (insEndUp k).toFun w.1)
  rw [hemb,
    canonGen_baseMapGen_canon (insEndUp (k + 1)) (hmk (k + 2)) markedB_ne_bot
      endPB_bot_ne_top,
    ← baseMapGen_comp, insEndUp_comp_emb k]

/-! ## The remaining obligations, named -/

/-- **The analysis.**  `eLeg k ∘ pLeg k` is `Φ` of the `k`-th deflation of `B`,
so this asks for `⨆ₖ Φ(Δ k) = Φ(id) = id`. -/
def PhiCoconeIsLUB : Prop :=
  ∀ z : phiB, IsLUB (Set.range fun k => eLeg k (pLeg k z)) z

/-- Chains staged into `Φ(D∞^Φ)` have suprema there. -/
def PhiSupExists : Prop :=
  ∀ d : phiTowerEP.shift.Bilim, ∃ x : phiB, IsLUB (Set.range fun k => eLeg k (d.1 k)) x

/-- …and the legs read them off levelwise. -/
def PhiProjContinuous : Prop :=
  ∀ (d : phiTowerEP.shift.Bilim) (x : phiB),
    IsLUB (Set.range fun k => eLeg k (d.1 k)) x →
    ∀ j, IsLUB (Set.range fun k => pLeg j (eLeg k (d.1 k))) (pLeg j x)

theorem isColimitCocone (h : PhiCoconeIsLUB) :
    phiTowerEP.shift.IsColimitCocone eLeg pLeg where
  retraction := cocone_retraction
  deflation := cocone_deflation
  compat := cocone_compat
  isLUB := h

/-- **Theorem A's order-theoretic half, assembled.**  Everything algebraic is
discharged; the three hypotheses are the analysis. -/
noncomputable def theoremA_orderIso (h : PhiCoconeIsLUB) (hsup : PhiSupExists)
    (hcont : PhiProjContinuous) : phiB ≃o phiTowerEP.Bilim :=
  EpPairTower.orderIsoBilim_shift phiTowerEP (isColimitCocone h)
    (fun k _ _ hxy => pLeg_monotone k hxy) (fun k _ _ hxy => eLeg_monotone k hxy)
    hsup hcont

end PhiCocone
