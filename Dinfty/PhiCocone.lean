import Dinfty.PhiBilimit
import Dinfty.TowerShift
import Dinfty.CanonFixed

open GluingTowerLibrary SierpinskiApplication

-- [D-2433] §of-the-colimit-cocone-rebuilt-on-values
namespace PhiCocone

attribute [-instance] OrderHom.instDecidableEqOfForall

open PhiIterateTower PhiBilimit EpPairTower PhiTriFunctor GenContinuity

-- [D-2434] hmk
private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-2435] hbtk
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-2436] §The-tower-s-cocone-as-tripointed-morphisms
-- [D-2437] insEndUp
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

-- [D-2438] projEndDown
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

-- [D-2439] §The-two-composites-before
-- [D-2440] projEndDown_insEndUp
theorem projEndDown_insEndUp (k : ℕ) :
    (projEndDown k).toFun.comp (insEndUp k).toFun
      = (OrderHom.id : EndP (D (k + 1)) →o EndP (D (k + 1))) := by
  refine OrderHom.ext _ _ (funext (fun h => ?_))
  refine OrderHom.ext _ _ (funext (fun x => ?_))
  show ((phiTowerEP.ins k (h ((phiTowerEP.ins k x).1 k))) : B).1 k = h x
  simp only [EpPairTower.ins_self]

-- [D-2441] insEndUp_projEndDown_le
theorem insEndUp_projEndDown_le (k : ℕ) :
    (insEndUp k).toFun.comp (projEndDown k).toFun
      ≤ (OrderHom.id : ScottEndP B →o ScottEndP B) := by
  intro H
  rw [scottEndP_le_def]
  intro y
  show phiTowerEP.ins k ((H.1 (phiTowerEP.ins k (y.1 k))).1 k) ≤ H.1 y
  refine le_trans (ins_monotone k ?_) (ins_le_self (H.1 y) k)
  exact H.1.monotone (ins_le_self y k) k

-- [D-2442] insEndUp_comp_emb
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

-- [D-2443] §The-legs-built-on-values
-- [D-2444] eLeg
noncomputable def eLeg (k : ℕ) (x : D (k + 2)) : phiB :=
  ⟨canonGen markedB (baseMapGen (insEndUp k).toFun x.1),
    canonGen_idem markedB markedB_ne_bot endPB_bot_ne_top _⟩

-- [D-2445] pLeg
noncomputable def pLeg (k : ℕ) (z : phiB) : D (k + 2) :=
  ⟨canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun z.1),
    canonGen_idem (markedPt (k + 1)) (hmk (k + 1)) (hbtk (k + 1)) _⟩

-- [D-2446] eLeg_monotone
theorem eLeg_monotone (k : ℕ) {x y : D (k + 2)} (h : x ≤ y) : eLeg k x ≤ eLeg k y := by
  show leGlueGen markedB (canonGen markedB (baseMapGen (insEndUp k).toFun x.1))
    (canonGen markedB (baseMapGen (insEndUp k).toFun y.1))
  exact leGlueGen_canon markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
    (leGlueGen_map (insEndUp k) markedB_ne_top h)

-- [D-2447] pLeg_monotone
theorem pLeg_monotone (k : ℕ) {x y : phiB} (h : x ≤ y) : pLeg k x ≤ pLeg k y := by
  show leGlueGen (markedPt (k + 1))
    (canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun x.1))
    (canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun y.1))
  exact leGlueGen_canon (markedPt (k + 1)) (hmk (k + 1))
    ((D_marked_point_nondegenerate (k + 1)).2.1) (hbtk (k + 1))
    (leGlueGen_map (projEndDown k) ((D_marked_point_nondegenerate (k + 1)).2.1) h)

-- [D-2448] §Three-of-the-four-IsColimitCocone-fields
-- [D-2449] cocone_retraction
set_option maxHeartbeats 1000000 in
theorem cocone_retraction (k : ℕ) (x : D (k + 2)) : pLeg k (eLeg k x) = x := by
  refine Subtype.ext ?_
  show canonGen (markedPt (k + 1)) (baseMapGen (projEndDown k).toFun
      (canonGen markedB (baseMapGen (insEndUp k).toFun x.1))) = x.1
  rw [canonGen_baseMapGen_canon (projEndDown k) markedB_ne_bot (hmk (k + 1))
      (hbtk (k + 1)),
    ← baseMapGen_comp, projEndDown_insEndUp k, baseMapGen_id]
  exact x.2

-- [D-2450] cocone_deflation
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

-- [D-2451] cocone_compat
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

-- [D-2452] §The-remaining-obligations-named
-- [D-2453] PhiCoconeIsLUB
def PhiCoconeIsLUB : Prop :=
  ∀ z : phiB, IsLUB (Set.range fun k => eLeg k (pLeg k z)) z

-- [D-2454] PhiSupExists
def PhiSupExists : Prop :=
  ∀ d : phiTowerEP.shift.Bilim, ∃ x : phiB, IsLUB (Set.range fun k => eLeg k (d.1 k)) x

-- [D-2455] PhiProjContinuous
def PhiProjContinuous : Prop :=
  ∀ (d : phiTowerEP.shift.Bilim) (x : phiB),
    IsLUB (Set.range fun k => eLeg k (d.1 k)) x →
    ∀ j, IsLUB (Set.range fun k => pLeg j (eLeg k (d.1 k))) (pLeg j x)

-- [D-2456] isColimitCocone
theorem isColimitCocone (h : PhiCoconeIsLUB) :
    phiTowerEP.shift.IsColimitCocone eLeg pLeg where
  retraction := cocone_retraction
  deflation := cocone_deflation
  compat := cocone_compat
  isLUB := h

-- [D-2457] theoremA_orderIso
noncomputable def theoremA_orderIso (h : PhiCoconeIsLUB) (hsup : PhiSupExists)
    (hcont : PhiProjContinuous) : phiB ≃o phiTowerEP.Bilim :=
  EpPairTower.orderIsoBilim_shift phiTowerEP (isColimitCocone h)
    (fun k _ _ hxy => pLeg_monotone k hxy) (fun k _ _ hxy => eLeg_monotone k hxy)
    hsup hcont

end PhiCocone
