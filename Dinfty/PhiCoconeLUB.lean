import Dinfty.PhiCocone

open GluingTowerLibrary SierpinskiApplication

-- [D-2477] §The-analysis-id-on-D
namespace PhiCoconeLUB

open PhiIterateTower PhiBilimit EpPairTower PhiTriFunctor GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2478] hmk
private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1

-- [D-2479] §Two-facts-about-monotone-families
section General

variable {α : Type*} [PartialOrder α]

-- [D-2480] eventually_ne_of_isLUB
theorem eventually_ne_of_isLUB {f : ℕ → α} (hmono : Monotone f) {c : α}
    (hc : IsLUB (Set.range f) c) {v : α} (hv : c ≠ v) :
    ∃ N, ∀ k, N ≤ k → f k ≠ v := by
  by_contra hcon
  push_neg at hcon
  have hub : v ∈ upperBounds (Set.range f) := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk, hkv⟩ := hcon j
    exact le_trans (hmono hk) (le_of_eq hkv)
  obtain ⟨k0, _, hk0⟩ := hcon 0
  exact hv (le_antisymm (hc.2 hub) (le_trans (le_of_eq hk0.symm) (hc.1 ⟨k0, rfl⟩)))

-- [D-2481] isLUB_tail
theorem isLUB_tail {f : ℕ → α} (hmono : Monotone f) {c : α}
    (hc : IsLUB (Set.range f) c) (N : ℕ) :
    IsLUB (Set.range fun k => f (N + k)) c := by
  constructor
  · rintro _ ⟨k, rfl⟩
    exact hc.1 ⟨N + k, rfl⟩
  · intro w hw
    refine hc.2 ?_
    rintro _ ⟨j, rfl⟩
    exact le_trans (hmono (Nat.le_add_left j N)) (hw ⟨j, rfl⟩)

end General

-- [D-2482] §The-deflations-of-B-and-h-h
-- [D-2483] defl
noncomputable def defl (k : ℕ) (y : B) : B := phiTowerEP.ins k (y.1 k)

-- [D-2484] defl_scott
theorem defl_scott (k : ℕ) : ScottContinuous (defl k) := by
  have h := (proj_scottContinuous k).comp (ins_scottContinuous k)
  show ScottContinuous (fun y : B => phiTowerEP.ins k (y.1 k))
  simpa [Function.comp_def] using h

-- [D-2485] defl_index_mono
theorem defl_index_mono (y : B) {i j : ℕ} (h : i ≤ j) : defl i y ≤ defl j y :=
  ins_chain_mono y h

-- [D-2486] defl_dir
theorem defl_dir (i j : ℕ) :
    ∃ k, (∀ x : B, defl i x ≤ defl k x) ∧ (∀ x : B, defl j x ≤ defl k x) :=
  ⟨max i j, fun x => defl_index_mono x (le_max_left i j),
    fun x => defl_index_mono x (le_max_right i j)⟩

-- [D-2487] defl_lub
theorem defl_lub (y : B) : IsLUB (Set.range fun k => defl k y) y :=
  chainSet_isLUB y

-- [D-2488] end_defl_isLUB
theorem end_defl_isLUB {h : B → B} (hh : ScottContinuous h) (y : B) :
    IsLUB (Set.range fun k => defl k (h (defl k y))) (h y) := by
  have hlub := EndLocalContinuity.deflation_isLUB (ι := ℕ) defl id h defl_dir
    defl_lub hh defl_scott y
  simpa using hlub

-- [D-2489] §The-same-in-ScottEndP-B-the-map-is-applied
-- [D-2490] bigDelta
noncomputable def bigDelta (k : ℕ) : ScottEndP B →o ScottEndP B :=
  (PhiCocone.insEndUp k).toFun.comp (PhiCocone.projEndDown k).toFun

-- [D-2491] bigDelta_apply
theorem bigDelta_apply (k : ℕ) (H : ScottEndP B) (y : B) :
    (bigDelta k H).1 y = defl k (H.1 (defl k y)) := rfl

-- [D-2492] bigDelta_isLUB
theorem bigDelta_isLUB (H : ScottEndP B) : IsLUB (Set.range fun k => bigDelta k H) H := by
  constructor
  · rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mpr (fun y => (end_defl_isLUB H.2 y).1 ⟨k, rfl⟩)
  · intro w hw
    refine scottEndP_le_def.mpr (fun y => ?_)
    refine (end_defl_isLUB H.2 y).2 ?_
    rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mp (hw ⟨k, rfl⟩) y

-- [D-2493] bigDelta_mono
theorem bigDelta_mono (H : ScottEndP B) : Monotone (fun k => bigDelta k H) := by
  intro i j hij
  refine scottEndP_le_def.mpr (fun y => ?_)
  show defl i (H.1 (defl i y)) ≤ defl j (H.1 (defl j y))
  refine le_trans ?_ (defl_index_mono (H.1 (defl j y)) hij)
  exact ins_monotone i (H.1.monotone (defl_index_mono y hij) i)

-- [D-2494] §Through-the-glue
-- [D-2495] eLeg_pLeg_val
theorem eLeg_pLeg_val (k : ℕ) (z : PhiBilimit.phiB) :
    (PhiCocone.eLeg k (PhiCocone.pLeg k z)).1
      = canonGen markedB (baseMapGen (bigDelta k) z.1) := by
  show canonGen markedB (baseMapGen (PhiCocone.insEndUp k).toFun
      (canonGen (markedPt (k + 1)) (baseMapGen (PhiCocone.projEndDown k).toFun z.1)))
    = _
  rw [canonGen_baseMapGen_canon (PhiCocone.insEndUp k) (hmk (k + 1)) markedB_ne_bot
      endPB_bot_ne_top, ← baseMapGen_comp]
  rfl

-- [D-2496] least_of_tail
private theorem least_of_tail {z w : PhiBilimit.phiB} {f : ℕ → ScottEndP B}
    (hw : w ∈ upperBounds (Set.range fun k => PhiCocone.eLeg k (PhiCocone.pLeg k z)))
    (N : ℕ) (t : ScottEndP B → PhiBilimit.phiB)
    (hid : ∀ k, PhiCocone.eLeg (N + k) (PhiCocone.pLeg (N + k) z) = t (f (N + k)))
    (hlub : IsLUB (t '' Set.range fun k => f (N + k)) z) : z ≤ w := by
  refine hlub.2 ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rw [← hid k]
  exact hw ⟨N + k, rfl⟩

-- [D-2497] §The-theorem
-- [D-2498] phiCoconeIsLUB
set_option maxHeartbeats 1000000 in
theorem phiCoconeIsLUB : PhiCocone.PhiCoconeIsLUB := by
  intro z
  constructor
  · rintro _ ⟨k, rfl⟩
    exact PhiCocone.cocone_deflation k z
  · intro w hw
    have hfx : CanonFixed.Fixed markedB z.1 := (CanonFixed.fixed_iff markedB z.1).mp z.2
    rcases hv : z.1 with a | b | c
    · have hza : z = tagAGen markedB a := Subtype.ext hv
      refine least_of_tail hw 0 (tagAGen markedB) (f := fun k => bigDelta k a) ?_ ?_
      · intro k
        refine Subtype.ext ?_
        rw [eLeg_pLeg_val, hv]
        rfl
      · rw [hza]
        exact tagAGen_isLUB markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
          (isLUB_tail (bigDelta_mono a) (bigDelta_isLUB a) 0)
    · rw [hv] at hfx
      have hb : b ≠ (⊥ : ScottEndP B) := hfx
      have hzb : z = tagBGen markedB markedB_ne_bot endPB_bot_ne_top b := by
        refine Subtype.ext ?_
        show z.1 = canonGen markedB (Sum.inr (Sum.inl b))
        rw [← hv]
        exact z.2.symm
      obtain ⟨N, hN⟩ := eventually_ne_of_isLUB (bigDelta_mono b) (bigDelta_isLUB b) hb
      refine least_of_tail hw N (tagBGen markedB markedB_ne_bot endPB_bot_ne_top)
        (f := fun k => bigDelta k b) ?_ ?_
      · intro k
        refine Subtype.ext ?_
        rw [eLeg_pLeg_val, hv]
        rfl
      · rw [hzb]
        refine tagBGen_isLUB markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
          (isLUB_tail (bigDelta_mono b) (bigDelta_isLUB b) N) ⟨_, 0, rfl⟩ ?_
        rintro _ ⟨k, rfl⟩
        exact hN (N + k) (Nat.le_add_right N k)
    · rw [hv] at hfx
      have hcb : c ≠ (⊥ : ScottEndP B) := hfx.1
      have hcm : c ≠ markedB := hfx.2
      have hzc : z = tagCGen markedB markedB_ne_bot endPB_bot_ne_top c := by
        refine Subtype.ext ?_
        show z.1 = canonGen markedB (Sum.inr (Sum.inr c))
        rw [← hv]
        exact z.2.symm
      obtain ⟨N1, hN1⟩ := eventually_ne_of_isLUB (bigDelta_mono c) (bigDelta_isLUB c) hcb
      obtain ⟨N2, hN2⟩ := eventually_ne_of_isLUB (bigDelta_mono c) (bigDelta_isLUB c) hcm
      refine least_of_tail hw (max N1 N2) (tagCGen markedB markedB_ne_bot endPB_bot_ne_top)
        (f := fun k => bigDelta k c) ?_ ?_
      · intro k
        refine Subtype.ext ?_
        rw [eLeg_pLeg_val, hv]
        rfl
      · rw [hzc]
        refine tagCGen_isLUB markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
          (isLUB_tail (bigDelta_mono c) (bigDelta_isLUB c) (max N1 N2)) ⟨_, 0, rfl⟩ ?_ ?_
        · rintro _ ⟨k, rfl⟩
          exact hN1 _ (le_trans (le_max_left N1 N2) (Nat.le_add_right _ k))
        · rintro _ ⟨k, rfl⟩
          exact hN2 _ (le_trans (le_max_right N1 N2) (Nat.le_add_right _ k))

-- [D-2499] §What-is-now-unconditional
-- [D-2500] isColimitCocone
theorem isColimitCocone :
    phiTowerEP.shift.IsColimitCocone PhiCocone.eLeg PhiCocone.pLeg :=
  PhiCocone.isColimitCocone phiCoconeIsLUB

-- [D-2501] hpm
private theorem hpm (k : ℕ) : Monotone (PhiCocone.pLeg k) :=
  fun _ _ hxy => PhiCocone.pLeg_monotone k hxy

-- [D-2502] hem
private theorem hem (k : ℕ) : Monotone (PhiCocone.eLeg k) :=
  fun _ _ hxy => PhiCocone.eLeg_monotone k hxy

-- [D-2503] toShiftBilim
noncomputable def toShiftBilim : PhiBilimit.phiB → phiTowerEP.shift.Bilim :=
  isColimitCocone.toBilim hpm hem

-- [D-2504] toShiftBilim_le_iff
theorem toShiftBilim_le_iff (x y : PhiBilimit.phiB) :
    toShiftBilim x ≤ toShiftBilim y ↔ x ≤ y :=
  isColimitCocone.toBilim_le_iff hpm hem x y

-- [D-2505] toShiftBilim_injective
theorem toShiftBilim_injective : Function.Injective toShiftBilim :=
  isColimitCocone.toBilim_injective hpm hem

-- [D-2506] theoremA_orderIso
noncomputable def theoremA_orderIso (hsup : PhiCocone.PhiSupExists)
    (hcont : PhiCocone.PhiProjContinuous) :
    PhiBilimit.phiB ≃o phiTowerEP.Bilim :=
  PhiCocone.theoremA_orderIso phiCoconeIsLUB hsup hcont

end PhiCoconeLUB
