import Dinfty.PhiCocone

open GluingTowerLibrary SierpinskiApplication

/-!
# The analysis: `⨆ₖ Φ(δₖ) = id` on `Φ(D∞^Φ)`

`PhiCocone` discharged the three *algebraic* fields of `IsColimitCocone` and
named the fourth, `PhiCoconeIsLUB`, as "the analysis".  This module proves it.

The shape of the argument is the one `DeflationContinuity` runs on the legacy
limit, with one difference that matters and is the reason it goes through here
where it did not there.

* Below the glue it is `EndLocalContinuity.deflation_isLUB` with all four
  hypotheses discharged from `EpPairTower`: joint directedness from
  `ins_chain_mono`, pointwise suprema from `chainSet_isLUB`, and Scott-continuity
  of each deflation from `PhiBilimit`'s two continuity theorems.  That gives
  `bigDelta_isLUB : IsLUB (range fun k => Δ k H) H` for **every** `H`, because
  `ScottEndP B`'s payloads are Scott-continuous by construction.

* Through the glue, `DeflationContinuity` could only do copy `A`: the copy-`B`
  and copy-`C` inclusions carry side conditions on the *values* of the family
  (`≠ ⊥` for `B`, and `≠ m` too for `C`), and at `F = ⊥` every approximant is
  `⊥`.  **That obstruction is absent here**, and for a reason, not by luck: the
  family is indexed by a point `z` of the glue that is already canon-fixed, so
  its copy-`B` payload is `≠ ⊥` and its copy-`C` payload is `≠ ⊥` and `≠ m`
  *by `CanonFixed.Fixed`*.  A monotone family whose supremum avoids a value
  eventually avoids it (`eventually_ne_of_isLUB`), and a monotone family's tail
  has the same supremum (`isLUB_tail`) — so each side condition holds on a
  cofinal tail, which is all `IsLUB` sees.

So the degenerate approximants are real (small `k` can send a copy-`B` point to
the glue's copy-`A` region) and they are simply discarded: they sit below the
supremum, and the upper-bound half of `IsLUB` is already `cocone_deflation`.
-/

namespace PhiCoconeLUB

open PhiIterateTower PhiBilimit EpPairTower PhiTriFunctor GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1

/-! ## Two facts about monotone `ℕ`-families

Both are about a family and its supremum only; neither mentions the glue. -/

section General

variable {α : Type*} [PartialOrder α]

/-- If a monotone family's supremum is not `v`, the family is eventually not
`v`.  (If it were `v` cofinally often, monotonicity would make `v` an upper
bound and a member below the supremum at once.) -/
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

/-- A monotone family and its `N`-tail have the same suprema. -/
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

/-! ## The deflations of `B`, and `⨆ₖ δₖ ∘ h ∘ δₖ = h` -/

/-- The `k`-th deflation of the `Φ`-iterate bilimit. -/
noncomputable def defl (k : ℕ) (y : B) : B := phiTowerEP.ins k (y.1 k)

theorem defl_scott (k : ℕ) : ScottContinuous (defl k) := by
  have h := (proj_scottContinuous k).comp (ins_scottContinuous k)
  show ScottContinuous (fun y : B => phiTowerEP.ins k (y.1 k))
  simpa [Function.comp_def] using h

theorem defl_index_mono (y : B) {i j : ℕ} (h : i ≤ j) : defl i y ≤ defl j y :=
  ins_chain_mono y h

theorem defl_dir (i j : ℕ) :
    ∃ k, (∀ x : B, defl i x ≤ defl k x) ∧ (∀ x : B, defl j x ≤ defl k x) :=
  ⟨max i j, fun x => defl_index_mono x (le_max_left i j),
    fun x => defl_index_mono x (le_max_right i j)⟩

theorem defl_lub (y : B) : IsLUB (Set.range fun k => defl k y) y :=
  chainSet_isLUB y

/-- **`⨆ₖ δₖ ∘ h ∘ δₖ = h`, pointwise, for Scott-continuous `h`.** -/
theorem end_defl_isLUB {h : B → B} (hh : ScottContinuous h) (y : B) :
    IsLUB (Set.range fun k => defl k (h (defl k y))) (h y) := by
  have hlub := EndLocalContinuity.deflation_isLUB (ι := ℕ) defl id h defl_dir
    defl_lub hh defl_scott y
  simpa using hlub

/-! ## The same in `ScottEndP B` — the map `Φ` is applied to -/

/-- `Δ k = ins k ∘ (·) ∘ proj k`, i.e. `PhiCocone`'s two legs composed before
the glue.  This is exactly the map whose `Φ`-image is `eLeg k ∘ pLeg k`. -/
noncomputable def bigDelta (k : ℕ) : ScottEndP B →o ScottEndP B :=
  (PhiCocone.insEndUp k).toFun.comp (PhiCocone.projEndDown k).toFun

theorem bigDelta_apply (k : ℕ) (H : ScottEndP B) (y : B) :
    (bigDelta k H).1 y = defl k (H.1 (defl k y)) := rfl

/-- **Every `H` is the supremum of its own deflation approximants.**  Unlike the
legacy `DeflationContinuity.endDefl_isLUB` this needs no side condition, because
`ScottEndP B` carries the continuity of `H` in its own data. -/
theorem bigDelta_isLUB (H : ScottEndP B) : IsLUB (Set.range fun k => bigDelta k H) H := by
  constructor
  · rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mpr (fun y => (end_defl_isLUB H.2 y).1 ⟨k, rfl⟩)
  · intro w hw
    refine scottEndP_le_def.mpr (fun y => ?_)
    refine (end_defl_isLUB H.2 y).2 ?_
    rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mp (hw ⟨k, rfl⟩) y

theorem bigDelta_mono (H : ScottEndP B) : Monotone (fun k => bigDelta k H) := by
  intro i j hij
  refine scottEndP_le_def.mpr (fun y => ?_)
  show defl i (H.1 (defl i y)) ≤ defl j (H.1 (defl j y))
  refine le_trans ?_ (defl_index_mono (H.1 (defl j y)) hij)
  exact ins_monotone i (H.1.monotone (defl_index_mono y hij) i)

/-! ## Through the glue -/

/-- `eLeg k ∘ pLeg k` **is** `Φ (Δ k)`, on values. -/
theorem eLeg_pLeg_val (k : ℕ) (z : PhiBilimit.phiB) :
    (PhiCocone.eLeg k (PhiCocone.pLeg k z)).1
      = canonGen markedB (baseMapGen (bigDelta k) z.1) := by
  show canonGen markedB (baseMapGen (PhiCocone.insEndUp k).toFun
      (canonGen (markedPt (k + 1)) (baseMapGen (PhiCocone.projEndDown k).toFun z.1)))
    = _
  rw [canonGen_baseMapGen_canon (PhiCocone.insEndUp k) (hmk (k + 1)) markedB_ne_bot
      endPB_bot_ne_top, ← baseMapGen_comp]
  rfl

/-- The least-upper-bound half, from a cofinal tail that lands in one copy. -/
private theorem least_of_tail {z w : PhiBilimit.phiB} {f : ℕ → ScottEndP B}
    (hw : w ∈ upperBounds (Set.range fun k => PhiCocone.eLeg k (PhiCocone.pLeg k z)))
    (N : ℕ) (t : ScottEndP B → PhiBilimit.phiB)
    (hid : ∀ k, PhiCocone.eLeg (N + k) (PhiCocone.pLeg (N + k) z) = t (f (N + k)))
    (hlub : IsLUB (t '' Set.range fun k => f (N + k)) z) : z ≤ w := by
  refine hlub.2 ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rw [← hid k]
  exact hw ⟨N + k, rfl⟩

/-! ## The theorem -/

set_option maxHeartbeats 1000000 in
/-- **The analysis.**  `⨆ₖ Φ(δₖ) = id` on `Φ(D∞^Φ)`. -/
theorem phiCoconeIsLUB : PhiCocone.PhiCoconeIsLUB := by
  intro z
  constructor
  · rintro _ ⟨k, rfl⟩
    exact PhiCocone.cocone_deflation k z
  · intro w hw
    have hfx : CanonFixed.Fixed markedB z.1 := (CanonFixed.fixed_iff markedB z.1).mp z.2
    rcases hv : z.1 with a | b | c
    -- copy `A`: no side condition at all.
    · have hza : z = tagAGen markedB a := Subtype.ext hv
      refine least_of_tail hw 0 (tagAGen markedB) (f := fun k => bigDelta k a) ?_ ?_
      · intro k
        refine Subtype.ext ?_
        rw [eLeg_pLeg_val, hv]
        rfl
      · rw [hza]
        exact tagAGen_isLUB markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
          (isLUB_tail (bigDelta_mono a) (bigDelta_isLUB a) 0)
    -- copy `B`: `b ≠ ⊥` from `Fixed`, so the approximants avoid `⊥` cofinally.
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
    -- copy `C`: `c ≠ ⊥` and `c ≠ m` from `Fixed`, so both hold cofinally.
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

/-! ## What is now unconditional

`PhiCocone.isColimitCocone` no longer takes a hypothesis, so everything the
`IsColimitCocone` structure gives for free is now a theorem: in particular
`Φ(D∞^Φ)` embeds in the shifted bilimit by an **order-reflecting** map.  Only
surjectivity — `PhiSupExists` and `PhiProjContinuous` — is still open. -/

/-- **The cocone is a colimit cocone.**  No hypothesis. -/
theorem isColimitCocone :
    phiTowerEP.shift.IsColimitCocone PhiCocone.eLeg PhiCocone.pLeg :=
  PhiCocone.isColimitCocone phiCoconeIsLUB

private theorem hpm (k : ℕ) : Monotone (PhiCocone.pLeg k) :=
  fun _ _ hxy => PhiCocone.pLeg_monotone k hxy

private theorem hem (k : ℕ) : Monotone (PhiCocone.eLeg k) :=
  fun _ _ hxy => PhiCocone.eLeg_monotone k hxy

/-- `x ↦ (pLeg k x)` at every level, into the shifted bilimit. -/
noncomputable def toShiftBilim : PhiBilimit.phiB → phiTowerEP.shift.Bilim :=
  isColimitCocone.toBilim hpm hem

/-- **Order-reflecting, unconditionally.** -/
theorem toShiftBilim_le_iff (x y : PhiBilimit.phiB) :
    toShiftBilim x ≤ toShiftBilim y ↔ x ≤ y :=
  isColimitCocone.toBilim_le_iff hpm hem x y

theorem toShiftBilim_injective : Function.Injective toShiftBilim :=
  isColimitCocone.toBilim_injective hpm hem

/-- **Theorem A, order-theoretic half**, with the analysis discharged: only the
two surjectivity hypotheses remain. -/
noncomputable def theoremA_orderIso (hsup : PhiCocone.PhiSupExists)
    (hcont : PhiCocone.PhiProjContinuous) :
    PhiBilimit.phiB ≃o phiTowerEP.Bilim :=
  PhiCocone.theoremA_orderIso phiCoconeIsLUB hsup hcont

end PhiCoconeLUB
