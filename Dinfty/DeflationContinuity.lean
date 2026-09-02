import Dinfty.EndLocalContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-2342] §The-tower-supplies-the-family-local-continuity
open scoped Classical

namespace DeflationContinuity

open EndLocalContinuity

-- [D-2343] §The-deflation-family-as-a-map
-- [D-2344] defl
noncomputable def defl (n : ℕ) (y : DBilimit) : DBilimit := insertAtLevel n (y.1 n)

-- [D-2345] defl_monotone
theorem defl_monotone (n : ℕ) : Monotone (defl n) := fun _ _ h =>
  insertAtLevel_monotone n (h n)

-- [D-2346] deflHom
noncomputable def deflHom (n : ℕ) : DBilimit →o DBilimit := ⟨defl n, defl_monotone n⟩

-- [D-2347] deflHom_apply
@[simp] theorem deflHom_apply (n : ℕ) (y : DBilimit) : deflHom n y = defl n y := rfl

-- [D-2348] proj_scottContinuous
theorem proj_scottContinuous (n : ℕ) :
    ScottContinuous (fun y : DBilimit => y.1 n) := by
  intro S hne hdir a ha
  have hkey := ha.dbilimit_apply hne hdir n
  show IsLUB ((fun y : DBilimit => y.1 n) '' S) (a.1 n)
  rw [hkey]
  exact isLUB_sSup _

-- [D-2349] insertAtLevel_scottContinuous
theorem insertAtLevel_scottContinuous (n : ℕ) : ScottContinuous (insertAtLevel n) :=
  monotone_scottContinuous_of_finite_dom (insertAtLevel_monotone n)

-- [D-2350] defl_scottContinuous
theorem defl_scottContinuous (n : ℕ) : ScottContinuous (defl n) := by
  have h := (proj_scottContinuous n).comp (insertAtLevel_scottContinuous n)
  unfold defl
  simpa [Function.comp_def] using h

-- [D-2351] defl_isLUB
theorem defl_isLUB (y : DBilimit) : IsLUB (Set.range fun n => defl n y) y := by
  simpa [chainSet, defl] using chainSet_isLUB y

-- [D-2352] defl_directed
theorem defl_directed (i j : ℕ) :
    ∃ k, (∀ y, defl i y ≤ defl k y) ∧ (∀ y, defl j y ≤ defl k y) :=
  ⟨max i j, fun y => insertAtLevel_chain_mono y (le_max_left i j),
            fun y => insertAtLevel_chain_mono y (le_max_right i j)⟩

-- [D-2353] §The-End-half-unconditionally-at-the-live-tower
-- [D-2354] end_defl_isLUB
theorem end_defl_isLUB {h : DBilimit → DBilimit} (hh : ScottContinuous h)
    (x : DBilimit) :
    IsLUB (Set.range fun n => defl n (h (defl n x))) (h x) := by
  have hlub := deflation_isLUB (ι := ℕ) defl id h defl_directed defl_isLUB hh
    defl_scottContinuous x
  simpa using hlub

-- [D-2355] §The-same-in-ScottEndP-DBilimit
-- [D-2356] endDefl
noncomputable def endDefl (n : ℕ) : ScottEndP DBilimit →o ScottEndP DBilimit where
  toFun F := ⟨(deflHom n).comp (F.1.comp (deflHom n)), by
    have h := ((defl_scottContinuous n).comp F.2).comp (defl_scottContinuous n)
    simpa [Function.comp_def] using h⟩
  monotone' _ _ hFG x := (deflHom n).monotone (hFG (defl n x))

-- [D-2357] endDefl_apply
@[simp] theorem endDefl_apply (n : ℕ) (F : ScottEndP DBilimit) (x : DBilimit) :
    (endDefl n F).1 x = defl n (F.1 (defl n x)) := rfl

-- [D-2358] endDefl_isLUB
theorem endDefl_isLUB (F : ScottEndP DBilimit) :
    IsLUB (Set.range fun n => endDefl n F) F := by
  constructor
  · rintro _ ⟨n, rfl⟩ x
    exact (end_defl_isLUB F.2 x).1 ⟨n, rfl⟩
  · intro w hw x
    refine (end_defl_isLUB F.2 x).2 ?_
    rintro _ ⟨n, rfl⟩
    exact hw ⟨n, rfl⟩ x

-- [D-2359] §Why-only-copy
section CopyALimit

-- [D-2360] defl_bot
theorem defl_bot (n : ℕ) : defl n (⊥ : DBilimit) = ⊥ :=
  le_antisymm (insertAtLevel_le_self ⊥ n) bot_le

-- [D-2361] endDefl_bot
theorem endDefl_bot (n : ℕ) : endDefl n (⊥ : ScottEndP DBilimit) = ⊥ := by
  apply Subtype.ext
  apply OrderHom.ext
  funext x
  show defl n ((⊥ : ScottEndP DBilimit).1 (defl n x)) = (⊥ : ScottEndP DBilimit).1 x
  rw [scottEndPBot_apply, scottEndPBot_apply, defl_bot]

end CopyALimit

-- [D-2362] §Through-s-morphism-action-at-the-live-target
-- [D-2363] psiTargetOrder_eq
theorem psiTargetOrder_eq :
    psiTargetOrder = glueCarPartialOrderGen scottEndPId scottEndPId_ne_bot
      scottEndPId_ne_top scottEndPBot_ne_top := rfl

-- [D-2364] phi_endDefl_isLUB
theorem phi_endDefl_isLUB (F : ScottEndP DBilimit) :
    letI := glueCarPartialOrderGen scottEndPId scottEndPId_ne_bot
      scottEndPId_ne_top scottEndPBot_ne_top
    IsLUB (Set.range fun n => tagAGen scottEndPId (endDefl n F))
      (tagAGen scottEndPId F) :=
  baseMapGen_isLUB_tagA scottEndPId scottEndPId_ne_bot scottEndPId_ne_top
    scottEndPBot_ne_top endDefl id (fun a => endDefl_isLUB a) F

end DeflationContinuity
