import Dinfty.DeflationContinuity
import Dinfty.EpPairTower

open GluingTowerLibrary SierpinskiApplication

-- [D-2365] §The-live-tower-as-an-abstract-ep-pair-tower
open scoped Classical

namespace EpPairTower

-- [D-2366] §The-deflation-family-abstractly
variable {T : _root_.EpPairTower}

-- [D-2367] defl
noncomputable def defl (T : _root_.EpPairTower) (n : ℕ) (y : T.Bilim) : T.Bilim :=
  T.ins n (y.1 n)

-- [D-2368] defl_monotone
theorem defl_monotone (n : ℕ) : Monotone (T.defl n) := fun _ _ h =>
  ins_monotone n (h n)

-- [D-2369] defl_range
@[simp] theorem defl_range (y : T.Bilim) :
    (Set.range fun n => T.defl n y) = T.chainSet y := rfl

-- [D-2370] defl_isLUB
theorem defl_isLUB (y : T.Bilim) : IsLUB (Set.range fun n => T.defl n y) y :=
  chainSet_isLUB y

-- [D-2371] defl_directed
theorem defl_directed (i j : ℕ) :
    ∃ k, (∀ y : T.Bilim, T.defl i y ≤ T.defl k y)
      ∧ (∀ y : T.Bilim, T.defl j y ≤ T.defl k y) :=
  ⟨max i j, fun y => ins_chain_mono y (le_max_left i j),
            fun y => ins_chain_mono y (le_max_right i j)⟩

-- [D-2372] proj_scottContinuous
theorem proj_scottContinuous (hT : T.IsDcpo) (n : ℕ) :
    ScottContinuous (fun y : T.Bilim => y.1 n) :=
  fun _S hne hdir _a ha => isLUB_bilim_apply hT ha hne hdir n

-- [D-2373] ins_scottContinuous_of_finite
theorem ins_scottContinuous_of_finite (n : ℕ) [Finite (T.carrier n)] :
    ScottContinuous (T.ins n) :=
  monotone_scottContinuous_of_finite_dom (ins_monotone n)

-- [D-2374] defl_scottContinuous
theorem defl_scottContinuous (hT : T.IsDcpo)
    (hins : ∀ n, ScottContinuous (T.ins n)) (n : ℕ) :
    ScottContinuous (T.defl n) := by
  have h := (proj_scottContinuous hT n).comp (hins n)
  unfold defl
  simpa [Function.comp_def] using h

-- [D-2375] end_defl_isLUB
theorem end_defl_isLUB (hT : T.IsDcpo) (hins : ∀ n, ScottContinuous (T.ins n))
    {h : T.Bilim → T.Bilim} (hh : ScottContinuous h) (x : T.Bilim) :
    IsLUB (Set.range fun n => T.defl n (h (T.defl n x))) (h x) := by
  have hlub := EndLocalContinuity.deflation_isLUB (ι := ℕ) T.defl id h
    defl_directed defl_isLUB hh (defl_scottContinuous hT hins) x
  simpa using hlub

end EpPairTower

-- [D-2376] §The-live-tower-is-one-of-these
namespace RealEpPairTower

-- [D-2377] realTower
noncomputable def realTower : _root_.EpPairTower where
  carrier := D
  order := fun k => inferInstance
  emb := iotaD
  prj := pD
  emb_mono := iotaD_monotone
  prj_mono := fun k w w' h => pD_monotone k w w' h
  retraction := pD_iotaD
  deflation := pD_deflation

-- [D-2378] realTower_carrier
@[simp] theorem realTower_carrier (k : ℕ) : realTower.carrier k = D k := rfl
-- [D-2379] realTower_prj
@[simp] theorem realTower_prj (k : ℕ) : realTower.prj k = pD k := rfl

-- [D-2380] realTower_bilim
theorem realTower_bilim : realTower.Bilim = DBilimit := rfl

-- [D-2381] realTower_finite
instance realTower_finite (k : ℕ) : Finite (realTower.carrier k) :=
  inferInstanceAs (Finite (D k))

-- [D-2382] realTower_isDcpo
theorem realTower_isDcpo : realTower.IsDcpo where
  carrier_lub := by
    intro k S hne hdir
    obtain ⟨t, htS, htmax⟩ := directedOn_exists_greatest_of_finite (Set.toFinite S) hne hdir
    exact ⟨t, fun s hs => htmax s hs, fun z hz => hz htS⟩
  prj_scott := fun k => monotone_scottContinuous_of_finite_dom (fun w w' h => pD_monotone k w w' h)

-- [D-2383] realTower_ins_scottContinuous
theorem realTower_ins_scottContinuous (n : ℕ) : ScottContinuous (realTower.ins n) :=
  EpPairTower.ins_scottContinuous_of_finite n

-- [D-2384] real_end_defl_isLUB
theorem real_end_defl_isLUB {h : realTower.Bilim → realTower.Bilim}
    (hh : ScottContinuous h) (x : realTower.Bilim) :
    IsLUB (Set.range fun n => realTower.defl n (h (realTower.defl n x))) (h x) :=
  EpPairTower.end_defl_isLUB realTower_isDcpo realTower_ins_scottContinuous hh x

end RealEpPairTower
