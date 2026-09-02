import Dinfty.PhiCocone

open GluingTowerLibrary SierpinskiApplication

-- [D-2458] §Chain-suprema-in-D-and-in-ScottEndP-D
namespace PhiChainSup

open PhiIterateTower PhiBilimit EpPairTower

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2459] §Monotone-families
-- [D-2460] range_nonempty
theorem range_nonempty {α : Type*} (f : ℕ → α) : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩

-- [D-2461] range_directedOn
theorem range_directedOn {α : Type*} [Preorder α] {f : ℕ → α} (hf : Monotone f) :
    DirectedOn (· ≤ ·) (Set.range f) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact ⟨f (max i j), ⟨max i j, rfl⟩, hf (le_max_left i j), hf (le_max_right i j)⟩

-- [D-2462] exists_eventually_const
theorem exists_eventually_const {f : ℕ → ℕ} (hf : Monotone f) {b : ℕ}
    (hb : ∀ k, f k ≤ b) : ∃ N, ∀ k, N ≤ k → f k = f N := by
  classical
  have hex : ∃ n, ∀ k, f k ≤ n := ⟨b, hb⟩
  have hub : ∀ k, f k ≤ Nat.find hex := Nat.find_spec hex
  have hattain : ∃ N, f N = Nat.find hex := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ k, f k < Nat.find hex := fun k => lt_of_le_of_ne (hub k) (hcon k)
    have hpos : 0 < Nat.find hex := lt_of_le_of_lt (Nat.zero_le _) (hlt 0)
    have hsmall : ∀ k, f k ≤ Nat.find hex - 1 := fun k => Nat.le_sub_one_of_lt (hlt k)
    have hle := Nat.find_min' hex hsmall
    omega
  obtain ⟨N, hN⟩ := hattain
  refine ⟨N, fun k hk => le_antisymm ?_ (hf hk)⟩
  rw [hN]
  exact hub k

-- [D-2463] §B-has-the-suprema-of-chains
-- [D-2464] exists_chain_lub
theorem exists_chain_lub {y : ℕ → B} (hy : Monotone y) : ∃ b : B, IsLUB (Set.range y) b :=
  Bilim.exists_isLUB_of_directedOn phiTowerEP_isDcpo _ (range_nonempty y) (range_directedOn hy)

-- [D-2465] §and-so-does-ScottEndP-B-pointwise
-- [D-2466] ptwise_mono
theorem ptwise_mono (F : ℕ → ScottEndP B) (hF : Monotone F) (y : B) :
    Monotone fun k => (F k).1 y :=
  fun _ _ h => scottEndP_le_def.mp (hF h) y

-- [D-2467] ptwise_ex
private theorem ptwise_ex (F : ℕ → ScottEndP B) (hF : Monotone F) (y : B) :
    ∃ b : B, IsLUB (Set.range fun k => (F k).1 y) b :=
  exists_chain_lub (ptwise_mono F hF y)

-- [D-2468] supFun
noncomputable def supFun (F : ℕ → ScottEndP B) (hF : Monotone F) (y : B) : B :=
  (ptwise_ex F hF y).choose

-- [D-2469] supFun_isLUB
theorem supFun_isLUB (F : ℕ → ScottEndP B) (hF : Monotone F) (y : B) :
    IsLUB (Set.range fun k => (F k).1 y) (supFun F hF y) := (ptwise_ex F hF y).choose_spec

-- [D-2470] supFun_mono
theorem supFun_mono (F : ℕ → ScottEndP B) (hF : Monotone F) : Monotone (supFun F hF) := by
  intro y y' h
  refine (supFun_isLUB F hF y).2 ?_
  rintro _ ⟨k, rfl⟩
  exact le_trans ((F k).1.monotone h) ((supFun_isLUB F hF y').1 ⟨k, rfl⟩)

-- [D-2471] supFun_scott
theorem supFun_scott (F : ℕ → ScottEndP B) (hF : Monotone F) :
    ScottContinuous (supFun F hF) := by
  intro S hne hdir a ha
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    exact supFun_mono F hF (ha.1 hs)
  · intro w hw
    refine (supFun_isLUB F hF a).2 ?_
    rintro _ ⟨k, rfl⟩
    refine ((F k).2 hne hdir ha).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact le_trans ((supFun_isLUB F hF s).1 ⟨k, rfl⟩) (hw ⟨s, hs, rfl⟩)

-- [D-2472] chainSup
noncomputable def chainSup (F : ℕ → ScottEndP B) (hF : Monotone F) : ScottEndP B :=
  ⟨⟨supFun F hF, supFun_mono F hF⟩, supFun_scott F hF⟩

-- [D-2473] chainSup_apply
@[simp] theorem chainSup_apply (F : ℕ → ScottEndP B) (hF : Monotone F) (y : B) :
    (chainSup F hF).1 y = supFun F hF y := rfl

-- [D-2474] chainSup_isLUB
theorem chainSup_isLUB (F : ℕ → ScottEndP B) (hF : Monotone F) :
    IsLUB (Set.range F) (chainSup F hF) := by
  constructor
  · rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mpr (fun y => (supFun_isLUB F hF y).1 ⟨k, rfl⟩)
  · intro w hw
    refine scottEndP_le_def.mpr (fun y => ?_)
    refine (supFun_isLUB F hF y).2 ?_
    rintro _ ⟨k, rfl⟩
    exact scottEndP_le_def.mp (hw ⟨k, rfl⟩) y

-- [D-2475] §The-projection-legs-carry-those-suprema
-- [D-2476] projEndDown_isLUB
theorem projEndDown_isLUB (F : ℕ → ScottEndP B) (hF : Monotone F) (j : ℕ) :
    IsLUB (Set.range fun k => (PhiCocone.projEndDown j).toFun (F k))
      ((PhiCocone.projEndDown j).toFun (chainSup F hF)) := by
  refine EndLocalContinuity.isLUB_orderHom_of_pointwise _ _ (fun x => ?_)
  have hlub := supFun_isLUB F hF (phiTowerEP.ins j x)
  have hne : (Set.range fun k => (F k).1 (phiTowerEP.ins j x)).Nonempty := range_nonempty _
  have hdir : DirectedOn (· ≤ ·) (Set.range fun k => (F k).1 (phiTowerEP.ins j x)) :=
    range_directedOn (ptwise_mono F hF (phiTowerEP.ins j x))
  have hread := isLUB_bilim_apply phiTowerEP_isDcpo hlub hne hdir j
  have himg : (fun z : B => z.1 j) '' (Set.range fun k => (F k).1 (phiTowerEP.ins j x))
      = Set.range fun k => ((F k).1 (phiTowerEP.ins j x)).1 j := by
    rw [← Set.range_comp]
    rfl
  rwa [himg] at hread

end PhiChainSup
