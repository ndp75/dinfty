import Dinfty.PhiTriIdentification
import Dinfty.NormalizedGlueMap
import Dinfty.EndPRigid
import Dinfty.TowerNoAbsorption

open GluingTowerLibrary SierpinskiApplication

-- [D-2072] §The-bridge-tri-v2-is-the-tower-s-step
universe u

namespace PhiTriTower

open PhiTriFunctor PhiTriIdentification GenContinuity TowerNoAbsorption

-- [D-2073] §The-Gen-layer-is-the-finite-layer
section Bridge

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

-- [D-2074] canon_eq
theorem canon_eq (m : P) : canon m = canonGen m := rfl
-- [D-2075] glueCar_eq
theorem glueCar_eq (m : P) : GlueCar (P := P) m = GlueCarGen (P := P) m := rfl
-- [D-2076] rawRule_eq
theorem rawRule_eq (m : P) : rawRule (P := P) m = rawRuleGen (P := P) m := rfl
-- [D-2077] occs_eq
theorem occs_eq (m : P) : occs (P := P) m = occsGen (P := P) m := rfl
-- [D-2078] leGlue_eq
theorem leGlue_eq (m : P) : leGlue (P := P) m = leGlueGen (P := P) m := rfl

-- [D-2079] baseMap_eq
theorem baseMap_eq (g : P →o P') :
    NormalizedGlueMap.baseMap g = baseMapGen g := by
  funext x
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl b => rfl
    | inr c => rfl

-- [D-2080] phiFun_eq_glueMap
theorem phiFun_eq_glueMap {m : P} {m' : P'} (f : TriHom m m')
    (hinj : Function.Injective f.toFun) (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt'
      = NormalizedGlueMap.glueMap f.toFun m m' hinj f.map_bot f.map_mark
          f.map_top hm := by
  funext x
  refine Subtype.ext ?_
  show canonGen m' (baseMapGen f.toFun x.1) = NormalizedGlueMap.baseMap f.toFun x.1
  rw [← baseMap_eq f.toFun]
  show canon m' (NormalizedGlueMap.baseMap f.toFun x.1)
    = NormalizedGlueMap.baseMap f.toFun x.1
  rw [NormalizedGlueMap.canon_baseMap f.toFun m m' hinj f.map_bot f.map_mark
        f.map_top hm x.1]
  exact congrArg (NormalizedGlueMap.baseMap f.toFun) x.2

end Bridge

-- [D-2081] §The-tower
section Tower

attribute [local instance 2000] endPDecidableEq

-- [D-2082] TowerHom
abbrev TowerHom (k k' : ℕ) : Type := TriHom (markedPt k) (markedPt k')

-- [D-2083] hmk
private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-2084] hmtk
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-2085] hbtk
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-2086] §The-bridge-at-the-tower-all-rfl
-- [D-2087] D_succ_eq
theorem D_succ_eq (k : ℕ) :
    D (k + 1) = GlueCarGen (P := EndP (D k)) (markedPt k) := rfl

-- [D-2088] le_succ_eq
theorem le_succ_eq (k : ℕ) (x y : D (k + 1)) :
    (x ≤ y) = leGlueGen (markedPt k) x.1 y.1 := rfl

-- [D-2089] dMid_succ_eq
theorem dMid_succ_eq (k : ℕ) : dMid (k + 1) = triMark (markedPt k) := rfl

-- [D-2090] bot_succ_eq
theorem bot_succ_eq (k : ℕ) : (⊥ : D (k + 1)) = triBot (markedPt k) := rfl

-- [D-2091] top_succ_eq
theorem top_succ_eq (k : ℕ) :
    (⊤ : D (k + 1)) = (triTop (markedPt k) (hmtk k) (hbtk k) : D (k + 1)) := by
  refine le_antisymm ?_ le_top
  exact le_triTop (markedPt k) (hmtk k) (hbtk k) (⊤ : D (k + 1))

-- [D-2092] §on-the-tower
-- [D-2093] finiteEndPD
noncomputable instance finiteEndPD (k : ℕ) : Finite (EndP (D k)) :=
  Finite.of_injective (fun f : EndP (D k) => (f : D k → D k))
    (fun _ _ h => OrderHom.ext _ _ h)

-- [D-2094] phiTower
@[reducible] noncomputable def phiTower {k k' : ℕ} (f : TowerHom k k') :=
  phiFun f (hmk k') (hbtk k')

-- [D-2095] phiTowerD
noncomputable def phiTowerD {k k' : ℕ} (f : TowerHom k k') : D (k + 1) → D (k' + 1) :=
  phiTower f

-- [D-2096] phiTower_id
theorem phiTower_id (k : ℕ) : phiTower (TriHom.id (markedPt k)) = id :=
  phiFun_id (markedPt k) (hmk k) (hbtk k)

-- [D-2097] phiTower_comp
theorem phiTower_comp {k k' k'' : ℕ} (f : TowerHom k k') (f' : TowerHom k' k'') :
    phiTower (f'.comp f) = phiTower f' ∘ phiTower f :=
  phiFun_comp f f' (hmk k') (hbtk k') (hmk k'') (hbtk k'')

-- [D-2098] phiTower_monotone
theorem phiTower_monotone {k k' : ℕ} (f : TowerHom k k')
    {x y : GlueCarGen (P := EndP (D k)) (markedPt k)} (h : x ≤ y) :
    phiTower f x ≤ phiTower f y :=
  phiFun_monotone f (hmk k') (hmtk k') (hbtk k') h

-- [D-2099] phiTower_triBot
theorem phiTower_triBot {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triBot (markedPt k)) = triBot (markedPt k') :=
  phiFun_triBot f (hmk k') (hbtk k')

-- [D-2100] phiTower_triMark
theorem phiTower_triMark {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triMark (markedPt k)) = triMark (markedPt k') :=
  phiFun_triMark f (hmk k') (hbtk k')

-- [D-2101] phiTower_triTop
theorem phiTower_triTop {k k' : ℕ} (f : TowerHom k k') :
    phiTower f (triTop (markedPt k) (hmtk k) (hbtk k))
      = triTop (markedPt k') (hmtk k') (hbtk k') :=
  phiFun_triTop f (hmtk k) (hbtk k) (hmk k') (hmtk k') (hbtk k')

-- [D-2102] phiTower_eq_glueMap
theorem phiTower_eq_glueMap {k k' : ℕ} [Fintype (EndP (D k))]
    [Fintype (EndP (D k'))] (f : TowerHom k k')
    (hinj : Function.Injective f.toFun) :
    phiTower f
      = NormalizedGlueMap.glueMap f.toFun (markedPt k) (markedPt k') hinj
          f.map_bot f.map_mark f.map_top (hmk k) :=
  phiFun_eq_glueMap f hinj (hmk k) (hmk k') (hbtk k')

-- [D-2103] phiTower_unique_of_rigid
theorem phiTower_unique_of_rigid (k : ℕ)
    (hrigid : Subsingleton (EndP (D k) ≃o EndP (D k)))
    (f : TowerHom k k) (hf : Function.Injective f.toFun)
    (ψ : EndP (D k) →o EndP (D k)) (hψ : Function.Injective ψ) :
    phiTwist f ψ (hmk k) (hbtk k) = phiTower f :=
  phiTwist_eq_phiFun_of_rigid hrigid f hf ψ hψ (hmk k) (hbtk k)

-- [D-2104] §The-hypothesis-discharged-EndP-D-k-is-rigid
-- [D-2105] joinIrred_lamD
theorem joinIrred_lamD (k : ℕ) : JoinIrred (D k) (lamD k) := by
  refine ⟨lamD_ne_bot k, fun b c hbc => ?_⟩
  by_cases hb : b = (⊥ : D k)
  · subst hb; right; simpa using hbc
  · left
    have hble : b ≤ lamD k := hbc ▸ le_sup_left
    exact le_antisymm (lamD_le k b hb) hble |>.symm ▸ rfl

-- [D-2106] nonemptyJD
instance nonemptyJD (k : ℕ) : Nonempty {x : D k // JoinIrred (D k) x} :=
  ⟨⟨lamD k, joinIrred_lamD k⟩⟩

-- [D-2107] endP_D_rigid
theorem endP_D_rigid (k : ℕ) [Fintype (EndP (D k))] :
    Subsingleton (EndP (D k) ≃o EndP (D k)) := by
  letI := realUniqueAtomCoatom k
  exact EndPRigid.endP_rigid (D_all_rigid k)

-- [D-2108] phiTower_unique
theorem phiTower_unique (k : ℕ) [Fintype (EndP (D k))]
    (f : TowerHom k k) (hf : Function.Injective f.toFun)
    (ψ : EndP (D k) →o EndP (D k)) (hψ : Function.Injective ψ) :
    phiTwist f ψ (hmk k) (hbtk k) = phiTower f :=
  phiTower_unique_of_rigid k (endP_D_rigid k) f hf ψ hψ

end Tower

end PhiTriTower
