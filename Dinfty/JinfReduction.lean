import Dinfty.TwoPointHypothesis

open GluingTowerLibrary SierpinskiApplication

-- [D-1689] §Attacking-TwoPointFixed-reduce-to-the-join
open scoped Classical

namespace JinfReduction

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

-- [D-1690] §The-join-irreducible-poset
-- [D-1691] Jinf
def Jinf : Type := {z : DInfty // JoinIrred DInfty z}

-- [D-1692] inst-PartialOrder
noncomputable instance : PartialOrder Jinf := Subtype.partialOrder _

-- [D-1693] Jinf_le_iff
@[simp] theorem Jinf_le_iff (a b : Jinf) : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

-- [D-1694] Jmap
noncomputable def Jmap (θ : DInfty ≃o DInfty) : Jinf ≃o Jinf where
  toFun z := ⟨θ z.1, GluingTowerLibrary.joinIrred_orderIso θ z.2⟩
  invFun z := ⟨θ.symm z.1, GluingTowerLibrary.joinIrred_orderIso θ.symm z.2⟩
  left_inv z := Subtype.ext (θ.symm_apply_apply z.1)
  right_inv z := Subtype.ext (θ.apply_symm_apply z.1)
  map_rel_iff' := θ.map_rel_iff

-- [D-1695] Jmap_val
@[simp] theorem Jmap_val (θ : DInfty ≃o DInfty) (z : Jinf) : (Jmap θ z).1 = θ z.1 := rfl

-- [D-1696] §J-is-the-increasing-union-of-the-finite-J-D-k
-- [D-1697] jinf_exists_stage
theorem jinf_exists_stage : ∀ z : DInfty, JoinIrred DInfty z →
    ∃ (k : ℕ) (x : D k), JoinIrred (D k) x ∧ z = toD k x := by
  intro z
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    intro hz
    exact ⟨k, x, (joinIrred_toD_iff k x).mp hz, rfl⟩

-- [D-1698] mem_jinf_of_stage
theorem mem_jinf_of_stage (k : ℕ) (x : D k) (hx : JoinIrred (D k) x) :
    JoinIrred DInfty (toD k x) :=
  (joinIrred_toD_iff k x).mpr hx

-- [D-1699] stage_jinf_finite
theorem stage_jinf_finite (k : ℕ) :
    (Set.range (fun x : {x : D k // JoinIrred (D k) x} => toD k x.1)).Finite :=
  Set.finite_range _

-- [D-1700] §The-two-points-and-the-transported-hypothesis
-- [D-1701] midJ
noncomputable def midJ : Jinf := ⟨midInf, joinIrred_midInf⟩

-- [D-1702] topJ
noncomputable def topJ : Jinf := ⟨toD 0 (⊤ : D 0), joinIrred_toD_zero_top⟩

-- [D-1703] midJ_lt_topJ
theorem midJ_lt_topJ : midJ < topJ := midInf_lt_top_zero

-- [D-1704] twoPointFixed_iff_jinf
theorem twoPointFixed_iff_jinf :
    TwoPointFixed ↔ ∀ θ : DInfty ≃o DInfty, Jmap θ midJ = midJ ∧ Jmap θ topJ = topJ := by
  constructor
  · intro h θ
    exact ⟨Subtype.ext (h θ).1, Subtype.ext (h θ).2⟩
  · intro h θ
    exact ⟨congrArg Subtype.val (h θ).1, congrArg Subtype.val (h θ).2⟩

-- [D-1705] not_stageFixed_of_jinf_moves
theorem not_stageFixed_of_jinf_moves
    (h : ¬ ∀ θ : DInfty ≃o DInfty, Jmap θ midJ = midJ ∧ Jmap θ topJ = topJ) :
    ¬ StageFixed :=
  not_stageFixed_of_not_twoPointFixed (fun hc => h (twoPointFixed_iff_jinf.mp hc))

end JinfReduction
