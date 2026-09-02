import Dinfty.AssemblyChain

open GluingTowerLibrary SierpinskiApplication

-- [D-1614] §Piping-colimit-compat-two-of-the-three-open
open scoped Classical

namespace ColimitCompatPipe

open Assembly AssemblyChain

-- [D-1615] §toD-k-is-a-least-element-of-DInfty
-- [D-1616] iotaD_bot
theorem iotaD_bot (k : ℕ) : iotaD k (⊥ : D k) = (⊥ : D (k + 1)) := by
  first
    | rfl
    | (apply Subtype.ext; rfl)
    | (apply Subtype.ext
       show (Sum.inl (constHom (⊥ : D k)) : GlueBase (EndP (D k)))
         = Sum.inl (⊥ : EndP (D k))
       congr 1
       ext x
       rfl)

-- [D-1617] iotaLe_bot
theorem iotaLe_bot {k n : ℕ} (h : k ≤ n) : iotaLe h (⊥ : D k) = (⊥ : D n) := by
  induction n, h using Nat.le_induction with
  | base => exact iotaLe_self _ _
  | succ m hm ih =>
      rw [iotaLe_succ hm (Nat.le_succ_of_le hm), ih, iotaD_bot]

-- [D-1618] toD_bot_le
theorem toD_bot_le (k : ℕ) (z : DInfty) : toD k (⊥ : D k) ≤ z := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨n, y⟩ := p
    show toD k (⊥ : D k) ≤ toD n y
    rw [toD_le_iff k n (⊥ : D k) y (le_max_left k n) (le_max_right k n), iotaLe_bot]
    exact bot_le

-- [D-1619] §toD-k-preserves-finite-joins
-- [D-1620] toD_sup_le
theorem toD_sup_le (k : ℕ) (w : DInfty) :
    ∀ T : Finset (D k), (∀ y ∈ T, toD k y ≤ w) → toD k (T.sup id) ≤ w := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using toD_bot_le k w
  | @insert a T _ha ih =>
      intro hw
      have h1 : toD k a ≤ w := hw a (Finset.mem_insert_self a T)
      have h2 : toD k (T.sup id) ≤ w := ih (fun y hy => hw y (Finset.mem_insert_of_mem hy))
      rw [Finset.sup_insert, show (id a ⊔ T.sup id) = a ⊔ T.sup id from rfl, ← toD_sup']
      exact sup_le h1 h2

-- [D-1621] §The-two-Props
-- [D-1622] stageJoinRecoverable
theorem stageJoinRecoverable : StageJoinRecoverable := by
  intro k x
  have hx : x = (Finset.univ.filter (fun q : D k => JoinIrred (D k) q ∧ q ≤ x)).sup id :=
    finite_lattice_eq_sup_joinIrreds x
  constructor
  · rintro z ⟨y, _hy, _hyz, hle⟩
    exact hle
  · intro w hw
    rw [hx]
    refine toD_sup_le k w _ ?_
    intro y hy
    have hy' : JoinIrred (D k) y ∧ y ≤ x := (Finset.mem_filter.mp hy).2
    exact hw ⟨y, hy'.1, rfl, (toD_le_iff' k y x).mpr hy'.2⟩

-- [D-1623] stageSupClosed
theorem stageSupClosed : StageSupClosed := by
  intro k S z hS hz
  refine ⟨(Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id, ?_⟩
  have hle : toD k ((Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id) ≤ z :=
    toD_sup_le k z _ (fun y hy => hz.1 (Finset.mem_filter.mp hy).2)
  have hub : ∀ w ∈ S, w ≤ toD k ((Finset.univ.filter (fun y : D k => toD k y ∈ S)).sup id) := by
    intro w hw
    obtain ⟨y, rfl⟩ := hS w hw
    refine (toD_le_iff' k y _).mpr ?_
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hw⟩)
  exact le_antisymm hle (hz.2 hub)

-- [D-1624] stage_finite
theorem stage_finite (k : ℕ) : (Set.range (toD k)).Finite := Set.finite_range _

-- [D-1625] §The-chain-with-one-link-left
-- [D-1626] colimit_rigid_of_joinIrredStagePreserved
theorem colimit_rigid_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_rigid_of_stageDefinable
    (stageDefinable_of h1 stageJoinRecoverable stageSupClosed)

-- [D-1627] DBilimit_rigid_of_joinIrredStagePreserved
theorem DBilimit_rigid_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_chain h1 stageJoinRecoverable stageSupClosed

-- [D-1628] colimit_compat_of_joinIrredStagePreserved
theorem colimit_compat_of_joinIrredStagePreserved (h1 : JoinIrredStagePreserved) :
    Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k) :=
  ⟨fun _ _ => D_all_rigid _, fun _ => colimit_rigid_of_joinIrredStagePreserved h1⟩

-- [D-1629] DBilimit_rigid_of_joinIrredStagePreserved'
theorem DBilimit_rigid_of_joinIrredStagePreserved' (h1 : JoinIrredStagePreserved) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_colimit_compat (colimit_compat_of_joinIrredStagePreserved h1)

end ColimitCompatPipe
