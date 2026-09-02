import Dinfty.GluingTowerLibrary
import Dinfty.MigrationCloseout
import Mathlib.SetTheory.Cardinal.Continuum

open scoped Classical
open Relation

universe u

open GluingTowerLibrary

namespace SierpinskiApplication

section RecursiveTower

-- [D-0770] TowerLevel
structure TowerLevel : Type (u + 1) where
  carrier : Type u
  dec : DecidableEq carrier
  lat : Lattice carrier
  bdd : BoundedOrder carrier
  fin : Fintype carrier
  nontriv : Nontrivial carrier
  mid : carrier
  mid_ne_bot : letI := lat; letI := bdd; mid ≠ (⊥ : carrier)
  mid_ne_top : letI := lat; letI := bdd; mid ≠ (⊤ : carrier)

-- [D-0771] towerLevel0
noncomputable def towerLevel0 : TowerLevel where
  carrier := Fin 3
  dec := inferInstance
  lat := inferInstance
  bdd := inferInstance
  fin := inferInstance
  nontriv := ⟨0, 1, by decide⟩
  mid := 1
  mid_ne_bot := by decide
  mid_ne_top := by decide

-- [D-0772] towerLevelSucc
noncomputable def towerLevelSucc (prev : TowerLevel) : TowerLevel :=
  letI := prev.dec
  letI := prev.lat
  letI := prev.bdd
  letI := prev.fin
  letI := prev.nontriv
  have hbtPrev : (⊥ : prev.carrier) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm : (constHom prev.mid : EndP prev.carrier) ≠ ⊥ := by
    intro h
    have hb : (⊥ : EndP prev.carrier) = constHom (⊥ : prev.carrier) := by ext x; rfl
    exact prev.mid_ne_bot (constHom_injective (h.trans hb))
  have hmt : (constHom prev.mid : EndP prev.carrier) ≠ ⊤ := fun h =>
    prev.mid_ne_top (constHom_injective (h.trans endP_top_eq_constHom_top))
  have hbt : (⊥ : EndP prev.carrier) ≠ (⊤ : EndP prev.carrier) := endP_bot_ne_top hbtPrev
  { carrier := GlueCar (P := EndP prev.carrier) (constHom prev.mid)
    dec := inferInstance
    lat := glueLattice (constHom prev.mid) hm hmt hbt
    bdd := glueBoundedOrder (constHom prev.mid) hm hmt hbt
    fin := inferInstance
    nontriv := glueCar_nontrivial (constHom prev.mid) hm hmt hbt
    mid := midM prev.mid
    mid_ne_bot := midM_ne_bot prev.mid_ne_bot prev.mid_ne_top hbtPrev
    mid_ne_top := midM_ne_top prev.mid_ne_bot prev.mid_ne_top hbtPrev }

-- [D-0773] towerLevel
noncomputable def towerLevel : ℕ → TowerLevel
  | 0 => towerLevel0
  | k + 1 => towerLevelSucc (towerLevel k)

-- [D-0774] D
@[reducible] noncomputable def D (k : ℕ) : Type := (towerLevel k).carrier

-- [D-0775] instDecidableEqD
noncomputable instance instDecidableEqD (k : ℕ) : DecidableEq (D k) := (towerLevel k).dec
-- [D-0776] instLatticeD
noncomputable instance instLatticeD (k : ℕ) : Lattice (D k) := (towerLevel k).lat
-- [D-0777] instBoundedOrderD
noncomputable instance instBoundedOrderD (k : ℕ) : BoundedOrder (D k) := (towerLevel k).bdd
-- [D-0778] instFintypeD
noncomputable instance instFintypeD (k : ℕ) : Fintype (D k) := (towerLevel k).fin
-- [D-0779] instNontrivialD
noncomputable instance instNontrivialD (k : ℕ) : Nontrivial (D k) := (towerLevel k).nontriv

-- [D-0780] dMid
noncomputable def dMid (k : ℕ) : D k := (towerLevel k).mid

-- [D-0781] dMid_ne_bot
theorem dMid_ne_bot (k : ℕ) : dMid k ≠ (⊥ : D k) := (towerLevel k).mid_ne_bot
-- [D-0782] dMid_ne_top
theorem dMid_ne_top (k : ℕ) : dMid k ≠ (⊤ : D k) := (towerLevel k).mid_ne_top

-- [D-0783] markedPt
noncomputable def markedPt (k : ℕ) : EndP (D k) := constHom (dMid k)

-- [D-0784] markedPt_apply
@[simp] theorem markedPt_apply (k : ℕ) (x : D k) : markedPt k x = dMid k := rfl

-- [D-0785] markedPt_ne_bot
theorem markedPt_ne_bot (k : ℕ) : markedPt k ≠ (⊥ : EndP (D k)) := by
  intro h
  have hb : (⊥ : EndP (D k)) = constHom (⊥ : D k) := by ext x; rfl
  exact dMid_ne_bot k (constHom_injective (h.trans hb))

-- [D-0786] markedPt_ne_top
theorem markedPt_ne_top (k : ℕ) : markedPt k ≠ (⊤ : EndP (D k)) := fun h =>
  dMid_ne_top k (constHom_injective (h.trans endP_top_eq_constHom_top))

-- [D-0787] finThreeUniqueAtomCoatom
instance finThreeUniqueAtomCoatom : UniqueAtomCoatom (Fin 3) where
  unique_atom := existsUnique_atom_of_least_nonzero (a := (1 : Fin 3)) (by decide) (by decide)
  unique_coatom :=
    existsUnique_coatom_of_greatest_ne_top (a := (1 : Fin 3)) (by decide) (by decide)

-- [D-0788] D_marked_point_nondegenerate
theorem D_marked_point_nondegenerate (k : ℕ) :
    (markedPt k) ≠ ⊥ ∧ (markedPt k) ≠ ⊤ ∧
    (⊥ : EndP (D k)) ≠ (⊤ : EndP (D k)) :=
  have hbt : (⊥ : D k) ≠ ⊤ := bot_ne_top_of_nontrivial
  ⟨markedPt_ne_bot k, markedPt_ne_top k, endP_bot_ne_top hbt⟩

-- [D-0789] D_has_interior_point
theorem D_has_interior_point : ∀ k, ∃ x : D k, x ≠ ⊥ ∧ x ≠ ⊤
  | 0 => ⟨(1 : Fin 3),
      (fun heq => absurd (show (1 : Fin 3) = 0 from heq) (by decide)),
      (fun heq => absurd (show (1 : Fin 3) = 2 from heq) (by decide))⟩
  | k + 1 => by
      have h := D_marked_point_nondegenerate k
      exact ⟨glueA (markedPt k) (markedPt k),
        fun hc => h.1 (glueA_injective (markedPt k) hc),
        glueA_ne_top (markedPt k) h.1 h.2.1 h.2.2 (markedPt k)⟩

-- [D-0790] realUniqueAtomCoatom
noncomputable def realUniqueAtomCoatom : ∀ k, UniqueAtomCoatom (D k)
  | 0 => finThreeUniqueAtomCoatom
  | k + 1 =>
      letI := realUniqueAtomCoatom k
      letI := endPUniqueAtomCoatom (P := D k)
      have h := D_marked_point_nondegenerate k
      have heq : coatomOf (EndP (D k)) = cospikeHom (coatomOf (D k)) :=
        coatomOf_endP_eq_cospikeHom (D k)
      have hbtDk : (⊥ : D k) ≠ (⊤ : D k) := bot_ne_top_of_nontrivial
      have hnb : (⊥ : EndP (D k)) ≠ coatomOf (EndP (D k)) := by
        rw [heq]
        intro hc
        have h1 : (⊥ : EndP (D k)) (⊤ : D k) = cospikeHom (coatomOf (D k)) (⊤ : D k) :=
          congrArg (· (⊤ : D k)) hc
        rw [endPBot_apply, cospikeHom_apply_of_ne _ hbtDk.symm] at h1
        exact hbtDk h1
      have hcm : coatomOf (EndP (D k)) ≠ markedPt k := by
        rw [heq]
        intro hc
        have h1 : cospikeHom (coatomOf (D k)) (⊤ : D k) = (markedPt k) (⊤ : D k) :=
          congrArg (· (⊤ : D k)) hc
        rw [cospikeHom_apply_of_ne _ hbtDk.symm, markedPt_apply] at h1
        exact dMid_ne_top k h1.symm
      glueUniqueAtomCoatom (P := EndP (D k)) (markedPt k) h.1 h.2.1 h.2.2 hnb hcm

end RecursiveTower

-- [D-0791] D0_rigid
theorem D0_rigid : Subsingleton (D 0 ≃o D 0) := finThree_rigid

-- [D-0792] D_top_hasUniqueDownCover
theorem D_top_hasUniqueDownCover (k : ℕ) : HasUniqueDownCover (⊤ : D k) :=
  letI := realUniqueAtomCoatom k
  hasUniqueDownCover_top

-- [D-0793] D_bot_hasUniqueUpCover
theorem D_bot_hasUniqueUpCover (k : ℕ) : HasUniqueUpCover (⊥ : D k) :=
  letI := realUniqueAtomCoatom k
  hasUniqueUpCover_bot

-- [D-0794] D_has_second_joinIrred
theorem D_has_second_joinIrred : ∀ k, ∃ y : D k, JoinIrred (D k) y ∧ y ≠ (⊤ : D k)
  | 0 => by
      show ∃ y : Fin 3, JoinIrred (Fin 3) y ∧ y ≠ (⊤ : Fin 3)
      exact ⟨1, ⟨by decide, by decide⟩, by decide⟩
  | k + 1 => by
      obtain ⟨y, hy_ji, _hy_ne⟩ := D_has_second_joinIrred k
      have h := D_marked_point_nondegenerate k
      have hy_udc : HasUniqueDownCover y := (hasUniqueDownCover_iff_joinIrred y).mpr hy_ji
      have hcy_udc : HasUniqueDownCover (constHom y : EndP (D k)) :=
        (hasUniqueDownCover_constHom_iff y).mpr hy_udc
      have hcy_ji : JoinIrred (EndP (D k)) (constHom y) :=
        (hasUniqueDownCover_iff_joinIrred (constHom y)).mp hcy_udc
      exact ⟨glueA (markedPt k) (constHom y),
        joinIrred_glueA_of_joinIrred (markedPt k) h.1 h.2.1 h.2.2
          (constHom y) hcy_ji,
        glueA_ne_top (markedPt k) h.1 h.2.1 h.2.2 (constHom y)⟩

-- [D-0795] D_card_ge_three
theorem D_card_ge_three (k : ℕ) : 3 ≤ Fintype.card (D k) := by
  obtain ⟨x, hxb, hxt⟩ := D_has_interior_point k
  have hbt : (⊥ : D k) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hcard3 : ({⊥, x, ⊤} : Finset (D k)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxb.symm, hbt]),
      Finset.card_insert_of_notMem (by simp [hxt]), Finset.card_singleton]
  calc (3 : ℕ) = ({⊥, x, ⊤} : Finset (D k)).card := hcard3.symm
    _ ≤ Fintype.card (D k) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)

-- [D-0796] D_mid_joinIrred
theorem D_mid_joinIrred : ∀ k, JoinIrred (D k) (dMid k)
  | 0 => by
      show JoinIrred (Fin 3) (1 : Fin 3)
      exact ⟨by decide, by decide⟩
  | k + 1 => by
      letI := realUniqueAtomCoatom k
      have h := D_marked_point_nondegenerate k
      show JoinIrred (D (k + 1)) (glueA (markedPt k) (constHom (dMid k)))
      exact (joinIrred_glueA_iff (markedPt k) h.1 h.2.1 h.2.2 (constHom (dMid k))).mpr
        ((joinIrred_constHom_iff (dMid k)).mpr (D_mid_joinIrred k))

-- [D-0797] card_joinIrred_D_succ
theorem card_joinIrred_D_succ (k : ℕ) :
    Fintype.card {x : D (k + 1) // JoinIrred (D (k + 1)) x} =
      3 * Fintype.card {x : D k // JoinIrred (D k) x} * Fintype.card (D k) - 2 := by
  letI := realUniqueAtomCoatom k
  have hbt : (⊥ : D k) ≠ ⊤ := bot_ne_top_of_nontrivial
  exact card_joinIrred_glueCar_endP_constHom (dMid k) (dMid_ne_bot k) (dMid_ne_top k)
    hbt (D_card_ge_three k) (D_mid_joinIrred k)

-- [D-0798] D_up_transfer
theorem D_up_transfer (k : ℕ) :
    Subsingleton (EndP (D k) ≃o EndP (D k)) → Subsingleton (D (k+1) ≃o D (k+1)) := by
  intro hEnd
  have h := D_marked_point_nondegenerate k
  have hp1 : ¬ (OrderHom.id : EndP (D k)) ≤ markedPt k := fun hc =>
    dMid_ne_top k (le_antisymm le_top (hc ⊤))
  have hp2 : ¬ markedPt k ≤ (OrderHom.id : EndP (D k)) := fun hc =>
    dMid_ne_bot k (le_bot_iff.mp (hc ⊥))
  exact glue_rigid_of_incomparable (P := EndP (D k)) (markedPt k) h.1 h.2.1 h.2.2
    hEnd (OrderHom.id) hp1 hp2

section H0Rigid

-- [D-0799] downCard
def downCard {α : Type*} [Fintype α] [Preorder α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] (z : α) : ℕ :=
  (Finset.univ.filter (· ≤ z)).card

-- [D-0800] upCard
def upCard {α : Type*} [Fintype α] [Preorder α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] (z : α) : ℕ :=
  (Finset.univ.filter (z ≤ ·)).card

-- [D-0801] downCard_map
theorem downCard_map {α : Type*} [Fintype α] [Preorder α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] (φ : α ≃o α) (z : α) :
    downCard (φ z) = downCard z := by
  unfold downCard
  have himg : Finset.univ.filter (· ≤ φ z) = (Finset.univ.filter (· ≤ z)).image φ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      have h2 : φ (φ.symm w) ≤ φ z := by rw [φ.apply_symm_apply]; exact h
      exact φ.le_iff_le.mp h2
    · rintro ⟨w', hw', rfl⟩; exact φ.le_iff_le.mpr hw'
  rw [himg, Finset.card_image_of_injective _ φ.injective]

-- [D-0802] upCard_map
theorem upCard_map {α : Type*} [Fintype α] [Preorder α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] (φ : α ≃o α) (z : α) :
    upCard (φ z) = upCard z := by
  unfold upCard
  have himg : Finset.univ.filter (φ z ≤ ·) = (Finset.univ.filter (z ≤ ·)).image φ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      have h2 : φ z ≤ φ (φ.symm w) := by rw [φ.apply_symm_apply]; exact h
      exact φ.le_iff_le.mp h2
    · rintro ⟨w', hw', rfl⟩; exact φ.le_iff_le.mpr hw'
  rw [himg, Finset.card_image_of_injective _ φ.injective]

-- [D-0803] endPFin3_inv_injective
theorem endPFin3_inv_injective :
    Function.Injective (fun f : EndP (Fin 3) => (downCard f, upCard f)) := by
  decide

-- [D-0804] H0_rigid_fixes
theorem H0_rigid_fixes (h : EndP (Fin 3) ≃o EndP (Fin 3)) (f : EndP (Fin 3)) :
    h f = f := by
  apply endPFin3_inv_injective
  simp only
  exact Prod.ext (downCard_map h f) (upCard_map h f)

-- [D-0805] H0_rigid
theorem H0_rigid : Subsingleton (EndP (Fin 3) ≃o EndP (Fin 3)) := by
  constructor
  intro f g
  apply OrderIso.ext
  funext x
  exact (H0_rigid_fixes f x).trans (H0_rigid_fixes g x).symm

end H0Rigid

-- [D-0806] D1_rigid
theorem D1_rigid : Subsingleton (D 1 ≃o D 1) := D_up_transfer 0 H0_rigid

-- [D-0807] D0_J_connected
theorem D0_J_connected : (Graph.Hasse {x : D 0 // JoinIrred (D 0) x}).Connected := by
  intro a b
  have htot : (a : D 0) ≤ (b : D 0) ∨ (b : D 0) ≤ (a : D 0) :=
    Fin.le_total (a.1 : Fin 3) (b.1 : Fin 3)
  rcases htot with hab | hba
  · exact connected_of_le_subtype' (JoinIrred (D 0)) a b hab
  · exact reflTransGen_symm_of_symm
      (fun x y hxy => (Graph.Hasse {x : D 0 // JoinIrred (D 0) x}).symm hxy)
      (connected_of_le_subtype' (JoinIrred (D 0)) b a hba)

-- [D-0808] D_J_connected
theorem D_J_connected : ∀ k, (Graph.Hasse {x : D k // JoinIrred (D k) x}).Connected
  | 0 => D0_J_connected
  | k + 1 => by
      have h := D_marked_point_nondegenerate k
      letI := realUniqueAtomCoatom k
      have hconn := hasse_hasUniqueDownCover_glueCar_connected
        (P := EndP (D k)) (markedPt k) h.1 h.2.1 h.2.2
      exact connected_of_pointwise_iff HasUniqueDownCover (JoinIrred (D (k + 1)))
        hasUniqueDownCover_iff_joinIrred hconn

-- [D-0809] D_down_transfer
theorem D_down_transfer (k : ℕ) :
    Subsingleton (D k ≃o D k) → Subsingleton (EndP (D k) ≃o EndP (D k)) := by
  intro hDk
  letI := realUniqueAtomCoatom k
  haveI : Nonempty {x : D k // JoinIrred (D k) x} :=
    ⟨⟨⊤, joinIrred_of_hasUniqueDownCover (D_top_hasUniqueDownCover k)⟩⟩
  have hJconn := D_J_connected k
  suffices hall : ∀ φ₀ : EndP (D k) ≃o EndP (D k), φ₀ = OrderIso.refl _ by
    exact ⟨fun a b => (hall a).trans (hall b).symm⟩
  intro φ₀
  set φ : {f : EndP (D k) // JoinIrred (EndP (D k)) f} ≃
      {f : EndP (D k) // JoinIrred (EndP (D k)) f} :=
    { toFun := fun x => ⟨φ₀ x.1, joinIrred_orderIso φ₀ x.2⟩
      invFun := fun x => ⟨φ₀.symm x.1, joinIrred_orderIso φ₀.symm x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp } with hφdef
  have hφval : ∀ x : {f : EndP (D k) // JoinIrred (EndP (D k)) f}, (φ x).1 = φ₀ x.1 := fun x => rfl
  have hφord : ∀ v w, v ≤ w ↔ φ v ≤ φ w := by
    intro v w
    show (v : EndP (D k)) ≤ w ↔ φ₀ v.1 ≤ φ₀ w.1
    exact φ₀.le_iff_le.symm
  let Φ : {f : EndP (D k) // JoinIrred (EndP (D k)) f} ≃o
      {f : EndP (D k) // JoinIrred (EndP (D k)) f} :=
    { toEquiv := φ, map_rel_iff' := fun {v w} => (hφord v w).symm }
  have hφadj : ∀ v w, (Graph.Hasse {f : EndP (D k) // JoinIrred (EndP (D k)) f}).adj v w ↔
      (Graph.Hasse {f : EndP (D k) // JoinIrred (EndP (D k)) f}).adj (φ v) (φ w) := by
    intro v w
    constructor
    · rintro (hc | hc)
      · exact Or.inl (covers_orderIso Φ hc)
      · exact Or.inr (covers_orderIso Φ hc)
    · rintro (hc | hc)
      · have hc' : Covers (Φ v) (Φ w) := hc
        have h2 := covers_orderIso Φ.symm hc'
        rw [Φ.symm_apply_apply, Φ.symm_apply_apply] at h2
        exact Or.inl h2
      · have hc' : Covers (Φ w) (Φ v) := hc
        have h2 := covers_orderIso Φ.symm hc'
        rw [Φ.symm_apply_apply, Φ.symm_apply_apply] at h2
        exact Or.inr h2
  obtain ⟨γA, γB, hγA_ord, hγB_ord, hdecomp⟩ := jh_product_order_level_full hJconn φ hφadj hφord
  have ΓA_map : ∀ a b : D k, a ≤ b ↔ γA a ≤ γA b := hγA_ord
  let ΓA : D k ≃o D k := { toEquiv := γA, map_rel_iff' := fun {a b} => (ΓA_map a b).symm }
  have hΓA_id : ΓA = OrderIso.refl (D k) := Subsingleton.elim _ _
  have hγA_id : ∀ q : D k, γA q = q := fun q => DFunLike.congr_fun hΓA_id q
  have hvert : ∀ (x : D k) (hx : JoinIrred (D k) x) (q : D k),
      φ₀ (stepMap x q) = stepMap (γB ⟨x, hx⟩).1 q := by
    intro x hx q
    have hd := hdecomp (q, ⟨x, hx⟩)
    have := congrArg Subtype.val hd
    simp only [hφdef, Equiv.coe_fn_mk, jiEquiv, Equiv.coe_fn_mk] at this
    rw [hγA_id q] at this
    exact this
  have hγB_ord' : ∀ b1 b2 : {x : D k // JoinIrred (D k) x}, b1 ≤ b2 ↔ γB b1 ≤ γB b2 := hγB_ord
  have ΓB_map : ∀ v v' : D k, v ≤ v' ↔ tauHat γB v ≤ tauHat γB v' :=
    fun v v' => (tauHat_le_iff γB φ₀ hvert v v').symm
  have hΓB_bij : Function.Bijective (tauHat γB) :=
    Finite.injective_iff_bijective.mp (tauHat_injective γB φ₀ hvert)
  let ΓB : D k ≃o D k :=
    { toEquiv := Equiv.ofBijective (tauHat γB) hΓB_bij,
      map_rel_iff' := fun {a b} => (ΓB_map a b).symm }
  have hΓB_id : ΓB = OrderIso.refl (D k) := Subsingleton.elim _ _
  have hγB_id : ∀ v : D k, tauHat γB v = v := fun v => DFunLike.congr_fun hΓB_id v
  have hγB_fix : ∀ x : {x : D k // JoinIrred (D k) x}, γB x = x := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have := hγB_id x
    rw [tauHat_eq_of_joinIrred γB hγB_ord' x hx] at this
    exact this
  have hφ_fix : ∀ f : {f : EndP (D k) // JoinIrred (EndP (D k)) f}, φ₀ f.1 = f.1 := by
    intro f
    set q := (jiEquiv.symm f).1 with hqdef
    set x := (jiEquiv.symm f).2 with hxdef
    have hf : jiEquiv (q, x) = f := by rw [hqdef, hxdef]; exact jiEquiv.apply_symm_apply f
    have hd := hdecomp (q, x)
    rw [hf] at hd
    have hval := congrArg Subtype.val hd
    simp only [hφdef, Equiv.coe_fn_mk] at hval
    rw [hval, hγA_id, hγB_fix, hf]
  apply orderIso_eq_of_joinIrred_eq
  intro q hq
  show φ₀ q = q
  exact hφ_fix ⟨q, hq⟩

-- [D-0810] realGluingTower
noncomputable instance realGluingTower :
    GluingTower D instLatticeD instBoundedOrderD instFintypeD where
  uac := realUniqueAtomCoatom
  base0_rigid := D0_rigid
  base1_rigid := D1_rigid

-- [D-0811] realGluingTowerUp
noncomputable instance realGluingTowerUp : GluingTowerUp D where
  up_transfer := D_up_transfer

-- [D-0812] realGluingTowerDown
noncomputable instance realGluingTowerDown : GluingTowerDown D where
  down_transfer := D_down_transfer

-- [D-0813] D_all_rigid
theorem D_all_rigid : ∀ k, Subsingleton (D k ≃o D k) :=
  aut_D_k_trivial D D0_rigid

section GasketIFS

open Metric TopologicalSpace

-- [D-0814] Plane
abbrev Plane := ℝ × ℝ

-- [D-0815] vA
def vA : Plane := (0, 0)
-- [D-0816] vB
def vB : Plane := (1, 0)
-- [D-0817] vC
def vC : Plane := (0, 1)

-- [D-0818] fA
noncomputable def fA (x : Plane) : Plane := (2⁻¹ : ℝ) • (x + vA)
-- [D-0819] fB
noncomputable def fB (x : Plane) : Plane := (2⁻¹ : ℝ) • (x + vB)
-- [D-0820] fC
noncomputable def fC (x : Plane) : Plane := (2⁻¹ : ℝ) • (x + vC)

-- [D-0821] dist_fA
theorem dist_fA (x y : Plane) : dist (fA x) (fA y) = 2⁻¹ * dist x y := by
  simp only [fA, dist_eq_norm]
  have : (2⁻¹ : ℝ) • (x + vA) - (2⁻¹ : ℝ) • (y + vA) = (2⁻¹ : ℝ) • (x - y) := by
    module
  rw [this, norm_smul]
  simp

-- [D-0822] dist_fB
theorem dist_fB (x y : Plane) : dist (fB x) (fB y) = 2⁻¹ * dist x y := by
  simp only [fB, dist_eq_norm]
  have : (2⁻¹ : ℝ) • (x + vB) - (2⁻¹ : ℝ) • (y + vB) = (2⁻¹ : ℝ) • (x - y) := by
    module
  rw [this, norm_smul]
  simp

-- [D-0823] dist_fC
theorem dist_fC (x y : Plane) : dist (fC x) (fC y) = 2⁻¹ * dist x y := by
  simp only [fC, dist_eq_norm]
  have : (2⁻¹ : ℝ) • (x + vC) - (2⁻¹ : ℝ) • (y + vC) = (2⁻¹ : ℝ) • (x - y) := by
    module
  rw [this, norm_smul]
  simp

-- [D-0824] lipschitzWith_fA
theorem lipschitzWith_fA : LipschitzWith (2⁻¹ : NNReal) fA :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [dist_fA]; norm_num

-- [D-0825] lipschitzWith_fB
theorem lipschitzWith_fB : LipschitzWith (2⁻¹ : NNReal) fB :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [dist_fB]; norm_num

-- [D-0826] lipschitzWith_fC
theorem lipschitzWith_fC : LipschitzWith (2⁻¹ : NNReal) fC :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [dist_fC]; norm_num

-- [D-0827] Delta
def Delta : Set Plane := {p : Plane | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

-- [D-0828] isClosed_Delta
theorem isClosed_Delta : IsClosed Delta := by
  have h1 : IsClosed {p : Plane | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : Plane | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : Plane | p.1 + p.2 ≤ 1} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  exact h1.inter (h2.inter h3)

-- [D-0829] isBounded_Delta
theorem isBounded_Delta : Bornology.IsBounded Delta := by
  have hball : Bornology.IsBounded (Metric.closedBall (0 : Plane) 1) :=
    Metric.isBounded_closedBall
  refine hball.subset (fun p hp => ?_)
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy, hxy⟩ := hp
  simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero]
  rw [sub_zero, sub_zero, abs_of_nonneg hx, abs_of_nonneg hy]
  exact max_le (by linarith) (by linarith)

-- [D-0830] isCompact_Delta
theorem isCompact_Delta : IsCompact Delta :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_Delta, isBounded_Delta⟩

-- [D-0831] nonempty_Delta
theorem nonempty_Delta : Delta.Nonempty := ⟨vA, by simp [Delta, vA]⟩

-- [D-0832] vA_mem_Delta
theorem vA_mem_Delta : vA ∈ Delta := by simp [Delta, vA]
-- [D-0833] vB_mem_Delta
theorem vB_mem_Delta : vB ∈ Delta := by simp [Delta, vB]
-- [D-0834] vC_mem_Delta
theorem vC_mem_Delta : vC ∈ Delta := by simp [Delta, vC]

-- [D-0835] image_fA_Delta
theorem image_fA_Delta :
    fA '' Delta = {q : Plane | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ 2⁻¹} := by
  ext ⟨qx, qy⟩
  simp only [Set.mem_image, Delta, Set.mem_setOf_eq, fA, vA, Prod.add_def, Prod.smul_mk,
    smul_eq_mul, add_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨px, py⟩, ⟨hpx, hpy, hpxy⟩, hqx, hqy⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hqx, hqy, hqxy⟩
    exact ⟨(2 * qx, 2 * qy), ⟨by linarith, by linarith, by linarith⟩, by ring, by ring⟩

-- [D-0836] image_fB_Delta
theorem image_fB_Delta :
    fB '' Delta = {q : Plane | 2⁻¹ ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ 1} := by
  ext ⟨qx, qy⟩
  simp only [Set.mem_image, Delta, Set.mem_setOf_eq, fB, vB, Prod.add_def, Prod.smul_mk,
    smul_eq_mul, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨px, py⟩, ⟨hpx, hpy, hpxy⟩, hqx, hqy⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hqx, hqy, hqxy⟩
    exact ⟨(2 * qx - 1, 2 * qy), ⟨by linarith, by linarith, by linarith⟩, by ring, by ring⟩

-- [D-0837] image_fC_Delta
theorem image_fC_Delta :
    fC '' Delta = {q : Plane | 0 ≤ q.1 ∧ 2⁻¹ ≤ q.2 ∧ q.1 + q.2 ≤ 1} := by
  ext ⟨qx, qy⟩
  simp only [Set.mem_image, Delta, Set.mem_setOf_eq, fC, vC, Prod.add_def, Prod.smul_mk,
    smul_eq_mul, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨px, py⟩, ⟨hpx, hpy, hpxy⟩, hqx, hqy⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hqx, hqy, hqxy⟩
    exact ⟨(2 * qx, 2 * qy - 1), ⟨by linarith, by linarith, by linarith⟩, by ring, by ring⟩

-- [D-0838] touch_fA_fB
theorem touch_fA_fB : fA '' Delta ∩ fB '' Delta = {(2⁻¹, 0)} := by
  rw [image_fA_Delta, image_fB_Delta]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx1, hy1, hxy1⟩, ⟨hx2, hy2, hxy2⟩⟩
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    subst hx; subst hy; norm_num

-- [D-0839] touch_fA_fC
theorem touch_fA_fC : fA '' Delta ∩ fC '' Delta = {(0, 2⁻¹)} := by
  rw [image_fA_Delta, image_fC_Delta]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx1, hy1, hxy1⟩, ⟨hx2, hy2, hxy2⟩⟩
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    subst hx; subst hy; norm_num

-- [D-0840] touch_fB_fC
theorem touch_fB_fC : fB '' Delta ∩ fC '' Delta = {(2⁻¹, 2⁻¹)} := by
  rw [image_fB_Delta, image_fC_Delta]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx1, hy1, hxy1⟩, ⟨hx2, hy2, hxy2⟩⟩
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    subst hx; subst hy; norm_num

-- [D-0841] §The-Hutchinson-operator-a-1-2-contraction
-- [D-0842] infDist_image_le_of_lipschitz
theorem infDist_image_le_of_lipschitz {K : NNReal} (hK : 0 < K) {f : Plane → Plane}
    (hf : LipschitzWith K f) (x : Plane) (s : Set Plane) (hs : s.Nonempty) :
    Metric.infDist (f x) (f '' s) ≤ (K : ℝ) * Metric.infDist x s := by
  have hbound : ∀ y ∈ s, Metric.infDist (f x) (f '' s) ≤ (K : ℝ) * dist x y := fun y hy =>
    (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem f hy)).trans (hf.dist_le_mul x y)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hle : Metric.infDist (f x) (f '' s) / (K : ℝ) ≤ Metric.infDist x s := by
    rw [Metric.le_infDist hs]
    intro y hy
    rw [div_le_iff₀ hKpos]
    simpa [mul_comm] using hbound y hy
  calc Metric.infDist (f x) (f '' s)
      = Metric.infDist (f x) (f '' s) / (K : ℝ) * (K : ℝ) := by field_simp
    _ ≤ Metric.infDist x s * (K : ℝ) := by
        apply mul_le_mul_of_nonneg_right hle hKpos.le
    _ = (K : ℝ) * Metric.infDist x s := mul_comm _ _

-- [D-0843] hausdorffDist_image_le_of_lipschitz
theorem hausdorffDist_image_le_of_lipschitz {K : NNReal} (hK : 0 < K) {f : Plane → Plane}
    (hf : LipschitzWith K f) {s t : Set Plane} (hs : s.Nonempty) (ht : t.Nonempty)
    (hsb : Bornology.IsBounded s) (htb : Bornology.IsBounded t) :
    Metric.hausdorffDist (f '' s) (f '' t) ≤ (K : ℝ) * Metric.hausdorffDist s t := by
  have hfin : Metric.hausdorffEDist s t ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hs ht hsb htb
  have hfin' : Metric.hausdorffEDist t s ≠ ⊤ := by rwa [Metric.hausdorffEDist_comm]
  apply Metric.hausdorffDist_le_of_infDist (mul_nonneg (by positivity) Metric.hausdorffDist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    calc Metric.infDist (f x) (f '' t)
        ≤ (K : ℝ) * Metric.infDist x t := infDist_image_le_of_lipschitz hK hf x t ht
      _ ≤ (K : ℝ) * Metric.hausdorffDist s t := by
          gcongr
          exact Metric.infDist_le_hausdorffDist_of_mem hx hfin
  · rintro _ ⟨y, hy, rfl⟩
    calc Metric.infDist (f y) (f '' s)
        ≤ (K : ℝ) * Metric.infDist y s := infDist_image_le_of_lipschitz hK hf y s hs
      _ ≤ (K : ℝ) * Metric.hausdorffDist s t := by
          gcongr
          rw [Metric.hausdorffDist_comm]
          exact Metric.infDist_le_hausdorffDist_of_mem hy hfin'

-- [D-0844] mapNC
def mapNC (f : Plane → Plane) (hf : Continuous f) (X : NonemptyCompacts Plane) :
    NonemptyCompacts Plane where
  carrier := f '' X.carrier
  isCompact' := X.isCompact.image hf
  nonempty' := X.nonempty.image f

-- [D-0845] coe_mapNC
theorem coe_mapNC (f : Plane → Plane) (hf : Continuous f) (X : NonemptyCompacts Plane) :
    (mapNC f hf X : Set Plane) = f '' (X : Set Plane) := rfl

-- [D-0846] lipschitzWith_mapNC
theorem lipschitzWith_mapNC {K : NNReal} (hK : 0 < K) {f : Plane → Plane} (hf : Continuous f)
    (hfL : LipschitzWith K f) : LipschitzWith K (mapNC f hf) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  rw [Metric.NonemptyCompacts.dist_eq, Metric.NonemptyCompacts.dist_eq, coe_mapNC, coe_mapNC]
  exact hausdorffDist_image_le_of_lipschitz hK hfL X.nonempty Y.nonempty
    X.isCompact.isBounded Y.isCompact.isBounded

-- [D-0847] dist_sup_le_max
theorem dist_sup_le_max (p q p' q' : NonemptyCompacts Plane) :
    dist (p ⊔ q) (p' ⊔ q') ≤ max (dist p p') (dist q q') := by
  have h := (NonemptyCompacts.lipschitz_sup (α := Plane)).dist_le_mul (p, q) (p', q')
  simpa [Prod.dist_eq] using h

-- [D-0848] Hutchinson
noncomputable def Hutchinson (X : NonemptyCompacts Plane) : NonemptyCompacts Plane :=
  mapNC fA lipschitzWith_fA.continuous X ⊔ mapNC fB lipschitzWith_fB.continuous X ⊔
    mapNC fC lipschitzWith_fC.continuous X

-- [D-0849] hutchinson_dist_le
theorem hutchinson_dist_le (X Y : NonemptyCompacts Plane) :
    dist (Hutchinson X) (Hutchinson Y) ≤ 2⁻¹ * dist X Y := by
  have hA : dist (mapNC fA lipschitzWith_fA.continuous X) (mapNC fA lipschitzWith_fA.continuous Y)
      ≤ 2⁻¹ * dist X Y := (lipschitzWith_mapNC (by norm_num) lipschitzWith_fA.continuous
        lipschitzWith_fA).dist_le_mul X Y
  have hB : dist (mapNC fB lipschitzWith_fB.continuous X) (mapNC fB lipschitzWith_fB.continuous Y)
      ≤ 2⁻¹ * dist X Y := (lipschitzWith_mapNC (by norm_num) lipschitzWith_fB.continuous
        lipschitzWith_fB).dist_le_mul X Y
  have hC : dist (mapNC fC lipschitzWith_fC.continuous X) (mapNC fC lipschitzWith_fC.continuous Y)
      ≤ 2⁻¹ * dist X Y := (lipschitzWith_mapNC (by norm_num) lipschitzWith_fC.continuous
        lipschitzWith_fC).dist_le_mul X Y
  have hAB : dist (mapNC fA lipschitzWith_fA.continuous X ⊔ mapNC fB lipschitzWith_fB.continuous X)
      (mapNC fA lipschitzWith_fA.continuous Y ⊔ mapNC fB lipschitzWith_fB.continuous Y)
      ≤ 2⁻¹ * dist X Y := (dist_sup_le_max _ _ _ _).trans (max_le hA hB)
  set CX := mapNC fC lipschitzWith_fC.continuous X
  set CY := mapNC fC lipschitzWith_fC.continuous Y
  set ABX := mapNC fA lipschitzWith_fA.continuous X ⊔ mapNC fB lipschitzWith_fB.continuous X
  set ABY := mapNC fA lipschitzWith_fA.continuous Y ⊔ mapNC fB lipschitzWith_fB.continuous Y
  calc dist (Hutchinson X) (Hutchinson Y)
      ≤ max (dist ABX ABY) (dist CX CY) := dist_sup_le_max _ _ _ _
    _ ≤ 2⁻¹ * dist X Y := max_le hAB hC

-- [D-0850] lipschitzWith_hutchinson
theorem lipschitzWith_hutchinson : LipschitzWith (2⁻¹ : NNReal) Hutchinson :=
  LipschitzWith.of_dist_le_mul hutchinson_dist_le

-- [D-0851] contractingWith_hutchinson
theorem contractingWith_hutchinson : ContractingWith (2⁻¹ : NNReal) Hutchinson :=
  ⟨by norm_num, lipschitzWith_hutchinson⟩

-- [D-0852] inst-Nonempty
instance : Nonempty (NonemptyCompacts Plane) := ⟨{
  carrier := {vA}
  isCompact' := isCompact_singleton
  nonempty' := Set.singleton_nonempty vA }⟩

-- [D-0853] GammaNC
noncomputable def GammaNC : NonemptyCompacts Plane := contractingWith_hutchinson.fixedPoint

-- [D-0854] GammaNC_fixed
theorem GammaNC_fixed : Hutchinson GammaNC = GammaNC :=
  contractingWith_hutchinson.fixedPoint_isFixedPt

-- [D-0855] Gamma
def Gamma : Set Plane := (GammaNC : Set Plane)

-- [D-0856] isCompact_Gamma
theorem isCompact_Gamma : IsCompact Gamma := GammaNC.isCompact
-- [D-0857] nonempty_Gamma
theorem nonempty_Gamma : Gamma.Nonempty := GammaNC.nonempty

-- [D-0858] Gamma_self_similar
theorem Gamma_self_similar : Gamma = fA '' Gamma ∪ fB '' Gamma ∪ fC '' Gamma := by
  conv_lhs => rw [Gamma, ← GammaNC_fixed]
  rfl

end GasketIFS

-- [D-0859] iotaD
noncomputable def iotaD (k : ℕ) (x : D k) : D (k + 1) :=
  glueA (markedPt k) (constHom x)

-- [D-0860] iotaD_le_iff
theorem iotaD_le_iff (k : ℕ) (x y : D k) : iotaD k x ≤ iotaD k y ↔ x ≤ y :=
  (glueA_le_iff (markedPt k) (D_marked_point_nondegenerate k).1
      (constHom x) (constHom y)).trans (constHom_le_iff x y)

-- [D-0861] iotaD_injective
theorem iotaD_injective (k : ℕ) : Function.Injective (iotaD k) := by
  intro x y h
  exact constHom_injective (glueA_injective (markedPt k) h)

-- [D-0862] iotaD_monotone
theorem iotaD_monotone (k : ℕ) : Monotone (iotaD k) := fun x y h =>
  (iotaD_le_iff k x y).mpr h

-- [D-0863] iotaD_lt_iff
theorem iotaD_lt_iff (k : ℕ) (x y : D k) : iotaD k x < iotaD k y ↔ x < y := by
  constructor
  · intro h
    refine lt_of_le_of_ne ((iotaD_le_iff k x y).mp h.le) (fun heq => h.ne ?_)
    rw [heq]
  · intro h
    exact lt_of_le_of_ne ((iotaD_le_iff k x y).mpr h.le)
      (fun heq => h.ne (iotaD_injective k heq))

-- [D-0864] iotaD_strictMono
theorem iotaD_strictMono (k : ℕ) : StrictMono (iotaD k) := fun x y h =>
  (iotaD_lt_iff k x y).mpr h

-- [D-0865] iotaD_sup
theorem iotaD_sup (k : ℕ) (x y : D k) : iotaD k x ⊔ iotaD k y = iotaD k (x ⊔ y) := by
  have h := D_marked_point_nondegenerate k
  letI := glueLattice (markedPt k) h.1 h.2.1 h.2.2
  show glueA (markedPt k) (constHom x) ⊔ glueA (markedPt k) (constHom y)
      = glueA (markedPt k) (constHom (x ⊔ y))
  rw [glueA_sup (markedPt k) h.1 h.2.1 h.2.2, constHom_sup]

-- [D-0866] iotaD_inf
theorem iotaD_inf (k : ℕ) (x y : D k) : iotaD k x ⊓ iotaD k y = iotaD k (x ⊓ y) := by
  have h := D_marked_point_nondegenerate k
  letI := glueLattice (markedPt k) h.1 h.2.1 h.2.2
  show glueA (markedPt k) (constHom x) ⊓ glueA (markedPt k) (constHom y)
      = glueA (markedPt k) (constHom (x ⊓ y))
  rw [glueA_inf (markedPt k) h.1 h.2.1 h.2.2, constHom_inf]

-- [D-0867] sigmaD
noncomputable def sigmaD (k : ℕ) (x : D k) : D (k + 1) :=
  glueA (markedPt k) (meetHom x)

-- [D-0868] sigmaD_le_iff
theorem sigmaD_le_iff (k : ℕ) (x y : D k) : sigmaD k x ≤ sigmaD k y ↔ x ≤ y :=
  (glueA_le_iff (markedPt k) (D_marked_point_nondegenerate k).1
      (meetHom x) (meetHom y)).trans (meetHom_le_iff x y)

-- [D-0869] sigmaD_injective
theorem sigmaD_injective (k : ℕ) : Function.Injective (sigmaD k) := by
  intro x y h
  exact meetHom_injective (glueA_injective (markedPt k) h)

-- [D-0870] sigmaD_monotone
theorem sigmaD_monotone (k : ℕ) : Monotone (sigmaD k) := fun x y h =>
  (sigmaD_le_iff k x y).mpr h

-- [D-0871] sigmaD_lt_iff
theorem sigmaD_lt_iff (k : ℕ) (x y : D k) : sigmaD k x < sigmaD k y ↔ x < y := by
  constructor
  · intro h
    refine lt_of_le_of_ne ((sigmaD_le_iff k x y).mp h.le) (fun heq => h.ne ?_)
    rw [heq]
  · intro h
    exact lt_of_le_of_ne ((sigmaD_le_iff k x y).mpr h.le)
      (fun heq => h.ne (sigmaD_injective k heq))

-- [D-0872] sigmaD_strictMono
theorem sigmaD_strictMono (k : ℕ) : StrictMono (sigmaD k) := fun x y h =>
  (sigmaD_lt_iff k x y).mpr h

-- [D-0873] sigmaD_top
theorem sigmaD_top (k : ℕ) :
    sigmaD k (⊤ : D k) = glueA (markedPt k) (OrderHom.id : EndP (D k)) := by
  unfold sigmaD; rw [meetHom_top]

-- [D-0874] sigmaD_bot_eq_iotaD_bot
theorem sigmaD_bot_eq_iotaD_bot (k : ℕ) : sigmaD k (⊥ : D k) = iotaD k (⊥ : D k) := by
  unfold sigmaD iotaD; rw [meetHom_bot]

section DInftyColimit

-- [D-0875] iotaLe
noncomputable def iotaLe {k n : ℕ} (h : k ≤ n) : D k → D n :=
  Nat.leRecOn h (fun {j} => iotaD j)

-- [D-0876] iotaLe_self
theorem iotaLe_self {k : ℕ} (h : k ≤ k) (x : D k) : iotaLe h x = x :=
  Nat.leRecOn_self x

-- [D-0877] iotaLe_succ
theorem iotaLe_succ {k n : ℕ} (h : k ≤ n) (h' : k ≤ n + 1) (x : D k) :
    iotaLe h' x = iotaD n (iotaLe h x) :=
  Nat.leRecOn_succ h x

-- [D-0878] iotaLe_trans
theorem iotaLe_trans {k n m : ℕ} (h1 : k ≤ n) (h2 : n ≤ m) (x : D k) :
    iotaLe (h1.trans h2) x = iotaLe h2 (iotaLe h1 x) :=
  Nat.leRecOn_trans h1 h2 x

-- [D-0879] iotaLe_le_iff
theorem iotaLe_le_iff {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n) (x y : D k),
    iotaLe h x ≤ iotaLe h y ↔ x ≤ y := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x y; rw [iotaLe_self, iotaLe_self]
  | succ n hkn ih =>
      intro x y
      rw [iotaLe_succ hkn (Nat.le_succ_of_le hkn), iotaLe_succ hkn (Nat.le_succ_of_le hkn)]
      rw [iotaD_le_iff]
      exact ih x y

-- [D-0880] iotaLe_injective
theorem iotaLe_injective {k n : ℕ} (h : k ≤ n) : Function.Injective (iotaLe h) := by
  intro x y hxy
  exact (iotaLe_le_iff h x y).mp hxy.le |>.antisymm ((iotaLe_le_iff h y x).mp hxy.ge)

-- [D-0881] iotaLe_sup
theorem iotaLe_sup {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n) (x y : D k),
    iotaLe h x ⊔ iotaLe h y = iotaLe h (x ⊔ y) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x y; rw [iotaLe_self, iotaLe_self, iotaLe_self]
  | succ n hkn ih =>
      intro x y
      rw [iotaLe_succ hkn (Nat.le_succ_of_le hkn), iotaLe_succ hkn (Nat.le_succ_of_le hkn),
          iotaLe_succ hkn (Nat.le_succ_of_le hkn), iotaD_sup]
      congr 1
      exact ih x y

-- [D-0882] iotaLe_inf
theorem iotaLe_inf {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n) (x y : D k),
    iotaLe h x ⊓ iotaLe h y = iotaLe h (x ⊓ y) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x y; rw [iotaLe_self, iotaLe_self, iotaLe_self]
  | succ n hkn ih =>
      intro x y
      rw [iotaLe_succ hkn (Nat.le_succ_of_le hkn), iotaLe_succ hkn (Nat.le_succ_of_le hkn),
          iotaLe_succ hkn (Nat.le_succ_of_le hkn), iotaD_inf]
      congr 1
      exact ih x y

-- [D-0883] §The-colimit-relation-on-k-D-k
-- [D-0884] DInftyRel
def DInftyRel (p q : Σ k, D k) : Prop :=
  ∃ (n : ℕ) (h1 : p.1 ≤ n) (h2 : q.1 ≤ n), iotaLe h1 p.2 = iotaLe h2 q.2

-- [D-0885] chase_eq_level_indep
theorem chase_eq_level_indep {k k' n n' : ℕ} (h : k ≤ n) (h' : k' ≤ n)
    (hn : n ≤ n') (h2 : k ≤ n') (h2' : k' ≤ n') (x : D k) (y : D k')
    (he : iotaLe h x = iotaLe h' y) : iotaLe h2 x = iotaLe h2' y := by
  rw [iotaLe_trans h hn x, iotaLe_trans h' hn y, he]

-- [D-0886] chase_eq_of_rel
theorem chase_eq_of_rel {a c : Σ k, D k} (h : DInftyRel a c) {N : ℕ}
    (ha : a.1 ≤ N) (hc : c.1 ≤ N) : iotaLe ha a.2 = iotaLe hc c.2 := by
  obtain ⟨m, hm, hm', he⟩ := h
  rcases le_total N m with hNm | hmN
  · apply iotaLe_injective hNm
    have e1 : iotaLe hNm (iotaLe ha a.2) = iotaLe hm a.2 := (iotaLe_trans ha hNm a.2).symm
    have e2 : iotaLe hNm (iotaLe hc c.2) = iotaLe hm' c.2 := (iotaLe_trans hc hNm c.2).symm
    rw [e1, e2, he]
  · exact chase_eq_level_indep hm hm' hmN ha hc a.2 c.2 he

-- [D-0887] DInftyRel_refl
theorem DInftyRel_refl (p : Σ k, D k) : DInftyRel p p :=
  ⟨p.1, le_refl p.1, le_refl p.1, rfl⟩

-- [D-0888] DInftyRel_symm
theorem DInftyRel_symm {p q : Σ k, D k} (h : DInftyRel p q) : DInftyRel q p := by
  obtain ⟨n, h1, h2, he⟩ := h
  exact ⟨n, h2, h1, he.symm⟩

-- [D-0889] DInftyRel_trans
theorem DInftyRel_trans {p q r : Σ k, D k} (hpq : DInftyRel p q) (hqr : DInftyRel q r) :
    DInftyRel p r := by
  obtain ⟨n, h1, h2, he1⟩ := hpq
  obtain ⟨n', h2', h3, he2⟩ := hqr
  refine ⟨max n n', h1.trans (le_max_left n n'), h3.trans (le_max_right n n'), ?_⟩
  have key1 : iotaLe (h1.trans (le_max_left n n')) p.2 = iotaLe (h2.trans (le_max_left n n')) q.2 :=
    chase_eq_level_indep h1 h2 (le_max_left n n') _ _ p.2 q.2 he1
  have key2 : iotaLe (h2'.trans (le_max_right n n')) q.2 = iotaLe (h3.trans (le_max_right n n')) r.2 :=
    chase_eq_level_indep h2' h3 (le_max_right n n') _ _ q.2 r.2 he2
  exact key1.trans key2

-- [D-0890] dInftySetoid
instance dInftySetoid : Setoid (Σ k, D k) where
  r := DInftyRel
  iseqv := ⟨DInftyRel_refl, DInftyRel_symm, DInftyRel_trans⟩

-- [D-0891] DInfty
def DInfty : Type := Quotient dInftySetoid

-- [D-0892] §Canonical-inclusions-D-k-D
-- [D-0893] toD
noncomputable def toD (k : ℕ) (x : D k) : DInfty := Quotient.mk dInftySetoid ⟨k, x⟩

-- [D-0894] toD_iotaD
theorem toD_iotaD (k : ℕ) (x : D k) : toD (k + 1) (iotaD k x) = toD k x := by
  apply Quotient.sound
  refine ⟨k + 1, le_refl (k + 1), Nat.le_succ k, ?_⟩
  rw [iotaLe_self, iotaLe_succ (le_refl k) (Nat.le_succ k), iotaLe_self]

-- [D-0895] toD_injective
theorem toD_injective (k : ℕ) : Function.Injective (toD k) := by
  intro x y hxy
  obtain ⟨n, h1, h2, he⟩ := Quotient.exact hxy
  exact iotaLe_injective h1 (by rw [he])

-- [D-0896] toD_surjective
theorem toD_surjective : ∀ z : DInfty, ∃ k x, toD k x = z := by
  intro z
  obtain ⟨p, hp⟩ := Quotient.exists_rep z
  exact ⟨p.1, p.2, hp⟩

-- [D-0897] §The-order-on-D
-- [D-0898] DInftyLeRel
def DInftyLeRel (p q : Σ k, D k) : Prop :=
  iotaLe (le_max_left p.1 q.1) p.2 ≤ iotaLe (le_max_right p.1 q.1) q.2

-- [D-0899] DInftyLeRel_iff_atLevel
theorem DInftyLeRel_iff_atLevel {p q : Σ k, D k} {N : ℕ} (hp : p.1 ≤ N) (hq : q.1 ≤ N) :
    DInftyLeRel p q ↔ iotaLe hp p.2 ≤ iotaLe hq q.2 := by
  unfold DInftyLeRel
  set N0 := max p.1 q.1 with hN0
  rcases le_total N0 N with h | h
  · rw [show iotaLe hp p.2 = iotaLe h (iotaLe (le_max_left p.1 q.1) p.2) from
        (iotaLe_trans (le_max_left p.1 q.1) h p.2),
      show iotaLe hq q.2 = iotaLe h (iotaLe (le_max_right p.1 q.1) q.2) from
        (iotaLe_trans (le_max_right p.1 q.1) h q.2),
      iotaLe_le_iff h]
  · rw [show iotaLe (le_max_left p.1 q.1) p.2 = iotaLe h (iotaLe hp p.2) from
        (iotaLe_trans hp h p.2),
      show iotaLe (le_max_right p.1 q.1) q.2 = iotaLe h (iotaLe hq q.2) from
        (iotaLe_trans hq h q.2),
      iotaLe_le_iff h]

-- [D-0900] DInftyLeRel_congr
theorem DInftyLeRel_congr {a b c d : Σ k, D k} (hac : DInftyRel a c) (hbd : DInftyRel b d) :
    DInftyLeRel a b ↔ DInftyLeRel c d := by
  set N := max (max a.1 b.1) (max c.1 d.1) with hN
  have haN : a.1 ≤ N := le_trans (le_max_left a.1 b.1) (le_max_left _ _)
  have hbN : b.1 ≤ N := le_trans (le_max_right a.1 b.1) (le_max_left _ _)
  have hcN : c.1 ≤ N := le_trans (le_max_left c.1 d.1) (le_max_right _ _)
  have hdN : d.1 ≤ N := le_trans (le_max_right c.1 d.1) (le_max_right _ _)
  rw [DInftyLeRel_iff_atLevel haN hbN, DInftyLeRel_iff_atLevel hcN hdN,
      chase_eq_of_rel hac haN hcN, chase_eq_of_rel hbd hbN hdN]

-- [D-0901] DInftyLE
def DInftyLE : DInfty → DInfty → Prop :=
  Quotient.lift₂ DInftyLeRel (fun _a _b _c _d hac hbd => propext (DInftyLeRel_congr hac hbd))

-- [D-0902] inst-LE
noncomputable instance : LE DInfty := ⟨DInftyLE⟩

-- [D-0903] toD_le_iff
theorem toD_le_iff (k n : ℕ) (x : D k) (y : D n) {N : ℕ} (hx : k ≤ N) (hy : n ≤ N) :
    toD k x ≤ toD n y ↔ iotaLe hx x ≤ iotaLe hy y :=
  DInftyLeRel_iff_atLevel hx hy

-- [D-0904] inst-PartialOrder
noncomputable instance : PartialOrder DInfty where
  le := DInftyLE
  le_refl := by
    intro z
    induction z using Quotient.inductionOn with
    | _ p => exact (DInftyLeRel_iff_atLevel (le_refl p.1) (le_refl p.1)).mpr (le_refl _)
  le_trans := by
    intro x y z
    induction x using Quotient.inductionOn with | _ p =>
    induction y using Quotient.inductionOn with | _ q =>
    induction z using Quotient.inductionOn with | _ r =>
    intro hxy hyz
    set N := max (max p.1 q.1) r.1 with hN
    have hpN : p.1 ≤ N := le_trans (le_max_left p.1 q.1) (le_max_left _ _)
    have hqN : q.1 ≤ N := le_trans (le_max_right p.1 q.1) (le_max_left _ _)
    have hrN : r.1 ≤ N := le_max_right _ _
    have h1 := (DInftyLeRel_iff_atLevel hpN hqN).mp hxy
    have h2 := (DInftyLeRel_iff_atLevel hqN hrN).mp hyz
    exact (DInftyLeRel_iff_atLevel hpN hrN).mpr (h1.trans h2)
  le_antisymm := by
    intro x y
    induction x using Quotient.inductionOn with | _ p =>
    induction y using Quotient.inductionOn with | _ q =>
    intro hxy hyx
    set N := max p.1 q.1 with hN
    have hpN : p.1 ≤ N := le_max_left _ _
    have hqN : q.1 ≤ N := le_max_right _ _
    have h1 := (DInftyLeRel_iff_atLevel hpN hqN).mp hxy
    have h2 := (DInftyLeRel_iff_atLevel hqN hpN).mp hyx
    exact Quotient.sound ⟨N, hpN, hqN, le_antisymm h1 h2⟩

-- [D-0905] toD_le_iff'
theorem toD_le_iff' (k : ℕ) (x y : D k) : toD k x ≤ toD k y ↔ x ≤ y := by
  have := toD_le_iff k k x y (le_refl k) (le_refl k)
  rwa [iotaLe_self, iotaLe_self] at this

-- [D-0906] toD_strictMono
theorem toD_strictMono (k : ℕ) : StrictMono (toD k) := by
  intro x y h
  refine lt_of_le_of_ne ((toD_le_iff' k x y).mpr h.le) (fun heq => h.ne ?_)
  exact toD_injective k heq

-- [D-0907] §Giving-D-a-Lattice-structure-2026-08-20-session
-- [D-0908] toD_iotaLe
theorem toD_iotaLe {k n : ℕ} (h : k ≤ n) (x : D k) : toD n (iotaLe h x) = toD k x :=
  Quotient.sound ⟨n, le_refl n, h, iotaLe_self (le_refl n) (iotaLe h x)⟩

-- [D-0909] DInftySupRep
noncomputable def DInftySupRep (p q : Σ k, D k) : DInfty :=
  toD (max p.1 q.1) (iotaLe (le_max_left p.1 q.1) p.2 ⊔ iotaLe (le_max_right p.1 q.1) q.2)

-- [D-0910] DInftySupRep_atLevel
theorem DInftySupRep_atLevel {p q : Σ k, D k} {N : ℕ} (hp : p.1 ≤ N) (hq : q.1 ≤ N) :
    DInftySupRep p q = toD N (iotaLe hp p.2 ⊔ iotaLe hq q.2) := by
  unfold DInftySupRep
  set N0 := max p.1 q.1 with hN0
  rcases le_total N0 N with h | h
  · rw [show iotaLe hp p.2 = iotaLe h (iotaLe (le_max_left p.1 q.1) p.2) from
        (iotaLe_trans (le_max_left p.1 q.1) h p.2),
      show iotaLe hq q.2 = iotaLe h (iotaLe (le_max_right p.1 q.1) q.2) from
        (iotaLe_trans (le_max_right p.1 q.1) h q.2),
      iotaLe_sup, toD_iotaLe]
  · rw [show iotaLe (le_max_left p.1 q.1) p.2 = iotaLe h (iotaLe hp p.2) from
        (iotaLe_trans hp h p.2),
      show iotaLe (le_max_right p.1 q.1) q.2 = iotaLe h (iotaLe hq q.2) from
        (iotaLe_trans hq h q.2),
      iotaLe_sup, toD_iotaLe]

-- [D-0911] DInftySupRep_congr
theorem DInftySupRep_congr {a b c d : Σ k, D k} (hac : DInftyRel a c) (hbd : DInftyRel b d) :
    DInftySupRep a b = DInftySupRep c d := by
  set N := max (max a.1 b.1) (max c.1 d.1) with hN
  have haN : a.1 ≤ N := le_trans (le_max_left a.1 b.1) (le_max_left _ _)
  have hbN : b.1 ≤ N := le_trans (le_max_right a.1 b.1) (le_max_left _ _)
  have hcN : c.1 ≤ N := le_trans (le_max_left c.1 d.1) (le_max_right _ _)
  have hdN : d.1 ≤ N := le_trans (le_max_right c.1 d.1) (le_max_right _ _)
  rw [DInftySupRep_atLevel haN hbN, DInftySupRep_atLevel hcN hdN,
      chase_eq_of_rel hac haN hcN, chase_eq_of_rel hbd hbN hdN]

-- [D-0912] DInftySup
noncomputable def DInftySup : DInfty → DInfty → DInfty :=
  Quotient.lift₂ DInftySupRep (fun _a _b _c _d hac hbd => DInftySupRep_congr hac hbd)

-- [D-0913] inst-Max
noncomputable instance : Max DInfty := ⟨DInftySup⟩

-- [D-0914] toD_sup
theorem toD_sup (k n : ℕ) (x : D k) (y : D n) {N : ℕ} (hx : k ≤ N) (hy : n ≤ N) :
    toD k x ⊔ toD n y = toD N (iotaLe hx x ⊔ iotaLe hy y) :=
  DInftySupRep_atLevel hx hy

-- [D-0915] toD_sup'
theorem toD_sup' (k : ℕ) (x y : D k) : toD k x ⊔ toD k y = toD k (x ⊔ y) := by
  have := toD_sup k k x y (le_refl k) (le_refl k)
  rwa [iotaLe_self, iotaLe_self] at this

-- [D-0916] DInftySup_le_left
theorem DInftySup_le_left (a b : DInfty) : a ≤ a ⊔ b := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  rw [toD_sup k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff k (max k n) x _ (le_max_left k n) (le_refl (max k n)), iotaLe_self]
  exact le_sup_left

-- [D-0917] DInftySup_le_right
theorem DInftySup_le_right (a b : DInfty) : b ≤ a ⊔ b := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  rw [toD_sup k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff n (max k n) y _ (le_max_right k n) (le_refl (max k n)), iotaLe_self]
  exact le_sup_right

-- [D-0918] DInftySup_le
theorem DInftySup_le (a b c : DInfty) (hac : a ≤ c) (hbc : b ≤ c) : a ⊔ b ≤ c := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  obtain ⟨p, z, rfl⟩ := toD_surjective c
  set N := max (max k n) p with hN
  have hkN : k ≤ N := le_trans (le_max_left k n) (le_max_left _ _)
  have hnN : n ≤ N := le_trans (le_max_right k n) (le_max_left _ _)
  have hpN : p ≤ N := le_max_right _ _
  have hxz : iotaLe hkN x ≤ iotaLe hpN z := (toD_le_iff k p x z hkN hpN).mp hac
  have hyz : iotaLe hnN y ≤ iotaLe hpN z := (toD_le_iff n p y z hnN hpN).mp hbc
  have hmn : max k n ≤ N := le_max_left _ _
  have heqx : iotaLe hkN x = iotaLe hmn (iotaLe (le_max_left k n) x) :=
    iotaLe_trans (le_max_left k n) hmn x
  have heqy : iotaLe hnN y = iotaLe hmn (iotaLe (le_max_right k n) y) :=
    iotaLe_trans (le_max_right k n) hmn y
  rw [toD_sup k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff (max k n) p _ z hmn hpN, ← iotaLe_sup, ← heqx, ← heqy]
  exact sup_le hxz hyz

-- [D-0919] inst-SemilatticeSup
noncomputable instance : SemilatticeSup DInfty :=
  { (inferInstance : PartialOrder DInfty) with
    sup := DInftySup
    le_sup_left := DInftySup_le_left
    le_sup_right := DInftySup_le_right
    sup_le := DInftySup_le }

-- [D-0920] DInftyInfRep
noncomputable def DInftyInfRep (p q : Σ k, D k) : DInfty :=
  toD (max p.1 q.1) (iotaLe (le_max_left p.1 q.1) p.2 ⊓ iotaLe (le_max_right p.1 q.1) q.2)

-- [D-0921] DInftyInfRep_atLevel
theorem DInftyInfRep_atLevel {p q : Σ k, D k} {N : ℕ} (hp : p.1 ≤ N) (hq : q.1 ≤ N) :
    DInftyInfRep p q = toD N (iotaLe hp p.2 ⊓ iotaLe hq q.2) := by
  unfold DInftyInfRep
  set N0 := max p.1 q.1 with hN0
  rcases le_total N0 N with h | h
  · rw [show iotaLe hp p.2 = iotaLe h (iotaLe (le_max_left p.1 q.1) p.2) from
        (iotaLe_trans (le_max_left p.1 q.1) h p.2),
      show iotaLe hq q.2 = iotaLe h (iotaLe (le_max_right p.1 q.1) q.2) from
        (iotaLe_trans (le_max_right p.1 q.1) h q.2),
      iotaLe_inf, toD_iotaLe]
  · rw [show iotaLe (le_max_left p.1 q.1) p.2 = iotaLe h (iotaLe hp p.2) from
        (iotaLe_trans hp h p.2),
      show iotaLe (le_max_right p.1 q.1) q.2 = iotaLe h (iotaLe hq q.2) from
        (iotaLe_trans hq h q.2),
      iotaLe_inf, toD_iotaLe]

-- [D-0922] DInftyInfRep_congr
theorem DInftyInfRep_congr {a b c d : Σ k, D k} (hac : DInftyRel a c) (hbd : DInftyRel b d) :
    DInftyInfRep a b = DInftyInfRep c d := by
  set N := max (max a.1 b.1) (max c.1 d.1) with hN
  have haN : a.1 ≤ N := le_trans (le_max_left a.1 b.1) (le_max_left _ _)
  have hbN : b.1 ≤ N := le_trans (le_max_right a.1 b.1) (le_max_left _ _)
  have hcN : c.1 ≤ N := le_trans (le_max_left c.1 d.1) (le_max_right _ _)
  have hdN : d.1 ≤ N := le_trans (le_max_right c.1 d.1) (le_max_right _ _)
  rw [DInftyInfRep_atLevel haN hbN, DInftyInfRep_atLevel hcN hdN,
      chase_eq_of_rel hac haN hcN, chase_eq_of_rel hbd hbN hdN]

-- [D-0923] DInftyInf
noncomputable def DInftyInf : DInfty → DInfty → DInfty :=
  Quotient.lift₂ DInftyInfRep (fun _a _b _c _d hac hbd => DInftyInfRep_congr hac hbd)

-- [D-0924] inst-Min
noncomputable instance : Min DInfty := ⟨DInftyInf⟩

-- [D-0925] toD_inf
theorem toD_inf (k n : ℕ) (x : D k) (y : D n) {N : ℕ} (hx : k ≤ N) (hy : n ≤ N) :
    toD k x ⊓ toD n y = toD N (iotaLe hx x ⊓ iotaLe hy y) :=
  DInftyInfRep_atLevel hx hy

-- [D-0926] toD_inf'
theorem toD_inf' (k : ℕ) (x y : D k) : toD k x ⊓ toD k y = toD k (x ⊓ y) := by
  have := toD_inf k k x y (le_refl k) (le_refl k)
  rwa [iotaLe_self, iotaLe_self] at this

-- [D-0927] DInftyInf_le_left
theorem DInftyInf_le_left (a b : DInfty) : a ⊓ b ≤ a := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  rw [toD_inf k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff (max k n) k _ x (le_refl (max k n)) (le_max_left k n), iotaLe_self]
  exact inf_le_left

-- [D-0928] DInftyInf_le_right
theorem DInftyInf_le_right (a b : DInfty) : a ⊓ b ≤ b := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  rw [toD_inf k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff (max k n) n _ y (le_refl (max k n)) (le_max_right k n), iotaLe_self]
  exact inf_le_right

-- [D-0929] DInftyLe_inf
theorem DInftyLe_inf (c a b : DInfty) (hca : c ≤ a) (hcb : c ≤ b) : c ≤ a ⊓ b := by
  obtain ⟨k, x, rfl⟩ := toD_surjective a
  obtain ⟨n, y, rfl⟩ := toD_surjective b
  obtain ⟨p, z, rfl⟩ := toD_surjective c
  set N := max (max k n) p with hN
  have hkN : k ≤ N := le_trans (le_max_left k n) (le_max_left _ _)
  have hnN : n ≤ N := le_trans (le_max_right k n) (le_max_left _ _)
  have hpN : p ≤ N := le_max_right _ _
  have hzx : iotaLe hpN z ≤ iotaLe hkN x := (toD_le_iff p k z x hpN hkN).mp hca
  have hzy : iotaLe hpN z ≤ iotaLe hnN y := (toD_le_iff p n z y hpN hnN).mp hcb
  have hmn : max k n ≤ N := le_max_left _ _
  have heqx : iotaLe hkN x = iotaLe hmn (iotaLe (le_max_left k n) x) :=
    iotaLe_trans (le_max_left k n) hmn x
  have heqy : iotaLe hnN y = iotaLe hmn (iotaLe (le_max_right k n) y) :=
    iotaLe_trans (le_max_right k n) hmn y
  rw [toD_inf k n x y (le_max_left k n) (le_max_right k n),
      toD_le_iff p (max k n) z _ hpN hmn, ← iotaLe_inf, ← heqx, ← heqy]
  exact le_inf hzx hzy

-- [D-0930] inst-SemilatticeInf
noncomputable instance : SemilatticeInf DInfty :=
  { (inferInstance : PartialOrder DInfty) with
    inf := DInftyInf
    inf_le_left := DInftyInf_le_left
    inf_le_right := DInftyInf_le_right
    le_inf := DInftyLe_inf }

-- [D-0931] inst-Lattice
noncomputable instance : Lattice DInfty :=
  { (inferInstance : SemilatticeSup DInfty), (inferInstance : SemilatticeInf DInfty) with }

end DInftyColimit

-- [D-0932] pD
noncomputable def pD (k : ℕ) : D (k + 1) → D k := pGenM (L := D k) (dMid k)

-- [D-0933] pD_iotaD
theorem pD_iotaD (k : ℕ) (x : D k) : pD k (iotaD k x) = x := pGenM_section (dMid k) x

-- [D-0934] pD_deflation
theorem pD_deflation (k : ℕ) (w : D (k + 1)) : iotaD k (pD k w) ≤ w :=
  pGenM_deflation (L := D k) (dMid k) w

-- [D-0935] pD_monotone
theorem pD_monotone (k : ℕ) (w w' : D (k + 1)) (hle : w ≤ w') : pD k w ≤ pD k w' :=
  pGenM_monotone (L := D k) (dMid_ne_bot k) bot_ne_top_of_nontrivial w w' hle

-- [D-0936] pD_top
theorem pD_top (k : ℕ) : pD k (⊤ : D (k + 1)) = (⊤ : D k) := by
  exact pGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-0937] DBilimit
def DBilimit : Type := {x : ∀ k, D k // ∀ k, pD k (x (k + 1)) = x k}

-- [D-0938] inst-PartialOrder
noncomputable instance : PartialOrder DBilimit := Subtype.partialOrder _

-- [D-0939] topSeq
noncomputable def topSeq : DBilimit := ⟨fun k => (⊤ : D k), pD_top⟩

-- [D-0940] inst-Nonempty
noncomputable instance : Nonempty DBilimit := ⟨topSeq⟩

-- [D-0941] completeLatticeD
noncomputable instance completeLatticeD (k : ℕ) : CompleteLattice (D k) :=
  Fintype.toCompleteLattice (D k)

-- [D-0942] pD_sSup_image
theorem pD_sSup_image (k : ℕ) {T : Set (D (k + 1))} (hne : T.Nonempty)
    (hdir : DirectedOn (· ≤ ·) T) :
    pD k (sSup T) = sSup (pD k '' T) :=
  monotone_sSup_image_of_finite_directed (fun _ _ h => pD_monotone k _ _ h)
    (Set.toFinite T) hne hdir

-- [D-0943] DBilimit_directed_image
theorem DBilimit_directed_image (k : ℕ) {S : Set DBilimit} (hdir : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≤ ·) ((fun x : DBilimit => x.1 k) '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
  exact ⟨z.1 k, ⟨z, hz, rfl⟩, hxz k, hyz k⟩

-- [D-0944] DBilimit.exists_isLUB_of_directedOn
theorem DBilimit.exists_isLUB_of_directedOn (S : Set DBilimit) (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : ∃ y, IsLUB S y := by
  set T : ∀ k, Set (D k) := fun k => (fun x : DBilimit => x.1 k) '' S with hT
  have hTne : ∀ k, (T k).Nonempty := fun k => hne.image _
  have hTdir : ∀ k, DirectedOn (· ≤ ·) (T k) := fun k => DBilimit_directed_image k hdir
  have hTimg : ∀ k, T k = pD k '' T (k + 1) := by
    intro k
    ext v
    simp only [hT, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1 (k + 1), ⟨x, hx, rfl⟩, x.2 k⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (x.2 k).symm⟩
  have hcompat : ∀ k, pD k (sSup (T (k + 1))) = sSup (T k) := by
    intro k
    rw [hTimg k]
    exact pD_sSup_image k (hTne (k + 1)) (hTdir (k + 1))
  refine ⟨⟨fun k => sSup (T k), hcompat⟩, ?_, ?_⟩
  · rintro x hx k
    exact le_sSup ⟨x, hx, rfl⟩
  · rintro z hz k
    apply sSup_le
    rintro v ⟨x, hx, rfl⟩
    exact hz hx k

section DBilimitScott

-- [D-0945] inst-TopologicalSpace
noncomputable instance : TopologicalSpace DBilimit := Topology.scott DBilimit Set.univ

-- [D-0946] inst-IsScott
instance : Topology.IsScott DBilimit Set.univ := ⟨rfl⟩

-- [D-0947] example-T0Space
example : T0Space DBilimit := inferInstance

-- [D-0948] example-Set
example (s : Set DBilimit) : IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s :=
  Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed

end DBilimitScott

section DInftyBilimitEmbedding

-- [D-0949] pLe
noncomputable def pLe {j n : ℕ} (h : j ≤ n) : D n → D j :=
  Nat.leRecOn (C := fun k => D k → D j) h (fun {k} (f : D k → D j) => f ∘ pD k) id

-- [D-0950] pLe_self
theorem pLe_self (j : ℕ) (h : j ≤ j) (x : D j) : pLe h x = x := by
  unfold pLe
  rw [Nat.leRecOn_self]
  rfl

-- [D-0951] pLe_succ
theorem pLe_succ {j n : ℕ} (h : j ≤ n) (h' : j ≤ n + 1) (w : D (n + 1)) :
    pLe h' w = pLe h (pD n w) := by
  unfold pLe
  rw [Nat.leRecOn_succ h]
  rfl

-- [D-0952] pLe_pD_comm
theorem pLe_pD_comm {j : ℕ} : ∀ {k : ℕ} (h1 : j + 1 ≤ k) (h2 : j ≤ k) (y : D k),
    pD j (pLe h1 y) = pLe h2 y := by
  intro k h1
  induction k, h1 using Nat.le_induction with
  | base =>
      intro h2 y
      rw [pLe_self (j + 1) (le_refl (j + 1)) y]
      rw [pLe_succ (le_refl j) h2 y, pLe_self j (le_refl j) (pD j y)]
  | succ k hjk ih =>
      intro h2 y
      rw [pLe_succ hjk (Nat.le_succ_of_le hjk) y,
          pLe_succ (Nat.le_of_succ_le hjk) h2 y]
      exact ih (Nat.le_of_succ_le hjk) (pD k y)

-- [D-0953] seqOf
noncomputable def seqOf (p : Σ k, D k) (j : ℕ) : D j :=
  if h : j ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2

-- [D-0954] seqOf_compat
theorem seqOf_compat (p : Σ k, D k) (j : ℕ) :
    pD j (seqOf p (j + 1)) = seqOf p j := by
  by_cases h1 : j + 1 ≤ p.1
  · have h2 : j ≤ p.1 := Nat.le_of_succ_le h1
    show pD j (if h : j + 1 ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
       = (if h : j ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
    rw [dif_pos h1, dif_pos h2]
    exact pLe_pD_comm h1 h2 p.2
  · by_cases h2 : j ≤ p.1
    · have hpj : p.1 = j := le_antisymm (Nat.lt_succ_iff.mp (not_le.mp h1)) h2
      show pD j (if h : j + 1 ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
         = (if h : j ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
      rw [dif_neg h1, dif_pos h2]
      subst hpj
      rw [pLe_self p.1 (le_refl p.1) p.2]
      have heq : iotaLe (not_le.mp h1).le p.2 = iotaD p.1 p.2 := by
        rw [iotaLe_succ (le_refl p.1) (not_le.mp h1).le, iotaLe_self]
      rw [heq, pD_iotaD]
    · show pD j (if h : j + 1 ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
         = (if h : j ≤ p.1 then pLe h p.2 else iotaLe (not_le.mp h).le p.2)
      rw [dif_neg h1, dif_neg h2]
      have heq : iotaLe (not_le.mp h1).le p.2 = iotaD j (iotaLe (not_le.mp h2).le p.2) :=
        iotaLe_succ (not_le.mp h2).le (not_le.mp h1).le p.2
      rw [heq, pD_iotaD]

-- [D-0955] seqOf_iotaD_step
theorem seqOf_iotaD_step (n : ℕ) (w : D n) :
    seqOf ⟨n + 1, iotaD n w⟩ = seqOf ⟨n, w⟩ := by
  funext j
  show (if h : j ≤ n + 1 then pLe h (iotaD n w) else iotaLe (not_le.mp h).le (iotaD n w))
     = (if h : j ≤ n then pLe h w else iotaLe (not_le.mp h).le w)
  by_cases h1 : j ≤ n
  · have h2 : j ≤ n + 1 := le_trans h1 (Nat.le_succ n)
    rw [dif_pos h2, dif_pos h1, pLe_succ h1 h2, pD_iotaD]
  · by_cases h2 : j = n + 1
    · subst h2
      rw [dif_pos (le_refl (n + 1)), dif_neg h1, pLe_self (n + 1) (le_refl (n + 1)) (iotaD n w)]
      have heq : iotaLe (not_le.mp h1).le w = iotaD n w := by
        rw [iotaLe_succ (le_refl n) (not_le.mp h1).le, iotaLe_self]
      rw [heq]
    · have h3 : ¬ (j ≤ n + 1) := by omega
      rw [dif_neg h3, dif_neg h1]
      have hstep : n ≤ n + 1 := Nat.le_succ n
      have hchase : iotaLe (not_le.mp h1).le w
          = iotaLe (not_le.mp h3).le (iotaLe hstep w) := by
        rw [iotaLe_trans hstep (not_le.mp h3).le]
      have hstepval : iotaLe hstep w = iotaD n w := by
        rw [iotaLe_succ (le_refl n) hstep, iotaLe_self]
      rw [hchase, hstepval]

-- [D-0956] seqOf_iotaLe_invariant
theorem seqOf_iotaLe_invariant (p : Σ k, D k) : ∀ {n : ℕ} (h : p.1 ≤ n),
    seqOf ⟨n, iotaLe h p.2⟩ = seqOf p := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [iotaLe_self]
  | succ n hpn ih =>
      rw [iotaLe_succ hpn (Nat.le_succ_of_le hpn)]
      rw [seqOf_iotaD_step n (iotaLe hpn p.2)]
      exact ih

-- [D-0957] seqOf_congr
theorem seqOf_congr {p q : Σ k, D k} (h : DInftyRel p q) : seqOf p = seqOf q := by
  obtain ⟨n, h1, h2, he⟩ := h
  rw [← seqOf_iotaLe_invariant p h1, ← seqOf_iotaLe_invariant q h2, he]

-- [D-0958] toDBilimit
noncomputable def toDBilimit : DInfty → DBilimit :=
  Quotient.lift (fun p => (Subtype.mk (seqOf p) (seqOf_compat p) : DBilimit))
    (fun _ _ h => Subtype.ext (seqOf_congr h))

-- [D-0959] toDBilimit_toD
theorem toDBilimit_toD (k : ℕ) (x : D k) :
    (toDBilimit (toD k x)).1 k = x := by
  show seqOf ⟨k, x⟩ k = x
  show (if h : k ≤ k then pLe h x else iotaLe (not_le.mp h).le x) = x
  rw [dif_pos (le_refl k), pLe_self k (le_refl k) x]

-- [D-0960] seqOf_eq_iotaLe
theorem seqOf_eq_iotaLe (p : Σ k, D k) {n : ℕ} (h : p.1 ≤ n) : seqOf p n = iotaLe h p.2 := by
  show (if h' : n ≤ p.1 then pLe h' p.2 else iotaLe (not_le.mp h').le p.2) = iotaLe h p.2
  by_cases heq : p.1 = n
  · subst heq
    rw [dif_pos (le_refl p.1), pLe_self p.1 (le_refl p.1) p.2, iotaLe_self]
  · have hlt : ¬ (n ≤ p.1) := by
      have : p.1 < n := lt_of_le_of_ne h heq
      omega
    rw [dif_neg hlt]

-- [D-0961] toDBilimit_injective
theorem toDBilimit_injective : Function.Injective toDBilimit := by
  intro z1 z2 hz
  obtain ⟨k, x, hkx⟩ := toD_surjective z1
  obtain ⟨k', x', hkx'⟩ := toD_surjective z2
  subst hkx
  subst hkx'
  apply Quotient.sound
  refine ⟨max k k', le_max_left k k', le_max_right k k', ?_⟩
  have hz' : (toDBilimit (toD k x)).1 (max k k') = (toDBilimit (toD k' x')).1 (max k k') := by
    rw [hz]
  show iotaLe (le_max_left k k') x = iotaLe (le_max_right k k') x'
  rw [← seqOf_eq_iotaLe ⟨k, x⟩ (le_max_left k k'),
      ← seqOf_eq_iotaLe ⟨k', x'⟩ (le_max_right k k')]
  exact hz'

-- [D-0962] pLe_monotone
theorem pLe_monotone {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n) (x y : D n), x ≤ y → pLe h x ≤ pLe h y := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x y hxy; rw [pLe_self, pLe_self]; exact hxy
  | succ n hjn ih =>
      intro x y hxy
      rw [pLe_succ hjn (Nat.le_succ_of_le hjn), pLe_succ hjn (Nat.le_succ_of_le hjn)]
      exact ih (pD n x) (pD n y) (pD_monotone n x y hxy)

-- [D-0963] seqOf_monotone_atLevel
theorem seqOf_monotone_atLevel (N : ℕ) (w w' : D N) (hww : w ≤ w') (j : ℕ) :
    seqOf ⟨N, w⟩ j ≤ seqOf ⟨N, w'⟩ j := by
  show (if h : j ≤ N then pLe h w else iotaLe (not_le.mp h).le w)
     ≤ (if h : j ≤ N then pLe h w' else iotaLe (not_le.mp h).le w')
  by_cases h : j ≤ N
  · rw [dif_pos h, dif_pos h]
    exact pLe_monotone h w w' hww
  · rw [dif_neg h, dif_neg h]
    exact (iotaLe_le_iff (not_le.mp h).le w w').mpr hww

-- [D-0964] toDBilimit_monotone
theorem toDBilimit_monotone : Monotone toDBilimit := by
  intro z1 z2 hz
  obtain ⟨k, x, hkx⟩ := toD_surjective z1
  obtain ⟨k', x', hkx'⟩ := toD_surjective z2
  subst hkx
  subst hkx'
  intro j
  have hkN : k ≤ max k k' := le_max_left k k'
  have hkN' : k' ≤ max k k' := le_max_right k k'
  have hzN : iotaLe hkN x ≤ iotaLe hkN' x' := (toD_le_iff k k' x x' hkN hkN').mp hz
  show seqOf ⟨k, x⟩ j ≤ seqOf ⟨k', x'⟩ j
  rw [← seqOf_iotaLe_invariant ⟨k, x⟩ hkN, ← seqOf_iotaLe_invariant ⟨k', x'⟩ hkN']
  exact seqOf_monotone_atLevel (max k k') (iotaLe hkN x) (iotaLe hkN' x') hzN j

-- [D-0965] toDBilimit_reflects_le
theorem toDBilimit_reflects_le {z1 z2 : DInfty} (h : toDBilimit z1 ≤ toDBilimit z2) :
    z1 ≤ z2 := by
  obtain ⟨k, x, hkx⟩ := toD_surjective z1
  obtain ⟨k', x', hkx'⟩ := toD_surjective z2
  subst hkx
  subst hkx'
  have hkN : k ≤ max k k' := le_max_left k k'
  have hkN' : k' ≤ max k k' := le_max_right k k'
  have hjN := h (max k k')
  rw [toD_le_iff k k' x x' hkN hkN']
  rw [← seqOf_eq_iotaLe ⟨k, x⟩ hkN, ← seqOf_eq_iotaLe ⟨k', x'⟩ hkN']
  exact hjN

-- [D-0966] toDBilimit_le_iff
theorem toDBilimit_le_iff {z1 z2 : DInfty} : toDBilimit z1 ≤ toDBilimit z2 ↔ z1 ≤ z2 :=
  ⟨toDBilimit_reflects_le, fun h => toDBilimit_monotone h⟩

-- [D-0967] toDBilimitEmb
noncomputable def toDBilimitEmb : DInfty ↪o DBilimit :=
  OrderEmbedding.ofMapLEIff toDBilimit (fun _ _ => toDBilimit_le_iff)

end DInftyBilimitEmbedding

section EndPEpPair

-- [D-0968] iotaEndP
noncomputable def iotaEndP (k : ℕ) (f : EndP (D k)) : EndP (D (k + 1)) where
  toFun w := iotaD k (f (pD k w))
  monotone' _ _ hle := iotaD_monotone k (f.monotone (pD_monotone k _ _ hle))

-- [D-0969] pEndP
noncomputable def pEndP (k : ℕ) (g : EndP (D (k + 1))) : EndP (D k) where
  toFun x := pD k (g (iotaD k x))
  monotone' _ _ hle := pD_monotone k _ _ (g.monotone (iotaD_monotone k hle))

-- [D-0970] pEndP_iotaEndP
theorem pEndP_iotaEndP (k : ℕ) (f : EndP (D k)) : pEndP k (iotaEndP k f) = f := by
  ext x
  show pD k (iotaD k (f (pD k (iotaD k x)))) = f x
  rw [pD_iotaD, pD_iotaD]

-- [D-0971] iotaEndP_pEndP_deflation
theorem iotaEndP_pEndP_deflation (k : ℕ) (g : EndP (D (k + 1))) :
    iotaEndP k (pEndP k g) ≤ g := by
  rw [OrderHom.le_def]
  intro w
  show iotaD k (pD k (g (iotaD k (pD k w)))) ≤ g w
  have h1 : g (iotaD k (pD k w)) ≤ g w := g.monotone (pD_deflation k w)
  have h2 : pD k (g (iotaD k (pD k w))) ≤ pD k (g w) := pD_monotone k _ _ h1
  have h3 : iotaD k (pD k (g (iotaD k (pD k w)))) ≤ iotaD k (pD k (g w)) :=
    iotaD_monotone k h2
  exact h3.trans (pD_deflation k (g w))

-- [D-0972] iotaEndP_monotone
theorem iotaEndP_monotone (k : ℕ) : Monotone (iotaEndP k) := by
  intro f f' hle
  rw [OrderHom.le_def]
  intro w
  show iotaD k (f (pD k w)) ≤ iotaD k (f' (pD k w))
  exact iotaD_monotone k (OrderHom.le_def.mp hle (pD k w))

-- [D-0973] pEndP_monotone
theorem pEndP_monotone (k : ℕ) : Monotone (pEndP k) := by
  intro g g' hle
  rw [OrderHom.le_def]
  intro x
  show pD k (g (iotaD k x)) ≤ pD k (g' (iotaD k x))
  exact pD_monotone k _ _ (OrderHom.le_def.mp hle (iotaD k x))

end EndPEpPair

section EndPBilimitSection

-- [D-0974] EndPBilimit
def EndPBilimit : Type := {x : ∀ k, EndP (D k) // ∀ k, pEndP k (x (k + 1)) = x k}

-- [D-0975] inst-PartialOrder
noncomputable instance : PartialOrder EndPBilimit := Subtype.partialOrder _

-- [D-0976] insertAtLevel
noncomputable def insertAtLevel (k : ℕ) (w : D k) : DBilimit :=
  ⟨seqOf ⟨k, w⟩, seqOf_compat ⟨k, w⟩⟩

-- [D-0977] insertAtLevel_iotaD
theorem insertAtLevel_iotaD (k : ℕ) (w : D k) :
    insertAtLevel (k + 1) (iotaD k w) = insertAtLevel k w :=
  Subtype.ext (seqOf_iotaD_step k w)

-- [D-0978] insertAtLevel_monotone
theorem insertAtLevel_monotone (k : ℕ) : Monotone (insertAtLevel k) := by
  intro w w' hle j
  exact seqOf_monotone_atLevel k w w' hle j

-- [D-0979] toEndPBilimitAt
noncomputable def toEndPBilimitAt (F : EndP DBilimit) (k : ℕ) : EndP (D k) where
  toFun w := (F (insertAtLevel k w)).1 k
  monotone' _ _ hle := F.monotone (insertAtLevel_monotone k hle) k

-- [D-0980] toEndPBilimit
noncomputable def toEndPBilimit (F : EndP DBilimit) : EndPBilimit :=
  ⟨fun k => toEndPBilimitAt F k, fun k => by
    ext w
    show pD k ((F (insertAtLevel (k + 1) (iotaD k w))).1 (k + 1))
        = (F (insertAtLevel k w)).1 k
    rw [insertAtLevel_iotaD]
    exact (F (insertAtLevel k w)).2 k⟩

end EndPBilimitSection

section EndPBilimitApply

-- [D-0981] chain_deflate_le
theorem chain_deflate_le (f : EndPBilimit) (y : DBilimit) (n : ℕ) :
    f.1 n (y.1 n) ≤ pD n (f.1 (n + 1) (y.1 (n + 1))) := by
  have hcompat : f.1 n (y.1 n) = pD n (f.1 (n + 1) (iotaD n (y.1 n))) := by
    have h := f.2 n
    show f.1 n (y.1 n) = (pEndP n (f.1 (n + 1))) (y.1 n)
    rw [h]
  rw [hcompat]
  have hdefl : iotaD n (y.1 n) ≤ y.1 (n + 1) := by
    rw [show y.1 n = pD n (y.1 (n + 1)) from (y.2 n).symm]
    exact pD_deflation n (y.1 (n + 1))
  exact pD_monotone n _ _ ((f.1 (n + 1)).monotone hdefl)

-- [D-0982] chaseDown
noncomputable def chaseDown (f : EndPBilimit) (y : DBilimit) {k n : ℕ} (h : k ≤ n) : D k :=
  pLe h (f.1 n (y.1 n))

-- [D-0983] chaseDown_mono
theorem chaseDown_mono (f : EndPBilimit) (y : DBilimit) {k n : ℕ} (h : k ≤ n) :
    ∀ {n' : ℕ} (h' : n ≤ n'), chaseDown f y h ≤ chaseDown f y (h.trans h') := by
  intro n' h'
  induction n', h' using Nat.le_induction with
  | base => exact le_refl _
  | succ n' hn' ih =>
      refine ih.trans ?_
      show pLe (h.trans hn') (f.1 n' (y.1 n'))
          ≤ pLe (h.trans (hn'.trans (Nat.le_succ n'))) (f.1 (n' + 1) (y.1 (n' + 1)))
      rw [pLe_succ (h.trans hn') (h.trans (hn'.trans (Nat.le_succ n')))]
      exact pLe_monotone (h.trans hn') _ _ (chain_deflate_le f y n')

-- [D-0984] chaseDownSet
noncomputable def chaseDownSet (f : EndPBilimit) (y : DBilimit) (k : ℕ) : Set (D k) :=
  {v | ∃ n, ∃ h : k ≤ n, v = chaseDown f y h}

-- [D-0985] chaseDownSet_nonempty
theorem chaseDownSet_nonempty (f : EndPBilimit) (y : DBilimit) (k : ℕ) :
    (chaseDownSet f y k).Nonempty :=
  ⟨chaseDown f y (le_refl k), k, le_refl k, rfl⟩

-- [D-0986] chaseDownSet_directed
theorem chaseDownSet_directed (f : EndPBilimit) (y : DBilimit) (k : ℕ) :
    DirectedOn (· ≤ ·) (chaseDownSet f y k) := by
  rintro a ⟨n1, h1, rfl⟩ b ⟨n2, h2, rfl⟩
  exact ⟨chaseDown f y (h1.trans (le_max_left n1 n2)),
    ⟨max n1 n2, h1.trans (le_max_left n1 n2), rfl⟩,
    chaseDown_mono f y h1 (le_max_left n1 n2),
    chaseDown_mono f y h2 (le_max_right n1 n2)⟩

-- [D-0987] levelSup
noncomputable def levelSup (f : EndPBilimit) (y : DBilimit) (k : ℕ) : D k :=
  sSup (chaseDownSet f y k)

-- [D-0988] levelSup_compat
theorem levelSup_compat (f : EndPBilimit) (y : DBilimit) (k : ℕ) :
    pD k (levelSup f y (k + 1)) = levelSup f y k := by
  have hne : (chaseDownSet f y (k + 1)).Nonempty := chaseDownSet_nonempty f y (k + 1)
  have hdir : DirectedOn (· ≤ ·) (chaseDownSet f y (k + 1)) := chaseDownSet_directed f y (k + 1)
  show pD k (sSup (chaseDownSet f y (k + 1))) = sSup (chaseDownSet f y k)
  rw [pD_sSup_image k hne hdir]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨v, ⟨n, h, rfl⟩, rfl⟩
    have heq : pD k (chaseDown f y h) = chaseDown f y (Nat.le_of_succ_le h) := by
      show pD k (pLe h (f.1 n (y.1 n))) = pLe (Nat.le_of_succ_le h) (f.1 n (y.1 n))
      exact pLe_pD_comm h (Nat.le_of_succ_le h) (f.1 n (y.1 n))
    rw [heq]
    exact le_sSup ⟨n, Nat.le_of_succ_le h, rfl⟩
  · apply sSup_le
    rintro _ ⟨n, h, rfl⟩
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hnk : n = k := le_antisymm (Nat.lt_succ_iff.mp hlt) h
      subst hnk
      have hval : chaseDown f y h = f.1 n (y.1 n) := pLe_self n h (f.1 n (y.1 n))
      have hmem : chaseDown f y (le_refl (n + 1)) ∈ chaseDownSet f y (n + 1) :=
        ⟨n + 1, le_refl (n + 1), rfl⟩
      have hcd : chaseDown f y (le_refl (n + 1)) = f.1 (n + 1) (y.1 (n + 1)) :=
        pLe_self (n + 1) (le_refl (n + 1)) (f.1 (n + 1) (y.1 (n + 1)))
      rw [hval]
      calc f.1 n (y.1 n) ≤ pD n (f.1 (n + 1) (y.1 (n + 1))) := chain_deflate_le f y n
        _ = pD n (chaseDown f y (le_refl (n + 1))) := by rw [hcd]
        _ ≤ sSup (pD n '' chaseDownSet f y (n + 1)) :=
              le_sSup ⟨chaseDown f y (le_refl (n + 1)), hmem, rfl⟩
    · have heq : chaseDown f y h = pD k (chaseDown f y hge) := by
        show pLe h (f.1 n (y.1 n)) = pD k (pLe hge (f.1 n (y.1 n)))
        exact (pLe_pD_comm hge h (f.1 n (y.1 n))).symm
      rw [heq]
      exact le_sSup ⟨chaseDown f y hge, ⟨n, hge, rfl⟩, rfl⟩

-- [D-0989] applyEndPBilimit
noncomputable def applyEndPBilimit (f : EndPBilimit) (y : DBilimit) : DBilimit :=
  ⟨fun k => levelSup f y k, fun k => levelSup_compat f y k⟩

-- [D-0990] chaseDown_mono_in_y
theorem chaseDown_mono_in_y (f : EndPBilimit) {k n : ℕ} (h : k ≤ n) (y y' : DBilimit)
    (hyy' : y ≤ y') : chaseDown f y h ≤ chaseDown f y' h :=
  pLe_monotone h _ _ ((f.1 n).monotone (hyy' n))

-- [D-0991] applyEndPBilimit_monotone
theorem applyEndPBilimit_monotone (f : EndPBilimit) : Monotone (applyEndPBilimit f) := by
  intro y y' hyy' k
  show levelSup f y k ≤ levelSup f y' k
  apply sSup_le
  rintro _ ⟨n, h, rfl⟩
  exact (chaseDown_mono_in_y f h y y' hyy').trans (le_sSup ⟨n, h, rfl⟩)

-- [D-0992] ofEndPBilimit
noncomputable def ofEndPBilimit (f : EndPBilimit) : EndP DBilimit where
  toFun := applyEndPBilimit f
  monotone' := applyEndPBilimit_monotone f

end EndPBilimitApply

section CounterexampleCheck

open Classical

-- [D-0993] le_topSeq
theorem le_topSeq (z : DBilimit) : z ≤ topSeq := fun _ => le_top

-- [D-0994] DBilimit_pLe_eq
theorem DBilimit_pLe_eq (z : DBilimit) {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n), pLe h (z.1 n) = z.1 k := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact pLe_self k (le_refl k) (z.1 k)
  | succ n hn ih =>
      rw [pLe_succ hn (hn.trans (Nat.le_succ n))]
      rw [z.2 n]
      exact ih

-- [D-0995] iotaD_ne_top
theorem iotaD_ne_top (k : ℕ) (x : D k) : iotaD k x ≠ (⊤ : D (k + 1)) := by
  intro heq
  have h := D_marked_point_nondegenerate k
  have hval : (⊤ : D (k + 1)).1
      = canon (markedPt k) (Sum.inr (Sum.inr (⊤ : EndP (D k)))) := rfl
  have hcanon : canon (markedPt k) (Sum.inr (Sum.inr (⊤ : EndP (D k))))
      = Sum.inr (Sum.inr (⊤ : EndP (D k))) := by
    simp only [canon]
    split_ifs with h1 h2
    · exact absurd h1 h.2.2.symm
    · exact absurd h2 h.2.1.symm
    · rfl
  have hiotaD : (iotaD k x).1 = Sum.inl (constHom x : EndP (D k)) := rfl
  rw [heq, hval, hcanon] at hiotaD
  exact absurd hiotaD (by simp)

-- [D-0996] insertAtLevel_topSeq_ne
theorem insertAtLevel_topSeq_ne (n : ℕ) : insertAtLevel n (topSeq.1 n) ≠ topSeq := by
  intro heq
  have h1 : (insertAtLevel n (topSeq.1 n)).1 (n + 1) = topSeq.1 (n + 1) :=
    congrFun (congrArg Subtype.val heq) (n + 1)
  have h2 : (insertAtLevel n (topSeq.1 n)).1 (n + 1) = iotaD n (topSeq.1 n) := by
    have hle : n ≤ n + 1 := Nat.le_succ n
    have hnle : ¬ (n + 1 ≤ n) := by omega
    show (if h : n + 1 ≤ n then pLe h (topSeq.1 n) else iotaLe (not_le.mp h).le (topSeq.1 n))
        = iotaD n (topSeq.1 n)
    rw [dif_neg hnle, iotaLe_succ (le_refl n) hle, iotaLe_self]
  rw [h2] at h1
  exact iotaD_ne_top n (topSeq.1 n) h1

-- [D-0997] counterF
noncomputable def counterF : EndP DBilimit where
  toFun y := if topSeq ≤ y then topSeq else insertAtLevel 0 (⊥ : D 0)
  monotone' y y' hyy' := by
    by_cases hy : topSeq ≤ y
    · have hy' : topSeq ≤ y' := hy.trans hyy'
      simp only [if_pos hy, if_pos hy']
      exact le_refl _
    · by_cases hy' : topSeq ≤ y'
      · simp only [if_neg hy, if_pos hy']
        exact le_topSeq _
      · simp only [if_neg hy, if_neg hy']
        exact le_refl _

-- [D-0998] counterF_topSeq
theorem counterF_topSeq : counterF topSeq = topSeq := by
  show (if topSeq ≤ topSeq then topSeq else insertAtLevel 0 (⊥ : D 0)) = topSeq
  rw [if_pos (le_refl topSeq)]

-- [D-0999] counterF_approx
theorem counterF_approx (n : ℕ) :
    counterF (insertAtLevel n (topSeq.1 n)) = insertAtLevel 0 (⊥ : D 0) := by
  show (if topSeq ≤ insertAtLevel n (topSeq.1 n) then topSeq else insertAtLevel 0 (⊥ : D 0))
      = insertAtLevel 0 (⊥ : D 0)
  rw [if_neg]
  intro hle
  exact insertAtLevel_topSeq_ne n (le_antisymm (le_topSeq _) hle)

-- [D-1000] toEndPBilimit_ofEndPBilimit_not_roundtrip
theorem toEndPBilimit_ofEndPBilimit_not_roundtrip :
    ofEndPBilimit (toEndPBilimit counterF) ≠ counterF := by
  intro heq
  have h1 : ofEndPBilimit (toEndPBilimit counterF) topSeq = counterF topSeq :=
    congrFun (congrArg (fun G : EndP DBilimit => (G : DBilimit → DBilimit)) heq) topSeq
  rw [counterF_topSeq] at h1
  have h2 : ofEndPBilimit (toEndPBilimit counterF) topSeq
      = applyEndPBilimit (toEndPBilimit counterF) topSeq := rfl
  rw [h2] at h1
  have h3 : (applyEndPBilimit (toEndPBilimit counterF) topSeq).1 0 = topSeq.1 0 := by rw [h1]
  have h4 : (applyEndPBilimit (toEndPBilimit counterF) topSeq).1 0
      = levelSup (toEndPBilimit counterF) topSeq 0 := rfl
  rw [h4] at h3
  have hval : levelSup (toEndPBilimit counterF) topSeq 0 = (⊥ : D 0) := by
    have hset : chaseDownSet (toEndPBilimit counterF) topSeq 0 = {(⊥ : D 0)} := by
      ext v
      constructor
      · rintro ⟨n, h, rfl⟩
        show pLe h ((toEndPBilimit counterF).1 n (topSeq.1 n)) = (⊥ : D 0)
        have hstep : (toEndPBilimit counterF).1 n (topSeq.1 n)
            = (insertAtLevel 0 (⊥ : D 0)).1 n := by
          show (counterF (insertAtLevel n (topSeq.1 n))).1 n = (insertAtLevel 0 (⊥ : D 0)).1 n
          rw [counterF_approx n]
        rw [hstep, DBilimit_pLe_eq (insertAtLevel 0 (⊥ : D 0)) h]
        exact pLe_self 0 (le_refl 0) (⊥ : D 0)
      · intro hv
        have hv0 : v = (⊥ : D 0) := hv
        refine ⟨0, le_refl 0, ?_⟩
        have hins0 : (insertAtLevel 0 (⊥ : D 0)).1 0 = (⊥ : D 0) := by
          show (if h : (0:ℕ) ≤ 0 then pLe h (⊥ : D 0) else iotaLe (not_le.mp h).le (⊥ : D 0))
              = (⊥ : D 0)
          rw [dif_pos (le_refl 0)]
          exact pLe_self 0 (le_refl 0) (⊥ : D 0)
        have hstep0 : (toEndPBilimit counterF).1 0 (topSeq.1 0) = (⊥ : D 0) := by
          show (counterF (insertAtLevel 0 (topSeq.1 0))).1 0 = (⊥ : D 0)
          rw [counterF_approx 0]
          exact hins0
        show v = chaseDown (toEndPBilimit counterF) topSeq (le_refl 0)
        show v = pLe (le_refl 0) ((toEndPBilimit counterF).1 0 (topSeq.1 0))
        rw [hstep0, pLe_self 0 (le_refl 0)]
        exact hv0
    show sSup (chaseDownSet (toEndPBilimit counterF) topSeq 0) = (⊥ : D 0)
    rw [hset, csSup_singleton]
  rw [hval] at h3
  have h5 : (⊥ : D 0) = (⊤ : D 0) := h3
  exact bot_ne_top_of_nontrivial h5

end CounterexampleCheck

section ContinuousRoundtrip

-- [D-1001] iotaD_y_le
theorem iotaD_y_le (y : DBilimit) (n : ℕ) : iotaD n (y.1 n) ≤ y.1 (n + 1) := by
  rw [show y.1 n = pD n (y.1 (n + 1)) from (y.2 n).symm]
  exact pD_deflation n (y.1 (n + 1))

-- [D-1002] iotaLe_y_le
theorem iotaLe_y_le (y : DBilimit) {n : ℕ} : ∀ {n' : ℕ} (h : n ≤ n'), iotaLe h (y.1 n) ≤ y.1 n' := by
  intro n' h
  induction n', h using Nat.le_induction with
  | base => rw [iotaLe_self]
  | succ n' hn' ih =>
      rw [iotaLe_succ hn' (hn'.trans (Nat.le_succ n'))]
      exact (iotaD_monotone n' ih).trans (iotaD_y_le y n')

-- [D-1003] insertAtLevel_le_self
theorem insertAtLevel_le_self (y : DBilimit) (n : ℕ) : insertAtLevel n (y.1 n) ≤ y := by
  intro j
  show (if h : j ≤ n then pLe h (y.1 n) else iotaLe (not_le.mp h).le (y.1 n)) ≤ y.1 j
  by_cases hjn : j ≤ n
  · rw [dif_pos hjn, DBilimit_pLe_eq y hjn]
  · rw [dif_neg hjn]
    exact iotaLe_y_le y (not_le.mp hjn).le

-- [D-1004] insertAtLevel_chain_mono
theorem insertAtLevel_chain_mono (y : DBilimit) {n n' : ℕ} (h : n ≤ n') :
    insertAtLevel n (y.1 n) ≤ insertAtLevel n' (y.1 n') := by
  intro j
  show (if hj : j ≤ n then pLe hj (y.1 n) else iotaLe (not_le.mp hj).le (y.1 n))
     ≤ (if hj : j ≤ n' then pLe hj (y.1 n') else iotaLe (not_le.mp hj).le (y.1 n'))
  by_cases hjn : j ≤ n
  · have hjn' : j ≤ n' := hjn.trans h
    rw [dif_pos hjn, dif_pos hjn', DBilimit_pLe_eq y hjn, DBilimit_pLe_eq y hjn']
  · rw [dif_neg hjn]
    by_cases hjn' : j ≤ n'
    · rw [dif_pos hjn']
      exact (iotaLe_y_le y (not_le.mp hjn).le).trans_eq (DBilimit_pLe_eq y hjn').symm
    · rw [dif_neg hjn']
      have hnj : n ≤ j := (not_le.mp hjn).le
      have hn'j : n' ≤ j := (not_le.mp hjn').le
      have hrw : iotaLe hnj (y.1 n) = iotaLe hn'j (iotaLe h (y.1 n)) := iotaLe_trans h hn'j (y.1 n)
      rw [show iotaLe (not_le.mp hjn).le (y.1 n) = iotaLe hnj (y.1 n) from rfl, hrw]
      exact (iotaLe_le_iff hn'j _ _).mpr (iotaLe_y_le y h)

-- [D-1005] chainSet
noncomputable def chainSet (y : DBilimit) : Set DBilimit := Set.range (fun n => insertAtLevel n (y.1 n))

-- [D-1006] chainSet_nonempty
theorem chainSet_nonempty (y : DBilimit) : (chainSet y).Nonempty := ⟨_, 0, rfl⟩

-- [D-1007] chainSet_directedOn
theorem chainSet_directedOn (y : DBilimit) : DirectedOn (· ≤ ·) (chainSet y) := by
  rintro _ ⟨n1, rfl⟩ _ ⟨n2, rfl⟩
  exact ⟨insertAtLevel (max n1 n2) (y.1 (max n1 n2)), ⟨max n1 n2, rfl⟩,
    insertAtLevel_chain_mono y (le_max_left n1 n2), insertAtLevel_chain_mono y (le_max_right n1 n2)⟩

-- [D-1008] chainSet_isLUB
theorem chainSet_isLUB (y : DBilimit) : IsLUB (chainSet y) y := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact insertAtLevel_le_self y n
  · intro z hz j
    have hzj := hz ⟨j, rfl⟩ j
    show y.1 j ≤ z.1 j
    have heq : (insertAtLevel j (y.1 j)).1 j = y.1 j := by
      show (if h : j ≤ j then pLe h (y.1 j) else iotaLe (not_le.mp h).le (y.1 j)) = y.1 j
      rw [dif_pos (le_refl j)]
      exact pLe_self j (le_refl j) (y.1 j)
    rw [← heq]
    exact hzj

-- [D-1009] toEndPBilimit_ofEndPBilimit_of_continuous
theorem toEndPBilimit_ofEndPBilimit_of_continuous (F : EndP DBilimit)
    (hF : ScottContinuous (F : DBilimit → DBilimit)) :
    ofEndPBilimit (toEndPBilimit F) = F := by
  ext y
  show applyEndPBilimit (toEndPBilimit F) y = F y
  have hFLUB : IsLUB (F '' chainSet y) (F y) :=
    hF (chainSet_nonempty y) (chainSet_directedOn y) (chainSet_isLUB y)
  have hzLUB : IsLUB (F '' chainSet y) (applyEndPBilimit (toEndPBilimit F) y) := by
    constructor
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      intro k
      show (F (insertAtLevel n (y.1 n))).1 k ≤ levelSup (toEndPBilimit F) y k
      by_cases hkn : k ≤ n
      · have hle : (F (insertAtLevel n (y.1 n))).1 k
            = pLe hkn ((F (insertAtLevel n (y.1 n))).1 n) := (DBilimit_pLe_eq _ hkn).symm
        rw [hle]
        exact le_sSup ⟨n, hkn, rfl⟩
      · have hnk : n ≤ k := (not_le.mp hkn).le
        have hchain : insertAtLevel n (y.1 n) ≤ insertAtLevel k (y.1 k) :=
          insertAtLevel_chain_mono y hnk
        have hFmono : F (insertAtLevel n (y.1 n)) ≤ F (insertAtLevel k (y.1 k)) := F.monotone hchain
        refine (hFmono k).trans ?_
        show (toEndPBilimit F).1 k (y.1 k) ≤ levelSup (toEndPBilimit F) y k
        exact le_sSup ⟨k, le_refl k, (pLe_self k (le_refl k) _).symm⟩
    · intro w hw k
      show levelSup (toEndPBilimit F) y k ≤ w.1 k
      apply sSup_le
      rintro _ ⟨n, hkn, rfl⟩
      have hwn : F (insertAtLevel n (y.1 n)) ≤ w := hw ⟨_, ⟨n, rfl⟩, rfl⟩
      exact (pLe_monotone hkn _ _ (hwn n)).trans_eq (DBilimit_pLe_eq w hkn)
  exact (hFLUB.unique hzLUB).symm

end ContinuousRoundtrip

section EasyRoundtrip

-- [D-1010] insertAtLevel_self
theorem insertAtLevel_self (k : ℕ) (w : D k) : (insertAtLevel k w).1 k = w := by
  show (if h : k ≤ k then pLe h w else iotaLe (not_le.mp h).le w) = w
  rw [dif_pos (le_refl k)]
  exact pLe_self k (le_refl k) w

-- [D-1011] insertAtLevel_succ
theorem insertAtLevel_succ (k : ℕ) (w : D k) (n : ℕ) (h : k ≤ n) :
    (insertAtLevel k w).1 (n + 1) = iotaD n ((insertAtLevel k w).1 n) := by
  have h' : k ≤ n + 1 := h.trans (Nat.le_succ n)
  have hnk : ¬ (n + 1 ≤ k) := by omega
  show (if hh : n + 1 ≤ k then pLe hh w else iotaLe (not_le.mp hh).le w)
      = iotaD n ((insertAtLevel k w).1 n)
  rw [dif_neg hnk]
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · subst heq
    rw [iotaLe_succ (le_refl k) h', insertAtLevel_self, iotaLe_self]
  · have hnk2 : ¬ (n ≤ k) := by omega
    show iotaLe (not_le.mp hnk).le w = iotaD n (if hh : n ≤ k then pLe hh w else iotaLe (not_le.mp hh).le w)
    rw [dif_neg hnk2, iotaLe_succ (not_le.mp hnk2).le (not_le.mp hnk).le]

-- [D-1012] chaseDown_insertAtLevel_const
theorem chaseDown_insertAtLevel_const (f : EndPBilimit) (k : ℕ) (w : D k) :
    ∀ {n : ℕ} (h : k ≤ n), chaseDown f (insertAtLevel k w) h = f.1 k w := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      show pLe (le_refl k) (f.1 k ((insertAtLevel k w).1 k)) = f.1 k w
      rw [insertAtLevel_self, pLe_self]
  | succ n hkn ih =>
      show pLe (hkn.trans (Nat.le_succ n)) (f.1 (n + 1) ((insertAtLevel k w).1 (n + 1))) = f.1 k w
      rw [insertAtLevel_succ k w n hkn]
      have hcompat : f.1 n ((insertAtLevel k w).1 n)
          = pD n (f.1 (n + 1) (iotaD n ((insertAtLevel k w).1 n))) := by
        have hf := f.2 n
        show f.1 n ((insertAtLevel k w).1 n) = (pEndP n (f.1 (n + 1))) ((insertAtLevel k w).1 n)
        rw [hf]
      rw [pLe_succ hkn (hkn.trans (Nat.le_succ n)), ← hcompat]
      exact ih

-- [D-1013] toEndPBilimit_ofEndPBilimit
theorem toEndPBilimit_ofEndPBilimit (f : EndPBilimit) :
    toEndPBilimit (ofEndPBilimit f) = f := by
  apply Subtype.ext
  funext k
  ext w
  show ((ofEndPBilimit f) (insertAtLevel k w)).1 k = f.1 k w
  show levelSup f (insertAtLevel k w) k = f.1 k w
  have hset : chaseDownSet f (insertAtLevel k w) k = {f.1 k w} := by
    ext v
    constructor
    · rintro ⟨n, h, rfl⟩
      exact chaseDown_insertAtLevel_const f k w h
    · intro hv
      have hv0 : v = f.1 k w := hv
      exact ⟨k, le_refl k, hv0.trans (chaseDown_insertAtLevel_const f k w (le_refl k)).symm⟩
  show sSup (chaseDownSet f (insertAtLevel k w) k) = f.1 k w
  rw [hset, csSup_singleton]

end EasyRoundtrip

section ScottContinuousOf

-- [D-1014] _root_.IsLUB.dbilimit_apply
theorem _root_.IsLUB.dbilimit_apply {S : Set DBilimit} {a : DBilimit} (ha : IsLUB S a)
    (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) (k : ℕ) :
    a.1 k = sSup ((fun x : DBilimit => x.1 k) '' S) := by
  set T : ∀ j, Set (D j) := fun j => (fun x : DBilimit => x.1 j) '' S with hT
  have hTne : ∀ j, (T j).Nonempty := fun j => hne.image _
  have hTdir : ∀ j, DirectedOn (· ≤ ·) (T j) := fun j => DBilimit_directed_image j hdir
  have hTimg : ∀ j, T j = pD j '' T (j + 1) := by
    intro j
    ext v
    simp only [hT, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1 (j + 1), ⟨x, hx, rfl⟩, x.2 j⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (x.2 j).symm⟩
  have hcompat : ∀ j, pD j (sSup (T (j + 1))) = sSup (T j) := by
    intro j
    rw [hTimg j]
    exact pD_sSup_image j (hTne (j + 1)) (hTdir (j + 1))
  have hb : IsLUB S (⟨fun j => sSup (T j), hcompat⟩ : DBilimit) := by
    constructor
    · rintro x hx j; exact le_sSup ⟨x, hx, rfl⟩
    · rintro z hz j; apply sSup_le; rintro v ⟨x, hx, rfl⟩; exact hz hx j
  have hab := ha.unique hb
  rw [hab]

-- [D-1015] applyEndPBilimit_scottContinuous
theorem applyEndPBilimit_scottContinuous (f : EndPBilimit) :
    ScottContinuous (applyEndPBilimit f : DBilimit → DBilimit) := by
  intro S hSne hSdir a haLUB
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    exact applyEndPBilimit_monotone f (haLUB.1 hs)
  · intro z hz k
    show levelSup f a k ≤ z.1 k
    apply sSup_le
    rintro _ ⟨n, hkn, rfl⟩
    show pLe hkn (f.1 n (a.1 n)) ≤ z.1 k
    have han : a.1 n = sSup ((fun x : DBilimit => x.1 n) '' S) := haLUB.dbilimit_apply hSne hSdir n
    have hSnNe : ((fun x : DBilimit => x.1 n) '' S).Nonempty := hSne.image _
    have hSnDir : DirectedOn (· ≤ ·) ((fun x : DBilimit => x.1 n) '' S) :=
      DBilimit_directed_image n hSdir
    have hgDir : DirectedOn (· ≤ ·) ((fun s : DBilimit => f.1 n (s.1 n)) '' S) := by
      rintro _ ⟨s1, hs1, rfl⟩ _ ⟨s2, hs2, rfl⟩
      obtain ⟨s3, hs3, h13, h23⟩ := hSdir s1 hs1 s2 hs2
      exact ⟨f.1 n (s3.1 n), ⟨s3, hs3, rfl⟩, (f.1 n).monotone (h13 n), (f.1 n).monotone (h23 n)⟩
    have hfn : f.1 n (a.1 n) = sSup ((fun s : DBilimit => f.1 n (s.1 n)) '' S) := by
      rw [han, monotone_sSup_image_of_finite_directed (f.1 n).monotone (Set.toFinite _) hSnNe hSnDir,
          Set.image_image]
    rw [hfn]
    have hpLe : pLe hkn (sSup ((fun s : DBilimit => f.1 n (s.1 n)) '' S))
        = sSup ((fun s : DBilimit => pLe hkn (f.1 n (s.1 n))) '' S) := by
      rw [monotone_sSup_image_of_finite_directed (fun a b h => pLe_monotone hkn a b h)
        (Set.toFinite _) (hSne.image _) hgDir, Set.image_image]
    rw [hpLe]
    apply sSup_le
    rintro _ ⟨s, hs, rfl⟩
    have hle : pLe hkn (f.1 n (s.1 n)) ≤ levelSup f s k := le_sSup ⟨n, hkn, rfl⟩
    exact hle.trans (hz ⟨s, hs, rfl⟩ k)

end ScottContinuousOf

-- [D-1016] toEndPBilimit_monotone
theorem toEndPBilimit_monotone : Monotone (toEndPBilimit) := by
  intro F F' hFF' k w
  show (F (insertAtLevel k w)).1 k ≤ (F' (insertAtLevel k w)).1 k
  exact hFF' (insertAtLevel k w) k

-- [D-1017] ofEndPBilimit_monotone
theorem ofEndPBilimit_monotone : Monotone (ofEndPBilimit) := by
  intro f f' hff' y k
  show levelSup f y k ≤ levelSup f' y k
  apply sSup_le
  rintro _ ⟨n, h, rfl⟩
  have hle : f.1 n (y.1 n) ≤ f'.1 n (y.1 n) := hff' n (y.1 n)
  exact (pLe_monotone h _ _ hle).trans (le_sSup ⟨n, h, rfl⟩)

-- [D-1018] inst-PartialOrder
noncomputable instance : PartialOrder (ScottEndP DBilimit) := Subtype.partialOrder _

-- [D-1019] toEndPBilimitHom
noncomputable def toEndPBilimitHom : ScottEndP DBilimit →o EndPBilimit where
  toFun F := toEndPBilimit F.1
  monotone' _ _ h := toEndPBilimit_monotone h

-- [D-1020] ofEndPBilimitHom
noncomputable def ofEndPBilimitHom : EndPBilimit →o ScottEndP DBilimit where
  toFun f := ⟨ofEndPBilimit f, applyEndPBilimit_scottContinuous f⟩
  monotone' _ _ h := ofEndPBilimit_monotone h

-- [D-1021] toEndPBilimitHom_comp_ofEndPBilimitHom
theorem toEndPBilimitHom_comp_ofEndPBilimitHom :
    toEndPBilimitHom.comp ofEndPBilimitHom = OrderHom.id := by
  ext f
  show toEndPBilimit (ofEndPBilimit f) = f
  exact toEndPBilimit_ofEndPBilimit f

-- [D-1022] ofEndPBilimitHom_comp_toEndPBilimitHom
theorem ofEndPBilimitHom_comp_toEndPBilimitHom :
    ofEndPBilimitHom.comp toEndPBilimitHom = OrderHom.id := by
  ext F
  apply Subtype.ext
  show ofEndPBilimit (toEndPBilimit F.1) = F.1
  exact toEndPBilimit_ofEndPBilimit_of_continuous F.1 F.2

-- [D-1023] endPBilimitOrderIso
noncomputable def endPBilimitOrderIso : ScottEndP DBilimit ≃o EndPBilimit :=
  OrderIso.ofHomInv toEndPBilimitHom ofEndPBilimitHom
    toEndPBilimitHom_comp_ofEndPBilimitHom ofEndPBilimitHom_comp_toEndPBilimitHom

section Phase3aStep3

-- [D-1024] ShiftBilimit
def ShiftBilimit : Type := {y : ∀ k, D (k + 1) // ∀ k, pD (k + 1) (y (k + 1)) = y k}

-- [D-1025] inst-PartialOrder
noncomputable instance : PartialOrder ShiftBilimit := Subtype.partialOrder _

-- [D-1026] toShiftBilimit
noncomputable def toShiftBilimit (x : DBilimit) : ShiftBilimit :=
  ⟨fun k => x.1 (k + 1), fun k => x.2 (k + 1)⟩

-- [D-1027] ofShiftBilimit
noncomputable def ofShiftBilimit (y : ShiftBilimit) : DBilimit :=
  ⟨fun k => match k with
    | 0 => pD 0 (y.1 0)
    | n + 1 => y.1 n,
   by
    intro k
    cases k with
    | zero => rfl
    | succ n => exact y.2 n⟩

-- [D-1028] toShiftBilimit_ofShiftBilimit
theorem toShiftBilimit_ofShiftBilimit (y : ShiftBilimit) :
    toShiftBilimit (ofShiftBilimit y) = y := by
  apply Subtype.ext
  funext k
  rfl

-- [D-1029] ofShiftBilimit_toShiftBilimit
theorem ofShiftBilimit_toShiftBilimit (x : DBilimit) :
    ofShiftBilimit (toShiftBilimit x) = x := by
  apply Subtype.ext
  funext k
  cases k with
  | zero => exact x.2 0
  | succ n => rfl

-- [D-1030] toShiftBilimit_monotone
theorem toShiftBilimit_monotone : Monotone toShiftBilimit := by
  intro x x' hxx' k
  exact hxx' (k + 1)

-- [D-1031] ofShiftBilimit_monotone
theorem ofShiftBilimit_monotone : Monotone ofShiftBilimit := by
  intro y y' hyy' k
  cases k with
  | zero => exact pD_monotone 0 (y.1 0) (y'.1 0) (hyy' 0)
  | succ n => exact hyy' n

-- [D-1032] toShiftBilimitHom
noncomputable def toShiftBilimitHom : DBilimit →o ShiftBilimit where
  toFun := toShiftBilimit
  monotone' := toShiftBilimit_monotone

-- [D-1033] ofShiftBilimitHom
noncomputable def ofShiftBilimitHom : ShiftBilimit →o DBilimit where
  toFun := ofShiftBilimit
  monotone' := ofShiftBilimit_monotone

-- [D-1034] dBilimitShiftIso
noncomputable def dBilimitShiftIso : DBilimit ≃o ShiftBilimit :=
  OrderIso.ofHomInv toShiftBilimitHom ofShiftBilimitHom
    (by ext y; exact toShiftBilimit_ofShiftBilimit y)
    (by ext x; exact ofShiftBilimit_toShiftBilimit x)

-- [D-1035] glueA_pD_naive_square_fails
theorem glueA_pD_naive_square_fails :
    pD 1 (glueA (markedPt 1) (OrderHom.id : EndP (D 1)))
      ≠ glueA (markedPt 0) (pEndP 0 (OrderHom.id : EndP (D 1))) := by
  classical
  have hpEndP : pEndP 0 (OrderHom.id : EndP (D 1)) = (OrderHom.id : EndP (D 0)) := by
    ext x
    show pD 0 (iotaD 0 x) = x
    exact pD_iotaD 0 x
  rw [hpEndP]
  have hLHS : pD 1 (glueA (markedPt 1) (OrderHom.id : EndP (D 1)))
      = (⊥ : D 1) := by
    show (OrderHom.id : EndP (D 1)) (⊥ : D 1) = ⊥
    rfl
  rw [hLHS]
  have hbot : (⊥ : D 1) = glueA (markedPt 0) (⊥ : EndP (D 0)) := rfl
  rw [hbot]
  intro heq
  have hbt : (⊥ : D 0) ≠ ⊤ := bot_ne_top_of_nontrivial
  exact (endPId_ne_bot hbt) (glueA_injective (markedPt 0) heq).symm

end Phase3aStep3

-- [D-1036] liftEndP
noncomputable def liftEndP (k : ℕ) (f : EndP (D k)) : DBilimit → DBilimit :=
  fun x => insertAtLevel k (f (x.1 k))

-- [D-1037] liftEndP_monotone
theorem liftEndP_monotone (k : ℕ) (f : EndP (D k)) : Monotone (liftEndP k f) := by
  intro x x' hxx'
  exact insertAtLevel_monotone k (f.monotone (hxx' k))

-- [D-1038] liftEndP_scottContinuous
theorem liftEndP_scottContinuous (k : ℕ) (f : EndP (D k)) :
    ScottContinuous (liftEndP k f) := by
  intro S hSne hSdir a haLUB
  have han : a.1 k = sSup ((fun x : DBilimit => x.1 k) '' S) := haLUB.dbilimit_apply hSne hSdir k
  set T : Set (D k) := (fun x : DBilimit => x.1 k) '' S with hT
  have hTne : T.Nonempty := hSne.image _
  have hTdir : DirectedOn (· ≤ ·) T := DBilimit_directed_image k hSdir
  have hfTdir : DirectedOn (· ≤ ·) (f '' T) := directedOn_image_of_monotone f.monotone hTdir
  have hfTne : (f '' T).Nonempty := hTne.image _
  obtain ⟨t, htmem, htgr⟩ := directedOn_exists_greatest_of_finite (Set.toFinite (f '' T)) hfTne hfTdir
  have hft : f (a.1 k) = t := by
    rw [han, monotone_sSup_image_of_finite_directed f.monotone (Set.toFinite T) hTne hTdir]
    exact le_antisymm (sSup_le htgr) (le_sSup htmem)
  have haval : liftEndP k f a = insertAtLevel k t := by
    show insertAtLevel k (f (a.1 k)) = insertAtLevel k t
    rw [hft]
  rw [haval]
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show insertAtLevel k (f (s.1 k)) ≤ insertAtLevel k t
    exact insertAtLevel_monotone k (htgr (f (s.1 k)) ⟨s.1 k, ⟨s, hs, rfl⟩, rfl⟩)
  · intro z hz
    have : insertAtLevel k t ∈ liftEndP k f '' S := by
      obtain ⟨x, hx, hxeq⟩ := htmem
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨s, hs, by show insertAtLevel k (f (s.1 k)) = insertAtLevel k t; rw [hxeq]⟩
    exact hz this

-- [D-1039] liftEndP_iotaEndP
theorem liftEndP_iotaEndP (k : ℕ) (f : EndP (D k)) :
    liftEndP (k + 1) (iotaEndP k f) = liftEndP k f := by
  funext x
  show insertAtLevel (k + 1) (iotaD k (f (pD k (x.1 (k + 1))))) = insertAtLevel k (f (x.1 k))
  rw [insertAtLevel_iotaD, x.2 k]

-- [D-1040] pD_bot
theorem pD_bot (k : ℕ) : pD k (⊥ : D (k + 1)) = (⊥ : D k) := rfl

-- [D-1041] botSeq
noncomputable def botSeq : DBilimit := ⟨fun k => (⊥ : D k), pD_bot⟩

-- [D-1042] botSeq_le
theorem botSeq_le (z : DBilimit) : botSeq ≤ z := fun _ => bot_le

-- [D-1043] inst-OrderBot
noncomputable instance : OrderBot DBilimit := { bot := botSeq, bot_le := botSeq_le }

-- [D-1044] insertAtLevel_bot
theorem insertAtLevel_bot (k : ℕ) : insertAtLevel k (⊥ : D k) = botSeq := by
  apply le_antisymm
  · have h := insertAtLevel_le_self botSeq k
    rwa [show botSeq.1 k = (⊥ : D k) from rfl] at h
  · exact botSeq_le _

-- [D-1045] inst-OrderTop
noncomputable instance : OrderTop DBilimit := { top := topSeq, le_top := le_topSeq }

-- [D-1046] scottContinuous_const
theorem scottContinuous_const (v : DBilimit) :
    ScottContinuous (Function.const DBilimit v) := by
  intro S hSne _ a _
  constructor
  · rintro _ ⟨s, hs, rfl⟩; exact le_refl v
  · intro z hz
    obtain ⟨s, hs⟩ := hSne
    exact hz ⟨s, hs, rfl⟩

-- [D-1047] scottEndPBot
noncomputable def scottEndPBot : ScottEndP DBilimit :=
  ⟨OrderHom.const DBilimit ⊥, scottContinuous_const ⊥⟩
-- [D-1048] scottEndPTop
noncomputable def scottEndPTop : ScottEndP DBilimit :=
  ⟨OrderHom.const DBilimit ⊤, scottContinuous_const ⊤⟩

-- [D-1049] scottEndPBot_le
theorem scottEndPBot_le (F : ScottEndP DBilimit) : scottEndPBot ≤ F := fun _ => bot_le
-- [D-1050] le_scottEndPTop
theorem le_scottEndPTop (F : ScottEndP DBilimit) : F ≤ scottEndPTop := fun _ => le_top

-- [D-1051] inst-OrderBot
noncomputable instance : OrderBot (ScottEndP DBilimit) :=
  { bot := scottEndPBot, bot_le := scottEndPBot_le }

-- [D-1052] inst-OrderTop
noncomputable instance : OrderTop (ScottEndP DBilimit) :=
  { top := scottEndPTop, le_top := le_scottEndPTop }

-- [D-1053] inst-BoundedOrder
noncomputable instance : BoundedOrder (ScottEndP DBilimit) := {}

section PsiTargetType

-- [D-1054] botSeq_ne_topSeq
theorem botSeq_ne_topSeq : (botSeq : DBilimit) ≠ topSeq := by
  intro h
  exact bot_ne_top_of_nontrivial (congrArg (fun x : DBilimit => x.1 0) h)

-- [D-1055] scottEndPId
noncomputable def scottEndPId : ScottEndP DBilimit := ⟨OrderHom.id, by
  intro S hSne hSdir a haLUB
  simpa using haLUB⟩

-- [D-1056] scottEndPId_apply
@[simp] theorem scottEndPId_apply (x : DBilimit) :
    (scottEndPId : ScottEndP DBilimit).1 x = x := rfl
-- [D-1057] scottEndPBot_apply
@[simp] theorem scottEndPBot_apply (x : DBilimit) :
    (⊥ : ScottEndP DBilimit).1 x = (⊥ : DBilimit) := rfl
-- [D-1058] scottEndPTop_apply
@[simp] theorem scottEndPTop_apply (x : DBilimit) :
    (⊤ : ScottEndP DBilimit).1 x = (⊤ : DBilimit) := rfl

-- [D-1059] scottEndPId_ne_bot
theorem scottEndPId_ne_bot : (scottEndPId : ScottEndP DBilimit) ≠ ⊥ := by
  intro h
  have h1 := congrArg (fun f : ScottEndP DBilimit => f.1 topSeq) h
  simp only [scottEndPId_apply, scottEndPBot_apply] at h1
  exact botSeq_ne_topSeq h1.symm

-- [D-1060] scottEndPId_ne_top
theorem scottEndPId_ne_top : (scottEndPId : ScottEndP DBilimit) ≠ ⊤ := by
  intro h
  have h1 := congrArg (fun f : ScottEndP DBilimit => f.1 botSeq) h
  simp only [scottEndPId_apply, scottEndPTop_apply] at h1
  exact botSeq_ne_topSeq h1

-- [D-1061] scottEndPBot_ne_top
theorem scottEndPBot_ne_top : (⊥ : ScottEndP DBilimit) ≠ (⊤ : ScottEndP DBilimit) := by
  intro h
  have h1 := congrArg (fun f : ScottEndP DBilimit => f.1 topSeq) h
  simp only [scottEndPBot_apply, scottEndPTop_apply] at h1
  exact botSeq_ne_topSeq h1

-- [D-1062] psiTargetOrder
noncomputable def psiTargetOrder :
    PartialOrder (GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
  glueCarPartialOrderGen scottEndPId scottEndPId_ne_bot scottEndPId_ne_top scottEndPBot_ne_top

end PsiTargetType

-- [D-1063] glueAA
noncomputable def glueAA (k : ℕ) : D (k + 1) → D (k + 2) :=
  glueAAGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-1064] glueAA_monotone
theorem glueAA_monotone (k : ℕ) {x y : D (k + 1)} (hxy : x ≤ y) :
    glueAA k x ≤ glueAA k y :=
  glueAAGenM_monotone (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial hxy

-- [D-1065] glueAA_reflect
theorem glueAA_reflect (k : ℕ) {x y : D (k + 1)} (hxy : glueAA k x ≤ glueAA k y) : x ≤ y :=
  glueAAGenM_reflect (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial hxy

-- [D-1066] glueAA_le_iff
theorem glueAA_le_iff (k : ℕ) {x y : D (k + 1)} : glueAA k x ≤ glueAA k y ↔ x ≤ y :=
  ⟨glueAA_reflect k, glueAA_monotone k⟩

-- [D-1067] glueAA_injective
theorem glueAA_injective (k : ℕ) : Function.Injective (glueAA k) := fun x y h =>
  le_antisymm ((glueAA_le_iff k).mp h.le) ((glueAA_le_iff k).mp h.ge)

-- [D-1068] glueAA_iotaD
theorem glueAA_iotaD (k : ℕ) (x : D k) :
    glueAA k (iotaD k x) = iotaD (k + 1) (iotaD k x) :=
  glueAAGenM_iotaGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial x

-- [D-1069] pD_glueAA_deflation_tagA
theorem pD_glueAA_deflation_tagA (k : ℕ) (f : EndP (D k)) :
    pD (k + 1) (glueAA k (⟨Sum.inl f, rfl⟩ : D (k + 1))) ≤ (⟨Sum.inl f, rfl⟩ : D (k + 1)) :=
  glueAAGenM_pGenM_deflation_tagA (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial f

-- [D-1070] pD_glueAA_deflation_tagB
theorem pD_glueAA_deflation_tagB (k : ℕ) {f : EndP (D k)}
    (hxv : canon (markedPt k) (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl f))
    (hft : f ≠ (⊤ : EndP (D k))) :
    pD (k + 1) (glueAA k (⟨Sum.inr (Sum.inl f), hxv⟩ : D (k + 1)))
      ≤ (⟨Sum.inr (Sum.inl f), hxv⟩ : D (k + 1)) :=
  glueAAGenM_pGenM_deflation_tagB (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial hxv hft

-- [D-1071] pD_crossTag_CA_sufficient
theorem pD_crossTag_CA_sufficient (k : ℕ) (f : EndP (D k))
    (hfb : f ≠ (⊥ : EndP (D k))) (hfm : f ≠ (markedPt k))
    (hidf : (markedPt k) ≤ f)
    (hxv : canon (markedPt k) (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr f))
    (Y : D (k + 1))
    (hY : pD k Y = f (⊥ : D k)) :
    Y ≤ (⟨Sum.inr (Sum.inr f), hxv⟩ : D (k + 1)) := by
  have h := crossTag_CA_sufficientM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial f hfb hfm hidf Y hY
  exact le_of_le_of_eq h (Subtype.ext hxv)

section Phase3aStep4PsiInv

-- [D-1072] PsiInv
noncomputable def PsiInv (w : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) : DBilimit :=
  match w.1 with
  | Sum.inl x => x.1 botSeq
  | Sum.inr (Sum.inl x) => if x = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit)
  | Sum.inr (Sum.inr _) => (⊤ : DBilimit)

-- [D-1073] liftEndPHom
noncomputable def liftEndPHom (k : ℕ) (f : EndP (D k)) : ScottEndP DBilimit :=
  ⟨⟨liftEndP k f, liftEndP_monotone k f⟩, liftEndP_scottContinuous k f⟩

-- [D-1074] liftEndPHom_apply
theorem liftEndPHom_apply (k : ℕ) (f : EndP (D k)) (x : DBilimit) :
    (liftEndPHom k f).1 x = insertAtLevel k (f (x.1 k)) := rfl

-- [D-1075] PsiInv_liftEndPHom
theorem PsiInv_liftEndPHom (k : ℕ) (f : EndP (D k)) :
    PsiInv ⟨Sum.inl (liftEndPHom k f), rfl⟩ = insertAtLevel k (f (⊥ : D k)) := by
  show (liftEndPHom k f).1 botSeq = insertAtLevel k (f (⊥ : D k))
  rw [liftEndPHom_apply]
  have hb : (botSeq : DBilimit).1 k = (⊥ : D k) := rfl
  rw [hb]

end Phase3aStep4PsiInv

-- [D-1076] PsiInv_monotone
theorem PsiInv_monotone (w w' : GlueCarGen (P := ScottEndP DBilimit) scottEndPId)
    (hle : w ≤ w') : PsiInv w ≤ PsiInv w' := by
  rw [GlueCarGen.le_def] at hle
  obtain ⟨wv, hwv⟩ := w
  obtain ⟨wv', hwv'⟩ := w'
  simp only at hle
  rcases wv with x | x | x <;> rcases wv' with x' | x' | x'
  ·
    show x.1 botSeq ≤ x'.1 botSeq
    have h : x ≤ x' := (tagA_isoGen scottEndPId scottEndPId_ne_bot x x').mp hle
    exact h botSeq
  ·
    show x.1 botSeq ≤ (if x' = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit))
    by_cases hx't : x' = (⊤ : ScottEndP DBilimit)
    · rw [if_pos hx't]; exact le_top
    · rw [if_neg hx't]
      have hxm : x ≤ (scottEndPId : ScottEndP DBilimit) :=
        (leGlue_tagA_tagB_iffGen scottEndPId x x' hx't).mp hle
      exact hxm botSeq
  ·
    show x.1 botSeq ≤ (⊤ : DBilimit)
    exact le_top
  ·
    exact absurd hle (not_leGlue_tagB_tagAGen scottEndPId x x' scottEndPId_ne_bot
      scottEndPBot_ne_top (ne_bot_of_canon_tagBGen scottEndPId x hwv))
  ·
    show (if x = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit)) ≤
        (if x' = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit))
    by_cases hx't : x' = (⊤ : ScottEndP DBilimit)
    · rw [if_pos hx't]; exact le_top
    · have hxb : x ≠ (⊥ : ScottEndP DBilimit) := ne_bot_of_canon_tagBGen _ x hwv
      have hxle : x ≤ x' := (leGlue_tagB_tagB_iffGen scottEndPId x x' hx't hxb).mp hle
      have hxne : x ≠ (⊤ : ScottEndP DBilimit) := fun hxT => hx't (top_le_iff.mp (hxT ▸ hxle))
      rw [if_neg hxne, if_neg hx't]
  ·
    show (if x = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit)) ≤ (⊤ : DBilimit)
    exact le_top
  ·
    exact absurd hle (not_leGlue_tagC_tagAGen scottEndPId x x'
      (ne_bot_of_canon_tagCGen scottEndPId x hwv))
  ·
    by_cases hx't : x' = (⊤ : ScottEndP DBilimit)
    · show (⊤ : DBilimit) ≤ (if x' = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit))
      rw [if_pos hx't]
    · exact absurd hle (not_leGlue_tagC_tagBGen scottEndPId x x' hx't)
  ·
    show (⊤ : DBilimit) ≤ (⊤ : DBilimit)
    exact le_refl _

section Phase3aStep4PsiInvDeflation

-- [D-1077] constScottHom
noncomputable def constScottHom (v : DBilimit) : ScottEndP DBilimit :=
  ⟨OrderHom.const DBilimit v, scottContinuous_const v⟩

-- [D-1078] constScottHom_apply
theorem constScottHom_apply (v x : DBilimit) : (constScottHom v).1 x = v := rfl

-- [D-1079] PsiInv_deflation
theorem PsiInv_deflation (w : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :
    leGlueGen scottEndPId (Sum.inl (constScottHom (PsiInv w))) w.1 := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with x | x | x
  ·
    show leGlueGen scottEndPId (Sum.inl (constScottHom (x.1 botSeq))) (Sum.inl x)
    refine ⟨Sum.inl (constScottHom (x.1 botSeq)), self_mem_occsGen _ _, Sum.inl x,
      self_mem_occsGen _ _, ?_⟩
    show (constScottHom (x.1 botSeq) : ScottEndP DBilimit) ≤ x
    intro z
    exact x.1.monotone (botSeq_le z)
  ·
    show leGlueGen scottEndPId
        (Sum.inl (constScottHom
          (if x = (⊤ : ScottEndP DBilimit) then (⊤ : DBilimit) else (⊥ : DBilimit))))
        (Sum.inr (Sum.inl x))
    by_cases hxt : x = (⊤ : ScottEndP DBilimit)
    · rw [if_pos hxt, hxt]
      exact leGlue_tagA_tagB_topGen scottEndPId (constScottHom (⊤ : DBilimit))
    · rw [if_neg hxt]
      exact (leGlue_tagA_tagB_iffGen scottEndPId (constScottHom (⊥ : DBilimit)) x hxt).mpr (by
        intro z
        exact bot_le)
  ·
    show leGlueGen scottEndPId (Sum.inl (constScottHom (⊤ : DBilimit))) (Sum.inr (Sum.inr x))
    exact ⟨Sum.inl (constScottHom (⊤ : DBilimit)), self_mem_occsGen _ _, Sum.inr (Sum.inr x),
      self_mem_occsGen _ _, trivial⟩

end Phase3aStep4PsiInvDeflation

section Phase3aStep4Psi

-- [D-1080] Psi
noncomputable def Psi (x : DBilimit) : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inl (constScottHom x), rfl⟩

-- [D-1081] Psi_apply
@[simp] theorem Psi_apply (x : DBilimit) :
    (Psi x).1 = Sum.inl (constScottHom x) := rfl

-- [D-1082] PsiInv_Psi
theorem PsiInv_Psi (x : DBilimit) : PsiInv (Psi x) = x := rfl

-- [D-1083] Psi_monotone
theorem Psi_monotone (x x' : DBilimit) (hxx' : x ≤ x') : Psi x ≤ Psi x' := by
  show leGlueGen scottEndPId (Sum.inl (constScottHom x)) (Sum.inl (constScottHom x'))
  refine (tagA_isoGen scottEndPId scottEndPId_ne_bot (constScottHom x) (constScottHom x')).mpr ?_
  intro z
  exact hxx'

-- [D-1084] Psi_le_iff
theorem Psi_le_iff (x x' : DBilimit) : Psi x ≤ Psi x' ↔ x ≤ x' := by
  constructor
  · intro h
    have := PsiInv_monotone (Psi x) (Psi x') h
    rwa [PsiInv_Psi, PsiInv_Psi] at this
  · exact Psi_monotone x x'

-- [D-1085] Psi_injective
theorem Psi_injective : Function.Injective Psi :=
  Function.LeftInverse.injective PsiInv_Psi

-- [D-1086] Psi_PsiInv_le
theorem Psi_PsiInv_le (w : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :
    Psi (PsiInv w) ≤ w :=
  PsiInv_deflation w

end Phase3aStep4Psi

section PsiIsoStepB1

-- [D-1087] pEndP_id
theorem pEndP_id (k : ℕ) :
    pEndP k (OrderHom.id : EndP (D (k + 1))) = (OrderHom.id : EndP (D k)) := by
  ext x
  show pD k (iotaD k x) = x
  exact pD_iotaD k x

-- [D-1088] pEndP_bot
theorem pEndP_bot (k : ℕ) :
    pEndP k (⊥ : EndP (D (k + 1))) = (⊥ : EndP (D k)) := by
  ext x
  show pD k ((⊥ : EndP (D (k + 1))) (iotaD k x)) = (⊥ : D k)
  rw [endPBot_apply, pD_bot]

-- [D-1089] pEndP_top
theorem pEndP_top (k : ℕ) :
    pEndP k (⊤ : EndP (D (k + 1))) = (⊤ : EndP (D k)) := by
  ext x
  show pD k ((⊤ : EndP (D (k + 1))) (iotaD k x)) = (⊤ : D k)
  rw [endPTop_apply, pD_top]

-- [D-1090] ebId
noncomputable def ebId : EndPBilimit := ⟨fun _ => OrderHom.id, fun k => pEndP_id k⟩

-- [D-1091] ebBot
noncomputable def ebBot : EndPBilimit := ⟨fun _ => ⊥, fun k => pEndP_bot k⟩

-- [D-1092] ebTop
noncomputable def ebTop : EndPBilimit := ⟨fun _ => ⊤, fun k => pEndP_top k⟩

-- [D-1093] ebBot_le
theorem ebBot_le (f : EndPBilimit) : ebBot ≤ f := fun _ => bot_le
-- [D-1094] le_ebTop
theorem le_ebTop (f : EndPBilimit) : f ≤ ebTop := fun _ => le_top

-- [D-1095] inst-OrderBot
noncomputable instance : OrderBot EndPBilimit := { bot := ebBot, bot_le := ebBot_le }
-- [D-1096] inst-OrderTop
noncomputable instance : OrderTop EndPBilimit := { top := ebTop, le_top := le_ebTop }
-- [D-1097] inst-BoundedOrder
noncomputable instance : BoundedOrder EndPBilimit := {}

-- [D-1098] endPBilimitOrderIso_scottEndPId
theorem endPBilimitOrderIso_scottEndPId :
    endPBilimitOrderIso scottEndPId = ebId := by
  show toEndPBilimit scottEndPId.1 = ebId
  apply Subtype.ext
  funext k
  ext w
  change (scottEndPId.1 (insertAtLevel k w)).1 k = w
  exact insertAtLevel_self k w

-- [D-1099] glueCarGenScottEndPId_iso_ebId
noncomputable def glueCarGenScottEndPId_iso_ebId :
    GlueCarGen (P := ScottEndP DBilimit) scottEndPId ≃o
      GlueCarGen (P := EndPBilimit) ebId := by
  rw [← endPBilimitOrderIso_scottEndPId]
  exact glueCarGenOrderIso endPBilimitOrderIso scottEndPId

end PsiIsoStepB1

-- [D-1100] DBilimit_reflexive
theorem DBilimit_reflexive :
    (∀ x : DBilimit, PsiInv (Psi x) = x) ∧
    (∀ w, Psi (PsiInv w) ≤ w) ∧
    (∀ x x' : DBilimit, x ≤ x' → Psi x ≤ Psi x') ∧
    (∀ w w', w ≤ w' → PsiInv w ≤ PsiInv w') ∧
    (∀ x x' : DBilimit, Psi x ≤ Psi x' ↔ x ≤ x') :=
  ⟨PsiInv_Psi, Psi_PsiInv_le, fun x x' h => Psi_monotone x x' h,
   fun w w' h => PsiInv_monotone w w' h, Psi_le_iff⟩

section PsiIsoNatural

-- [D-1101] eK
noncomputable def eK (k : ℕ) : D k → DBilimit := toDBilimit ∘ toD k

-- [D-1102] eK_eq_insertAtLevel
theorem eK_eq_insertAtLevel (k : ℕ) : eK k = insertAtLevel k := by
  funext x
  show toDBilimit (toD k x) = insertAtLevel k x
  rfl

-- [D-1103] eK_monotone
theorem eK_monotone (k : ℕ) : Monotone (eK k) := by
  rw [eK_eq_insertAtLevel]; exact insertAtLevel_monotone k

-- [D-1104] eK_scottContinuous
theorem eK_scottContinuous (k : ℕ) : ScottContinuous (eK k) :=
  monotone_scottContinuous_of_finite_dom (eK_monotone k)

-- [D-1105] projK
noncomputable def projK (k : ℕ) : DBilimit → D k := fun z => z.1 k

-- [D-1106] projK_monotone
theorem projK_monotone (k : ℕ) : Monotone (projK k) := fun _ _ h => h k

-- [D-1107] projK_scottContinuous
theorem projK_scottContinuous (k : ℕ) : ScottContinuous (projK k) := by
  intro S hSne hSdir a haLUB
  rw [show projK k a = a.1 k from rfl, haLUB.dbilimit_apply hSne hSdir k]
  exact isLUB_sSup _

-- [D-1108] eK_projK_retraction
theorem eK_projK_retraction (k : ℕ) (x : D k) : projK k (eK k x) = x := toDBilimit_toD k x

-- [D-1109] eK_projK_deflation
theorem eK_projK_deflation (k : ℕ) (z : DBilimit) : eK k (projK k z) ≤ z := by
  rw [eK_eq_insertAtLevel]
  exact insertAtLevel_le_self z k

-- [D-1110] IsColimitCocone
structure IsColimitCocone {X : Type*} [PartialOrder X]
    (e : ∀ k, D k → X) (p : ∀ k, X → D k) : Prop where
  retraction : ∀ k x, p k (e k x) = x
  deflation : ∀ k z, e k (p k z) ≤ z
  compat : ∀ k w, e (k + 1) (iotaD k w) = e k w
  isLUB : ∀ z, IsLUB (Set.range (fun k => e k (p k z))) z

-- [D-1111] DBilimit_isColimitCocone
theorem DBilimit_isColimitCocone : IsColimitCocone eK projK where
  retraction := eK_projK_retraction
  deflation := eK_projK_deflation
  compat k w := by
    rw [eK_eq_insertAtLevel]
    exact insertAtLevel_iotaD k w
  isLUB z := by
    have h := chainSet_isLUB z
    have hset : chainSet z = Set.range (fun k => eK k (projK k z)) := by
      simp only [chainSet, eK_eq_insertAtLevel, projK]
    rwa [hset] at h

-- [D-1112] instPartialOrderScottEndPD
noncomputable instance instPartialOrderScottEndPD (k : ℕ) : PartialOrder (ScottEndP (D k)) :=
  Subtype.partialOrder _

-- [D-1113] scottEndPBotD
noncomputable def scottEndPBotD (k : ℕ) : ScottEndP (D k) :=
  ⟨OrderHom.const (D k) ⊥, monotone_scottContinuous_of_finite (OrderHom.const (D k) ⊥).monotone⟩
-- [D-1114] scottEndPTopD
noncomputable def scottEndPTopD (k : ℕ) : ScottEndP (D k) :=
  ⟨OrderHom.const (D k) ⊤, monotone_scottContinuous_of_finite (OrderHom.const (D k) ⊤).monotone⟩

-- [D-1115] scottEndPBotD_le
theorem scottEndPBotD_le (k : ℕ) (F : ScottEndP (D k)) : scottEndPBotD k ≤ F := fun _ => bot_le
-- [D-1116] le_scottEndPTopD
theorem le_scottEndPTopD (k : ℕ) (F : ScottEndP (D k)) : F ≤ scottEndPTopD k := fun _ => le_top

-- [D-1117] instOrderBotScottEndPD
noncomputable instance instOrderBotScottEndPD (k : ℕ) : OrderBot (ScottEndP (D k)) :=
  { bot := scottEndPBotD k, bot_le := scottEndPBotD_le k }
-- [D-1118] instOrderTopScottEndPD
noncomputable instance instOrderTopScottEndPD (k : ℕ) : OrderTop (ScottEndP (D k)) :=
  { top := scottEndPTopD k, le_top := le_scottEndPTopD k }
-- [D-1119] instBoundedOrderScottEndPD
noncomputable instance instBoundedOrderScottEndPD (k : ℕ) : BoundedOrder (ScottEndP (D k)) := {}

-- [D-1120] endPScottEndPIso
noncomputable def endPScottEndPIso (k : ℕ) : EndP (D k) ≃o ScottEndP (D k) :=
  OrderIso.ofHomInv
    { toFun := fun f => ⟨f, monotone_scottContinuous_of_finite f.monotone⟩,
      monotone' := fun _ _ h => h }
    { toFun := fun F => F.1, monotone' := fun _ _ h => h }
    (by ext f; rfl)
    (by ext F; rfl)

-- [D-1121] example-D
example (k : ℕ) : D (k + 1) = GlueCarGen (P := EndP (D k)) (markedPt k) := rfl

end PsiIsoNatural

section Phase3bCoreIFS

-- [D-1122] fA_mapsTo_Gamma
theorem fA_mapsTo_Gamma : fA '' Gamma ⊆ Gamma := by
  have h : fA '' Gamma ⊆ fA '' Gamma ∪ fB '' Gamma ∪ fC '' Gamma :=
    Set.subset_union_left.trans Set.subset_union_left
  rwa [← Gamma_self_similar] at h

-- [D-1123] fB_mapsTo_Gamma
theorem fB_mapsTo_Gamma : fB '' Gamma ⊆ Gamma := by
  have h : fB '' Gamma ⊆ fA '' Gamma ∪ fB '' Gamma ∪ fC '' Gamma :=
    Set.subset_union_right.trans Set.subset_union_left
  rwa [← Gamma_self_similar] at h

-- [D-1124] fC_mapsTo_Gamma
theorem fC_mapsTo_Gamma : fC '' Gamma ⊆ Gamma := by
  have h : fC '' Gamma ⊆ fA '' Gamma ∪ fB '' Gamma ∪ fC '' Gamma :=
    Set.subset_union_right
  rwa [← Gamma_self_similar] at h

end Phase3bCoreIFS
section Phase4Pi
-- [D-1125] Addr
abbrev Addr := ℕ → Fin 3

-- [D-1126] symF
noncomputable def symF : Fin 3 → Plane → Plane
  | 0 => fA
  | 1 => fB
  | 2 => fC

-- [D-1127] lipschitzWith_symF
theorem lipschitzWith_symF (i : Fin 3) : LipschitzWith (2⁻¹ : NNReal) (symF i) := by
  fin_cases i
  · exact lipschitzWith_fA
  · exact lipschitzWith_fB
  · exact lipschitzWith_fC

-- [D-1128] wordPrefix
def wordPrefix (w : Addr) (n : ℕ) : List (Fin 3) := (List.range n).map w

-- [D-1129] wordPrefix_length
theorem wordPrefix_length (w : Addr) (n : ℕ) : (wordPrefix w n).length = n := by
  simp [wordPrefix]

-- [D-1130] wordPrefix_succ
theorem wordPrefix_succ (w : Addr) (n : ℕ) :
    wordPrefix w (n + 1) = wordPrefix w n ++ [w n] := by
  simp [wordPrefix, List.range_succ]

-- [D-1131] applyList
noncomputable def applyList (l : List (Fin 3)) : Plane → Plane :=
  l.foldr (fun i acc => symF i ∘ acc) id

-- [D-1132] applyList_nil
theorem applyList_nil : applyList ([] : List (Fin 3)) = id := rfl

-- [D-1133] applyList_cons
theorem applyList_cons (a : Fin 3) (l : List (Fin 3)) :
    applyList (a :: l) = symF a ∘ applyList l := rfl

-- [D-1134] lipschitzWith_applyList
theorem lipschitzWith_applyList (l : List (Fin 3)) :
    LipschitzWith ((2⁻¹ : NNReal) ^ l.length) (applyList l) := by
  induction l with
  | nil => simpa [applyList_nil] using LipschitzWith.id (α := Plane)
  | cons a l ih =>
      rw [applyList_cons, List.length_cons, pow_succ']
      exact (lipschitzWith_symF a).comp ih

-- [D-1135] applyList_append_singleton
theorem applyList_append_singleton (l : List (Fin 3)) (a : Fin 3) (x : Plane) :
    applyList (l ++ [a]) x = applyList l (symF a x) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [applyList_cons, ih]

-- [D-1136] applyList_mem_Gamma
theorem applyList_mem_Gamma (l : List (Fin 3)) {x : Plane} (hx : x ∈ Gamma) :
    applyList l x ∈ Gamma := by
  induction l with
  | nil => simpa [applyList_nil] using hx
  | cons a l ih =>
      rw [applyList_cons]
      simp only [Function.comp_apply]
      fin_cases a
      · exact fA_mapsTo_Gamma ⟨_, ih, rfl⟩
      · exact fB_mapsTo_Gamma ⟨_, ih, rfl⟩
      · exact fC_mapsTo_Gamma ⟨_, ih, rfl⟩

-- [D-1137] fA_fixed_vA
theorem fA_fixed_vA : fA vA = vA := by
  simp only [fA, vA]
  module

-- [D-1138] contractingWith_fA
theorem contractingWith_fA : ContractingWith (2⁻¹ : NNReal) fA :=
  ⟨by norm_num, lipschitzWith_fA⟩

-- [D-1139] fixedPoint_fA_eq_vA
theorem fixedPoint_fA_eq_vA : ContractingWith.fixedPoint fA contractingWith_fA = vA :=
  (ContractingWith.fixedPoint_unique contractingWith_fA fA_fixed_vA).symm

-- [D-1140] fA_iterate_mem_Gamma
theorem fA_iterate_mem_Gamma (g0 : Plane) (hg0 : g0 ∈ Gamma) (n : ℕ) :
    fA^[n] g0 ∈ Gamma := by
  induction n with
  | zero => simpa using hg0
  | succ n ih =>
      rw [Function.iterate_succ']
      exact fA_mapsTo_Gamma ⟨fA^[n] g0, ih, rfl⟩

-- [D-1141] vA_mem_Gamma
theorem vA_mem_Gamma : vA ∈ Gamma := by
  obtain ⟨g0, hg0⟩ := nonempty_Gamma
  have htendsto : Filter.Tendsto (fun n => fA^[n] g0) Filter.atTop (nhds vA) := by
    rw [← fixedPoint_fA_eq_vA]
    exact ContractingWith.tendsto_iterate_fixedPoint contractingWith_fA g0
  exact isCompact_Gamma.isClosed.mem_of_tendsto htendsto
    (Filter.Eventually.of_forall (fA_iterate_mem_Gamma g0 hg0))

-- [D-1142] piApprox
noncomputable def piApprox (w : Addr) (n : ℕ) : Plane := applyList (wordPrefix w n) vA

-- [D-1143] piStepBound
noncomputable def piStepBound : ℝ :=
  max (dist (symF 0 vA) vA) (max (dist (symF 1 vA) vA) (dist (symF 2 vA) vA))

-- [D-1144] dist_symF_vA_le
theorem dist_symF_vA_le (i : Fin 3) : dist (symF i vA) vA ≤ piStepBound := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

-- [D-1145] piApprox_succ_dist
theorem piApprox_succ_dist (w : Addr) (n : ℕ) :
    dist (piApprox w n) (piApprox w (n + 1)) ≤ piStepBound * (2⁻¹ : ℝ) ^ n := by
  have heq : piApprox w (n + 1) = applyList (wordPrefix w n) (symF (w n) vA) := by
    simp only [piApprox, wordPrefix_succ]
    exact applyList_append_singleton _ _ _
  rw [heq, piApprox, dist_comm]
  have hlip := (lipschitzWith_applyList (wordPrefix w n)).dist_le_mul (symF (w n) vA) vA
  rw [wordPrefix_length] at hlip
  calc dist (applyList (wordPrefix w n) (symF (w n) vA)) (applyList (wordPrefix w n) vA)
      ≤ ((2⁻¹ : NNReal) ^ n : ℝ) * dist (symF (w n) vA) vA := hlip
    _ ≤ ((2⁻¹ : NNReal) ^ n : ℝ) * piStepBound :=
        mul_le_mul_of_nonneg_left (dist_symF_vA_le (w n)) (by positivity)
    _ = piStepBound * (2⁻¹ : ℝ) ^ n := by push_cast; ring

-- [D-1146] piApprox_cauchySeq
theorem piApprox_cauchySeq (w : Addr) : CauchySeq (piApprox w) :=
  cauchySeq_of_le_geometric (2⁻¹ : ℝ) piStepBound (by norm_num) (piApprox_succ_dist w)

-- [D-1147] piCoding
noncomputable def piCoding (w : Addr) : Plane :=
  (cauchySeq_tendsto_of_complete (piApprox_cauchySeq w)).choose

-- [D-1148] piCoding_tendsto
theorem piCoding_tendsto (w : Addr) :
    Filter.Tendsto (piApprox w) Filter.atTop (nhds (piCoding w)) :=
  (cauchySeq_tendsto_of_complete (piApprox_cauchySeq w)).choose_spec

-- [D-1149] piCoding_mem_Gamma
theorem piCoding_mem_Gamma (w : Addr) : piCoding w ∈ Gamma :=
  isCompact_Gamma.isClosed.mem_of_tendsto (piCoding_tendsto w)
    (Filter.Eventually.of_forall (fun n => applyList_mem_Gamma (wordPrefix w n) vA_mem_Gamma))

-- [D-1150] prependAddr
def prependAddr (i : Fin 3) (w : Addr) : Addr
  | 0 => i
  | n + 1 => w n

-- [D-1151] wordPrefix_prepend
theorem wordPrefix_prepend (i : Fin 3) (w : Addr) (n : ℕ) :
    wordPrefix (prependAddr i w) (n + 1) = i :: wordPrefix w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [wordPrefix_succ (prependAddr i w) (n + 1), ih, wordPrefix_succ w n]
      rfl

-- [D-1152] piApprox_prepend_succ
theorem piApprox_prepend_succ (i : Fin 3) (w : Addr) (n : ℕ) :
    piApprox (prependAddr i w) (n + 1) = symF i (piApprox w n) := by
  simp only [piApprox, wordPrefix_prepend, applyList_cons, Function.comp_apply]

-- [D-1153] piCoding_equivariant
theorem piCoding_equivariant (i : Fin 3) (w : Addr) :
    piCoding (prependAddr i w) = symF i (piCoding w) := by
  have h1 : Filter.Tendsto (fun n => piApprox (prependAddr i w) (n + 1)) Filter.atTop
      (nhds (piCoding (prependAddr i w))) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 (piCoding_tendsto (prependAddr i w))
  have h2 : Filter.Tendsto (fun n => symF i (piApprox w n)) Filter.atTop
      (nhds (symF i (piCoding w))) :=
    ((lipschitzWith_symF i).continuous.tendsto (piCoding w)).comp (piCoding_tendsto w)
  have h3 : (fun n => piApprox (prependAddr i w) (n + 1)) = (fun n => symF i (piApprox w n)) :=
    funext (piApprox_prepend_succ i w)
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end Phase4Pi

section Phase4Alpha

-- [D-1154] constScottHom_bot_eq
theorem constScottHom_bot_eq : constScottHom (⊥ : DBilimit) = (⊥ : ScottEndP DBilimit) := rfl

-- [D-1155] constScottHom_top_eq
theorem constScottHom_top_eq : constScottHom (⊤ : DBilimit) = (⊤ : ScottEndP DBilimit) := rfl

-- [D-1156] constScottHom_injective
theorem constScottHom_injective : Function.Injective constScottHom := by
  intro x y hxy
  have := congrArg (fun f => f.1 x) hxy
  simpa [constScottHom] using this

-- [D-1157] constScottHom_eq_bot_iff
theorem constScottHom_eq_bot_iff {x : DBilimit} :
    constScottHom x = (⊥ : ScottEndP DBilimit) ↔ x = ⊥ := by
  rw [← constScottHom_bot_eq]
  exact constScottHom_injective.eq_iff

-- [D-1158] constScottHom_eq_top_iff
theorem constScottHom_eq_top_iff {x : DBilimit} :
    constScottHom x = (⊤ : ScottEndP DBilimit) ↔ x = ⊤ := by
  rw [← constScottHom_top_eq]
  exact constScottHom_injective.eq_iff

-- [D-1159] constScottHom_monotone
theorem constScottHom_monotone {x x' : DBilimit} (hxx' : x ≤ x') :
    constScottHom x ≤ constScottHom x' := fun _ => hxx'

-- [D-1160] leGlue_tagB_tagB_topGen
theorem leGlue_tagB_tagB_topGen {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
    (m w : P) : leGlueGen m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inl (⊤ : P))) := by
  refine ⟨Sum.inr (Sum.inl w), self_mem_occsGen m _, Sum.inr (Sum.inr m), ?_, le_refl m⟩
  simp [occsGen]

-- [D-1161] tagC_one_le_tagB_top
theorem tagC_one_le_tagB_top :
    leGlueGen (⊤ : Fin 3) (Sum.inr (Sum.inr (1 : Fin 3))) (Sum.inr (Sum.inl (⊤ : Fin 3))) := by
  refine ⟨Sum.inr (Sum.inr (1 : Fin 3)), self_mem_occsGen _ _,
    Sum.inr (Sum.inr (⊤ : Fin 3)), List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
  show (1 : Fin 3) ≤ ⊤
  exact le_top

-- [D-1162] not_tagB_top_le_tagC_one
theorem not_tagB_top_le_tagC_one :
    ¬ leGlueGen (⊤ : Fin 3) (Sum.inr (Sum.inl (⊤ : Fin 3))) (Sum.inr (Sum.inr (1 : Fin 3))) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hu' : u ∈ ([Sum.inr (Sum.inl (⊤ : Fin 3)), Sum.inr (Sum.inr (⊤ : Fin 3))] :
      List (GlueBaseGen (Fin 3))) := hu
  have hv' : v ∈ ([Sum.inr (Sum.inr (1 : Fin 3))] : List (GlueBaseGen (Fin 3))) := hv
  have hveq : v = Sum.inr (Sum.inr (1 : Fin 3)) := List.mem_singleton.mp hv'
  subst hveq
  simp at hu'
  rcases hu' with rfl | rfl <;>
    · have hle : (⊤ : Fin 3) ≤ 1 := huv
      exact absurd hle (by decide)

-- [D-1163] tagC_cofinality_fails
theorem tagC_cofinality_fails :
    ∃ S : Set (GlueBaseGen (Fin 3)),
      (∃ w, Sum.inr (Sum.inr w) ∈ S) ∧
      DirectedOn (leGlueGen (⊤ : Fin 3)) S ∧
      ∃ v ∈ S, ∀ w, Sum.inr (Sum.inr w) ∈ S →
        ¬ leGlueGen (⊤ : Fin 3) v (Sum.inr (Sum.inr w)) := by
  refine ⟨{Sum.inr (Sum.inl (⊤ : Fin 3)), Sum.inr (Sum.inr (1 : Fin 3))},
    ⟨1, Set.mem_insert_of_mem _ rfl⟩, ?_, ?_⟩
  · rintro x (rfl | rfl) y (rfl | rfl) <;>
      exact ⟨Sum.inr (Sum.inl (⊤ : Fin 3)), Set.mem_insert _ _, by
        first | exact leGlueGen_refl _ _ | exact tagC_one_le_tagB_top,
        by first | exact leGlueGen_refl _ _ | exact tagC_one_le_tagB_top⟩
  · refine ⟨Sum.inr (Sum.inl (⊤ : Fin 3)), Set.mem_insert _ _, ?_⟩
    intro w hw hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hcontra | hweq
    · exact absurd hcontra (by simp)
    · have hweq' : w = (1 : Fin 3) := by
        rw [Sum.inr.injEq, Sum.inr.injEq] at hweq; exact hweq
      subst hweq'
      exact not_tagB_top_le_tagC_one hle

-- [D-1164] scottEndPId_ne_constScottHom
theorem scottEndPId_ne_constScottHom (v : DBilimit) : scottEndPId ≠ constScottHom v := by
  intro h
  have h1 := congrArg (fun f : ScottEndP DBilimit => f.1 botSeq) h
  have h2 := congrArg (fun f : ScottEndP DBilimit => f.1 topSeq) h
  simp only [scottEndPId_apply, constScottHom_apply] at h1 h2
  exact botSeq_ne_topSeq (h1.trans h2.symm)

section SigmaAContinuous
-- [D-1165] Psi_isLUB
theorem Psi_isLUB {S : Set DBilimit} {y : DBilimit} (hy : IsLUB S y) :
    IsLUB (Psi '' S) (Psi y) := by
  constructor
  · rintro _ ⟨w, hwS, rfl⟩
    exact Psi_monotone w y (hy.1 hwS)
  · intro b hb
    obtain ⟨bv, hbv⟩ := b
    rw [GlueCarGen.le_def]
    show leGlueGen scottEndPId (Sum.inl (constScottHom y)) bv
    rcases bv with s | t | r
    · have hcond : ∀ w ∈ S, constScottHom w ≤ s := by
        intro w hwS
        have h : Psi w ≤ (⟨Sum.inl s, hbv⟩ : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
          hb ⟨w, hwS, rfl⟩
        rw [GlueCarGen.le_def] at h
        exact (tagA_isoGen scottEndPId scottEndPId_ne_bot (constScottHom w) s).mp h
      have hsup : constScottHom y ≤ s := by
        intro d
        show y ≤ s.1 d
        apply hy.2
        intro w hwS
        exact hcond w hwS d
      exact (tagA_isoGen scottEndPId scottEndPId_ne_bot (constScottHom y) s).mpr hsup
    · by_cases htt : t = (⊤ : ScottEndP DBilimit)
      · subst htt
        exact leGlue_tagA_tagB_topGen scottEndPId (constScottHom y)
      · have hcond : ∀ w ∈ S, constScottHom w ≤ scottEndPId := by
          intro w hwS
          have h : Psi w ≤
              (⟨Sum.inr (Sum.inl t), hbv⟩ : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
            hb ⟨w, hwS, rfl⟩
          rw [GlueCarGen.le_def] at h
          exact (leGlue_tagA_tagB_iffGen scottEndPId (constScottHom w) t htt).mp h
        have hsup : constScottHom y ≤ scottEndPId := by
          intro d
          show y ≤ (scottEndPId : ScottEndP DBilimit).1 d
          apply hy.2
          intro w hwS
          exact hcond w hwS d
        exact (leGlue_tagA_tagB_iffGen scottEndPId (constScottHom y) t htt).mpr hsup
    · exact leGlue_tagA_tagCGen scottEndPId (constScottHom y) r

end SigmaAContinuous
end Phase4Alpha
section Phase4MaxPrime
-- [D-1166] topGen
noncomputable def topGen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inr (Sum.inr (⊤ : ScottEndP DBilimit)), by
    simp only [canonGen]
    rw [if_neg scottEndPBot_ne_top.symm, if_neg scottEndPId_ne_top.symm]⟩

-- [D-1167] topGen_isTop
theorem topGen_isTop (y : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) : y ≤ topGen := by
  rcases y with ⟨v, hv⟩
  show leGlueGen scottEndPId v topGen.1
  rcases v with x | x
  · exact leGlue_tagA_tagCGen scottEndPId x (⊤ : ScottEndP DBilimit)
  · rcases x with x | x
    · exact ⟨Sum.inr (Sum.inl x), self_mem_occsGen _ _,
        Sum.inr (Sum.inr (⊤ : ScottEndP DBilimit)), self_mem_occsGen _ _, le_top⟩
    · exact (leGlue_tagC_tagC_iffGen scottEndPId x (⊤ : ScottEndP DBilimit)).mpr le_top

end Phase4MaxPrime
section Phase4MaxPrimeOmega
-- [D-1168] topBGen
noncomputable def topBGen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inr (Sum.inl (⊤ : ScottEndP DBilimit)), by
    simp only [canonGen]
    rw [if_neg scottEndPBot_ne_top.symm]⟩

-- [D-1169] topBGen_ne_topGen
theorem topBGen_ne_topGen : topBGen ≠ topGen := by
  intro h
  have h1 : Sum.inr (Sum.inl (⊤ : ScottEndP DBilimit)) = Sum.inr (Sum.inr (⊤ : ScottEndP DBilimit)) :=
    congrArg Subtype.val h
  simp at h1

-- [D-1170] shiftAddr
def shiftAddr (w : Addr) : Addr := fun n => w (n + 1)

-- [D-1171] prependAddr_shiftAddr_eq
theorem prependAddr_shiftAddr_eq (w : Addr) : prependAddr (w 0) (shiftAddr w) = w := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

end Phase4MaxPrimeOmega
section Phase4FSCScoping
-- [D-1172] topSeq_notMem_range_toDBilimit
theorem topSeq_notMem_range_toDBilimit : topSeq ∉ Set.range toDBilimit := by
  rintro ⟨z, hz⟩
  obtain ⟨k, x, hkx⟩ := toD_surjective z
  subst hkx
  have hins : toDBilimit (toD k x) = insertAtLevel k x := rfl
  rw [hins] at hz
  have hx : x = topSeq.1 k := by
    have := insertAtLevel_self k x
    rw [hz] at this
    exact this.symm
  subst hx
  exact insertAtLevel_topSeq_ne k hz

-- [D-1173] botGen
noncomputable def botGen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inl (⊥ : ScottEndP DBilimit), rfl⟩

-- [D-1174] botGen_isBot
theorem botGen_isBot (y : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) : botGen ≤ y := by
  rcases y with ⟨v, hv⟩
  show leGlueGen scottEndPId botGen.1 v
  rcases v with x | x
  · exact ⟨Sum.inl (⊥ : ScottEndP DBilimit), self_mem_occsGen _ _, Sum.inl x,
      self_mem_occsGen _ _, bot_le⟩
  · rcases x with x | x
    · exact ⟨Sum.inl (⊥ : ScottEndP DBilimit), self_mem_occsGen _ _,
        Sum.inr (Sum.inl x), self_mem_occsGen _ _, bot_le⟩
    · exact leGlue_tagA_tagCGen scottEndPId (⊥ : ScottEndP DBilimit) x

-- [D-1175] leGlueGen_tagC_tagB_top_iff
theorem leGlueGen_tagC_tagB_top_iff {P : Type*} [DecidableEq P] [PartialOrder P]
    [BoundedOrder P] (m w' : P) :
    leGlueGen m (Sum.inr (Sum.inr w')) (Sum.inr (Sum.inl (⊤ : P))) ↔ w' ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr w') := by simpa [occsGen] using hu
    subst hu'
    have hv' : v = Sum.inr (Sum.inl (⊤ : P)) ∨ v = Sum.inr (Sum.inr m) := by
      simpa [occsGen] using hv
    rcases hv' with hv' | hv'
    · subst hv'; exact huv.elim
    · subst hv'; exact huv
  · intro hw'm
    exact ⟨Sum.inr (Sum.inr w'), self_mem_occsGen m _, Sum.inr (Sum.inr m),
      by simp [occsGen], hw'm⟩

end Phase4FSCScoping
section SigmaCContinuous
-- [D-1176] PsiC
noncomputable def PsiC (x : DBilimit) : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x))),
    canonGen_idem scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top _⟩

-- [D-1177] PsiC_apply_of_ne_bot
theorem PsiC_apply_of_ne_bot {x : DBilimit} (hx : x ≠ (⊥ : DBilimit)) :
    (PsiC x).1 = Sum.inr (Sum.inr (constScottHom x)) := by
  show canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x))) = _
  simp only [canonGen]
  rw [if_neg (fun h => hx (constScottHom_eq_bot_iff.mp h)),
      if_neg (scottEndPId_ne_constScottHom x).symm]

-- [D-1178] PsiC_apply_of_eq_bot
theorem PsiC_apply_of_eq_bot : (PsiC (⊥ : DBilimit)).1 = Sum.inl (⊤ : ScottEndP DBilimit) := by
  show canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom (⊥ : DBilimit)))) = _
  rw [constScottHom_bot_eq]
  simp [canonGen]

-- [D-1179] exists_ne_bot_of_ne_bot_sup
theorem exists_ne_bot_of_ne_bot_sup {S : Set DBilimit} {y : DBilimit} (hy : IsLUB S y)
    (hyb : y ≠ (⊥ : DBilimit)) : ∃ w ∈ S, w ≠ (⊥ : DBilimit) := by
  by_contra hcon
  push_neg at hcon
  apply hyb
  apply le_antisymm _ bot_le
  apply hy.2
  intro w hw
  exact le_of_eq (hcon w hw)

-- [D-1180] PsiC_monotone
theorem PsiC_monotone (x x' : DBilimit) (hxx' : x ≤ x') : PsiC x ≤ PsiC x' := by
  by_cases hx : x = (⊥ : DBilimit)
  · subst hx
    rw [GlueCarGen.le_def]
    show leGlueGen scottEndPId (PsiC (⊥ : DBilimit)).1 (PsiC x').1
    rw [PsiC_apply_of_eq_bot]
    by_cases hx' : x' = (⊥ : DBilimit)
    · subst hx'; rw [PsiC_apply_of_eq_bot]
      exact leGlueGen_refl scottEndPId (Sum.inl ⊤)
    · rw [PsiC_apply_of_ne_bot hx']
      exact leGlue_tagA_tagCGen scottEndPId _ _
  · have hx' : x' ≠ (⊥ : DBilimit) := by
      intro h; subst h
      exact hx (le_bot_iff.mp hxx')
    rw [GlueCarGen.le_def]
    show leGlueGen scottEndPId (PsiC x).1 (PsiC x').1
    rw [PsiC_apply_of_ne_bot hx, PsiC_apply_of_ne_bot hx']
    exact (leGlue_tagC_tagC_iffGen scottEndPId (constScottHom x) (constScottHom x')).mpr
      (constScottHom_monotone hxx')

-- [D-1181] PsiC_isLUB
theorem PsiC_isLUB {S : Set DBilimit} {y : DBilimit} (hS : S.Nonempty) (hy : IsLUB S y) :
    IsLUB (PsiC '' S) (PsiC y) := by
  constructor
  · rintro _ ⟨w, hwS, rfl⟩
    exact PsiC_monotone w y (hy.1 hwS)
  · intro b hb
    by_cases hyb : y = (⊥ : DBilimit)
    ·
      obtain ⟨w0, hw0S⟩ := hS
      have hw0y : w0 ≤ y := hy.1 hw0S
      rw [hyb] at hw0y
      have hw0b : w0 = (⊥ : DBilimit) := le_bot_iff.mp hw0y
      have : PsiC y = PsiC w0 := by rw [hyb, hw0b]
      rw [this]
      exact hb ⟨w0, hw0S, rfl⟩
    · obtain ⟨w0, hw0S, hw0b⟩ := exists_ne_bot_of_ne_bot_sup hy hyb
      obtain ⟨bv, hbv⟩ := b
      rw [GlueCarGen.le_def]
      show leGlueGen scottEndPId (PsiC y).1 bv
      rw [PsiC_apply_of_ne_bot hyb]
      rcases bv with s | t | r
      ·
        exfalso
        have h : PsiC w0 ≤ (⟨Sum.inl s, hbv⟩ : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
          hb ⟨w0, hw0S, rfl⟩
        rw [GlueCarGen.le_def] at h
        rw [PsiC_apply_of_ne_bot hw0b] at h
        exact not_leGlue_tagC_tagAGen scottEndPId (constScottHom w0) s
          (fun heq => hw0b (constScottHom_eq_bot_iff.mp heq)) h
      ·
        by_cases htt : t = (⊤ : ScottEndP DBilimit)
        · subst htt
          exfalso
          have h : PsiC w0 ≤
              (⟨Sum.inr (Sum.inl (⊤ : ScottEndP DBilimit)), hbv⟩ :
                GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
            hb ⟨w0, hw0S, rfl⟩
          rw [GlueCarGen.le_def] at h
          rw [PsiC_apply_of_ne_bot hw0b] at h
          have hmle : constScottHom w0 ≤ scottEndPId :=
            (leGlueGen_tagC_tagB_top_iff scottEndPId (constScottHom w0)).mp h
          exact hw0b (le_bot_iff.mp (hmle botSeq))
        · exfalso
          have h : PsiC w0 ≤
              (⟨Sum.inr (Sum.inl t), hbv⟩ : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
            hb ⟨w0, hw0S, rfl⟩
          rw [GlueCarGen.le_def] at h
          rw [PsiC_apply_of_ne_bot hw0b] at h
          exact not_leGlue_tagC_tagBGen scottEndPId (constScottHom w0) t htt h
      ·
        have hcond : ∀ w ∈ S, constScottHom w ≤ r := by
          intro w hwS
          by_cases hwb : w = (⊥ : DBilimit)
          · rw [hwb, constScottHom_bot_eq]; exact bot_le
          · have h : PsiC w ≤
                (⟨Sum.inr (Sum.inr r), hbv⟩ : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :=
              hb ⟨w, hwS, rfl⟩
            rw [GlueCarGen.le_def] at h
            rw [PsiC_apply_of_ne_bot hwb] at h
            exact (leGlue_tagC_tagC_iffGen scottEndPId (constScottHom w) r).mp h
        have hsup : constScottHom y ≤ r := by
          intro d
          show y ≤ r.1 d
          apply hy.2
          intro w hwS
          exact hcond w hwS d
        exact (leGlue_tagC_tagC_iffGen scottEndPId (constScottHom y) r).mpr hsup

end SigmaCContinuous
-- [D-1182] _root_.IsLUB.eq_topSeq_iff_forall_exists_top
theorem _root_.IsLUB.eq_topSeq_iff_forall_exists_top {S : Set DBilimit} {a : DBilimit}
    (ha : IsLUB S a) (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    a = topSeq ↔ ∀ j, ∃ x ∈ S, x.1 j = (⊤ : D j) := by
  constructor
  · intro heq j
    have hTfin : (Set.image (fun x : DBilimit => x.1 j) S).Finite := Set.toFinite _
    obtain ⟨t, htmem, htgr⟩ := directedOn_exists_greatest_of_finite hTfin (hne.image _)
      (DBilimit_directed_image j hdir)
    have htsup : sSup (Set.image (fun x : DBilimit => x.1 j) S) = t :=
      le_antisymm (sSup_le htgr) (le_sSup htmem)
    have hasup : a.1 j = sSup (Set.image (fun x : DBilimit => x.1 j) S) :=
      IsLUB.dbilimit_apply ha hne hdir j
    have haj : a.1 j = (⊤ : D j) := by rw [heq]; rfl
    have ht_eq_a : t = a.1 j := (hasup.trans htsup).symm
    obtain ⟨x, hxS, hxeq⟩ := htmem
    exact ⟨x, hxS, hxeq.trans (ht_eq_a.trans haj)⟩
  · intro hw
    apply Subtype.ext
    funext j
    obtain ⟨x, hxS, hxeq⟩ := hw j
    have hle : x.1 j ≤ a.1 j := (ha.1 hxS) j
    rw [hxeq] at hle
    exact top_le_iff.mp hle

-- [D-1183] insertAtLevel_isCompactElement
theorem insertAtLevel_isCompactElement (k : ℕ) (x : D k) :
    IsCompactElement (insertAtLevel k x) := by
  intro s u hs hdir hlub hle
  have hTfin : (Set.image (fun z : DBilimit => z.1 k) s).Finite := Set.toFinite _
  obtain ⟨t, htmem, htgr⟩ := directedOn_exists_greatest_of_finite hTfin (hs.image _)
    (DBilimit_directed_image k hdir)
  have htsup : sSup (Set.image (fun z : DBilimit => z.1 k) s) = t :=
    le_antisymm (sSup_le htgr) (le_sSup htmem)
  have husup : u.1 k = sSup (Set.image (fun z : DBilimit => z.1 k) s) :=
    IsLUB.dbilimit_apply hlub hs hdir k
  have ht_eq_u : t = u.1 k := (husup.trans htsup).symm
  obtain ⟨x0, hx0s, hx0eq⟩ := htmem
  have hxu : x ≤ u.1 k := by
    have h := hle k
    rwa [insertAtLevel_self] at h
  have hueq : u.1 k = x0.1 k := by rw [← ht_eq_u]; exact hx0eq.symm
  have hxx0 : x ≤ x0.1 k := hxu.trans_eq hueq
  refine ⟨x0, hx0s, ?_⟩
  calc insertAtLevel k x ≤ insertAtLevel k (x0.1 k) := insertAtLevel_monotone k hxx0
    _ ≤ x0 := insertAtLevel_le_self x0 k

-- [D-1184] _root_.IsCompactElement.exists_insertAtLevel
theorem _root_.IsCompactElement.exists_insertAtLevel {z : DBilimit}
    (hz : IsCompactElement z) : ∃ k x, z = insertAtLevel k x := by
  obtain ⟨w, hwmem, hzw⟩ := hz (chainSet z) z (chainSet_nonempty z)
    (chainSet_directedOn z) (chainSet_isLUB z) le_rfl
  obtain ⟨n, rfl⟩ := hwmem
  exact ⟨n, z.1 n, le_antisymm hzw (insertAtLevel_le_self z n)⟩

-- [D-1185] insertAtLevel_le_iff
theorem insertAtLevel_le_iff (k : ℕ) (x : D k) (y : DBilimit) :
    insertAtLevel k x ≤ y ↔ x ≤ y.1 k := by
  constructor
  · intro h
    have h' := h k
    rwa [insertAtLevel_self] at h'
  · intro h
    calc insertAtLevel k x ≤ insertAtLevel k (y.1 k) := insertAtLevel_monotone k h
      _ ≤ y := insertAtLevel_le_self y k

-- [D-1186] DBilimit_compacts_le_directedOn
theorem DBilimit_compacts_le_directedOn (y : DBilimit) :
    DirectedOn (· ≤ ·) {z : DBilimit | IsCompactElement z ∧ z ≤ y} := by
  rintro z1 ⟨hz1c, hz1y⟩ z2 ⟨hz2c, hz2y⟩
  obtain ⟨k1, x1, rfl⟩ := hz1c.exists_insertAtLevel
  obtain ⟨k2, x2, rfl⟩ := hz2c.exists_insertAtLevel
  refine ⟨insertAtLevel (max k1 k2) (y.1 (max k1 k2)),
    ⟨insertAtLevel_isCompactElement _ _, insertAtLevel_le_self y _⟩, ?_, ?_⟩
  · calc insertAtLevel k1 x1 ≤ insertAtLevel k1 (y.1 k1) :=
          insertAtLevel_monotone k1 ((insertAtLevel_le_iff k1 x1 y).mp hz1y)
      _ ≤ insertAtLevel (max k1 k2) (y.1 (max k1 k2)) :=
          insertAtLevel_chain_mono y (le_max_left k1 k2)
  · calc insertAtLevel k2 x2 ≤ insertAtLevel k2 (y.1 k2) :=
          insertAtLevel_monotone k2 ((insertAtLevel_le_iff k2 x2 y).mp hz2y)
      _ ≤ insertAtLevel (max k1 k2) (y.1 (max k1 k2)) :=
          insertAtLevel_chain_mono y (le_max_right k1 k2)

-- [D-1187] DBilimit_isLUB_compacts_le
theorem DBilimit_isLUB_compacts_le (y : DBilimit) :
    IsLUB {z : DBilimit | IsCompactElement z ∧ z ≤ y} y := by
  constructor
  · intro z hz
    exact hz.2
  · intro b hb
    apply (chainSet_isLUB y).2
    rintro _ ⟨n, rfl⟩
    exact hb ⟨insertAtLevel_isCompactElement n (y.1 n), insertAtLevel_le_self y n⟩

-- [D-1188] toDBilimit_toD_eq_insertAtLevel
theorem toDBilimit_toD_eq_insertAtLevel (k : ℕ) (x : D k) :
    toDBilimit (toD k x) = insertAtLevel k x := rfl

-- [D-1189] mem_range_toDBilimit_iff_isCompactElement
theorem mem_range_toDBilimit_iff_isCompactElement {z : DBilimit} :
    z ∈ Set.range toDBilimit ↔ IsCompactElement z := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨k, x, hkx⟩ := toD_surjective w
    rw [← hkx, toDBilimit_toD_eq_insertAtLevel]
    exact insertAtLevel_isCompactElement k x
  · intro hz
    obtain ⟨k, x, hkx⟩ := hz.exists_insertAtLevel
    exact ⟨toD k x, by rw [toDBilimit_toD_eq_insertAtLevel, ← hkx]⟩

-- [D-1190] DBilimit_rigid_of_DInfty_rigid
theorem DBilimit_rigid_of_DInfty_rigid
    (hDInfty : Subsingleton (DInfty ≃o DInfty)) :
    Subsingleton (DBilimit ≃o DBilimit) := by
  have hFix : ∀ (g : DBilimit ≃o DBilimit) (y : DBilimit), g y = y := by
    intro g
    have hex : ∀ w : DInfty, ∃ w', toDBilimit w' = g (toDBilimit w) := by
      intro w
      have hc : IsCompactElement (toDBilimit w) :=
        mem_range_toDBilimit_iff_isCompactElement.mp ⟨w, rfl⟩
      exact mem_range_toDBilimit_iff_isCompactElement.mpr (hc.orderIso g)
    have hex' : ∀ w : DInfty, ∃ w', toDBilimit w' = g.symm (toDBilimit w) := by
      intro w
      have hc : IsCompactElement (toDBilimit w) :=
        mem_range_toDBilimit_iff_isCompactElement.mp ⟨w, rfl⟩
      exact mem_range_toDBilimit_iff_isCompactElement.mpr (hc.orderIso g.symm)
    set h : DInfty → DInfty := fun w => (hex w).choose with hdef
    set hInv : DInfty → DInfty := fun w => (hex' w).choose with hInvdef
    have hspec : ∀ w, toDBilimit (h w) = g (toDBilimit w) := fun w => (hex w).choose_spec
    have hInvspec : ∀ w, toDBilimit (hInv w) = g.symm (toDBilimit w) :=
      fun w => (hex' w).choose_spec
    have hmono : Monotone h := by
      intro w1 w2 hw
      rw [← toDBilimit_le_iff, hspec, hspec]
      exact g.monotone (toDBilimit_monotone hw)
    have hInvmono : Monotone hInv := by
      intro w1 w2 hw
      rw [← toDBilimit_le_iff, hInvspec, hInvspec]
      exact g.symm.monotone (toDBilimit_monotone hw)
    have hleft : ∀ w, hInv (h w) = w := by
      intro w
      apply toDBilimit_injective
      rw [hInvspec, hspec, g.symm_apply_apply]
    have hright : ∀ w, h (hInv w) = w := by
      intro w
      apply toDBilimit_injective
      rw [hspec, hInvspec, g.apply_symm_apply]
    let hHom : DInfty →o DInfty := ⟨h, hmono⟩
    let hInvHom : DInfty →o DInfty := ⟨hInv, hInvmono⟩
    have hcomp1 : hHom.comp hInvHom = OrderHom.id := by
      ext w; exact hright w
    have hcomp2 : hInvHom.comp hHom = OrderHom.id := by
      ext w; exact hleft w
    let H : DInfty ≃o DInfty := OrderIso.ofHomInv hHom hInvHom hcomp1 hcomp2
    have hHeq : H = OrderIso.refl DInfty := Subsingleton.elim H (OrderIso.refl DInfty)
    have hHval : ∀ w, h w = w := by
      intro w
      have h1 : H w = w := by rw [hHeq]; rfl
      simpa [H, OrderIso.ofHomInv_apply, hHom] using h1
    have hFixCompact : ∀ z : DBilimit, IsCompactElement z → g z = z := by
      intro z hz
      obtain ⟨w, rfl⟩ := mem_range_toDBilimit_iff_isCompactElement.mpr hz
      rw [← hspec, hHval w]
    intro y
    have hSeteq : g '' {z : DBilimit | IsCompactElement z ∧ z ≤ y} =
        {z : DBilimit | IsCompactElement z ∧ z ≤ y} := by
      ext z
      constructor
      · rintro ⟨w, ⟨hwc, hwy⟩, rfl⟩
        rw [hFixCompact w hwc]
        exact ⟨hwc, hwy⟩
      · rintro ⟨hzc, hzy⟩
        exact ⟨z, ⟨hzc, hzy⟩, hFixCompact z hzc⟩
    have hLUB1 : IsLUB {z : DBilimit | IsCompactElement z ∧ z ≤ y} y :=
      DBilimit_isLUB_compacts_le y
    have hLUB2 : IsLUB (g '' {z : DBilimit | IsCompactElement z ∧ z ≤ y}) (g y) :=
      g.isLUB_image'.mpr hLUB1
    rw [hSeteq] at hLUB2
    exact (hLUB1.unique hLUB2).symm
  constructor
  intro g1 g2
  apply OrderIso.ext
  funext y
  rw [hFix g1 y, hFix g2 y]

-- [D-1191] DBilimit_rigid_of_colimit_compat
theorem DBilimit_rigid_of_colimit_compat
    (colimit_compat :
      Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k)) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_DInfty_rigid (colimit_compat.mpr D_all_rigid)

section SkeletonSixPoints

-- [D-1192] glue1Gen
noncomputable def glue1Gen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inl (scottEndPId : ScottEndP DBilimit), rfl⟩

-- [D-1193] glue2Gen
noncomputable def glue2Gen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inl (⊤ : ScottEndP DBilimit), rfl⟩

-- [D-1194] KEPT_A
noncomputable def KEPT_A : DBilimit := botSeq

-- [D-1195] KEPT_C
noncomputable def KEPT_C : DBilimit := topSeq

-- [D-1196] keptBGen
noncomputable def keptBGen : GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨Sum.inr (Sum.inl (scottEndPId : ScottEndP DBilimit)), by
    show canonGen scottEndPId (Sum.inr (Sum.inl (scottEndPId : ScottEndP DBilimit))) =
      Sum.inr (Sum.inl (scottEndPId : ScottEndP DBilimit))
    simp only [canonGen]
    rw [if_neg scottEndPId_ne_bot]⟩

end SkeletonSixPoints
section StageAndLemmaA2
-- [D-1197] Stage
noncomputable def Stage {z : DBilimit} (hz : IsCompactElement z) : ℕ :=
  Nat.find hz.exists_insertAtLevel

-- [D-1198] Stage_spec
theorem Stage_spec {z : DBilimit} (hz : IsCompactElement z) :
    ∃ x : D (Stage hz), z = insertAtLevel (Stage hz) x :=
  Nat.find_spec hz.exists_insertAtLevel

-- [D-1199] Stage_min
theorem Stage_min {z : DBilimit} (hz : IsCompactElement z) {k : ℕ} (hk : k < Stage hz) :
    ¬ ∃ x : D k, z = insertAtLevel k x :=
  Nat.find_min hz.exists_insertAtLevel hk

-- [D-1200] Stage_transport
theorem Stage_transport {a b : DBilimit} (h : a = b) (ha : IsCompactElement a) :
    Stage (h ▸ ha : IsCompactElement b) = Stage ha := by
  subst h; rfl

end StageAndLemmaA2

section LemmaA3

-- [D-1201] canonGen_tagB_constScottHom_eq
theorem canonGen_tagB_constScottHom_eq (v : DBilimit) :
    canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom v))) =
      if v = (⊥ : DBilimit) then Sum.inl (scottEndPId : ScottEndP DBilimit)
      else Sum.inr (Sum.inl (constScottHom v)) := by
  simp only [canonGen, constScottHom_eq_bot_iff]

-- [D-1202] canonGen_tagC_constScottHom_eq
theorem canonGen_tagC_constScottHom_eq (v : DBilimit) :
    canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom v))) =
      if v = (⊥ : DBilimit) then Sum.inl (⊤ : ScottEndP DBilimit)
      else Sum.inr (Sum.inr (constScottHom v)) := by
  simp only [canonGen]
  rw [if_neg (scottEndPId_ne_constScottHom v).symm]
  simp only [constScottHom_eq_bot_iff]

-- [D-1203] §Reconstructs-lemma-A3-s-6-fact-package-lemma-A3
section PsiIsoFreeLemmaA3

-- [D-1204] pD_glueA
theorem pD_glueA (k : ℕ) (f : EndP (D k)) :
    pD k (glueA (markedPt k) f) = f (⊥ : D k) := rfl

section BranchSeq

-- [D-1205] branchSeq
noncomputable def branchSeq (b : ℕ → Bool) : (k : ℕ) → D k
  | 0 => (⊥ : D 0)
  | (k + 1) => glueA (markedPt k)
      (cond (b k) (branchF1 (branchSeq b k)) (branchF2 (branchSeq b k)))

-- [D-1206] branchSeq_ne_top
theorem branchSeq_ne_top (b : ℕ → Bool) : ∀ k, branchSeq b k ≠ (⊤ : D k)
  | 0 => bot_ne_top_of_nontrivial
  | (k + 1) =>
      glueA_ne_top (markedPt k) (D_marked_point_nondegenerate k).1
        (D_marked_point_nondegenerate k).2.1 (D_marked_point_nondegenerate k).2.2 _

-- [D-1207] branchSeq_succ_apply_bot
theorem branchSeq_succ_apply_bot (b : ℕ → Bool) (k : ℕ) :
    pD k (branchSeq b (k + 1)) = branchSeq b k := by
  show pD k (glueA (markedPt k)
      (cond (b k) (branchF1 (branchSeq b k)) (branchF2 (branchSeq b k)))) = branchSeq b k
  rw [pD_glueA]
  cases hbk : b k with
  | true => simp only [cond_true]; exact branchF1_apply_bot (branchSeq b k)
  | false => simp only [cond_false]; exact branchF2_apply_bot (branchSeq b k)

-- [D-1208] branchPoint
noncomputable def branchPoint (b : ℕ → Bool) : DBilimit :=
  ⟨branchSeq b, branchSeq_succ_apply_bot b⟩

-- [D-1209] branchSeq_agree_of_agree
theorem branchSeq_agree_of_agree (b b' : ℕ → Bool) (n : ℕ)
    (hagree : ∀ i < n, b i = b' i) : branchSeq b n = branchSeq b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : branchSeq b n = branchSeq b' n :=
      ih (fun i hi => hagree i (Nat.lt_succ_of_lt hi))
    have hbn : b n = b' n := hagree n (Nat.lt_succ_self n)
    show glueA (markedPt n)
        (cond (b n) (branchF1 (branchSeq b n)) (branchF2 (branchSeq b n))) =
      glueA (markedPt n)
        (cond (b' n) (branchF1 (branchSeq b' n)) (branchF2 (branchSeq b' n)))
    rw [hprev, hbn]

-- [D-1210] branchSeq_succ_ne
theorem branchSeq_succ_ne (b b' : ℕ → Bool) (n : ℕ)
    (hagree : ∀ i < n, b i = b' i) (hne : b n ≠ b' n) :
    branchSeq b (n + 1) ≠ branchSeq b' (n + 1) := by
  have hprev : branchSeq b n = branchSeq b' n := branchSeq_agree_of_agree b b' n hagree
  have hv : branchSeq b n ≠ (⊤ : D n) := branchSeq_ne_top b n
  have hbtn : (⊥ : D n) ≠ (⊤ : D n) := bot_ne_top_of_nontrivial
  intro h
  have h1 : (cond (b n) (branchF1 (branchSeq b n)) (branchF2 (branchSeq b n))) =
      (cond (b' n) (branchF1 (branchSeq b' n)) (branchF2 (branchSeq b' n))) :=
    glueA_injective (markedPt n) h
  rw [hprev] at h1
  cases hbk : b n with
  | true =>
    cases hbk' : b' n with
    | true => exact hne (hbk.trans hbk'.symm)
    | false =>
      rw [hbk, hbk', cond_true, cond_false] at h1
      exact (branchF1_ne_branchF2 (branchSeq b' n) (hprev ▸ hv) hbtn) h1
  | false =>
    cases hbk' : b' n with
    | true =>
      rw [hbk, hbk', cond_false, cond_true] at h1
      exact (branchF1_ne_branchF2 (branchSeq b' n) (hprev ▸ hv) hbtn) h1.symm
    | false => exact hne (hbk.trans hbk'.symm)

-- [D-1211] branchPoint_injective
theorem branchPoint_injective : Function.Injective branchPoint := by
  intro b b' h
  by_contra hne
  have hex : ∃ n, b n ≠ b' n := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set n := Nat.find hex with hn_def
  have hn : b n ≠ b' n := Nat.find_spec hex
  have hagree : ∀ i < n, b i = b' i := fun i hi => by
    by_contra hci
    exact Nat.find_min hex hi hci
  have hcoord : branchSeq b (n + 1) ≠ branchSeq b' (n + 1) :=
    branchSeq_succ_ne b b' n hagree hn
  have heq : branchSeq b (n + 1) = branchSeq b' (n + 1) :=
    congrArg (fun x : DBilimit => x.1 (n + 1)) h
  exact hcoord heq

end BranchSeq

section ScottExt

-- [D-1212] scottEndP_ext
theorem scottEndP_ext {F G : ScottEndP DBilimit}
    (h : ∀ (k : ℕ) (x : D k), F.1 (insertAtLevel k x) = G.1 (insertAtLevel k x)) : F = G := by
  have hFG : ∀ z : DBilimit, IsCompactElement z → F.1 z = G.1 z := by
    intro z hz
    obtain ⟨k, x, rfl⟩ := hz.exists_insertAtLevel
    exact h k x
  apply Subtype.ext
  apply OrderHom.ext
  funext y
  have hLUB := DBilimit_isLUB_compacts_le y
  have hDir := DBilimit_compacts_le_directedOn y
  have hNe : {z : DBilimit | IsCompactElement z ∧ z ≤ y}.Nonempty :=
    ⟨insertAtLevel 0 (y.1 0), insertAtLevel_isCompactElement 0 (y.1 0), insertAtLevel_le_self y 0⟩
  have hFLUB : IsLUB (F.1 '' {z : DBilimit | IsCompactElement z ∧ z ≤ y}) (F.1 y) :=
    F.2 hNe hDir hLUB
  have hGLUB : IsLUB (G.1 '' {z : DBilimit | IsCompactElement z ∧ z ≤ y}) (G.1 y) :=
    G.2 hNe hDir hLUB
  have himg : F.1 '' {z : DBilimit | IsCompactElement z ∧ z ≤ y} =
      G.1 '' {z : DBilimit | IsCompactElement z ∧ z ≤ y} := by
    apply Set.image_congr
    intro z hz
    exact hFG z hz.1
  rw [himg] at hFLUB
  exact hFLUB.unique hGLUB

-- [D-1213] scottEndP_restrict_injective
theorem scottEndP_restrict_injective :
    Function.Injective
      (fun F : ScottEndP DBilimit => fun p : Σ k, D k => F.1 (insertAtLevel p.1 p.2)) := by
  intro F G h
  apply scottEndP_ext
  intro k x
  exact congrFun h ⟨k, x⟩

end ScottExt

section ScottEndPDirectedSup

-- [D-1214] scottEndP_directed_image
theorem scottEndP_directed_image (x : DBilimit) {S : Set (ScottEndP DBilimit)}
    (hdir : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≤ ·) ((fun F : ScottEndP DBilimit => F.1 x) '' S) := by
  rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
  obtain ⟨H, hH, hFH, hGH⟩ := hdir F hF G hG
  exact ⟨H.1 x, ⟨H, hH, rfl⟩, hFH x, hGH x⟩

-- [D-1215] scottEndPSupFun
noncomputable def scottEndPSupFun {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (x : DBilimit) : DBilimit :=
  (DBilimit.exists_isLUB_of_directedOn ((fun F : ScottEndP DBilimit => F.1 x) '' S)
    (hne.image _) (scottEndP_directed_image x hdir)).choose

-- [D-1216] scottEndPSupFun_isLUB
theorem scottEndPSupFun_isLUB {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (x : DBilimit) :
    IsLUB ((fun F : ScottEndP DBilimit => F.1 x) '' S) (scottEndPSupFun hne hdir x) :=
  (DBilimit.exists_isLUB_of_directedOn ((fun F : ScottEndP DBilimit => F.1 x) '' S)
    (hne.image _) (scottEndP_directed_image x hdir)).choose_spec

-- [D-1217] scottEndPSupFun_monotone
theorem scottEndPSupFun_monotone {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : Monotone (scottEndPSupFun hne hdir) := by
  intro x y hxy
  apply (scottEndPSupFun_isLUB hne hdir x).2
  rintro _ ⟨F, hF, rfl⟩
  exact (F.1.monotone hxy).trans ((scottEndPSupFun_isLUB hne hdir y).1 ⟨F, hF, rfl⟩)

-- [D-1218] scottEndPSupFun_scottContinuous
theorem scottEndPSupFun_scottContinuous {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : ScottContinuous (scottEndPSupFun hne hdir) := by
  intro T hTne hTdir y0 hy0
  constructor
  · rintro _ ⟨t, ht, rfl⟩
    exact scottEndPSupFun_monotone hne hdir (hy0.1 ht)
  · intro c hc
    apply (scottEndPSupFun_isLUB hne hdir y0).2
    rintro _ ⟨F, hF, rfl⟩
    have hFcont : IsLUB (F.1 '' T) (F.1 y0) := F.2 hTne hTdir hy0
    apply hFcont.2
    rintro _ ⟨t, ht, rfl⟩
    have h1 : F.1 t ≤ scottEndPSupFun hne hdir t :=
      (scottEndPSupFun_isLUB hne hdir t).1 ⟨F, hF, rfl⟩
    exact h1.trans (hc ⟨t, ht, rfl⟩)

-- [D-1219] scottEndPSup
noncomputable def scottEndPSup {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : ScottEndP DBilimit :=
  ⟨⟨scottEndPSupFun hne hdir, scottEndPSupFun_monotone hne hdir⟩,
    scottEndPSupFun_scottContinuous hne hdir⟩

-- [D-1220] scottEndPSup_isLUB
theorem scottEndPSup_isLUB {S : Set (ScottEndP DBilimit)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : IsLUB S (scottEndPSup hne hdir) := by
  constructor
  · intro F hF x
    exact (scottEndPSupFun_isLUB hne hdir x).1 ⟨F, hF, rfl⟩
  · intro G hG x
    exact (scottEndPSupFun_isLUB hne hdir x).2 (by rintro _ ⟨F, hF, rfl⟩; exact hG hF x)

-- [D-1221] ScottEndP.exists_isLUB_of_directedOn
theorem ScottEndP.exists_isLUB_of_directedOn (S : Set (ScottEndP DBilimit))
    (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) : ∃ u, IsLUB S u :=
  ⟨scottEndPSup hne hdir, scottEndPSup_isLUB hne hdir⟩

-- [D-1222] _root_.IsLUB.scottEndP_apply
theorem _root_.IsLUB.scottEndP_apply {S : Set (ScottEndP DBilimit)} {u : ScottEndP DBilimit}
    (hu : IsLUB S u) (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) (x : DBilimit) :
    u.1 x = scottEndPSupFun hne hdir x := by
  have h := hu.unique (scottEndPSup_isLUB hne hdir)
  rw [h]; rfl

end ScottEndPDirectedSup

section ConstScottHomCompact

-- [D-1223] constScottHom_isCompactElement_of_isCompactElement
theorem constScottHom_isCompactElement_of_isCompactElement {v : DBilimit}
    (hv : IsCompactElement v) : IsCompactElement (constScottHom v) := by
  intro s u hsne hsdir hu hle
  have hub : (constScottHom v).1 ⊥ ≤ u.1 ⊥ := hle ⊥
  rw [constScottHom_apply] at hub
  have heval : u.1 ⊥ = scottEndPSupFun hsne hsdir ⊥ := hu.scottEndP_apply hsne hsdir ⊥
  rw [heval] at hub
  obtain ⟨w, hwmem, hwle⟩ := hv ((fun F : ScottEndP DBilimit => F.1 ⊥) '' s) _
    (hsne.image _) (scottEndP_directed_image ⊥ hsdir) (scottEndPSupFun_isLUB hsne hsdir ⊥) hub
  obtain ⟨F0, hF0mem, rfl⟩ := hwmem
  refine ⟨F0, hF0mem, fun y => ?_⟩
  show v ≤ F0.1 y
  calc v ≤ F0.1 ⊥ := hwle
    _ ≤ F0.1 y := F0.1.monotone bot_le

end ConstScottHomCompact

section ScottEndPIdNonCompact

-- [D-1224] topSeq_not_isCompactElement
theorem topSeq_not_isCompactElement : ¬ IsCompactElement topSeq := by
  intro hc
  obtain ⟨x, hxmem, hxle⟩ :=
    hc (chainSet topSeq) topSeq (chainSet_nonempty topSeq) (chainSet_directedOn topSeq)
      (chainSet_isLUB topSeq) le_rfl
  obtain ⟨n, rfl⟩ := hxmem
  exact insertAtLevel_topSeq_ne n (le_antisymm (insertAtLevel_le_self topSeq n) hxle)

-- [D-1225] constScottHom_chainSet_topSeq_directedOn
theorem constScottHom_chainSet_topSeq_directedOn :
    DirectedOn (· ≤ ·) (constScottHom '' chainSet topSeq) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hcmem, hac, hbc⟩ := chainSet_directedOn topSeq a ha b hb
  exact ⟨constScottHom c, ⟨c, hcmem, rfl⟩,
    constScottHom_monotone hac, constScottHom_monotone hbc⟩

-- [D-1226] constScottHom_chainSet_topSeq_isLUB
theorem constScottHom_chainSet_topSeq_isLUB :
    IsLUB (constScottHom '' chainSet topSeq) (⊤ : ScottEndP DBilimit) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩; exact le_top
  · intro G hG x
    have hub : G.1 x ∈ upperBounds (chainSet topSeq) := by
      rintro w ⟨n, rfl⟩
      exact hG ⟨_, ⟨n, rfl⟩, rfl⟩ x
    exact (chainSet_isLUB topSeq).2 hub

-- [D-1227] scottEndPTop_not_isCompactElement
theorem scottEndPTop_not_isCompactElement :
    ¬ IsCompactElement (⊤ : ScottEndP DBilimit) := by
  intro hc
  obtain ⟨F, hFmem, hFle⟩ := hc _ (⊤ : ScottEndP DBilimit)
    ((chainSet_nonempty topSeq).image _)
    constScottHom_chainSet_topSeq_directedOn
    constScottHom_chainSet_topSeq_isLUB le_rfl
  obtain ⟨w, hw, rfl⟩ := hFmem
  obtain ⟨n, rfl⟩ := hw
  have htop : constScottHom (insertAtLevel n (topSeq.1 n)) = (⊤ : ScottEndP DBilimit) :=
    top_le_iff.mp hFle
  exact insertAtLevel_topSeq_ne n (constScottHom_eq_top_iff.mp htop)

-- [D-1228] Gk
noncomputable def Gk (k : ℕ) : ScottEndP DBilimit := liftEndPHom k (OrderHom.id)

-- [D-1229] Gk_apply
theorem Gk_apply (k : ℕ) (x : DBilimit) : (Gk k).1 x = insertAtLevel k (x.1 k) :=
  liftEndPHom_apply k OrderHom.id x

-- [D-1230] Gk_mono_succ
theorem Gk_mono_succ (k : ℕ) (x : DBilimit) : (Gk k).1 x ≤ (Gk (k + 1)).1 x := by
  rw [Gk_apply, Gk_apply, insertAtLevel_le_iff]
  show x.1 k ≤ (insertAtLevel (k + 1) (x.1 (k + 1))).1 k
  have h1 : (insertAtLevel (k + 1) (x.1 (k + 1))).1 k = pLe (Nat.le_succ k) (x.1 (k + 1)) := by
    show (if h : k ≤ k + 1 then pLe h (x.1 (k+1)) else iotaLe (not_le.mp h).le (x.1 (k+1)))
       = pLe (Nat.le_succ k) (x.1 (k + 1))
    rw [dif_pos (Nat.le_succ k)]
  rw [h1, pLe_succ (le_refl k) (Nat.le_succ k), pLe_self k (le_refl k), x.2 k]

-- [D-1231] Gk_mono
theorem Gk_mono : Monotone Gk := by
  intro k k' hkk'
  induction hkk' with
  | refl => exact le_refl _
  | step _ ih => exact fun x => (ih x).trans (Gk_mono_succ _ x)

-- [D-1232] Gk_range_directedOn
theorem Gk_range_directedOn : DirectedOn (· ≤ ·) (Set.range Gk) := by
  rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
  exact ⟨Gk (max k k'), ⟨max k k', rfl⟩, Gk_mono (le_max_left k k'), Gk_mono (le_max_right k k')⟩

-- [D-1233] Gk_range_nonempty
theorem Gk_range_nonempty : (Set.range Gk).Nonempty := ⟨Gk 0, 0, rfl⟩

-- [D-1234] Gk_isLUB_scottEndPId
theorem Gk_isLUB_scottEndPId : IsLUB (Set.range Gk) scottEndPId := by
  constructor
  · rintro _ ⟨k, rfl⟩ x
    show (Gk k).1 x ≤ x
    rw [Gk_apply]
    exact insertAtLevel_le_self x k
  · intro z hz x
    show x ≤ z.1 x
    apply (chainSet_isLUB x).2
    rintro _ ⟨n, rfl⟩
    have hzn : (Gk n).1 x ≤ z.1 x := hz (Set.mem_range_self n) x
    rwa [Gk_apply] at hzn

-- [D-1235] Gk_not_ge_scottEndPId
theorem Gk_not_ge_scottEndPId (k : ℕ) : ¬ scottEndPId ≤ Gk k := by
  intro hle
  have h : topSeq ≤ (Gk k).1 topSeq := hle topSeq
  rw [Gk_apply] at h
  exact insertAtLevel_topSeq_ne k (le_antisymm (insertAtLevel_le_self topSeq k) h)

-- [D-1236] scottEndPId_not_isCompactElement
theorem scottEndPId_not_isCompactElement :
    ¬ IsCompactElement (scottEndPId : ScottEndP DBilimit) := by
  intro hc
  obtain ⟨F, hFmem, hFle⟩ :=
    hc (Set.range Gk) scottEndPId Gk_range_nonempty Gk_range_directedOn
      Gk_isLUB_scottEndPId le_rfl
  obtain ⟨k, rfl⟩ := hFmem
  exact Gk_not_ge_scottEndPId k hFle

-- [D-1237] tagBGenC
noncomputable def tagBGenC (v : ScottEndP DBilimit) :
    GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  ⟨canonGen scottEndPId (Sum.inr (Sum.inl v)),
    canonGen_idem scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top _⟩

-- [D-1238] Gk_ne_bot
theorem Gk_ne_bot (k : ℕ) : Gk k ≠ (⊥ : ScottEndP DBilimit) := by
  intro h
  have h1 : (Gk k).1 topSeq = (⊥ : ScottEndP DBilimit).1 topSeq := by rw [h]
  rw [Gk_apply, scottEndPBot_apply] at h1
  have h2 : (⊤ : D k) = (⊥ : D k) := by
    have h3 := congrArg (fun y : DBilimit => y.1 k) h1
    rwa [insertAtLevel_self] at h3
  exact bot_ne_top_of_nontrivial h2.symm

-- [D-1239] Gk_ne_scottEndPId
theorem Gk_ne_scottEndPId (k : ℕ) : Gk k ≠ scottEndPId := by
  intro h
  exact Gk_not_ge_scottEndPId k (h ▸ le_refl _)

-- [D-1240] tagCFam_directedOn
theorem tagCFam_directedOn : letI := psiTargetOrder
    DirectedOn (· ≤ ·) (Set.range (fun k =>
      tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k))) := by
  letI := psiTargetOrder
  rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
  refine ⟨tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk (max k k')),
    ⟨max k k', rfl⟩, ?_, ?_⟩
  · show leGlueGen scottEndPId
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)).1
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk (max k k'))).1
    rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot k) (Gk_ne_scottEndPId k),
      tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot (max k k')) (Gk_ne_scottEndPId (max k k'))]
    exact (leGlue_tagC_tagC_iffGen scottEndPId (Gk k) (Gk (max k k'))).mpr
      (Gk_mono (le_max_left k k'))
  · show leGlueGen scottEndPId
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k')).1
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk (max k k'))).1
    rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot k') (Gk_ne_scottEndPId k'),
      tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot (max k k')) (Gk_ne_scottEndPId (max k k'))]
    exact (leGlue_tagC_tagC_iffGen scottEndPId (Gk k') (Gk (max k k'))).mpr
      (Gk_mono (le_max_right k k'))

-- [D-1241] tagCFam_isLUB_skelG3
theorem tagCFam_isLUB_skelG3 : letI := psiTargetOrder
    IsLUB (Set.range (fun k => tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)))
      (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top) := by
  letI := psiTargetOrder
  constructor
  · rintro _ ⟨k, rfl⟩
    show leGlueGen scottEndPId
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)).1
      (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1
    rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot k) (Gk_ne_scottEndPId k), skelG3Gen_val]
    exact (leGlue_tagC_tagB_top_iffGen scottEndPId (Gk k)).mpr
      ((Gk_isLUB_scottEndPId.1) (Set.mem_range_self k))
  · intro u hu
    show leGlueGen scottEndPId (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1 u.1
    rw [skelG3Gen_val]
    rcases hcase : u.1 with a' | b' | c'
    · exfalso
      have h0 : leGlueGen scottEndPId
          (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk 0)).1 u.1 :=
        hu (Set.mem_range_self 0)
      rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (Gk_ne_bot 0) (Gk_ne_scottEndPId 0), hcase] at h0
      exact not_leGlue_tagC_tagAGen scottEndPId (Gk 0) a' (Gk_ne_bot 0) h0
    · by_cases hb't : b' = ⊤
      · subst hb't
        exact ⟨_, self_mem_occsGen _ _, _, self_mem_occsGen _ _, le_refl (⊤ : ScottEndP DBilimit)⟩
      · exfalso
        have h0 : leGlueGen scottEndPId
            (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk 0)).1 u.1 :=
          hu (Set.mem_range_self 0)
        rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
          (Gk_ne_bot 0) (Gk_ne_scottEndPId 0), hcase] at h0
        exact not_leGlue_tagC_tagBGen scottEndPId (Gk 0) b' hb't h0
    · have hmc : ∀ k, Gk k ≤ c' := by
        intro k
        have h0 : leGlueGen scottEndPId
            (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)).1 u.1 :=
          hu (Set.mem_range_self k)
        rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
          (Gk_ne_bot k) (Gk_ne_scottEndPId k), hcase] at h0
        exact (leGlue_tagC_tagC_iffGen scottEndPId (Gk k) c').mp h0
      have hmc' : scottEndPId ≤ c' := Gk_isLUB_scottEndPId.2 (by
        rintro _ ⟨k, rfl⟩; exact hmc k)
      exact (leGlue_tagB_tagC_iffGen scottEndPId (⊤ : ScottEndP DBilimit) c').mpr hmc'

-- [D-1242] tagBGenC_not_isCompactElement
theorem tagBGenC_not_isCompactElement {v : ScottEndP DBilimit} (hvb : v ≠ ⊥) :
    letI := psiTargetOrder
    ¬ IsCompactElement (tagBGenC v) := by
  letI := psiTargetOrder
  have hval : (tagBGenC v).1 = Sum.inr (Sum.inl v) := by
    show canonGen scottEndPId (Sum.inr (Sum.inl v)) = Sum.inr (Sum.inl v)
    simp only [canonGen]; rw [if_neg hvb]
  intro hc
  obtain ⟨x, hxmem, hxle⟩ := hc
    (Set.range (fun k => tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)))
    (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top)
    ⟨_, 0, rfl⟩ tagCFam_directedOn tagCFam_isLUB_skelG3
    (by
      show leGlueGen scottEndPId (tagBGenC v).1
        (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1
      exact skelG3Gen_mem_upperBounds_of_pureAB scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
        (s := {tagBGenC v}) (by
          intro y hy; simp only [Set.mem_singleton_iff] at hy; subst hy
          exact Or.inr ⟨v, hval⟩)
        (Set.mem_singleton _))
  obtain ⟨k, rfl⟩ := hxmem
  have hxle' : leGlueGen scottEndPId (tagBGenC v).1
      (tagCGen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top (Gk k)).1 := hxle
  rw [tagCGen_val_of_generic scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top
    (Gk_ne_bot k) (Gk_ne_scottEndPId k), hval] at hxle'
  have hmk : scottEndPId ≤ Gk k := (leGlue_tagB_tagC_iffGen scottEndPId v (Gk k)).mp hxle'
  exact Gk_not_ge_scottEndPId k hmk

-- [D-1243] tagBGenC_val
theorem tagBGenC_val {v : ScottEndP DBilimit} (hv : v ≠ (⊥ : ScottEndP DBilimit)) :
    (tagBGenC v).1 = Sum.inr (Sum.inl v) := by
  show canonGen scottEndPId (Sum.inr (Sum.inl v)) = Sum.inr (Sum.inl v)
  simp only [canonGen]; rw [if_neg hv]

-- [D-1244] chainSet_topSeq_constScottHom_ne_bot
theorem chainSet_topSeq_constScottHom_ne_bot {w : DBilimit} (hw : w ∈ chainSet topSeq) :
    constScottHom w ≠ (⊥ : ScottEndP DBilimit) := by
  obtain ⟨n, rfl⟩ := hw
  intro h
  have hwb : insertAtLevel n (topSeq.1 n) = (⊥ : DBilimit) := constScottHom_eq_bot_iff.mp h
  have h2 : (⊤ : D n) = (⊥ : D n) := by
    have h3 := congrArg (fun y : DBilimit => y.1 n) hwb
    rwa [insertAtLevel_self] at h3
  exact bot_ne_top_of_nontrivial h2.symm

-- [D-1245] chainSet_topSeq_constScottHom_ne_top
theorem chainSet_topSeq_constScottHom_ne_top {w : DBilimit} (hw : w ∈ chainSet topSeq) :
    constScottHom w ≠ (⊤ : ScottEndP DBilimit) := by
  obtain ⟨n, rfl⟩ := hw
  intro h
  exact insertAtLevel_topSeq_ne n (constScottHom_eq_top_iff.mp h)

-- [D-1246] sigmaAFam_directedOn
theorem sigmaAFam_directedOn : letI := psiTargetOrder
    DirectedOn (· ≤ ·)
      ((fun w : DBilimit => tagBGenC (constScottHom w)) '' chainSet topSeq) := by
  letI := psiTargetOrder
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hcmem, hac, hbc⟩ := chainSet_directedOn topSeq a ha b hb
  refine ⟨tagBGenC (constScottHom c), ⟨c, hcmem, rfl⟩, ?_, ?_⟩
  · show leGlueGen scottEndPId (tagBGenC (constScottHom a)).1 (tagBGenC (constScottHom c)).1
    rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot ha),
        tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hcmem)]
    exact (leGlue_tagB_tagB_iffGen scottEndPId (constScottHom a) (constScottHom c)
      (chainSet_topSeq_constScottHom_ne_top hcmem)
      (chainSet_topSeq_constScottHom_ne_bot ha)).mpr (constScottHom_monotone hac)
  · show leGlueGen scottEndPId (tagBGenC (constScottHom b)).1 (tagBGenC (constScottHom c)).1
    rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hb),
        tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hcmem)]
    exact (leGlue_tagB_tagB_iffGen scottEndPId (constScottHom b) (constScottHom c)
      (chainSet_topSeq_constScottHom_ne_top hcmem)
      (chainSet_topSeq_constScottHom_ne_bot hb)).mpr (constScottHom_monotone hbc)

-- [D-1247] sigmaAFam_isLUB_skelG3
theorem sigmaAFam_isLUB_skelG3 : letI := psiTargetOrder
    IsLUB ((fun w : DBilimit => tagBGenC (constScottHom w)) '' chainSet topSeq)
      (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top) := by
  letI := psiTargetOrder
  constructor
  · rintro _ ⟨w, hw, rfl⟩
    show leGlueGen scottEndPId (tagBGenC (constScottHom w)).1
      (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1
    rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hw), skelG3Gen_val]
    exact leGlue_tagB_tagB_topGen scottEndPId (constScottHom w)
  · intro u hu
    show leGlueGen scottEndPId (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1 u.1
    rw [skelG3Gen_val]
    obtain ⟨w0, hw0⟩ := chainSet_nonempty topSeq
    rcases hcase : u.1 with a' | b' | c'
    · exfalso
      have h0 : leGlueGen scottEndPId (tagBGenC (constScottHom w0)).1 u.1 := hu ⟨w0, hw0, rfl⟩
      rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hw0), hcase] at h0
      exact not_leGlue_tagB_tagAGen scottEndPId (constScottHom w0) a' scottEndPId_ne_bot
        scottEndPBot_ne_top (chainSet_topSeq_constScottHom_ne_bot hw0) h0
    · by_cases hb't : b' = (⊤ : ScottEndP DBilimit)
      · subst hb't
        exact ⟨_, self_mem_occsGen _ _, _, self_mem_occsGen _ _, le_refl (⊤ : ScottEndP DBilimit)⟩
      · exfalso
        have hub : b' ∈ upperBounds (constScottHom '' chainSet topSeq) := by
          rintro _ ⟨w, hw, rfl⟩
          have h0 : leGlueGen scottEndPId (tagBGenC (constScottHom w)).1 u.1 := hu ⟨w, hw, rfl⟩
          rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hw), hcase] at h0
          exact (leGlue_tagB_tagB_iffGen scottEndPId (constScottHom w) b' hb't
            (chainSet_topSeq_constScottHom_ne_bot hw)).mp h0
        exact hb't (top_le_iff.mp (constScottHom_chainSet_topSeq_isLUB.2 hub))
    · have hmc : scottEndPId ≤ c' := by
        have h0 : leGlueGen scottEndPId (tagBGenC (constScottHom w0)).1 u.1 := hu ⟨w0, hw0, rfl⟩
        rw [tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hw0), hcase] at h0
        exact (leGlue_tagB_tagC_iffGen scottEndPId (constScottHom w0) c').mp h0
      exact (leGlue_tagB_tagC_iffGen scottEndPId (⊤ : ScottEndP DBilimit) c').mpr hmc

-- [D-1248] Psi_not_isCompactElement
theorem Psi_not_isCompactElement {x0 : DBilimit} (hx0 : x0 ≠ (⊥ : DBilimit)) :
    letI := psiTargetOrder
    ¬ IsCompactElement (Psi x0) := by
  letI := psiTargetOrder
  intro hc
  have hxm : ¬ constScottHom x0 ≤ scottEndPId := by
    intro hle
    have h1 : (constScottHom x0).1 (⊥ : DBilimit) ≤
        (scottEndPId : ScottEndP DBilimit).1 (⊥ : DBilimit) := hle (⊥ : DBilimit)
    simp only [constScottHom_apply, scottEndPId_apply] at h1
    exact hx0 (le_bot_iff.mp h1)
  obtain ⟨y, hymem, hyle⟩ := hc
    ((fun w : DBilimit => tagBGenC (constScottHom w)) '' chainSet topSeq)
    (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top)
    ((chainSet_nonempty topSeq).image _) sigmaAFam_directedOn sigmaAFam_isLUB_skelG3
    (by
      show leGlueGen scottEndPId (Psi x0).1
        (skelG3Gen scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top).1
      rw [Psi_apply, skelG3Gen_val]
      exact leGlue_tagA_tagB_topGen scottEndPId (constScottHom x0))
  obtain ⟨w, hw, rfl⟩ := hymem
  have hyle' : leGlueGen scottEndPId (Psi x0).1 (tagBGenC (constScottHom w)).1 := hyle
  rw [Psi_apply, tagBGenC_val (chainSet_topSeq_constScottHom_ne_bot hw)] at hyle'
  exact hxm ((leGlue_tagA_tagB_iffGen scottEndPId (constScottHom x0) (constScottHom w)
    (chainSet_topSeq_constScottHom_ne_top hw)).mp hyle')

end ScottEndPIdNonCompact
section DBilimitUpperBound
-- [D-1249] DBilimit_injective_compactSetBelow
theorem DBilimit_injective_compactSetBelow :
    Function.Injective (fun y : DBilimit => {z : DBilimit | IsCompactElement z ∧ z ≤ y}) := by
  intro y y' h
  dsimp only at h
  have hLUBy := DBilimit_isLUB_compacts_le y
  rw [h] at hLUBy
  have hLUBy' := DBilimit_isLUB_compacts_le y'
  exact hLUBy.unique hLUBy'

-- [D-1250] compactSetBelow_eq_image
theorem compactSetBelow_eq_image (y : DBilimit) :
    {z : DBilimit | IsCompactElement z ∧ z ≤ y} =
      (fun p : Σ k, D k => insertAtLevel p.1 p.2) ''
        {p : Σ k, D k | insertAtLevel p.1 p.2 ≤ y} := by
  ext z
  constructor
  · rintro ⟨hzc, hzy⟩
    obtain ⟨k, x, rfl⟩ := hzc.exists_insertAtLevel
    exact ⟨⟨k, x⟩, hzy, rfl⟩
  · rintro ⟨⟨k, x⟩, hp, rfl⟩
    exact ⟨insertAtLevel_isCompactElement k x, hp⟩

-- [D-1251] DBilimit_injective_repsBelow
theorem DBilimit_injective_repsBelow :
    Function.Injective (fun y : DBilimit => {p : Σ k, D k | insertAtLevel p.1 p.2 ≤ y}) := by
  intro y y' h
  dsimp only at h
  apply DBilimit_injective_compactSetBelow
  show {z : DBilimit | IsCompactElement z ∧ z ≤ y} = {z : DBilimit | IsCompactElement z ∧ z ≤ y'}
  rw [compactSetBelow_eq_image, compactSetBelow_eq_image, h]

-- [D-1252] inst-Countable
instance : Countable (Σ k : ℕ, D k) := inferInstance

-- [D-1253] dbilimit_mk_eq_continuum
open Cardinal in
theorem dbilimit_mk_eq_continuum : Cardinal.mk DBilimit = Cardinal.continuum := by
  apply le_antisymm
  · calc Cardinal.mk DBilimit
        ≤ Cardinal.mk (Set (Σ k, D k)) := Cardinal.mk_le_of_injective DBilimit_injective_repsBelow
      _ = 2 ^ Cardinal.mk (Σ k, D k) := Cardinal.mk_set
      _ ≤ 2 ^ Cardinal.aleph0 :=
          Cardinal.power_le_power_left (by norm_num) Cardinal.mk_le_aleph0
      _ = Cardinal.continuum := Cardinal.two_power_aleph0
  · calc Cardinal.continuum
        = 2 ^ Cardinal.aleph0 := Cardinal.two_power_aleph0.symm
      _ = Cardinal.mk (ℕ → Bool) := by
          rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
            Cardinal.lift_id]
      _ ≤ Cardinal.mk DBilimit := Cardinal.mk_le_of_injective branchPoint_injective

end DBilimitUpperBound

section FinalAssembly

open Cardinal

-- [D-1254] mk_arrow_dbilimit_le
theorem mk_arrow_dbilimit_le : Cardinal.mk ((Σ k, D k) → DBilimit) ≤ Cardinal.mk DBilimit := by
  rw [Cardinal.mk_arrow, dbilimit_mk_eq_continuum, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.continuum ^ Cardinal.mk (Σ k, D k)
      ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

-- [D-1255] scottEndP_dbilimit_mk_le
theorem scottEndP_dbilimit_mk_le : Cardinal.mk (ScottEndP DBilimit) ≤ Cardinal.mk DBilimit :=
  (Cardinal.mk_le_of_injective scottEndP_restrict_injective).trans mk_arrow_dbilimit_le

-- [D-1256] scottEndP_to_dbilimit_inj
noncomputable def scottEndP_to_dbilimit_inj : ScottEndP DBilimit ↪ DBilimit :=
  Classical.choice (Cardinal.le_def _ _ |>.mp scottEndP_dbilimit_mk_le)

-- [D-1257] glueCarGen_dbilimit_mk_le
theorem glueCarGen_dbilimit_mk_le :
    Cardinal.mk (GlueCarGen (P := ScottEndP DBilimit) scottEndPId) ≤ Cardinal.mk DBilimit := by
  have h1 : Cardinal.mk (GlueCarGen (P := ScottEndP DBilimit) scottEndPId) ≤
      Cardinal.mk (GlueBaseGen (ScottEndP DBilimit)) :=
    Cardinal.mk_le_of_injective Subtype.val_injective
  have h2 : Cardinal.mk (GlueBaseGen (ScottEndP DBilimit)) ≤ Cardinal.continuum := by
    show Cardinal.mk (ScottEndP DBilimit ⊕ ScottEndP DBilimit ⊕ ScottEndP DBilimit) ≤ _
    rw [Cardinal.mk_sum, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    have hle : Cardinal.mk (ScottEndP DBilimit) ≤ Cardinal.continuum :=
      scottEndP_dbilimit_mk_le.trans (le_of_eq dbilimit_mk_eq_continuum)
    calc Cardinal.mk (ScottEndP DBilimit) + (Cardinal.mk (ScottEndP DBilimit) +
          Cardinal.mk (ScottEndP DBilimit))
        ≤ Cardinal.continuum + (Cardinal.continuum + Cardinal.continuum) :=
          add_le_add hle (add_le_add hle hle)
      _ = Cardinal.continuum := by
          rw [Cardinal.continuum_add_self, Cardinal.continuum_add_self]
  calc Cardinal.mk (GlueCarGen (P := ScottEndP DBilimit) scottEndPId)
      ≤ Cardinal.mk (GlueBaseGen (ScottEndP DBilimit)) := h1
    _ ≤ Cardinal.continuum := h2
    _ = Cardinal.mk DBilimit := dbilimit_mk_eq_continuum.symm

-- [D-1258] glueCarGen_to_dbilimit_inj
noncomputable def glueCarGen_to_dbilimit_inj :
    GlueCarGen (P := ScottEndP DBilimit) scottEndPId ↪ DBilimit :=
  Classical.choice (Cardinal.le_def _ _ |>.mp glueCarGen_dbilimit_mk_le)

end FinalAssembly

section Lemma_A3_PsiIsoFree

-- [D-1259] rhoDF
noncomputable def rhoDF : GlueCarGen (P := ScottEndP DBilimit) scottEndPId → DBilimit :=
  glueCarGen_to_dbilimit_inj

-- [D-1260] rhoDF_injective
theorem rhoDF_injective : Function.Injective rhoDF := glueCarGen_to_dbilimit_inj.injective

-- [D-1261] inst-Nonempty
noncomputable instance : Nonempty (GlueCarGen (P := ScottEndP DBilimit) scottEndPId) := ⟨botGen⟩

-- [D-1262] psiDF
noncomputable def psiDF : DBilimit → GlueCarGen (P := ScottEndP DBilimit) scottEndPId :=
  Function.invFun rhoDF

-- [D-1263] psiDF_rhoDF
theorem psiDF_rhoDF (w : GlueCarGen (P := ScottEndP DBilimit) scottEndPId) :
    psiDF (rhoDF w) = w :=
  Function.leftInverse_invFun rhoDF_injective w

-- [D-1264] sigmaA'
noncomputable def sigmaA' (x : DBilimit) : DBilimit := rhoDF (Psi x)

-- [D-1265] sigmaB'
noncomputable def sigmaB' (x : DBilimit) : DBilimit :=
  rhoDF ⟨canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x))),
    canonGen_idem scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top _⟩

-- [D-1266] sigmaC'
noncomputable def sigmaC' (x : DBilimit) : DBilimit :=
  rhoDF ⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x))),
    canonGen_idem scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top _⟩

-- [D-1267] sigmaA'_injective
theorem sigmaA'_injective : Function.Injective sigmaA' := by
  intro x x' h
  have h1 : Psi x = Psi x' := rhoDF_injective h
  have h2 : (Psi x).1 = (Psi x').1 := congrArg Subtype.val h1
  rw [Psi_apply, Psi_apply] at h2
  exact constScottHom_injective (Sum.inl.inj h2)

-- [D-1268] sigmaB'_injective
theorem sigmaB'_injective : Function.Injective sigmaB' := by
  intro x x' h
  have h1 : (⟨canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x))), _⟩ :
      GlueCarGen (P := ScottEndP DBilimit) scottEndPId) =
      ⟨canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x'))), _⟩ :=
    rhoDF_injective h
  have h2 : canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x))) =
      canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x'))) := congrArg Subtype.val h1
  rw [canonGen_tagB_constScottHom_eq, canonGen_tagB_constScottHom_eq] at h2
  rcases eq_or_ne x (⊥ : DBilimit) with hx | hx
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [hx, hx']
    · rw [if_pos hx, if_neg hx'] at h2
      exact absurd h2 Sum.inl_ne_inr
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [if_neg hx, if_pos hx'] at h2
      exact absurd h2.symm Sum.inl_ne_inr
    · rw [if_neg hx, if_neg hx'] at h2
      exact constScottHom_injective (Sum.inl.inj (Sum.inr.inj h2))

-- [D-1269] sigmaC'_injective
theorem sigmaC'_injective : Function.Injective sigmaC' := by
  intro x x' h
  have h1 : (⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x))), _⟩ :
      GlueCarGen (P := ScottEndP DBilimit) scottEndPId) =
      ⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))), _⟩ :=
    rhoDF_injective h
  have h2 : canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x))) =
      canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))) := congrArg Subtype.val h1
  rw [canonGen_tagC_constScottHom_eq, canonGen_tagC_constScottHom_eq] at h2
  rcases eq_or_ne x (⊥ : DBilimit) with hx | hx
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [hx, hx']
    · rw [if_pos hx, if_neg hx'] at h2
      exact absurd h2 Sum.inl_ne_inr
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [if_neg hx, if_pos hx'] at h2
      exact absurd h2.symm Sum.inl_ne_inr
    · rw [if_neg hx, if_neg hx'] at h2
      exact constScottHom_injective (Sum.inr.inj (Sum.inr.inj h2))

-- [D-1270] sigmaA'_ne_sigmaB'
theorem sigmaA'_ne_sigmaB' (x x' : DBilimit) : sigmaA' x ≠ sigmaB' x' := by
  intro h
  have h1 : psiDF (sigmaA' x) = psiDF (sigmaB' x') := congrArg psiDF h
  have hAval : (psiDF (sigmaA' x)).1 = Sum.inl (constScottHom x) := by
    show (psiDF (rhoDF (Psi x))).1 = _
    rw [psiDF_rhoDF, Psi_apply]
  have hBval : (psiDF (sigmaB' x')).1 =
      canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x'))) := by
    show (psiDF (rhoDF ⟨canonGen scottEndPId
      (Sum.inr (Sum.inl (constScottHom x'))), _⟩)).1 = _
    rw [psiDF_rhoDF]
  have h2 : Sum.inl (constScottHom x) =
      canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x'))) := by
    rw [← hAval, ← hBval]; exact congrArg Subtype.val h1
  rw [canonGen_tagB_constScottHom_eq] at h2
  rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
  · rw [if_pos hx'] at h2
    exact (scottEndPId_ne_constScottHom x) (Sum.inl.inj h2).symm
  · rw [if_neg hx'] at h2
    exact Sum.inl_ne_inr h2

-- [D-1271] sigmaB'_ne_sigmaC'
theorem sigmaB'_ne_sigmaC' (x x' : DBilimit) : sigmaB' x ≠ sigmaC' x' := by
  intro h
  have h1 : (⟨canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x))), _⟩ :
      GlueCarGen (P := ScottEndP DBilimit) scottEndPId) =
      ⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))), _⟩ :=
    rhoDF_injective h
  have h2 : canonGen scottEndPId (Sum.inr (Sum.inl (constScottHom x))) =
      canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))) := congrArg Subtype.val h1
  rw [canonGen_tagB_constScottHom_eq, canonGen_tagC_constScottHom_eq] at h2
  rcases eq_or_ne x (⊥ : DBilimit) with hx | hx
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [if_pos hx, if_pos hx'] at h2
      exact scottEndPId_ne_top (Sum.inl.inj h2)
    · rw [if_pos hx, if_neg hx'] at h2
      exact Sum.inl_ne_inr h2
  · rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [if_neg hx, if_pos hx'] at h2
      exact absurd h2 Sum.inr_ne_inl
    · rw [if_neg hx, if_neg hx'] at h2
      exact absurd (Sum.inr.inj h2) Sum.inl_ne_inr

-- [D-1272] psi_topSeq_eq_tagC_botSeq
theorem psi_topSeq_eq_tagC_botSeq :
    Psi topSeq = (⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom botSeq))),
      canonGen_idem scottEndPId scottEndPId_ne_bot scottEndPBot_ne_top _⟩ :
      GlueCarGen (P := ScottEndP DBilimit) scottEndPId) := by
  apply Subtype.ext
  show Sum.inl (constScottHom topSeq) =
    canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom botSeq)))
  rw [canonGen_tagC_constScottHom_eq]
  have hbot : botSeq = (⊥ : DBilimit) := le_antisymm (botSeq_le _) bot_le
  rw [if_pos hbot]
  exact congrArg Sum.inl (constScottHom_eq_top_iff.mpr rfl)

-- [D-1273] sigmaC'_botSeq_eq_sigmaA'_topSeq
theorem sigmaC'_botSeq_eq_sigmaA'_topSeq : sigmaC' botSeq = sigmaA' topSeq :=
  congrArg rhoDF psi_topSeq_eq_tagC_botSeq.symm

-- [D-1274] sigmaA'_eq_sigmaC'_iff
theorem sigmaA'_eq_sigmaC'_iff {x x' : DBilimit} :
    sigmaA' x = sigmaC' x' ↔ x = topSeq ∧ x' = botSeq := by
  constructor
  · intro h
    have h0 : Psi x = (⟨canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))), _⟩ :
        GlueCarGen (P := ScottEndP DBilimit) scottEndPId) := rhoDF_injective h
    have h1 : (Psi x).1 = canonGen scottEndPId (Sum.inr (Sum.inr (constScottHom x'))) :=
      congrArg Subtype.val h0
    rw [Psi_apply, canonGen_tagC_constScottHom_eq] at h1
    rcases eq_or_ne x' (⊥ : DBilimit) with hx' | hx'
    · rw [if_pos hx'] at h1
      exact ⟨constScottHom_eq_top_iff.mp (Sum.inl.inj h1), hx'⟩
    · rw [if_neg hx'] at h1
      exact absurd h1 Sum.inl_ne_inr
  · rintro ⟨hx, hx'⟩
    subst hx; subst hx'
    exact sigmaC'_botSeq_eq_sigmaA'_topSeq.symm

-- [D-1275] lemma_A3_free
theorem lemma_A3_free :
    Function.Injective sigmaA' ∧ Function.Injective sigmaB' ∧ Function.Injective sigmaC' ∧
    (∀ x x' : DBilimit, sigmaA' x ≠ sigmaB' x') ∧ (∀ x x' : DBilimit, sigmaB' x ≠ sigmaC' x') ∧
    (∀ x x' : DBilimit, sigmaA' x = sigmaC' x' ↔ x = topSeq ∧ x' = botSeq) :=
  ⟨sigmaA'_injective, sigmaB'_injective, sigmaC'_injective, sigmaA'_ne_sigmaB',
    sigmaB'_ne_sigmaC', fun _ _ => sigmaA'_eq_sigmaC'_iff⟩

end Lemma_A3_PsiIsoFree

end PsiIsoFreeLemmaA3

-- [D-1276] botSeq_isCompactElement
theorem botSeq_isCompactElement : IsCompactElement botSeq := by
  intro s _u hs _hdir _hlub _hle
  obtain ⟨w, hws⟩ := hs
  exact ⟨w, hws, botSeq_le w⟩

end LemmaA3
section Phase4ConstCNeverStabilizes
-- [D-1277] prependAddr_constC
theorem prependAddr_constC :
    prependAddr (2 : Fin 3) (fun _ => (2 : Fin 3)) = fun _ => (2 : Fin 3) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

end Phase4ConstCNeverStabilizes
-- [D-1278] constScottHom_isLUB
theorem constScottHom_isLUB {S : Set DBilimit} {a : DBilimit} (ha : IsLUB S a) :
    IsLUB (constScottHom '' S) (constScottHom a) := by
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    intro x
    exact ha.1 hs
  · intro v hv
    intro x
    apply ha.2
    intro s hs
    exact hv ⟨s, hs, rfl⟩ x

section Phase4ConstBIsFixedPt
-- [D-1279] leGlueGen_tagB_tagC_iff
theorem leGlueGen_tagB_tagC_iff {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
    (m w y : P) : leGlueGen m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inr y)) ↔ m ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hv' : v = Sum.inr (Sum.inr y) := by simpa [occsGen] using hv
    subst hv'
    by_cases hwt : w = ⊤
    · subst hwt
      have hoc : occsGen m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by simp [occsGen]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m) := by simpa using hu
      rcases hu' with hu' | hu' <;> subst hu' <;> exact huv
    · have hoc : occsGen m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
        simp only [occsGen]; rw [if_neg hwt]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
      subst hu'
      exact huv
  · intro hmy
    exact ⟨Sum.inr (Sum.inl w), self_mem_occsGen m _, Sum.inr (Sum.inr y), self_mem_occsGen m _, hmy⟩

-- [D-1280] prependAddr_constB
theorem prependAddr_constB :
    prependAddr (1 : Fin 3) (fun _ => (1 : Fin 3)) = fun _ => (1 : Fin 3) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

end Phase4ConstBIsFixedPt
section TagStabilizes
-- [D-1281] tagOf
def tagOf {P : Type u} : P ⊕ P ⊕ P → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

-- [D-1282] tagOf_glueOrderBot
theorem tagOf_glueOrderBot {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L] (m : EndP L)
    (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : EndP L) ≠ (⊤ : EndP L)) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderBot m hm hmt hbt
    tagOf (⊥ : GlueCar (P := EndP L) m).1 = 0 := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderBot m hm hmt hbt
  rfl

-- [D-1283] tagOf_glueOrderTop
theorem tagOf_glueOrderTop {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L] (m : EndP L)
    (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : EndP L) ≠ (⊤ : EndP L)) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderTop m hm hmt hbt
    tagOf (⊤ : GlueCar (P := EndP L) m).1 = 2 := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderTop m hm hmt hbt
  have hval : (⊤ : GlueCar (P := EndP L) m).1
      = canon m (Sum.inr (Sum.inr (⊤ : EndP L))) := rfl
  have hcanon : canon m (Sum.inr (Sum.inr (⊤ : EndP L)))
      = Sum.inr (Sum.inr (⊤ : EndP L)) := by
    simp only [canon]
    split_ifs with h1 h2
    · exact absurd h1 hbt.symm
    · exact absurd h2 hmt.symm
    · rfl
  rw [hval, hcanon]
  rfl

-- [D-1284] tagOf_bot
theorem tagOf_bot (k : ℕ) : tagOf (⊥ : D (k + 1)).1 = 0 := by
  have h := D_marked_point_nondegenerate k
  exact tagOf_glueOrderBot (L := D k) (markedPt k) h.1 h.2.1 h.2.2

-- [D-1285] tagOf_top
theorem tagOf_top (k : ℕ) : tagOf (⊤ : D (k + 1)).1 = 2 := by
  have h := D_marked_point_nondegenerate k
  exact tagOf_glueOrderTop (L := D k) (markedPt k) h.1 h.2.1 h.2.2

-- [D-1286] interior_forces_tagA
theorem interior_forces_tagA (k : ℕ) (w : D (k + 1)) (h1 : pD k w ≠ ⊥) (h2 : pD k w ≠ ⊤)
    (h3 : pD k w ≠ dMid k) : tagOf w.1 = 0 := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with f | f | f
  · rfl
  · exfalso
    simp only [pD, pGenM] at h1 h2 h3
    split_ifs at h1 h2 h3 with hf
    · exact h2 rfl
    · exact h3 rfl
  · exfalso
    simp only [pD, pGenM] at h2
    exact h2 rfl

-- [D-1287] tagB_forces_prev_mid
theorem tagB_forces_prev_mid (k : ℕ) (w : D (k + 1)) (h : tagOf w.1 = 1)
    (h2 : pD k w ≠ ⊤) : pD k w = dMid k := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with f | f | f
  · exact absurd (show (0 : Fin 3) = 1 from h) (by decide)
  · simp only [pD, pGenM] at h2 ⊢
    split_ifs at h2 ⊢ with hf
    · exact absurd rfl h2
    · rfl
  · exact absurd (show (2 : Fin 3) = 1 from h) (by decide)

-- [D-1288] tagOf_ne_two_of_ne_top
theorem tagOf_ne_two_of_ne_top (k : ℕ) (w : D (k + 1)) (h2 : pD k w ≠ ⊤) :
    tagOf w.1 ≠ 2 := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with f | f | f
  · exact (show (0 : Fin 3) ≠ 2 by decide)
  · exact (show (1 : Fin 3) ≠ 2 by decide)
  · exfalso
    simp only [pD, pGenM] at h2
    exact h2 rfl

-- [D-1289] pD_dMid_succ
theorem pD_dMid_succ (k : ℕ) : pD k (dMid (k + 1)) = dMid k :=
  pGenM_section (dMid k) (dMid k)

-- [D-1290] tagOf_dMid_succ
theorem tagOf_dMid_succ (k : ℕ) : tagOf (dMid (k + 1)).1 = 0 := rfl

-- [D-1291] interior_gives_tagA
theorem interior_gives_tagA (x : DBilimit) (k : ℕ) (h1 : x.1 k ≠ ⊥) (h2 : x.1 k ≠ ⊤)
    (h3 : x.1 k ≠ dMid k) : tagOf (x.1 (k + 1)).1 = 0 := by
  apply interior_forces_tagA k (x.1 (k + 1))
  · rw [x.2 k]; exact h1
  · rw [x.2 k]; exact h2
  · rw [x.2 k]; exact h3

-- [D-1292] interior_persists
theorem interior_persists (x : DBilimit) (k : ℕ) (h1 : x.1 k ≠ ⊥) (h2 : x.1 k ≠ ⊤) :
    x.1 (k + 1) ≠ ⊥ ∧ x.1 (k + 1) ≠ ⊤ := by
  constructor
  · intro hbot; exact h1 (by rw [← x.2 k, hbot, pD_bot])
  · intro htop; exact h2 (by rw [← x.2 k, htop, pD_top])

-- [D-1293] tag_stabilizes
theorem tag_stabilizes (x : DBilimit) :
    ∃ N, ∀ k ≥ N, tagOf (x.1 (k + 1)).1 = tagOf (x.1 (N + 1)).1 := by
  by_cases hex : ∃ N, x.1 N ≠ ⊥ ∧ x.1 N ≠ ⊤
  ·
    obtain ⟨N, hb, ht⟩ := hex
    have hint : ∀ k ≥ N, x.1 k ≠ ⊥ ∧ x.1 k ≠ ⊤ := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hb, ht⟩
      | succ n _hn ih => exact interior_persists x n ih.1 ih.2
    have hstep : ∀ m, x.1 (m + 1) = dMid (m + 1) → x.1 m = dMid m := by
      intro m h; rw [← x.2 m, h, pD_dMid_succ]
    have hdesc : ∀ a b, a ≤ b → x.1 b = dMid b → x.1 a = dMid a := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact id
      | succ n _hn ih => intro h; exact ih (hstep n h)
    have hfin : ∀ t : Fin 3, t ≠ 2 → t = 0 ∨ t = 1 := by decide
    have hnot01 : ∀ k, N ≤ k → tagOf (x.1 (k + 1)).1 = 0 ∨ tagOf (x.1 (k + 1)).1 = 1 := by
      intro k hk
      refine hfin _ (tagOf_ne_two_of_ne_top k (x.1 (k + 1)) ?_)
      rw [x.2 k]; exact (hint k hk).2
    have hkey : ∀ j j', N ≤ j → j < j' →
        tagOf (x.1 (j + 1)).1 = 1 → tagOf (x.1 (j' + 1)).1 = 1 → False := by
      intro j j' hNj hjj' hj hj'
      have h2' : pD j' (x.1 (j' + 1)) ≠ ⊤ := by
        rw [x.2 j']; exact (hint j' (le_trans hNj hjj'.le)).2
      have hmidj' : x.1 j' = dMid j' := by
        rw [← x.2 j']; exact tagB_forces_prev_mid j' (x.1 (j' + 1)) hj' h2'
      have hmidj : x.1 (j + 1) = dMid (j + 1) := hdesc (j + 1) j' hjj' hmidj'
      rw [hmidj, tagOf_dMid_succ] at hj
      exact absurd hj (by decide)
    by_cases hB : ∃ j, N ≤ j ∧ tagOf (x.1 (j + 1)).1 = 1
    · obtain ⟨j, hNj, hj⟩ := hB
      refine ⟨j + 1, ?_⟩
      intro k hk
      have hk0 : tagOf (x.1 (k + 1)).1 = 0 := by
        rcases hnot01 k (le_trans hNj (Nat.le_of_succ_le hk)) with h | h
        · exact h
        · exact (hkey j k hNj (Nat.lt_of_succ_le hk) hj h).elim
      have hj1 : tagOf (x.1 (j + 1 + 1)).1 = 0 := by
        rcases hnot01 (j + 1) (le_trans hNj (Nat.le_succ j)) with h | h
        · exact h
        · exact (hkey j (j + 1) hNj (Nat.lt_succ_self j) hj h).elim
      rw [hk0, hj1]
    · push_neg at hB
      refine ⟨N, ?_⟩
      intro k hk
      have hk0 : tagOf (x.1 (k + 1)).1 = 0 := by
        rcases hnot01 k hk with h | h
        · exact h
        · exact absurd h (hB k hk)
      have hN0 : tagOf (x.1 (N + 1)).1 = 0 := by
        rcases hnot01 N le_rfl with h | h
        · exact h
        · exact absurd h (hB N le_rfl)
      rw [hk0, hN0]
  · have hb : ∀ N, x.1 N = ⊥ ∨ x.1 N = ⊤ := by
      intro N
      by_contra hcon
      push_neg at hcon
      exact hex ⟨N, hcon.1, hcon.2⟩
    have stepBot : ∀ j, x.1 j = ⊥ → x.1 (j + 1) = ⊥ := by
      intro j hj
      rcases hb (j + 1) with h | h
      · exact h
      · exfalso
        have hcontra : x.1 j = (⊤ : D j) := by rw [← x.2 j, h, pD_top]
        rw [hj] at hcontra
        exact bot_ne_top_of_nontrivial hcontra
    have stepTop : ∀ j, x.1 j = ⊤ → x.1 (j + 1) = ⊤ := by
      intro j hj
      rcases hb (j + 1) with h | h
      · exfalso
        have hcontra : x.1 j = (⊥ : D j) := by rw [← x.2 j, h, pD_bot]
        rw [hj] at hcontra
        exact bot_ne_top_of_nontrivial hcontra.symm
      · exact h
    refine ⟨0, ?_⟩
    intro k hk
    rcases hb 0 with h0 | h0
    · have hall : ∀ j, x.1 j = ⊥ := by
        intro j
        induction j with
        | zero => exact h0
        | succ n ih => exact stepBot n ih
      rw [show tagOf (x.1 (k + 1)).1 = 0 from by rw [hall (k + 1)]; exact tagOf_bot k,
          show tagOf (x.1 (0 + 1)).1 = 0 from by rw [hall (0 + 1)]; exact tagOf_bot 0]
    · have hall : ∀ j, x.1 j = ⊤ := by
        intro j
        induction j with
        | zero => exact h0
        | succ n ih => exact stepTop n ih
      rw [show tagOf (x.1 (k + 1)).1 = 2 from by rw [hall (k + 1)]; exact tagOf_top k,
          show tagOf (x.1 (0 + 1)).1 = 2 from by rw [hall (0 + 1)]; exact tagOf_top 0]

end TagStabilizes

section ColimitCoconeIso

variable {X : Type*} [PartialOrder X] {eX : ∀ k, D k → X} {pX : ∀ k, X → D k}

-- [D-1294] IsColimitCocone.proj_tower
theorem IsColimitCocone.proj_tower (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    (k : ℕ) (x : X) : pX k x = pD k (pX (k + 1) x) := by
  apply le_antisymm
  · have h1 : eX (k + 1) (iotaD k (pX k x)) ≤ x := by
      rw [h.compat k (pX k x)]; exact h.deflation k x
    have h2 : iotaD k (pX k x) ≤ pX (k + 1) x := by
      have := hpX (k + 1) h1
      rwa [h.retraction (k + 1) (iotaD k (pX k x))] at this
    have := pD_monotone k _ _ h2
    rwa [pD_iotaD k (pX k x)] at this
  · have h1 : eX (k + 1) (iotaD k (pD k (pX (k + 1) x))) ≤ x :=
      le_trans (heX (k + 1) (pD_deflation k (pX (k + 1) x))) (h.deflation (k + 1) x)
    have h2 : eX k (pD k (pX (k + 1) x)) ≤ x := by
      rwa [h.compat k (pD k (pX (k + 1) x))] at h1
    have := hpX k h2
    rwa [h.retraction k (pD k (pX (k + 1) x))] at this

-- [D-1295] IsColimitCocone.proj_pLe
theorem IsColimitCocone.proj_pLe (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    {j : ℕ} : ∀ {n : ℕ} (hjn : j ≤ n) (x : X), pX j x = pLe hjn (pX n x) := by
  intro n hjn
  induction n, hjn using Nat.le_induction with
  | base => intro x; rw [pLe_self j (le_refl j)]
  | succ n hjn ih =>
      intro x
      rw [pLe_succ hjn (Nat.le_succ_of_le hjn), ← h.proj_tower hpX heX n x]
      exact ih x

-- [D-1296] IsColimitCocone.toDBil
noncomputable def IsColimitCocone.toDBil (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k)) (x : X) : DBilimit :=
  ⟨fun k => pX k x, fun k => (h.proj_tower hpX heX k x).symm⟩

-- [D-1297] IsColimitCocone.toDBil_apply
@[simp] theorem IsColimitCocone.toDBil_apply (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k)) (x : X) (k : ℕ) :
    (h.toDBil hpX heX x).1 k = pX k x := rfl

-- [D-1298] IsColimitCocone.toDBil_le_iff
theorem IsColimitCocone.toDBil_le_iff (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k)) (x x' : X) :
    h.toDBil hpX heX x ≤ h.toDBil hpX heX x' ↔ x ≤ x' := by
  constructor
  · intro hle
    have hle' : ∀ k, pX k x ≤ pX k x' := hle
    have hub : x' ∈ upperBounds (Set.range (fun k => eX k (pX k x))) := by
      rintro _ ⟨k, rfl⟩
      exact le_trans (heX k (hle' k)) (h.deflation k x')
    exact (h.isLUB x).2 hub
  · intro hle
    show ∀ k, pX k x ≤ pX k x'
    exact fun k => hpX k hle

-- [D-1299] IsColimitCocone.toDBil_injective
theorem IsColimitCocone.toDBil_injective (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k)) :
    Function.Injective (h.toDBil hpX heX) := by
  intro a b hab
  exact le_antisymm ((h.toDBil_le_iff hpX heX a b).mp (le_of_eq hab))
    ((h.toDBil_le_iff hpX heX b a).mp (le_of_eq hab.symm))

-- [D-1300] IsColimitCocone.toDBil_surjective
theorem IsColimitCocone.toDBil_surjective (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    (hsup : ∀ d : DBilimit, ∃ x : X, IsLUB (Set.range (fun k => eX k (d.1 k))) x)
    (hcont : ∀ (d : DBilimit) (x : X),
      IsLUB (Set.range (fun k => eX k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (pX j x)) :
    Function.Surjective (h.toDBil hpX heX) := by
  intro d
  obtain ⟨x, hx⟩ := hsup d
  refine ⟨x, Subtype.ext (funext (fun j => ?_))⟩
  show pX j x = d.1 j
  have himg_ge : ∀ k, j ≤ k → pX j (eX k (d.1 k)) = d.1 j := by
    intro k hjk
    rw [h.proj_pLe hpX heX hjk (eX k (d.1 k)), h.retraction k (d.1 k)]
    exact DBilimit_pLe_eq d hjk
  have himg_le : ∀ k, k ≤ j → pX j (eX k (d.1 k)) ≤ d.1 j := by
    intro k hkj
    have hcompat_chase : ∀ {m : ℕ} (hkm : k ≤ m) (w : D k),
        eX k w = eX m (iotaLe hkm w) := by
      intro m hkm
      induction m, hkm using Nat.le_induction with
      | base => intro w; rw [iotaLe_self]
      | succ m hkm ih =>
          intro w
          rw [iotaLe_succ hkm (Nat.le_succ_of_le hkm), h.compat m (iotaLe hkm w)]
          exact ih w
    rw [hcompat_chase hkj (d.1 k), h.retraction j (iotaLe hkj (d.1 k))]
    have hval : (insertAtLevel k (d.1 k)).1 j = iotaLe hkj (d.1 k) :=
      seqOf_eq_iotaLe ⟨k, d.1 k⟩ hkj
    have hle := insertAtLevel_le_self d k j
    rwa [hval] at hle
  have hchain : ∀ k, eX k (d.1 k) ≤ eX (k + 1) (d.1 (k + 1)) := by
    intro k
    have hiota : iotaD k (d.1 k) ≤ d.1 (k + 1) := by
      rw [show d.1 k = pD k (d.1 (k + 1)) from (d.2 k).symm]
      exact pD_deflation k (d.1 (k + 1))
    calc eX k (d.1 k) = eX (k + 1) (iotaD k (d.1 k)) := (h.compat k (d.1 k)).symm
      _ ≤ eX (k + 1) (d.1 (k + 1)) := heX (k + 1) hiota
  have hlub2 : IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (pX j x) := hcont d x hx j
  have hLUB_dj : IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (d.1 j) := by
    constructor
    · rintro _ ⟨k, rfl⟩
      rcases le_total j k with hjk | hkj
      · exact (himg_ge k hjk).le
      · exact himg_le k hkj
    · intro w hw
      calc d.1 j = pX j (eX j (d.1 j)) := (himg_ge j (le_refl j)).symm
        _ ≤ w := hw ⟨j, rfl⟩
  exact hlub2.unique hLUB_dj

-- [D-1301] IsColimitCocone.orderIsoDBil
noncomputable def IsColimitCocone.orderIsoDBil (h : IsColimitCocone eX pX)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    (hsup : ∀ d : DBilimit, ∃ x : X, IsLUB (Set.range (fun k => eX k (d.1 k))) x)
    (hcont : ∀ (d : DBilimit) (x : X),
      IsLUB (Set.range (fun k => eX k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (pX j x)) :
    X ≃o DBilimit :=
  { Equiv.ofBijective (h.toDBil hpX heX)
      ⟨h.toDBil_injective hpX heX, h.toDBil_surjective hpX heX hsup hcont⟩ with
    map_rel_iff' := by
      intro a b
      exact h.toDBil_le_iff hpX heX a b }

end ColimitCoconeIso

-- [D-1302] DBilimit_isColimitCocone_toDBil
theorem DBilimit_isColimitCocone_toDBil (z : DBilimit) :
    DBilimit_isColimitCocone.toDBil (fun k => projK_monotone k) (fun k => eK_monotone k) z = z :=
  Subtype.ext (funext (fun _ => rfl))

-- [D-1303] isColimitCocone_orderIso
noncomputable def isColimitCocone_orderIso
    {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    {eX : ∀ k, D k → X} {pX : ∀ k, X → D k}
    {eY : ∀ k, D k → Y} {pY : ∀ k, Y → D k}
    (hX : IsColimitCocone eX pX) (hY : IsColimitCocone eY pY)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    (hpY : ∀ k, Monotone (pY k)) (heY : ∀ k, Monotone (eY k))
    (hsupX : ∀ d : DBilimit, ∃ x : X, IsLUB (Set.range (fun k => eX k (d.1 k))) x)
    (hcontX : ∀ (d : DBilimit) (x : X),
      IsLUB (Set.range (fun k => eX k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (pX j x))
    (hsupY : ∀ d : DBilimit, ∃ y : Y, IsLUB (Set.range (fun k => eY k (d.1 k))) y)
    (hcontY : ∀ (d : DBilimit) (y : Y),
      IsLUB (Set.range (fun k => eY k (d.1 k))) y →
      ∀ j, IsLUB (Set.range (fun k => pY j (eY k (d.1 k)))) (pY j y)) :
    X ≃o Y :=
  (hX.orderIsoDBil hpX heX hsupX hcontX).trans
    (hY.orderIsoDBil hpY heY hsupY hcontY).symm

end SierpinskiApplication
