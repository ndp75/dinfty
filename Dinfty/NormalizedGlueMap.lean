import Dinfty.HornBConjugation

open GluingTowerLibrary SierpinskiApplication

-- [D-1320] §s-morphism-action-under-the-const-L
namespace NormalizedGlueMap

universe u

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

-- [D-1321] baseMap
def baseMap (g : P →o P') : GlueBase P → GlueBase P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (g x))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

section Reflect

variable (g : P →o P')

-- [D-1322] map_eq_bot
theorem map_eq_bot (hginj : Function.Injective g) (hbot : g ⊥ = (⊥ : P')) (a : P) :
    g a = (⊥ : P') ↔ a = (⊥ : P) :=
  ⟨fun h => hginj (h.trans hbot.symm), fun h => h ▸ hbot⟩

-- [D-1323] map_eq_top
theorem map_eq_top (hginj : Function.Injective g) (htop : g ⊤ = (⊤ : P')) (a : P) :
    g a = (⊤ : P') ↔ a = (⊤ : P) :=
  ⟨fun h => hginj (h.trans htop.symm), fun h => h ▸ htop⟩

-- [D-1324] map_eq_mid
theorem map_eq_mid (m : P) (m' : P') (hginj : Function.Injective g) (hmid : g m = m')
    (a : P) : g a = m' ↔ a = m :=
  ⟨fun h => hginj (h.trans hmid.symm), fun h => h ▸ hmid⟩

end Reflect

section Tripointed

variable (g : P →o P') (m : P) (m' : P')

-- [D-1325] canon_baseMap
theorem canon_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueBase P) :
    canon m' (baseMap g x) = baseMap g (canon m x) := by
  have hm0' : m' ≠ (⊥ : P') := fun h => hm0 (hginj (hmid.trans (h.trans hbot.symm)))
  cases x with
  | inl a => rfl
  | inr y =>
    cases y with
    | inl a =>
      by_cases ha : a = (⊥ : P)
      · simp [baseMap, canon, ha, hbot, hmid]
      · simp [baseMap, canon, ha, (map_eq_bot g hginj hbot a).not.mpr ha]
    | inr a =>
      by_cases ha : a = (⊥ : P)
      · simp [baseMap, canon, ha, hbot, htop]
      · by_cases ham : a = m
        · simp [baseMap, canon, ham, hmid, htop, hm0, hm0',
            (map_eq_bot g hginj hbot a).not.mpr ha]
        · simp [baseMap, canon, ha, ham,
            (map_eq_bot g hginj hbot a).not.mpr ha,
            (map_eq_mid g m m' hginj hmid a).not.mpr ham]

-- [D-1326] occs_baseMap
theorem occs_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) (x : GlueBase P) :
    (occs m x).map (baseMap g) = occs m' (baseMap g x) := by
  have hmt' : m' ≠ (⊤ : P') := fun h => hmt (hginj (hmid.trans (h.trans htop.symm)))
  have hb := map_eq_bot g hginj hbot
  have ht := map_eq_top g hginj htop
  have hm := map_eq_mid g m m' hginj hmid
  cases x with
  | inl a =>
    by_cases ham : a = m
    · simp [baseMap, occs, ham, hmid, hbot]
    · by_cases hat : a = (⊤ : P)
      · have : g a ≠ m' := fun h => hmt' (by rw [← h, hat, htop])
        simp [baseMap, occs, hat, htop, hbot, this, Ne.symm hmt, Ne.symm hmt']
      · simp [baseMap, occs, ham, hat, (hm a).not.mpr ham, (ht a).not.mpr hat]
  | inr y =>
    cases y with
    | inl a =>
      by_cases hat : a = (⊤ : P)
      · simp [baseMap, occs, hat, htop, hmid]
      · simp [baseMap, occs, hat, (ht a).not.mpr hat]
    | inr a => simp [baseMap, occs]

-- [D-1327] rawRule_baseMap
theorem rawRule_baseMap (hmid : g m = m') {u v : GlueBase P}
    (h : rawRule m u v) : rawRule m' (baseMap g u) (baseMap g v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact g.monotone h
    | inr w =>
      cases w with
      | inl b => exact hmid ▸ g.monotone h
      | inr b => trivial
  | inr u' =>
    cases u' with
    | inl a =>
      cases v with
      | inl b => exact h.elim
      | inr w =>
        cases w with
        | inl b => exact g.monotone h
        | inr b => exact hmid ▸ g.monotone h
    | inr a =>
      cases v with
      | inl b => exact h.elim
      | inr w =>
        cases w with
        | inl b => exact h.elim
        | inr b => exact g.monotone h

-- [D-1328] leGlue_baseMap
theorem leGlue_baseMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) {x y : GlueBase P} (h : leGlue m x y) :
    leGlue m' (baseMap g x) (baseMap g y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  refine ⟨baseMap g u, ?_, baseMap g v, ?_, rawRule_baseMap g m m' hmid huv⟩
  · rw [← occs_baseMap g m m' hginj hbot hmid htop hmt]
    exact List.mem_map_of_mem hu
  · rw [← occs_baseMap g m m' hginj hbot hmid htop hmt]
    exact List.mem_map_of_mem hv

-- [D-1329] glueMap
def glueMap (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueCar (P := P) m) : GlueCar (P := P') m' :=
  ⟨baseMap g x.val, by
    rw [canon_baseMap g m m' hginj hbot hmid htop hm0, x.property]⟩

-- [D-1330] glueMap_val
@[simp] theorem glueMap_val (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hm0 : m ≠ (⊥ : P)) (x : GlueCar (P := P) m) :
    (glueMap g m m' hginj hbot hmid htop hm0 x).val = baseMap g x.val := rfl

-- [D-1331] glueMap_monotone
theorem glueMap_monotone (hginj : Function.Injective g)
    (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
    (hmt : m ≠ (⊤ : P)) (hm0 : m ≠ (⊥ : P))
    {x y : GlueCar (P := P) m} (h : leGlue m x.val y.val) :
    leGlue m' (glueMap g m m' hginj hbot hmid htop hm0 x).val
              (glueMap g m m' hginj hbot hmid htop hm0 y).val :=
  leGlue_baseMap g m m' hginj hbot hmid htop hmt h

section TripointedImage

variable (hginj : Function.Injective g)
  (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m') (htop : g ⊤ = (⊤ : P'))
  (hm0 : m ≠ (⊥ : P))

-- [D-1332] glueMap_bot
theorem glueMap_bot :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelT m, rfl⟩ = ⟨skelT m', rfl⟩ := by
  apply Subtype.ext; simp [baseMap, skelT, hbot]

-- [D-1333] glueMap_mid
theorem glueMap_mid (hmb : canon m (skelL m) = skelL m)
    (hmb' : canon m' (skelL m') = skelL m') :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelL m, hmb⟩ = ⟨skelL m', hmb'⟩ := by
  apply Subtype.ext; simp [baseMap, skelL, hmid]

-- [D-1334] glueA_self_eq_glue_aL_bT
theorem glueA_self_eq_glue_aL_bT (m : P) (hm0 : m ≠ (⊥ : P)) (hbt : (⊥ : P) ≠ ⊤) :
    glueA m m = incl m hm0 hbt (Sum.inr (Sum.inl (⊥ : P))) := by
  apply Subtype.ext
  show (Sum.inl m : GlueBase P) = canon m (Sum.inr (Sum.inl (⊥ : P)))
  rw [canon, if_pos rfl]

-- [D-1335] glueMap_top
theorem glueMap_top (hrt : canon m (skelR m) = skelR m)
    (hrt' : canon m' (skelR m') = skelR m') :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelR m, hrt⟩ = ⟨skelR m', hrt'⟩ := by
  apply Subtype.ext; simp [baseMap, skelR, htop]

-- [D-1336] glueMap_midA
theorem glueMap_midA :
    glueMap g m m' hginj hbot hmid htop hm0 ⟨skelG1 m, rfl⟩ = ⟨skelG1 m', rfl⟩ := by
  apply Subtype.ext
  simp [baseMap, skelG1, hmid]

end TripointedImage

end Tripointed

-- [D-1337] §The-normalized-tower
-- [D-1338] §Theorem-B-s-up-transfer-survives
namespace UpTransfer

variable {X : Type u} [Lattice X] [BoundedOrder X]

-- [D-1339] id_not_le_constHom
theorem id_not_le_constHom (mid : X) (hmt : mid ≠ (⊤ : X)) :
    ¬ (OrderHom.id : EndP X) ≤ constHom mid := fun h =>
  hmt (le_antisymm le_top (h ⊤))

-- [D-1340] constHom_not_le_id
theorem constHom_not_le_id (mid : X) (hm0 : mid ≠ (⊥ : X)) :
    ¬ (constHom mid : EndP X) ≤ (OrderHom.id : EndP X) := fun h =>
  hm0 (le_bot_iff.mp (h ⊥))

end UpTransfer

-- [D-1341] tri_up_transfer
open scoped Classical in

theorem tri_up_transfer {X : Type u} [DecidableEq X] [Lattice X] [BoundedOrder X]
    [Fintype X] (mid : X) (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X))
    (hbt : (⊥ : X) ≠ (⊤ : X))
    (hAut : Subsingleton (EndP X ≃o EndP X)) :
    Subsingleton (GlueCar (P := EndP X) (constHom mid)
      ≃o GlueCar (P := EndP X) (constHom mid)) := by
  have hMb : (constHom mid : EndP X) ≠ ⊥ := by
    intro h
    have hb : (⊥ : EndP X) = constHom (⊥ : X) := by ext x; rfl
    exact hm0 (constHom_injective (h.trans hb))
  have hMt : (constHom mid : EndP X) ≠ ⊤ := by
    intro h
    exact hmt (constHom_injective (h.trans endP_top_eq_constHom_top))
  exact glue_rigid_of_incomparable (P := EndP X) (constHom mid) hMb hMt
    (endP_bot_ne_top hbt) hAut OrderHom.id
    (UpTransfer.id_not_le_constHom mid hmt) (UpTransfer.constHom_not_le_id mid hm0)

-- [D-1342] tri_level1_rigid
open scoped Classical in
theorem tri_level1_rigid :
    Subsingleton (GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))
      ≃o GlueCar (P := EndP (Fin 3)) (constHom (1 : Fin 3))) :=
  tri_up_transfer (1 : Fin 3) (by decide) (by decide) (by decide) H0_rigid

-- [D-1343] §D-down-transfer-s-inputs-normalized
namespace DownInputs

variable {X : Type u} [Lattice X] [BoundedOrder X]

-- [D-1344] constHom_ne_bot
theorem constHom_ne_bot (mid : X) (hm0 : mid ≠ (⊥ : X)) :
    (constHom mid : EndP X) ≠ ⊥ := by
  intro h
  have hb : (⊥ : EndP X) = constHom (⊥ : X) := by ext x; rfl
  exact hm0 (constHom_injective (h.trans hb))

-- [D-1345] constHom_ne_top
theorem constHom_ne_top (mid : X) (hmt : mid ≠ (⊤ : X)) :
    (constHom mid : EndP X) ≠ ⊤ := fun h =>
  hmt (constHom_injective (h.trans endP_top_eq_constHom_top))

-- [D-1346] bot_ne_coatomOf_endP
theorem bot_ne_coatomOf_endP [UniqueAtomCoatom X] (hbt : (⊥ : X) ≠ ⊤) :
    (⊥ : EndP X) ≠ coatomOf (EndP X) := by
  rw [coatomOf_endP_eq_cospikeHom]
  intro hc
  have h1 : (⊥ : EndP X) (⊤ : X) = cospikeHom (coatomOf X) (⊤ : X) :=
    congrArg (· (⊤ : X)) hc
  rw [endPBot_apply, cospikeHom_apply_of_ne _ hbt.symm] at h1
  exact hbt h1

-- [D-1347] coatomOf_endP_ne_constHom
theorem coatomOf_endP_ne_constHom [UniqueAtomCoatom X] (mid : X)
    (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    coatomOf (EndP X) ≠ constHom mid := by
  rw [coatomOf_endP_eq_cospikeHom]
  intro hc
  have h1 : cospikeHom (coatomOf X) (⊤ : X) = (constHom mid : EndP X) (⊤ : X) :=
    congrArg (· (⊤ : X)) hc
  rw [cospikeHom_apply_of_ne _ hbt.symm, constHom_apply] at h1
  exact hmt h1.symm

end DownInputs

-- [D-1348] tri_uniqueAtomCoatom
open scoped Classical in
noncomputable def tri_uniqueAtomCoatom {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := DownInputs.constHom_ne_bot mid hm0
    @UniqueAtomCoatom (GlueCar (P := EndP X) (constHom mid))
      (glueLattice (constHom mid) (DownInputs.constHom_ne_bot mid hm0)
        (DownInputs.constHom_ne_top mid hmt) (endP_bot_ne_top hbt))
      (glueBoundedOrder (constHom mid) (DownInputs.constHom_ne_bot mid hm0)
        (DownInputs.constHom_ne_top mid hmt) (endP_bot_ne_top hbt)) :=
  glueUniqueAtomCoatom (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
    (DownInputs.bot_ne_coatomOf_endP hbt)
    (DownInputs.coatomOf_endP_ne_constHom mid hmt hbt)

-- [D-1349] tri_J_connected
open scoped Classical in
theorem tri_J_connected {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueCarPartialOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    (Graph.Hasse {x : GlueCar (P := EndP X) (constHom mid) //
      HasUniqueDownCover x}).Connected :=
  hasse_hasUniqueDownCover_glueCar_connected (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)

section TriCovers

variable {X : Type u} [DecidableEq X] [Lattice X] [BoundedOrder X] [Fintype X]
  [UniqueAtomCoatom X] (mid : X) (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X))
  (hbt : (⊥ : X) ≠ ⊤)

-- [D-1350] tri_has_interior_point
open scoped Classical in
theorem tri_has_interior_point :
    letI := glueCarPartialOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    glueA (P := EndP X) (constHom mid) (constHom mid) ≠ ⊥ ∧
    glueA (P := EndP X) (constHom mid) (constHom mid) ≠ ⊤ := by
  letI := glueCarPartialOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  refine ⟨fun h => DownInputs.constHom_ne_bot mid hm0 (glueA_injective _ h), ?_⟩
  exact glueA_ne_top (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt) (constHom mid)

end TriCovers

-- [D-1351] §The-two-cover-corollaries-landed
-- [D-1352] tri_top_hasUniqueDownCover
open scoped Classical in
theorem tri_top_hasUniqueDownCover {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    HasUniqueDownCover (⊤ : GlueCar (P := EndP X) (constHom mid)) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  exact hasUniqueDownCover_top

-- [D-1353] tri_bot_hasUniqueUpCover
open scoped Classical in
theorem tri_bot_hasUniqueUpCover {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    HasUniqueUpCover (⊥ : GlueCar (P := EndP X) (constHom mid)) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  exact hasUniqueUpCover_bot

-- [D-1354] §D-down-transfer-itself-level-parametric
-- [D-1355] general_down_transfer
open scoped Classical in

theorem general_down_transfer {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X]
    (hTop : HasUniqueDownCover (⊤ : X))
    (hJconn : (Graph.Hasse {x : X // JoinIrred X x}).Connected) :
    Subsingleton (X ≃o X) → Subsingleton (EndP X ≃o EndP X) := by
  intro hDk
  haveI : Nonempty {x : X // JoinIrred X x} :=
    ⟨⟨⊤, joinIrred_of_hasUniqueDownCover hTop⟩⟩
  suffices hall : ∀ φ₀ : EndP (X) ≃o EndP (X), φ₀ = OrderIso.refl _ by
    exact ⟨fun a b => (hall a).trans (hall b).symm⟩
  intro φ₀
  set φ : {f : EndP (X) // JoinIrred (EndP (X)) f} ≃
      {f : EndP (X) // JoinIrred (EndP (X)) f} :=
    { toFun := fun x => ⟨φ₀ x.1, joinIrred_orderIso φ₀ x.2⟩
      invFun := fun x => ⟨φ₀.symm x.1, joinIrred_orderIso φ₀.symm x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp } with hφdef
  have hφval : ∀ x : {f : EndP (X) // JoinIrred (EndP (X)) f}, (φ x).1 = φ₀ x.1 := fun x => rfl
  have hφord : ∀ v w, v ≤ w ↔ φ v ≤ φ w := by
    intro v w
    show (v : EndP (X)) ≤ w ↔ φ₀ v.1 ≤ φ₀ w.1
    exact φ₀.le_iff_le.symm
  let Φ : {f : EndP (X) // JoinIrred (EndP (X)) f} ≃o
      {f : EndP (X) // JoinIrred (EndP (X)) f} :=
    { toEquiv := φ, map_rel_iff' := fun {v w} => (hφord v w).symm }
  have hφadj : ∀ v w, (Graph.Hasse {f : EndP (X) // JoinIrred (EndP (X)) f}).adj v w ↔
      (Graph.Hasse {f : EndP (X) // JoinIrred (EndP (X)) f}).adj (φ v) (φ w) := by
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
  have ΓA_map : ∀ a b : X, a ≤ b ↔ γA a ≤ γA b := hγA_ord
  let ΓA : X ≃o X := { toEquiv := γA, map_rel_iff' := fun {a b} => (ΓA_map a b).symm }
  have hΓA_id : ΓA = OrderIso.refl (X) := Subsingleton.elim _ _
  have hγA_id : ∀ q : X, γA q = q := fun q => DFunLike.congr_fun hΓA_id q
  have hvert : ∀ (x : X) (hx : JoinIrred (X) x) (q : X),
      φ₀ (stepMap x q) = stepMap (γB ⟨x, hx⟩).1 q := by
    intro x hx q
    have hd := hdecomp (q, ⟨x, hx⟩)
    have := congrArg Subtype.val hd
    simp only [hφdef, Equiv.coe_fn_mk, jiEquiv, Equiv.coe_fn_mk] at this
    rw [hγA_id q] at this
    exact this
  have hγB_ord' : ∀ b1 b2 : {x : X // JoinIrred (X) x}, b1 ≤ b2 ↔ γB b1 ≤ γB b2 := hγB_ord
  have ΓB_map : ∀ v v' : X, v ≤ v' ↔ tauHat γB v ≤ tauHat γB v' :=
    fun v v' => (tauHat_le_iff γB φ₀ hvert v v').symm
  have hΓB_bij : Function.Bijective (tauHat γB) :=
    Finite.injective_iff_bijective.mp (tauHat_injective γB φ₀ hvert)
  let ΓB : X ≃o X :=
    { toEquiv := Equiv.ofBijective (tauHat γB) hΓB_bij,
      map_rel_iff' := fun {a b} => (ΓB_map a b).symm }
  have hΓB_id : ΓB = OrderIso.refl (X) := Subsingleton.elim _ _
  have hγB_id : ∀ v : X, tauHat γB v = v := fun v => DFunLike.congr_fun hΓB_id v
  have hγB_fix : ∀ x : {x : X // JoinIrred (X) x}, γB x = x := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have := hγB_id x
    rw [tauHat_eq_of_joinIrred γB hγB_ord' x hx] at this
    exact this
  have hφ_fix : ∀ f : {f : EndP (X) // JoinIrred (EndP (X)) f}, φ₀ f.1 = f.1 := by
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

-- [D-1356] general_down_transfer_recovers_D_down_transfer
open scoped Classical in
theorem general_down_transfer_recovers_D_down_transfer (k : ℕ) :
    Subsingleton (D k ≃o D k) → Subsingleton (EndP (D k) ≃o EndP (D k)) := by
  letI := realUniqueAtomCoatom k
  exact general_down_transfer (D_top_hasUniqueDownCover k) (D_J_connected k)

-- [D-1357] tri_down_transfer
open scoped Classical in

theorem tri_down_transfer {X : Type u} [DecidableEq X] [Lattice X]
    [BoundedOrder X] [Fintype X] [UniqueAtomCoatom X] (mid : X)
    (hm0 : mid ≠ (⊥ : X)) (hmt : mid ≠ (⊤ : X)) (hbt : (⊥ : X) ≠ ⊤) :
    letI := glueLattice (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    letI := glueBoundedOrder (P := EndP X) (constHom mid)
      (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
      (endP_bot_ne_top hbt)
    Subsingleton (GlueCar (P := EndP X) (constHom mid) ≃o GlueCar (P := EndP X) (constHom mid)) →
      Subsingleton (EndP (GlueCar (P := EndP X) (constHom mid))
        ≃o EndP (GlueCar (P := EndP X) (constHom mid))) := by
  letI := glueLattice (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := glueBoundedOrder (P := EndP X) (constHom mid)
    (DownInputs.constHom_ne_bot mid hm0) (DownInputs.constHom_ne_top mid hmt)
    (endP_bot_ne_top hbt)
  letI := tri_uniqueAtomCoatom (X := X) mid hm0 hmt hbt
  refine general_down_transfer hasUniqueDownCover_top ?_
  exact connected_of_pointwise_iff HasUniqueDownCover
    (JoinIrred (GlueCar (P := EndP X) (constHom mid)))
    hasUniqueDownCover_iff_joinIrred (tri_J_connected (X := X) mid hm0 hmt hbt)

namespace NormalizedTower

-- [D-1358] TriLevel
structure TriLevel : Type (u + 1) where
  carrier : Type u
  dec : DecidableEq carrier
  lat : Lattice carrier
  bdd : BoundedOrder carrier
  fin : Fintype carrier
  nontriv : Nontrivial carrier
  mid : carrier
  mid_ne_bot : letI := lat; letI := bdd; mid ≠ (⊥ : carrier)
  mid_ne_top : letI := lat; letI := bdd; mid ≠ (⊤ : carrier)

-- [D-1359] triLevel0
def triLevel0 : TriLevel where
  carrier := Fin 3
  dec := inferInstance
  lat := inferInstance
  bdd := inferInstance
  fin := inferInstance
  nontriv := ⟨0, 1, by decide⟩
  mid := 1
  mid_ne_bot := by decide
  mid_ne_top := by decide

section Succ

variable (prev : TriLevel)

-- [D-1360] markedPoint
def markedPoint : letI := prev.lat; letI := prev.bdd; EndP prev.carrier :=
  letI := prev.lat; letI := prev.bdd; constHom prev.mid

-- [D-1361] markedPoint_ne_bot
theorem markedPoint_ne_bot :
    letI := prev.lat; letI := prev.bdd
    markedPoint prev ≠ (⊥ : EndP prev.carrier) := by
  letI := prev.lat; letI := prev.bdd
  intro h
  have hb : (⊥ : EndP prev.carrier) = constHom (⊥ : prev.carrier) := by ext x; rfl
  exact prev.mid_ne_bot (constHom_injective (h.trans hb))

-- [D-1362] markedPoint_ne_top
theorem markedPoint_ne_top :
    letI := prev.lat; letI := prev.bdd
    markedPoint prev ≠ (⊤ : EndP prev.carrier) := by
  letI := prev.lat; letI := prev.bdd
  intro h
  exact prev.mid_ne_top (constHom_injective (h.trans endP_top_eq_constHom_top))

end Succ

-- [D-1363] triLevelSucc
open scoped Classical in

noncomputable def triLevelSucc (prev : TriLevel) : TriLevel :=
  letI := prev.dec
  letI := prev.lat
  letI := prev.bdd
  letI := prev.fin
  letI := prev.nontriv
  have hbtPrev : (⊥ : prev.carrier) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm : markedPoint prev ≠ (⊥ : EndP prev.carrier) := markedPoint_ne_bot prev
  have hmt : markedPoint prev ≠ (⊤ : EndP prev.carrier) := markedPoint_ne_top prev
  have hbt : (⊥ : EndP prev.carrier) ≠ (⊤ : EndP prev.carrier) := endP_bot_ne_top hbtPrev
  { carrier := GlueCar (P := EndP prev.carrier) (markedPoint prev)
    dec := inferInstance
    lat := glueLattice (markedPoint prev) hm hmt hbt
    bdd := glueBoundedOrder (markedPoint prev) hm hmt hbt
    fin := inferInstance
    nontriv := glueCar_nontrivial (markedPoint prev) hm hmt hbt
    mid := glueA (markedPoint prev) (markedPoint prev)
    mid_ne_bot := by
      letI := glueCarPartialOrder (markedPoint prev) hm hmt hbt
      letI := glueBoundedOrder (markedPoint prev) hm hmt hbt
      intro h
      have hb : (⊥ : GlueCar (P := EndP prev.carrier) (markedPoint prev))
          = incl (markedPoint prev) hm hbt (Sum.inl ⊥) := rfl
      rw [hb] at h
      have hv := congrArg Subtype.val h
      simp only [glueA, incl, canon] at hv
      exact hm (Sum.inl.inj hv)
    mid_ne_top := by
      letI := glueCarPartialOrder (markedPoint prev) hm hmt hbt
      letI := glueBoundedOrder (markedPoint prev) hm hmt hbt
      intro h
      have ht : (⊤ : GlueCar (P := EndP prev.carrier) (markedPoint prev))
          = incl (markedPoint prev) hm hbt (Sum.inr (Sum.inr ⊤)) := rfl
      rw [ht] at h
      have hv := congrArg Subtype.val h
      simp only [glueA, incl, canon] at hv
      rw [if_neg (Ne.symm hbt), if_neg (Ne.symm hmt)] at hv
      exact absurd hv (by simp) }

-- [D-1364] triLevel
noncomputable def triLevel : ℕ → TriLevel
  | 0 => triLevel0
  | k + 1 => triLevelSucc (triLevel k)

-- [D-1365] triLevelSucc_mid_val
theorem triLevelSucc_mid_val (prev : TriLevel) :
    letI := prev.dec; letI := prev.lat; letI := prev.bdd
    letI := prev.fin; letI := prev.nontriv
    ((triLevelSucc prev).mid : GlueCar (P := EndP prev.carrier) (markedPoint prev)).1
      = Sum.inl (markedPoint prev) := by
  letI := prev.dec; letI := prev.lat; letI := prev.bdd
  letI := prev.fin; letI := prev.nontriv
  rfl

end NormalizedTower

end NormalizedGlueMap
