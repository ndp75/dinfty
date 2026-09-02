import Dinfty.PhiIterateTower
import Dinfty.RealEpPairTower

open GluingTowerLibrary SierpinskiApplication

-- [D-2385] §D-the-iterate-tower-s-bilimit
open scoped Classical

namespace PhiBilimit

open PhiIterateTower EpPairTower

-- [D-2386] B
abbrev B : Type := phiTowerEP.Bilim

-- [D-2387] §The-three-points-assemble
-- [D-2388] botB
noncomputable def botB : B := ⟨fun n => (⊥ : D (n + 1)), fun n => (iter n).prj_bot⟩

-- [D-2389] midB
noncomputable def midB : B := ⟨fun n => dMid (n + 1), fun n => (iter n).prj_mid⟩

-- [D-2390] topB
noncomputable def topB : B := ⟨fun n => (⊤ : D (n + 1)), fun n => (iter n).prj_top⟩

-- [D-2391] midB_apply
@[simp] theorem midB_apply (n : ℕ) : (midB.1 n : D (n + 1)) = dMid (n + 1) := rfl

-- [D-2392] botB_le
theorem botB_le (y : B) : botB ≤ y := by
  intro n
  show (⊥ : D (n + 1)) ≤ y.1 n
  exact bot_le

-- [D-2393] le_topB
theorem le_topB (y : B) : y ≤ topB := by
  intro n
  exact @le_top (D (n + 1)) _ _ (y.1 n)

-- [D-2394] inst-OrderBot
noncomputable instance : OrderBot B where
  bot := botB
  bot_le := botB_le

-- [D-2395] inst-OrderTop
noncomputable instance : OrderTop B where
  top := topB
  le_top := le_topB

-- [D-2396] inst-BoundedOrder
noncomputable instance : BoundedOrder B := {}

-- [D-2397] midB_ne_botB
theorem midB_ne_botB : midB ≠ botB := by
  intro h
  have h1 : (dMid 1 : D 1) = (⊥ : D 1) := congrArg (fun z : B => z.1 0) h
  exact dMid_ne_bot 1 h1

-- [D-2398] midB_ne_topB
theorem midB_ne_topB : midB ≠ topB := by
  intro h
  have h1 : (dMid 1 : D 1) = (⊤ : D 1) := congrArg (fun z : B => z.1 0) h
  exact dMid_ne_top 1 h1

-- [D-2399] botB_ne_topB
theorem botB_ne_topB : botB ≠ topB := by
  intro h
  have h1 : (⊥ : D 1) = (⊤ : D 1) := congrArg (fun z : B => z.1 0) h
  exact bot_ne_top_of_nontrivial h1

-- [D-2400] §The-staging-maps-are-tripointed
-- [D-2401] embLe_bot
theorem embLe_bot {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (⊥ : D (k + 1)) = (⊥ : D (n + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_bot

-- [D-2402] embLe_mid
theorem embLe_mid {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (dMid (k + 1)) = dMid (n + 1) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_mid

-- [D-2403] embLe_top
theorem embLe_top {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (⊤ : D (k + 1)) = (⊤ : D (n + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_top

-- [D-2404] prjLe_bot
theorem prjLe_bot {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (⊥ : D (n + 1)) = (⊥ : D (j + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (⊥ : D (n + 2))) = _
      rw [(iter n).prj_bot, ih]

-- [D-2405] prjLe_mid
theorem prjLe_mid {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (dMid (n + 1)) = dMid (j + 1) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (dMid (n + 2))) = _
      rw [(iter n).prj_mid, ih]

-- [D-2406] prjLe_top
theorem prjLe_top {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (⊤ : D (n + 1)) = (⊤ : D (j + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (⊤ : D (n + 2))) = _
      rw [(iter n).prj_top, ih]

-- [D-2407] §hence-so-is-ins
-- [D-2408] ins_bot
theorem ins_bot (k : ℕ) : phiTowerEP.ins k (⊥ : D (k + 1)) = botB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (⊥ : D (k + 1)) j = (⊥ : D (j + 1))
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_bot h
  · exact embLe_bot (not_le.mp h).le

-- [D-2409] ins_mid
theorem ins_mid (k : ℕ) : phiTowerEP.ins k (dMid (k + 1)) = midB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (dMid (k + 1)) j = dMid (j + 1)
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_mid h
  · exact embLe_mid (not_le.mp h).le

-- [D-2410] ins_top
theorem ins_top (k : ℕ) : phiTowerEP.ins k (⊤ : D (k + 1)) = topB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (⊤ : D (k + 1)) j = (⊤ : D (j + 1))
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_top h
  · exact embLe_top (not_le.mp h).le

-- [D-2411] ins_tripointed
theorem ins_tripointed (k : ℕ) :
    phiTowerEP.ins k (⊥ : D (k + 1)) = botB
      ∧ phiTowerEP.ins k (dMid (k + 1)) = midB
      ∧ phiTowerEP.ins k (⊤ : D (k + 1)) = topB :=
  ⟨ins_bot k, ins_mid k, ins_top k⟩

-- [D-2412] §D-is-directed-complete
-- [D-2413] finiteCarrier
noncomputable instance finiteCarrier (k : Nat) : Finite (phiTowerEP.carrier k) :=
  Finite.of_fintype (D (k + 1))

-- [D-2414] phiTowerEP_isDcpo
theorem phiTowerEP_isDcpo : phiTowerEP.IsDcpo where
  carrier_lub := by
    intro k S hne hdir
    obtain ⟨t, htS, htmax⟩ :=
      directedOn_exists_greatest_of_finite (Set.toFinite S) hne hdir
    exact ⟨t, fun s hs => htmax s hs, fun z hz => hz htS⟩
  prj_scott := fun k =>
    monotone_scottContinuous_of_finite_dom (iter k).prj_mono

-- [D-2415] ins_scottContinuous
theorem ins_scottContinuous (k : ℕ) : ScottContinuous (phiTowerEP.ins k) :=
  EpPairTower.ins_scottContinuous_of_finite k

-- [D-2416] proj_scottContinuous
theorem proj_scottContinuous (k : ℕ) :
    ScottContinuous (fun z : B => z.1 k) :=
  EpPairTower.proj_scottContinuous phiTowerEP_isDcpo k

-- [D-2417] §D-is-statable-over-ScottEndP-not-EndP
-- [D-2418] scottContinuous_const
theorem scottContinuous_const (c : B) : ScottContinuous (fun _ : B => c) := by
  intro S hne _ a _
  have himg : (fun _ : B => c) '' S = {c} := by
    ext w
    constructor
    · rintro ⟨y, _, rfl⟩; rfl
    · rintro rfl
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, rfl⟩
  rw [himg]
  exact isLUB_singleton

-- [D-2419] constS
noncomputable def constS (c : B) : ScottEndP B :=
  ⟨⟨fun _ => c, fun _ _ _ => le_refl c⟩, scottContinuous_const c⟩

-- [D-2420] constS_apply
@[simp] theorem constS_apply (c y : B) : (constS c).1 y = c := rfl

-- [D-2421] inst-PartialOrder
noncomputable instance : PartialOrder (ScottEndP B) := Subtype.partialOrder _

-- [D-2422] scottEndP_le_def
theorem scottEndP_le_def {F G : ScottEndP B} : F ≤ G ↔ ∀ y, F.1 y ≤ G.1 y := by
  constructor
  · intro h y; exact (OrderHom.le_def.mp h) y
  · intro h; exact OrderHom.le_def.mpr h

-- [D-2423] inst-OrderBot
noncomputable instance : OrderBot (ScottEndP B) where
  bot := constS botB
  bot_le F := scottEndP_le_def.mpr (fun y => botB_le (F.1 y))

-- [D-2424] inst-OrderTop
noncomputable instance : OrderTop (ScottEndP B) where
  top := constS topB
  le_top F := scottEndP_le_def.mpr (fun y => le_topB (F.1 y))

-- [D-2425] inst-BoundedOrder
noncomputable instance : BoundedOrder (ScottEndP B) := {}

-- [D-2426] decEqScottEndPB
noncomputable instance decEqScottEndPB : DecidableEq (ScottEndP B) := Classical.decEq _

-- [D-2427] markedB
noncomputable def markedB : ScottEndP B := constS midB

-- [D-2428] markedB_ne_bot
theorem markedB_ne_bot : markedB ≠ (⊥ : ScottEndP B) := by
  intro h
  have h1 : (markedB : ScottEndP B).1 botB = (⊥ : ScottEndP B).1 botB := by rw [h]
  exact midB_ne_botB h1

-- [D-2429] markedB_ne_top
theorem markedB_ne_top : markedB ≠ (⊤ : ScottEndP B) := by
  intro h
  have h1 : (markedB : ScottEndP B).1 botB = (⊤ : ScottEndP B).1 botB := by rw [h]
  exact midB_ne_topB h1

-- [D-2430] endPB_bot_ne_top
theorem endPB_bot_ne_top : (⊥ : ScottEndP B) ≠ (⊤ : ScottEndP B) := by
  intro h
  have h1 : (⊥ : ScottEndP B).1 botB = (⊤ : ScottEndP B).1 botB := by rw [h]
  exact botB_ne_topB h1

-- [D-2431] phiB
abbrev phiB : Type := GlueCarGen (P := ScottEndP B) markedB

-- [D-2432] inst-PartialOrder
noncomputable instance : PartialOrder phiB :=
  glueCarPartialOrderGen markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top

end PhiBilimit
