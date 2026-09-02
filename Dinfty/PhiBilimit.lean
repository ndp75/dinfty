import Dinfty.PhiIterateTower
import Dinfty.RealEpPairTower

open GluingTowerLibrary SierpinskiApplication

/-!
# `D∞^Φ` — the Φ-iterate tower's bilimit, and `Φ` of it

§84 built the tower whose embeddings are `Φ` of one another.  This module gives
its bilimit the structure `Φ` needs, so that **`Φ(D∞^Φ)` is a statable object**
and Theorem A becomes a comparison between two things that both exist.

## What assembles, and why

Every level map of the tower is tripointed (`emb_tripointed`), and the
projections inherit it from the retraction, so the three points survive the
inverse limit:

```lean
botB, midB, topB : phiTowerEP.Bilim
```

with `BoundedOrder` and `midB` strictly between.  That is *not* automatic — it
is exactly what fails for the constant-embedding tower, whose `iotaD` misses
`⊤`.

The staging maps inherit it too: `embLe`/`prjLe` preserve all three by induction
along the tower, hence so does `ins`:

```lean
ins_bot, ins_mid, ins_top : phiTowerEP.ins k ⊥/dMid (k+1)/⊤ = botB/midB/topB
```

`ins k` being tripointed is what will make `End (ins k, proj k)` tripointed, and
therefore `Φ (ins k)` exist — the cocone legs the bilimit argument needs.

## `Φ(D∞^Φ)`

`EndP B` needs only a `PartialOrder` and bounds on `B`, not a lattice, so it has
both; `markedB := constHom midB` is nondegenerate; and `phiB` is
`GlueCarGen (EndP B) markedB` with the glue order.  Nothing here claims it is
isomorphic to `B` — that is the analysis, and it is the next step.
-/

open scoped Classical

namespace PhiBilimit

open PhiIterateTower EpPairTower

/-- The Φ-iterate tower's bilimit: `D∞^Φ`. -/
abbrev B : Type := phiTowerEP.Bilim

/-! ## The three points assemble -/

noncomputable def botB : B := ⟨fun n => (⊥ : D (n + 1)), fun n => (iter n).prj_bot⟩

noncomputable def midB : B := ⟨fun n => dMid (n + 1), fun n => (iter n).prj_mid⟩

noncomputable def topB : B := ⟨fun n => (⊤ : D (n + 1)), fun n => (iter n).prj_top⟩

@[simp] theorem midB_apply (n : ℕ) : (midB.1 n : D (n + 1)) = dMid (n + 1) := rfl

theorem botB_le (y : B) : botB ≤ y := by
  intro n
  show (⊥ : D (n + 1)) ≤ y.1 n
  exact bot_le

theorem le_topB (y : B) : y ≤ topB := by
  intro n
  exact @le_top (D (n + 1)) _ _ (y.1 n)

noncomputable instance : OrderBot B where
  bot := botB
  bot_le := botB_le

noncomputable instance : OrderTop B where
  top := topB
  le_top := le_topB

noncomputable instance : BoundedOrder B := {}

theorem midB_ne_botB : midB ≠ botB := by
  intro h
  have h1 : (dMid 1 : D 1) = (⊥ : D 1) := congrArg (fun z : B => z.1 0) h
  exact dMid_ne_bot 1 h1

theorem midB_ne_topB : midB ≠ topB := by
  intro h
  have h1 : (dMid 1 : D 1) = (⊤ : D 1) := congrArg (fun z : B => z.1 0) h
  exact dMid_ne_top 1 h1

theorem botB_ne_topB : botB ≠ topB := by
  intro h
  have h1 : (⊥ : D 1) = (⊤ : D 1) := congrArg (fun z : B => z.1 0) h
  exact bot_ne_top_of_nontrivial h1

/-! ## The staging maps are tripointed -/

theorem embLe_bot {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (⊥ : D (k + 1)) = (⊥ : D (n + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_bot

theorem embLe_mid {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (dMid (k + 1)) = dMid (n + 1) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_mid

theorem embLe_top {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n),
    phiTowerEP.embLe h (⊤ : D (k + 1)) = (⊤ : D (n + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact embLe_self _ _
  | succ n hn ih =>
      rw [embLe_succ hn (Nat.le_succ_of_le hn), ih]
      exact (iter n).emb_top

theorem prjLe_bot {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (⊥ : D (n + 1)) = (⊥ : D (j + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (⊥ : D (n + 2))) = _
      rw [(iter n).prj_bot, ih]

theorem prjLe_mid {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (dMid (n + 1)) = dMid (j + 1) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (dMid (n + 2))) = _
      rw [(iter n).prj_mid, ih]

theorem prjLe_top {j : ℕ} : ∀ {n : ℕ} (h : j ≤ n),
    phiTowerEP.prjLe h (⊤ : D (n + 1)) = (⊤ : D (j + 1)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self _ _ _
  | succ n hn ih =>
      rw [prjLe_succ hn (Nat.le_succ_of_le hn)]
      show phiTowerEP.prjLe hn ((iter n).prj (⊤ : D (n + 2))) = _
      rw [(iter n).prj_top, ih]

/-! ## …hence so is `ins` -/

theorem ins_bot (k : ℕ) : phiTowerEP.ins k (⊥ : D (k + 1)) = botB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (⊥ : D (k + 1)) j = (⊥ : D (j + 1))
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_bot h
  · exact embLe_bot (not_le.mp h).le

theorem ins_mid (k : ℕ) : phiTowerEP.ins k (dMid (k + 1)) = midB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (dMid (k + 1)) j = dMid (j + 1)
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_mid h
  · exact embLe_mid (not_le.mp h).le

theorem ins_top (k : ℕ) : phiTowerEP.ins k (⊤ : D (k + 1)) = topB := by
  refine Subtype.ext (funext (fun j => ?_))
  show phiTowerEP.seqOf k (⊤ : D (k + 1)) j = (⊤ : D (j + 1))
  unfold EpPairTower.seqOf
  split_ifs with h
  · exact prjLe_top h
  · exact embLe_top (not_le.mp h).le

/-- **The colimit cocone's legs are tripointed.**  This is what will make
`End (ins k, proj k)` tripointed, and therefore `Φ (ins k)` exist. -/
theorem ins_tripointed (k : ℕ) :
    phiTowerEP.ins k (⊥ : D (k + 1)) = botB
      ∧ phiTowerEP.ins k (dMid (k + 1)) = midB
      ∧ phiTowerEP.ins k (⊤ : D (k + 1)) = topB :=
  ⟨ins_bot k, ins_mid k, ins_top k⟩

/-! ## `D∞^Φ` is directed-complete

Both fields come from finiteness of the *levels*, never of `B` — the same place
`RealEpPairTower.realTower_isDcpo` spends it. -/

/-- Stated at the  spelling, since instance search does not unfold
. -/
noncomputable instance finiteCarrier (k : Nat) : Finite (phiTowerEP.carrier k) :=
  Finite.of_fintype (D (k + 1))

theorem phiTowerEP_isDcpo : phiTowerEP.IsDcpo where
  carrier_lub := by
    intro k S hne hdir
    obtain ⟨t, htS, htmax⟩ :=
      directedOn_exists_greatest_of_finite (Set.toFinite S) hne hdir
    exact ⟨t, fun s hs => htmax s hs, fun z hz => hz htS⟩
  prj_scott := fun k =>
    monotone_scottContinuous_of_finite_dom (iter k).prj_mono

theorem ins_scottContinuous (k : ℕ) : ScottContinuous (phiTowerEP.ins k) :=
  EpPairTower.ins_scottContinuous_of_finite k

theorem proj_scottContinuous (k : ℕ) :
    ScottContinuous (fun z : B => z.1 k) :=
  EpPairTower.proj_scottContinuous phiTowerEP_isDcpo k

/-! ## `Φ(D∞^Φ)` is statable — over `ScottEndP`, not `EndP`

§89: building the Ψ-target on `EndP B` makes `PhiCoconeIsLUB` **false**, because
`⨆ₖ δₖ ∘ H ∘ δₖ = H` needs `H` to preserve the supremum `⨆ₖ δₖ y = y`.  At the
finite levels the distinction is invisible — a monotone map on a finite poset is
Scott-continuous — which is why `D (k+1)` is built on `EndP`.  At the limit it is
not, and `SierpinskiApplication`'s own Ψ-target
(`GlueCarGen (ScottEndP DBilimit) scottEndPId`) already had this right. -/

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

/-- The constant endomorphism, as a Scott-continuous one. -/
noncomputable def constS (c : B) : ScottEndP B :=
  ⟨⟨fun _ => c, fun _ _ _ => le_refl c⟩, scottContinuous_const c⟩

@[simp] theorem constS_apply (c y : B) : (constS c).1 y = c := rfl

noncomputable instance : PartialOrder (ScottEndP B) := Subtype.partialOrder _

theorem scottEndP_le_def {F G : ScottEndP B} : F ≤ G ↔ ∀ y, F.1 y ≤ G.1 y := by
  constructor
  · intro h y; exact (OrderHom.le_def.mp h) y
  · intro h; exact OrderHom.le_def.mpr h

noncomputable instance : OrderBot (ScottEndP B) where
  bot := constS botB
  bot_le F := scottEndP_le_def.mpr (fun y => botB_le (F.1 y))

noncomputable instance : OrderTop (ScottEndP B) where
  top := constS topB
  le_top F := scottEndP_le_def.mpr (fun y => le_topB (F.1 y))

noncomputable instance : BoundedOrder (ScottEndP B) := {}

/-- **The one `DecidableEq (ScottEndP B)`.**  Named, so every downstream file
resolves to *this* instance (§86: the carrier does not depend on the choice, but
the elaborator's `synthesized = inferred` check does). -/
noncomputable instance decEqScottEndPB : DecidableEq (ScottEndP B) := Classical.decEq _

/-- The marked point of `D∞^Φ`, as a Scott-continuous endomorphism. -/
noncomputable def markedB : ScottEndP B := constS midB

theorem markedB_ne_bot : markedB ≠ (⊥ : ScottEndP B) := by
  intro h
  have h1 : (markedB : ScottEndP B).1 botB = (⊥ : ScottEndP B).1 botB := by rw [h]
  exact midB_ne_botB h1

theorem markedB_ne_top : markedB ≠ (⊤ : ScottEndP B) := by
  intro h
  have h1 : (markedB : ScottEndP B).1 botB = (⊤ : ScottEndP B).1 botB := by rw [h]
  exact midB_ne_topB h1

theorem endPB_bot_ne_top : (⊥ : ScottEndP B) ≠ (⊤ : ScottEndP B) := by
  intro h
  have h1 : (⊥ : ScottEndP B).1 botB = (⊤ : ScottEndP B).1 botB := by rw [h]
  exact botB_ne_topB h1

/-- **`Φ(D∞^Φ)`**, on the carrier the limit actually needs. -/
abbrev phiB : Type := GlueCarGen (P := ScottEndP B) markedB

noncomputable instance : PartialOrder phiB :=
  glueCarPartialOrderGen markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top

end PhiBilimit
