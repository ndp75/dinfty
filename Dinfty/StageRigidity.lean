import Dinfty.CopyIdeal

open GluingTowerLibrary SierpinskiApplication

/-!
# Does Theorem B's rigidity survive from the copy-`A` ideal to the whole?

§106 left this as the live question.  The answer has three parts.

## 1.  Not by restriction — the ideal is not sup-dense

`CopyIdeal` showed the legacy tower is confined, level by level, to copy `A`, a
proper down-set.  The temptation is to say "θ is the identity on the ideal by
Theorem B, and the ideal generates".  It does not generate: copy `A` never
contains the top (`glueA_ne_top`), while **every** embedding of the `Φ`-tower
sends `⊤` to `⊤` — that is a `TriEP` field, `emb_top`, holding at every level,
not just at `glueAA 0`.  `phi_emb_top_not_legacy` below states the consequence:
the `Φ`-tower's stage image is never inside the legacy stage image, at `⊤`
already.  So knowing an automorphism of `B` is the identity on the copy-`A` part
constrains nothing above it.

(A correction to §106 while we are here: `legacy_confined_phi_not` is stated
with `glueAA k`, and `glueAA k` is the tower's embedding **only at `k = 0`** —
`iter 0 = baseEP` has `emb := glueAA 0`, but `iter (n+1)`'s embedding is `Φ` of
the previous one, and `glueAA (k+1)` is not `Φ (glueAA k)` (round 52).  The
statement below is the one that holds at every level, and it goes through
`emb_top` rather than through `glueAA`.)

## 2.  But rigidity does survive — by re-running pillar B's architecture

Pillar B's assembly is
`StageDefinable ⟹ every automorphism is the identity`
(`Assembly.eq_refl_of_stageDefinable`), and it uses exactly two things: the
stages are order-embedded copies of the finite levels, and every element is
reachable from the stages.  For `DInfty` "reachable" is `Quotient.inductionOn` —
a colimit is *literally* the union of its stages.  A bilimit is not, so that step
is unavailable verbatim.

It is available in the form that matters.  `EpPairTower.chainSet_isLUB` says
every bilimit point is the supremum of its own stage approximants, and an order
isomorphism preserves suprema.  So:

```lean
StageRigidity.rigid_of_stageDefinable :
  LevelsMaximallyRigid T → StageDefinable T → Subsingleton (T.Bilim ≃o T.Bilim)
```

holds for **any** ep-pair tower, and `LevelsMaximallyRigid phiTowerEP` is free:
the levels are the same `D k`, and `TowerRigidity.D_monotone_injection_eq_id`
already says every monotone injection of one is the identity.  Instantiating:

```lean
PhiRigidity.B_rigid_of_stageDefinable : PhiStageDefinable → Subsingleton (B ≃o B)
```

So Theorem A's carrier is rigid the moment its stages are order-definable, and
the whole of pillar B's *abstract* half transfers with no hypothesis at all.
The same statement for the legacy bilimit drops out of the same abstract lemma
(`legacyStageDefinable_gives_rigid`), so the two pillars now stand on one
reduction rather than two.

## 3.  What does **not** transfer: the one open `Prop`

`PhiStageDefinable` is not `Assembly.StageDefinable`, and pillar B's proof of
the latter does not supply it.  Pillar B reached it through `FirstSlice n`,
whose statement is *"no **non-copy-`A`** join-irreducible of `D (n+1)` carries
the seed of a stage-`n` point"* — copy `A` there is exactly the legacy stage's
copy, so "non-copy-`A`" is exactly "new at this level".  For the `Φ`-tower the
stage image is tripointed, hence meets all three copies (part 1), so
"non-copy-`A`" is no longer "new" and `FirstSlice`'s case split does not match
the question.  The seed comparison would have to be redone against
`Set.range (T.emb n)` instead of against copy `A`.

That is the residue, and it is a *level-local* statement about `D (n+1)`,
`D (n+2)` and seeds — the same kind of object `FirstSliceCHigh` is, not a new
kind of problem.
-/

open scoped Classical

open Set

universe u

namespace StageRigidity

open EpPairTower

variable {T : EpPairTower}

/-! ## 1.  The stage maps are order-embeddings -/

theorem ins_le_iff (k : ℕ) (w w' : T.carrier k) : T.ins k w ≤ T.ins k w' ↔ w ≤ w' := by
  constructor
  · intro h
    have hk := h k
    rwa [ins_self k w, ins_self k w'] at hk
  · exact fun h => ins_monotone k h

/-- **`ins k` is a left adjoint to reading off level `k`.**  One line each way,
and it is the engine of `PhiStagePipe`: it turns any question about a stage point
and an arbitrary bilimit point into a question inside the *finite* level `k`. -/
theorem ins_le_iff' (k : ℕ) (a : T.carrier k) (u : T.Bilim) :
    T.ins k a ≤ u ↔ a ≤ u.1 k := by
  constructor
  · intro h
    have hk := h k
    rwa [ins_self k a] at hk
  · intro h
    exact (ins_monotone k h).trans (ins_le_self u k)

theorem ins_injective (k : ℕ) : Function.Injective (T.ins k) := fun w w' h =>
  le_antisymm ((ins_le_iff k w w').mp h.le) ((ins_le_iff k w' w).mp h.ge)

/-! ## 2.  The two hypotheses -/

/-- Every order-automorphism of the bilimit carries each stage into itself —
`Assembly.StageDefinable`, stated for an arbitrary ep-pair tower's bilimit
instead of for the colimit `DInfty`. -/
def StageDefinable (T : EpPairTower) : Prop :=
  ∀ (θ : T.Bilim ≃o T.Bilim) (k : ℕ) (x : T.carrier k),
    ∃ y : T.carrier k, θ (T.ins k x) = T.ins k y

/-- Every monotone injection of a level is the identity — strictly stronger than
rigidity of the levels, and what the argument actually consumes. -/
def LevelsMaximallyRigid (T : EpPairTower) : Prop :=
  ∀ (k : ℕ) (f : T.carrier k → T.carrier k), Monotone f → Function.Injective f → f = id

/-! ## 3.  The transport

`Assembly.eq_refl_of_stageDefinable`, with `Quotient.inductionOn` replaced by
`chainSet_isLUB`.  A colimit *is* the union of its stages; a bilimit is only the
directed supremum of them, and that is enough, because an order isomorphism
preserves suprema. -/

/-- On each stage, `θ` restricts to a monotone injection of a level, hence to
the identity. -/
theorem eq_on_stages (hr : LevelsMaximallyRigid T) (hs : StageDefinable T)
    (θ : T.Bilim ≃o T.Bilim) (k : ℕ) (x : T.carrier k) : θ (T.ins k x) = T.ins k x := by
  choose f hf using hs θ k
  have hmono : Monotone f := by
    intro a b hab
    have h2 : θ (T.ins k a) ≤ θ (T.ins k b) := θ.monotone ((ins_le_iff k a b).mpr hab)
    rw [hf a, hf b] at h2
    exact (ins_le_iff k (f a) (f b)).mp h2
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : θ (T.ins k a) = θ (T.ins k b) := by rw [hf a, hf b, hab]
    exact ins_injective k (θ.injective h1)
  have hid : f = id := hr k f hmono hinj
  rw [hf x, congrFun hid x]
  rfl

/-- **The unconditional half.**  An order-automorphism of a bilimit is
determined by its action on the stages — no hypothesis at all.  This is where a
bilimit replaces a colimit: `DInfty` *is* the union of its stages
(`Quotient.inductionOn`), while `T.Bilim` is only their directed supremum
(`chainSet_isLUB`), and an order isomorphism preserves suprema. -/
theorem eq_refl_of_fixes_stages (θ : T.Bilim ≃o T.Bilim)
    (key : ∀ (k : ℕ) (x : T.carrier k), θ (T.ins k x) = T.ins k x) :
    θ = OrderIso.refl T.Bilim := by
  refine RelIso.ext (fun z => ?_)
  have h1 : IsLUB (T.chainSet z) z := chainSet_isLUB z
  have h2 : IsLUB (θ '' T.chainSet z) (θ z) := (OrderIso.isLUB_image' θ).mpr h1
  have h3 : θ '' T.chainSet z = T.chainSet z := by
    ext u
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (key n (z.1 n)).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨T.ins n (z.1 n), ⟨n, rfl⟩, key n (z.1 n)⟩
  rw [h3] at h2
  exact h2.unique h1

/-- **The transport.**  Stage-definability forces every order-automorphism of the
bilimit to be the identity. -/
theorem eq_refl_of_stageDefinable (hr : LevelsMaximallyRigid T) (hs : StageDefinable T)
    (θ : T.Bilim ≃o T.Bilim) : θ = OrderIso.refl T.Bilim :=
  eq_refl_of_fixes_stages θ (eq_on_stages hr hs θ)

theorem rigid_of_stageDefinable (hr : LevelsMaximallyRigid T) (hs : StageDefinable T) :
    Subsingleton (T.Bilim ≃o T.Bilim) :=
  ⟨fun a b => (eq_refl_of_stageDefinable hr hs a).trans
    (eq_refl_of_stageDefinable hr hs b).symm⟩

end StageRigidity

/-! ## 4.  At the `Φ`-tower -/

namespace PhiRigidity

open PhiIterateTower PhiBilimit EpPairTower StageRigidity

/-- **The residue**: every order-automorphism of `B` carries each stage into
itself.  This is the `Φ`-tower's analogue of `Assembly.StageDefinable`, and it
is *not* implied by it — see §3 of the module docstring. -/
def PhiStageDefinable : Prop := StageDefinable phiTowerEP

/-- Free: the `Φ`-tower's levels are the same `D k`, which admit no nontrivial
monotone self-injection at all. -/
theorem levels_maximally_rigid : LevelsMaximallyRigid phiTowerEP :=
  fun k f hmono hinj => TowerRigidity.D_monotone_injection_eq_id (k + 1) hmono hinj

/-- **Theorem A's carrier is rigid as soon as its stages are definable.**  The
whole abstract half of pillar B transfers; only the stage-definability `Prop` is
tower-specific. -/
theorem B_rigid_of_stageDefinable (h : PhiStageDefinable) : Subsingleton (B ≃o B) :=
  rigid_of_stageDefinable levels_maximally_rigid h

/-- Every automorphism of `B` is already pinned on the stages, given the
residue. -/
theorem eq_id_of_stageDefinable (h : PhiStageDefinable) (θ : B ≃o B) :
    θ = OrderIso.refl B :=
  eq_refl_of_stageDefinable levels_maximally_rigid h θ

/-! ### Why restriction to the copy-`A` ideal cannot be the route

The legacy tower and the `Φ`-tower do agree where §106 said they do — on copy
`A`, `glueAA k ∘ iotaD k = iotaD (k+1) ∘ iotaD k` — so the legacy tower is a
subtower.  But the `Φ`-tower's embeddings preserve `⊤` at every level, and the
legacy ones never reach it, so the `Φ`-stage is never contained in the legacy
stage. -/

/-- The legacy tower sits inside the `Φ`-tower: `glueAA_iotaD`, named as the
commuting square of a tower morphism. -/
theorem legacy_subtower (k : ℕ) (x : D k) :
    glueAA k (iotaD k x) = iotaD (k + 1) (iotaD k x) := glueAA_iotaD k x

/-- **…and it is a proper subtower, at `⊤`, at every level.**  Unlike
`CopyIdeal.legacy_confined_phi_not`, this is about the tower's actual embedding
`(iter n).emb`, which is `glueAA n` only for `n = 0`. -/
theorem phi_emb_top_not_legacy (n : ℕ) (x : D (n + 1)) :
    (iter n).emb (⊤ : D (n + 1)) ≠ iotaD (n + 1) x := by
  rw [(iter n).emb_top]
  exact fun hc => iotaD_ne_top (n + 1) x hc.symm

/-- The same fact at the bilimit: `topB` is in every stage, and no stage point
of the legacy kind is above it. -/
theorem ins_top (n : ℕ) : phiTowerEP.ins n (⊤ : D (n + 1)) = topB :=
  PhiBilimit.ins_top n

/-! ### The two pillars now rest on one reduction -/

/-- Both pillars, one shape: rigidity of a bilimit follows from
stage-definability plus level rigidity, and the levels are free in both cases.
For the legacy side the conclusion is already a theorem
(`CopyCHigh.DBilimit_rigid`); this records that it is an instance of the same
lemma, so what separates the pillars is exactly the stage-definability `Prop`. -/
theorem pillars_share_one_reduction :
    (PhiStageDefinable → Subsingleton (B ≃o B))
      ∧ Subsingleton (DBilimit ≃o DBilimit) :=
  ⟨B_rigid_of_stageDefinable, CopyCHigh.DBilimit_rigid⟩

end PhiRigidity
