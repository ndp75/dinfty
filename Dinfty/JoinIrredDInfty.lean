import Dinfty.ColimitCompatPipe

open GluingTowerLibrary SierpinskiApplication

/-!
# The `DInfty`-level half of clause (3b), and the residue with no join-irreducibility left in it

`Dinfty/AssemblyChain.lean` names, as missing, "`sig3`'s components shown
order-invariant *as computed in `DInfty`*, which is where `JoinIrredLevelStable`
and the missing `DInfty`-level half of clause (3b) enter."

This module supplies that half:

    joinIrred_toD_iff :  JoinIrred DInfty (toD k x)  ↔  JoinIrred (D k) x

It needed one thing that did not exist: an `OrderBot` on `DInfty`, so that
`JoinIrred DInfty` is even a statement. `ColimitCompatPipe.toD_bot_le` supplies
it — `DInfty` has a least element, it simply carried no instance.

## What it buys

Join-irreducibility is an order-theoretic property, so any `θ : DInfty ≃o DInfty`
preserves it (`joinIrred_orderIso`). Combined with `joinIrred_toD_iff`, the
`JoinIrred (D k) y` half of `JoinIrredStagePreserved` becomes **automatic**: if
`θ (toD k x) = toD k y` and `x` is join-irreducible, then so is `y`.

So the residue drops to `StageFixed` below, which says only

    θ does not move a stage-`k` join-irreducible off stage `k`

with no join-irreducibility left in its conclusion. `colimit_compat` follows
from that alone (`colimit_compat_of_stageFixed`).

**This does not close pillar B.** `StageFixed` is a pure *level* statement and
it is still open. What changed is that the remaining question no longer has two
things tangled in it: the join-irreducibility bookkeeping is discharged, and
what is left is exactly "can an automorphism raise a join-irreducible's level".

## Why the obvious attacks on `StageFixed` do not apply, recorded so they are not retried

* **Rank / down-set counting is unavailable.** `DInfty` down-sets are not
  locally finite (handoff; and `iotaD` does not preserve atoms — `iotaD k a` is
  `glueA m (constHom a)`, while `EndP (D k)`'s atom is the spike at `⊤`, which
  is strictly smaller — so `DInfty` has no atoms at all to induct from).
* **Counting join-irreducibles below a point does not help either**, for the
  same reason: `{w ∈ J∞ : w ≤ toD k x}` picks up new join-irreducibles at every
  level, since `joinIrred_iotaLe_iff` only classifies those *in the image* of
  `iotaLe`.
* **Cross-level embedding rigidity is false** — 1248 three-chains in the real
  `D_1` against one canonical (`_archive/check_normalized_pillarB_numerics.py`),
  so a monotone injection `D k → D N` need not be `iotaLe`.
-/

open scoped Classical

namespace JoinIrredDInfty

open ColimitCompatPipe Assembly AssemblyChain JoinIrredLevelStable

/-- **`DInfty` has a least element.**  It carried no instance; `toD_bot_le`
proves the content, so the instance is just packaging.  There is no competing
`Bot DInfty`, so this introduces no diamond. -/
noncomputable instance : OrderBot DInfty where
  bot := toD 0 (⊥ : D 0)
  bot_le := toD_bot_le 0

theorem bot_eq_toD (k : ℕ) : (⊥ : DInfty) = toD k (⊥ : D k) :=
  le_antisymm (bot_le) (toD_bot_le k _)

theorem toD_eq_bot_iff (k : ℕ) (x : D k) : toD k x = (⊥ : DInfty) ↔ x = (⊥ : D k) := by
  rw [bot_eq_toD k]
  exact ⟨fun h => toD_inj k h, fun h => by rw [h]⟩

/-! ## Order isomorphisms preserve join-irreducibility

`joinIrred_orderIso` was **already in the library** (`GluingTowerLibrary.lean:6526`,
general `L ≃o M`).  A version was briefly re-proved here before that was noticed;
it has been removed and the library lemma is used instead.  Tenth instance in
this project of a result that already existed — and the first where the
duplication was mine. -/

/-! ## The `DInfty`-level characterization -/

/-- **The missing half of clause (3b).**  Join-irreducibility in the colimit is
join-irreducibility at the stage — in both directions, at every level.

Forward: a stage-level factorization transports up by `toD_sup'`.  Backward: any
`DInfty` factorization chases to a common level `N`, where `joinIrred_iotaLe_iff`
(`JoinIrredLevelStable.lean`) says `iotaLe x` is join-irreducible exactly when
`x` is. -/
theorem joinIrred_toD_iff (k : ℕ) (x : D k) :
    JoinIrred DInfty (toD k x) ↔ JoinIrred (D k) x := by
  constructor
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hx => hne ((toD_eq_bot_iff k x).mpr hx), ?_⟩
    intro b c hbc
    have h' : toD k x = toD k b ⊔ toD k c := by rw [toD_sup', ← hbc]
    rcases hsplit _ _ h' with hh | hh
    · left; exact toD_inj k hh
    · right; exact toD_inj k hh
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hb => hne ((toD_eq_bot_iff k x).mp hb), ?_⟩
    intro b c hbc
    induction b using Quotient.inductionOn with
    | _ pb =>
      induction c using Quotient.inductionOn with
      | _ pc =>
        obtain ⟨p, u⟩ := pb
        obtain ⟨q, v⟩ := pc
        set N := max k (max p q) with hN
        have hkN : k ≤ N := le_max_left _ _
        have hpN : p ≤ N := le_trans (le_max_left p q) (le_max_right k _)
        have hqN : q ≤ N := le_trans (le_max_right p q) (le_max_right k _)
        have hx : toD k x = toD N (iotaLe hkN x) := (toD_iotaLe hkN x).symm
        have hu : toD p u = toD N (iotaLe hpN u) := (toD_iotaLe hpN u).symm
        have hv : toD q v = toD N (iotaLe hqN v) := (toD_iotaLe hqN v).symm
        have hjoin : toD N (iotaLe hkN x)
            = toD N (iotaLe hpN u ⊔ iotaLe hqN v) := by
          rw [← toD_sup', ← hu, ← hv, ← hx]; exact hbc
        have heq : iotaLe hkN x = iotaLe hpN u ⊔ iotaLe hqN v := toD_inj N hjoin
        have hji : JoinIrred (D N) (iotaLe hkN x) :=
          (joinIrred_iotaLe_iff hkN x).mpr ⟨hne, hsplit⟩
        rcases hji.2 _ _ heq with hh | hh
        · left
          show toD k x = toD p u
          rw [hx, hu, hh]
        · right
          show toD k x = toD q v
          rw [hx, hv, hh]

/-! ## The residue, with the join-irreducibility bookkeeping removed -/

/-- **What is actually left of pillar B.**  An automorphism of `DInfty` does not
move a stage-`k` join-irreducible off stage `k`.

Compare `AssemblyChain.JoinIrredStagePreserved`, which also demanded the image
be join-irreducible *in that stage*; `joinIrred_toD_iff` makes that automatic,
so this is the whole of the remaining content. -/
def StageFixed : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), JoinIrred (D k) x →
    ∃ y : D k, θ (toD k x) = toD k y

theorem joinIrredStagePreserved_of_stageFixed (h : StageFixed) :
    JoinIrredStagePreserved := by
  intro θ k x hx
  obtain ⟨y, hy⟩ := h θ k x hx
  refine ⟨y, ?_, hy⟩
  have h1 : JoinIrred DInfty (toD k x) := (joinIrred_toD_iff k x).mpr hx
  have h2 : JoinIrred DInfty (toD k y) := by
    rw [← hy]; exact GluingTowerLibrary.joinIrred_orderIso θ h1
  exact (joinIrred_toD_iff k y).mp h2

/-! ## `colimit_compat` from the tightened residue -/

theorem colimit_rigid_of_stageFixed (h : StageFixed) :
    Subsingleton (DInfty ≃o DInfty) :=
  colimit_rigid_of_joinIrredStagePreserved (joinIrredStagePreserved_of_stageFixed h)

theorem colimit_compat_of_stageFixed (h : StageFixed) :
    Subsingleton (DInfty ≃o DInfty) ↔ ∀ k, Subsingleton (D k ≃o D k) :=
  colimit_compat_of_joinIrredStagePreserved (joinIrredStagePreserved_of_stageFixed h)

theorem DBilimit_rigid_of_stageFixed (h : StageFixed) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_joinIrredStagePreserved' (joinIrredStagePreserved_of_stageFixed h)

end JoinIrredDInfty
