import Dinfty.SeedLevelStep
import Dinfty.SeedSeparation

open GluingTowerLibrary SierpinskiApplication

/-!
# `JBelow z` is the increasing union of the level-wise seeds

`ChainUnion` needs both sides of the shape identification presented as
increasing unions.  This module does the `DInfty` side: for a join-irreducible
`z = toD N y`,

```lean
jBelowPres : ChainUnion.Pres (JBelow z) (fun k => LevelSeed (N + k) (yAt k))
```

where `yAt k = iotaLe y` is `y` pushed to level `N + k`.  The three obligations
are exactly the tower's own facts:

* `incl_le_iff` — `toD_le_iff'`, the colimit maps are order-embeddings;
* `incl_step` — `toD_iotaLe`, the chain is coherent;
* `incl_surj` — `SeedSeparation.exists_stage`, every element of `DInfty` lives
  at some level, together with `joinIrred_toD_iff` to carry join-irreducibility
  down and `toD_le_iff'` to carry `≤ z` down.

Nothing here is new mathematics; it is the statement that the colimit really is
a union, in the form `ChainUnion` consumes.
-/

open scoped Classical

namespace SeedChain

open SeedLevelStep SeedSeparation ChainUnion JoinIrredLevelStable JoinIrredDInfty

variable (N : ℕ) (y : D N) (hy : JoinIrred (D N) y)

/-- `y` pushed up to level `N + k`.  Defined by recursion rather than through
`iotaLe`, so that `yAt (k+1) = iotaD (N+k) (yAt k)` holds **definitionally** —
which is what lets `levelStepIso` be applied without transporting types. -/
noncomputable def yAt : ∀ k : ℕ, D (N + k)
  | 0 => y
  | k + 1 => iotaD (N + k) (yAt k)

@[simp] theorem yAt_zero : yAt N y 0 = y := rfl

@[simp] theorem yAt_succ (k : ℕ) : yAt N y (k + 1) = iotaD (N + k) (yAt N y k) := rfl

theorem toD_yAt (k : ℕ) : toD (N + k) (yAt N y k) = toD N y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show toD (N + k + 1) (iotaD (N + k) (yAt N y k)) = toD N y
      have h := toD_iotaLe (Nat.le_succ (N + k)) (yAt N y k)
      rw [iotaLe_succ (le_refl (N + k)) (Nat.le_succ (N + k)) (yAt N y k),
          iotaLe_self (le_refl (N + k)) (yAt N y k)] at h
      exact h.trans ih

/-- `yAt` stays join-irreducible. -/
theorem joinIrred_yAt (hy : JoinIrred (D N) y) (k : ℕ) :
    JoinIrred (D (N + k)) (yAt N y k) := by
  induction k with
  | zero => exact hy
  | succ k ih => exact (joinIrred_iotaD_iff (N + k) (yAt N y k)).mpr ih

/-! ## The chain -/

/-- The level-`(N+k)` seed of `z`. -/
abbrev SeedAt (k : ℕ) : Type := LevelSeed (N + k) (yAt N y k)

/-- One step of the chain: the tower's own embedding. -/
noncomputable def seedStep (k : ℕ) (u : SeedAt N y k) : SeedAt N y (k + 1) :=
  ⟨iotaD (N + k) u.1,
   (joinIrred_iotaD_iff (N + k) u.1).mpr u.2.1,
   (iotaD_le_iff (N + k) u.1 (yAt N y k)).mpr u.2.2⟩

/-- The inclusion of a level into `JBelow z`. -/
noncomputable def seedIncl (k : ℕ) (u : SeedAt N y k) : JBelow (toD N y) :=
  ⟨toD (N + k) u.1,
   (joinIrred_toD_iff (N + k) u.1).mpr u.2.1,
   by
     have h : toD (N + k) u.1 ≤ toD (N + k) (yAt N y k) :=
       (toD_le_iff' (N + k) u.1 (yAt N y k)).mpr u.2.2
     rwa [toD_yAt N y k] at h⟩

theorem seedIncl_le_iff (k : ℕ) (a b : SeedAt N y k) :
    seedIncl N y k a ≤ seedIncl N y k b ↔ a ≤ b :=
  toD_le_iff' (N + k) a.1 b.1

theorem seedIncl_step (k : ℕ) (u : SeedAt N y k) :
    seedIncl N y (k + 1) (seedStep N y k u) = seedIncl N y k u := by
  apply Subtype.ext
  show toD (N + k + 1) (iotaD (N + k) u.1) = toD (N + k) u.1
  have h := toD_iotaLe (Nat.le_succ (N + k)) u.1
  rwa [iotaLe_succ (le_refl (N + k)) (Nat.le_succ (N + k)) u.1,
       iotaLe_self (le_refl (N + k)) u.1] at h

theorem seedIncl_surj (w : JBelow (toD N y)) :
    ∃ (k : ℕ) (u : SeedAt N y k), seedIncl N y k u = w := by
  obtain ⟨M, x, hx⟩ := exists_stage w.1
  refine ⟨M, ⟨iotaLe (Nat.le_add_left M N) x, ?_, ?_⟩, ?_⟩
  · refine (joinIrred_toD_iff (N + M) _).mp ?_
    rw [toD_iotaLe (Nat.le_add_left M N) x, ← hx]
    exact w.2.1
  · refine (toD_le_iff' (N + M) _ (yAt N y M)).mp ?_
    rw [toD_iotaLe (Nat.le_add_left M N) x, toD_yAt N y M, ← hx]
    exact w.2.2
  · apply Subtype.ext
    show toD (N + M) (iotaLe (Nat.le_add_left M N) x) = w.1
    rw [toD_iotaLe (Nat.le_add_left M N) x, ← hx]

/-- **`JBelow z` is the increasing union of the level-wise seeds.** -/
noncomputable def jBelowPres : Pres (JBelow (toD N y)) (SeedAt N y) where
  step := seedStep N y
  incl := seedIncl N y
  incl_le_iff := seedIncl_le_iff N y
  incl_step := seedIncl_step N y
  incl_surj := seedIncl_surj N y

end SeedChain
