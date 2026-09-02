import Dinfty.SeedLevelStep
import Dinfty.SeedSeparation

open GluingTowerLibrary SierpinskiApplication

-- [D-1749] §JBelow-z-is-the-increasing-union-of-the-level
open scoped Classical

namespace SeedChain

open SeedLevelStep SeedSeparation ChainUnion JoinIrredLevelStable JoinIrredDInfty

variable (N : ℕ) (y : D N) (hy : JoinIrred (D N) y)

-- [D-1750] yAt
noncomputable def yAt : ∀ k : ℕ, D (N + k)
  | 0 => y
  | k + 1 => iotaD (N + k) (yAt k)

-- [D-1751] yAt_zero
@[simp] theorem yAt_zero : yAt N y 0 = y := rfl

-- [D-1752] yAt_succ
@[simp] theorem yAt_succ (k : ℕ) : yAt N y (k + 1) = iotaD (N + k) (yAt N y k) := rfl

-- [D-1753] toD_yAt
theorem toD_yAt (k : ℕ) : toD (N + k) (yAt N y k) = toD N y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show toD (N + k + 1) (iotaD (N + k) (yAt N y k)) = toD N y
      have h := toD_iotaLe (Nat.le_succ (N + k)) (yAt N y k)
      rw [iotaLe_succ (le_refl (N + k)) (Nat.le_succ (N + k)) (yAt N y k),
          iotaLe_self (le_refl (N + k)) (yAt N y k)] at h
      exact h.trans ih

-- [D-1754] joinIrred_yAt
theorem joinIrred_yAt (hy : JoinIrred (D N) y) (k : ℕ) :
    JoinIrred (D (N + k)) (yAt N y k) := by
  induction k with
  | zero => exact hy
  | succ k ih => exact (joinIrred_iotaD_iff (N + k) (yAt N y k)).mpr ih

-- [D-1755] §The-chain
-- [D-1756] SeedAt
abbrev SeedAt (k : ℕ) : Type := LevelSeed (N + k) (yAt N y k)

-- [D-1757] seedStep
noncomputable def seedStep (k : ℕ) (u : SeedAt N y k) : SeedAt N y (k + 1) :=
  ⟨iotaD (N + k) u.1,
   (joinIrred_iotaD_iff (N + k) u.1).mpr u.2.1,
   (iotaD_le_iff (N + k) u.1 (yAt N y k)).mpr u.2.2⟩

-- [D-1758] seedIncl
noncomputable def seedIncl (k : ℕ) (u : SeedAt N y k) : JBelow (toD N y) :=
  ⟨toD (N + k) u.1,
   (joinIrred_toD_iff (N + k) u.1).mpr u.2.1,
   by
     have h : toD (N + k) u.1 ≤ toD (N + k) (yAt N y k) :=
       (toD_le_iff' (N + k) u.1 (yAt N y k)).mpr u.2.2
     rwa [toD_yAt N y k] at h⟩

-- [D-1759] seedIncl_le_iff
theorem seedIncl_le_iff (k : ℕ) (a b : SeedAt N y k) :
    seedIncl N y k a ≤ seedIncl N y k b ↔ a ≤ b :=
  toD_le_iff' (N + k) a.1 b.1

-- [D-1760] seedIncl_step
theorem seedIncl_step (k : ℕ) (u : SeedAt N y k) :
    seedIncl N y (k + 1) (seedStep N y k u) = seedIncl N y k u := by
  apply Subtype.ext
  show toD (N + k + 1) (iotaD (N + k) u.1) = toD (N + k) u.1
  have h := toD_iotaLe (Nat.le_succ (N + k)) u.1
  rwa [iotaLe_succ (le_refl (N + k)) (Nat.le_succ (N + k)) u.1,
       iotaLe_self (le_refl (N + k)) u.1] at h

-- [D-1761] seedIncl_surj
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

-- [D-1762] jBelowPres
noncomputable def jBelowPres : Pres (JBelow (toD N y)) (SeedAt N y) where
  step := seedStep N y
  incl := seedIncl N y
  incl_le_iff := seedIncl_le_iff N y
  incl_step := seedIncl_step N y
  incl_surj := seedIncl_surj N y

end SeedChain
