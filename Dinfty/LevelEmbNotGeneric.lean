import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

-- [D-3539] §Running-the-split-LevelImageStableJI-cannot-be
namespace LevelEmbNotGeneric

-- [D-3540] embChainA
def embChainA : Fin 3 → Fin 4 := ![0, 1, 3]

-- [D-3541] embChainB
def embChainB : Fin 3 → Fin 4 := ![0, 2, 3]

-- [D-3542] embChainA_mono
theorem embChainA_mono : Monotone embChainA := by decide

-- [D-3543] embChainB_mono
theorem embChainB_mono : Monotone embChainB := by decide

-- [D-3544] embChainA_reflect
theorem embChainA_reflect : ∀ a b : Fin 3, embChainA a ≤ embChainA b → a ≤ b := by decide

-- [D-3545] embChainB_reflect
theorem embChainB_reflect : ∀ a b : Fin 3, embChainB a ≤ embChainB b → a ≤ b := by decide

-- [D-3546] embChainA_bot
theorem embChainA_bot : embChainA ⊥ = ⊥ := by decide

-- [D-3547] embChainB_bot
theorem embChainB_bot : embChainB ⊥ = ⊥ := by decide

-- [D-3548] embChainA_top
theorem embChainA_top : embChainA ⊤ = ⊤ := by decide

-- [D-3549] embChainB_top
theorem embChainB_top : embChainB ⊤ = ⊤ := by decide

-- [D-3550] embChainA_sup
theorem embChainA_sup : ∀ a b : Fin 3, embChainA (a ⊔ b) = embChainA a ⊔ embChainA b := by decide

-- [D-3551] embChainB_sup
theorem embChainB_sup : ∀ a b : Fin 3, embChainB (a ⊔ b) = embChainB a ⊔ embChainB b := by decide

-- [D-3552] embChain_ne
theorem embChain_ne : embChainA ≠ embChainB := by decide

-- [D-3553] chain_not_unique
theorem chain_not_unique :
    ∃ f g : Fin 3 → Fin 4,
      (Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b) ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤
        ∧ ∀ a b, f (a ⊔ b) = f a ⊔ f b)
      ∧ (Monotone g ∧ (∀ a b, g a ≤ g b → a ≤ b) ∧ g ⊥ = ⊥ ∧ g ⊤ = ⊤
        ∧ ∀ a b, g (a ⊔ b) = g a ⊔ g b)
      ∧ f ≠ g :=
  ⟨embChainA, embChainB,
    ⟨embChainA_mono, embChainA_reflect, embChainA_bot, embChainA_top, embChainA_sup⟩,
    ⟨embChainB_mono, embChainB_reflect, embChainB_bot, embChainB_top, embChainB_sup⟩,
    embChain_ne⟩

end LevelEmbNotGeneric
