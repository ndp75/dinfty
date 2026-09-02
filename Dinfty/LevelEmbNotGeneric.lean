import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Running the split: `LevelImageStableJI` cannot be proved generically

The stopping rule from §113 says the next commit proves `LevelImageStableJI` or
refutes it.  This is the outcome of running that, and it is a partial answer:
**the statement is false as a general fact about bounded lattices**, so any proof
of it must use `D`-specific structure.  It is *not* refuted at the `D` levels.

## The general pattern is false

`LevelEmbUnique`-shaped statements say: a monotone, order-reflecting,
`⊥`/`⊤`-preserving, join-preserving map between two finite bounded lattices is
the canonical one.  For a three-chain into a four-chain there are **two** such
maps — the middle element has two places to go, and every hypothesis is
satisfied by both.

```lean
embChainA, embChainB : Fin 3 → Fin 4
```

Both are monotone, order-reflecting, `⊥`- and `⊤`-preserving and join-preserving,
and they are different (`chain_not_unique`).

## What that means for the residue

Nothing in the derivation of `LevelImageStableJI` used any property of `D` beyond
"finite bounded lattice with an ep-pair to the next level".  The counterexample
above has all of that.  So:

* a proof of `LevelImageStableJI` **must** consume `D`-specific structure — the
  copy hierarchy, `D_all_rigid`, the seed classification — exactly as pillar B's
  `FirstSliceCHigh` did;
* an *abstract* attempt is refuted before it starts, and should not be made;
* the domain in the real statement is `D (k+1)`, never a chain (the `Φ`-tower's
  levels start at `D 1`), so this counterexample does **not** refute the residue.

The residue is therefore **open, and open on `D`-specific grounds**.
-/

namespace LevelEmbNotGeneric

/-- Two bounded join-embeddings of a three-chain into a four-chain. -/
def embChainA : Fin 3 → Fin 4 := ![0, 1, 3]

def embChainB : Fin 3 → Fin 4 := ![0, 2, 3]

theorem embChainA_mono : Monotone embChainA := by decide

theorem embChainB_mono : Monotone embChainB := by decide

theorem embChainA_reflect : ∀ a b : Fin 3, embChainA a ≤ embChainA b → a ≤ b := by decide

theorem embChainB_reflect : ∀ a b : Fin 3, embChainB a ≤ embChainB b → a ≤ b := by decide

theorem embChainA_bot : embChainA ⊥ = ⊥ := by decide

theorem embChainB_bot : embChainB ⊥ = ⊥ := by decide

theorem embChainA_top : embChainA ⊤ = ⊤ := by decide

theorem embChainB_top : embChainB ⊤ = ⊤ := by decide

theorem embChainA_sup : ∀ a b : Fin 3, embChainA (a ⊔ b) = embChainA a ⊔ embChainA b := by decide

theorem embChainB_sup : ∀ a b : Fin 3, embChainB (a ⊔ b) = embChainB a ⊔ embChainB b := by decide

theorem embChain_ne : embChainA ≠ embChainB := by decide

/-- **The general pattern is false.**  There are two bounded join-embeddings of a
three-chain into a four-chain, so no argument that uses only "finite bounded
lattices with an ep-pair" can prove `LevelImageStableJI`. -/
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
