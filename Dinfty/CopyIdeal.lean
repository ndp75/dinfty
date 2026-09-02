import Dinfty.BilimitGap
import Dinfty.CopyHierarchy

open GluingTowerLibrary SierpinskiApplication

/-!
# Copy `A` is a proper order-ideal, and that is which object is which

`BilimitGap.no_orderIso` says `B` and `DBilimit` are not isomorphic but does not
say what the relation between them *is*.  `CopyHierarchy` answers that, and the
answer was already in the repository — outside the release closure, which is why
it went unused.

## The copy hierarchy

`CopyHierarchy.copyIdx_mono` reads the bridging digraph off `rawRuleGen`:
`a → {a,b,c}`, `b → {b,c}`, `c → {c}`.  Its two corollaries are the ones that
matter here:

* **`tagA_source`** — nothing sits below a copy-`A` point except copy-`A`
  points.  So **copy `A` is a down-set**.
* **`tagC_sink`** — nothing generic sits above a copy-`C` point except copy-`C`
  points.  So copy `C` is an up-set.

## What that says about the two towers

`iotaD k x = glueA (markedPt k) (constHom x)` lands in copy `A` *by definition*,
and copy `A` never contains the top (`glueA_ne_top`).  So

> **the legacy tower is confined, at every level, to a proper down-set of
> `D (k+1)`** — `iotaD_mem_copyA` and `copyA_isLowerSet` below —

while `glueAA k ⊤ = ⊤` puts the `Φ`-iterate tower outside it.  That is the
structural content of `no_orderIso`: `DBilimit` is built inside a proper ideal,
`B` is not.  The two theorems are not about "two unrelated domains" — they are
about an ideal and the thing it sits in.

## Which object the redefinition should be about

`B`.  Copy `C` is the sink of the hierarchy, `glueAA` is the tower that reaches
it, and `topB` is compact there precisely because the top is *attained* at a
finite level rather than approached.  `DBilimit` is the copy-`A` shadow.

What is **not** settled here is whether Theorem B's rigidity survives passing
from the ideal to the whole; `BilimitGap.rigid_of_orderIso` shows the cheap
route (transport along an iso) is unavailable, and this file says the honest
replacement is a statement about an ideal inclusion, not an equivalence.
-/

open Set

namespace CopyIdeal

universe u

open CopyHierarchy

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- The copy-`A` part of a glued level. -/
def CopyA (m : P) : Set (GlueCarGen (P := P) m) := {x | ∃ a : P, x.1 = Sum.inl a}

/-- **Copy `A` is a down-set** — `tagA_source`, packaged. -/
theorem copyA_isLowerSet (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLowerSet (CopyA m) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  rintro x y hyx ⟨a, ha⟩
  have hfix : canonGen m y.1 = y.1 := y.2
  have hle : leGlueGen m y.1 (Sum.inl a) := by
    have : leGlueGen m y.1 x.1 := hyx
    rwa [ha] at this
  exact tagA_source m hm hbt hfix hle

/-- A down-set containing an upper bound of everything is everything.  So as
soon as *one* point lies outside copy `A`, the top does too. -/
theorem not_mem_copyA_of_isTop (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    ∀ {t w : GlueCarGen (P := P) m}, (∀ z, z ≤ t) → w ∉ CopyA m → t ∉ CopyA m := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  intro t w ht hw htA
  exact hw (copyA_isLowerSet m hm hmt hbt (ht w) htA)

end CopyIdeal

/-! ## At the tower

`iotaD k x = glueA (markedPt k) (constHom x)` lands in copy `A` by definition.
Copy `A` is a down-set (above) that omits the top (`iotaD_ne_top`, which is
obstruction (T)'s one line), and `glueAA k ⊤ = ⊤` puts the `Φ`-iterate tower
outside it.  So the legacy tower is confined, level by level, to a **proper
order-ideal** of the level the `Φ`-tower uses in full. -/

namespace CopyIdeal

open PhiIterateTower FTowerTripointed

/-- The legacy tower lands in copy `A`. -/
theorem iotaD_mem_copyA (k : ℕ) (x : D k) :
    iotaD k x ∈ CopyA (markedPt k) := ⟨constHom x, rfl⟩

/-- **The contrast, in ideal form.**  Every `iotaD` image is in copy `A` and
none of them is the top, while `glueAA` hits the top exactly. -/
theorem legacy_confined_phi_not (k : ℕ) :
    (∀ x : D k, iotaD k x ∈ CopyA (markedPt k) ∧ iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  ⟨fun x => ⟨iotaD_mem_copyA k x, iotaD_ne_top k x⟩, glueAA_top k⟩

end CopyIdeal
