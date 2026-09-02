import Dinfty.DeflationContinuity
import Dinfty.EpPairTower

open GluingTowerLibrary SierpinskiApplication

/-!
# The live tower as an abstract ep-pair tower, and the deflation results made
level-agnostic

`Dinfty/EpPairTower.lean` is the abstract ω-tower — Mathlib-only, `Fintype`-free,
with directed-completeness taken as a hypothesis (`IsDcpo`) rather than derived.
It was written as a reusable artefact and then imported by nothing, while
`SierpinskiApplication` grew its own concrete copies of the same constructions
(`insertAtLevel` for `ins`, its own `chainSet`/`chainSet_isLUB`).

This module closes that gap in both directions.

**Upward.** `EpPairTower.defl` and `EpPairTower.end_defl_isLUB` restate
`DeflationContinuity`'s results for an *arbitrary* ep-pair tower: for any
`h` Scott-continuous, `⨆ₙ δₙ ∘ h ∘ δₙ = h`, pointwise, where `δ n y = ins n (y n)`.
Both hypotheses that were discharged concretely there are discharged abstractly
here — pointwise suprema from `chainSet_isLUB`, joint directedness from
`ins_chain_mono`, both already on file in the abstract module.

**Downward.** `realTower` exhibits the live `D`-tower as an `EpPairTower`; all
four fields were already proven (`iotaD_monotone`, `pD_monotone`, `pD_iotaD`,
`pD_deflation`), so it is a structure literal. `realTower_isDcpo` and
`realTower_ins_scottContinuous` discharge the two hypotheses using finiteness of
the *levels*, and `real_end_defl_isLUB` is the instantiation.

**Where the finiteness goes, which is the point of doing this.** In the abstract
theorem there is none: `IsDcpo` and `ScottContinuous (ins n)` are hypotheses. At
the real tower they are discharged from `Fintype (D n)` — finiteness of a
*level*, never of the bilimit. Anything proved up here is available to any other
ep-pair tower over any levels, finite or not, which is the level-agnostic form
the recursion-wall criterion asks for.

**Scope.** This does not identify `realTower.ins` with `insertAtLevel`, nor
retire the duplicated concrete lemmas; both towers are on file and parallel.
Doing that identification is bookkeeping, but it is bookkeeping against the
`SierpinskiApplication` spine and is deliberately left out of this module.
-/

open scoped Classical

namespace EpPairTower

/-! ## The deflation family, abstractly -/

variable {T : _root_.EpPairTower}

/-- The `n`-th deflation of the bilimit: read off level `n`, insert back.
`chainSet` is exactly the range of this at a fixed point. -/
noncomputable def defl (T : _root_.EpPairTower) (n : ℕ) (y : T.Bilim) : T.Bilim :=
  T.ins n (y.1 n)

theorem defl_monotone (n : ℕ) : Monotone (T.defl n) := fun _ _ h =>
  ins_monotone n (h n)

@[simp] theorem defl_range (y : T.Bilim) :
    (Set.range fun n => T.defl n y) = T.chainSet y := rfl

/-- **Pointwise suprema — already proved abstractly.** -/
theorem defl_isLUB (y : T.Bilim) : IsLUB (Set.range fun n => T.defl n y) y :=
  chainSet_isLUB y

/-- **Joint directedness — already proved abstractly.** -/
theorem defl_directed (i j : ℕ) :
    ∃ k, (∀ y : T.Bilim, T.defl i y ≤ T.defl k y)
      ∧ (∀ y : T.Bilim, T.defl j y ≤ T.defl k y) :=
  ⟨max i j, fun y => ins_chain_mono y (le_max_left i j),
            fun y => ins_chain_mono y (le_max_right i j)⟩

/-- Reading a directed supremum at level `n` is Scott-continuous — this is
`isLUB_bilim_apply` restated as continuity of the projection. -/
theorem proj_scottContinuous (hT : T.IsDcpo) (n : ℕ) :
    ScottContinuous (fun y : T.Bilim => y.1 n) :=
  fun _S hne hdir _a ha => isLUB_bilim_apply hT ha hne hdir n

/-- `ins n` is Scott-continuous whenever its *domain* — the level `carrier n` —
is finite.  No condition on the bilimit. -/
theorem ins_scottContinuous_of_finite (n : ℕ) [Finite (T.carrier n)] :
    ScottContinuous (T.ins n) :=
  monotone_scottContinuous_of_finite_dom (ins_monotone n)

theorem defl_scottContinuous (hT : T.IsDcpo)
    (hins : ∀ n, ScottContinuous (T.ins n)) (n : ℕ) :
    ScottContinuous (T.defl n) := by
  have h := (proj_scottContinuous hT n).comp (hins n)
  unfold defl
  simpa [Function.comp_def] using h

/-- **`⨆ₙ δₙ ∘ h ∘ δₙ = h`, pointwise, over an arbitrary ep-pair tower.**

`EndLocalContinuity.deflation_isLUB` with every hypothesis discharged from the
abstract module: joint directedness from `ins_chain_mono`, pointwise suprema
from `chainSet_isLUB`, Scott-continuity of each `δₙ` from the factorisation
`δ n = ins n ∘ (· .1 n)`. -/
theorem end_defl_isLUB (hT : T.IsDcpo) (hins : ∀ n, ScottContinuous (T.ins n))
    {h : T.Bilim → T.Bilim} (hh : ScottContinuous h) (x : T.Bilim) :
    IsLUB (Set.range fun n => T.defl n (h (T.defl n x))) (h x) := by
  have hlub := EndLocalContinuity.deflation_isLUB (ι := ℕ) T.defl id h
    defl_directed defl_isLUB hh (defl_scottContinuous hT hins) x
  simpa using hlub

end EpPairTower

/-! ## The live tower is one of these -/

namespace RealEpPairTower

/-- The `D`-tower as an abstract ep-pair tower.  Every field was already on
file; this is only the assembly. -/
noncomputable def realTower : _root_.EpPairTower where
  carrier := D
  order := fun k => inferInstance
  emb := iotaD
  prj := pD
  emb_mono := iotaD_monotone
  prj_mono := fun k w w' h => pD_monotone k w w' h
  retraction := pD_iotaD
  deflation := pD_deflation

@[simp] theorem realTower_carrier (k : ℕ) : realTower.carrier k = D k := rfl
@[simp] theorem realTower_prj (k : ℕ) : realTower.prj k = pD k := rfl

/-- The bilimit of the abstract tower is the concrete `DBilimit`, definitionally. -/
theorem realTower_bilim : realTower.Bilim = DBilimit := rfl

/-- The levels are finite — stated against `realTower.carrier` so that instance
search finds it without having to reduce the projection. -/
instance realTower_finite (k : ℕ) : Finite (realTower.carrier k) :=
  inferInstanceAs (Finite (D k))

/-- `IsDcpo` for the real tower: levels are finite lattices, so directed subsets
attain their suprema, and `pD` has finite domain. -/
theorem realTower_isDcpo : realTower.IsDcpo where
  carrier_lub := by
    intro k S hne hdir
    obtain ⟨t, htS, htmax⟩ := directedOn_exists_greatest_of_finite (Set.toFinite S) hne hdir
    exact ⟨t, fun s hs => htmax s hs, fun z hz => hz htS⟩
  prj_scott := fun k => monotone_scottContinuous_of_finite_dom (fun w w' h => pD_monotone k w w' h)

theorem realTower_ins_scottContinuous (n : ℕ) : ScottContinuous (realTower.ins n) :=
  EpPairTower.ins_scottContinuous_of_finite n

/-- **The instantiation.**  `⨆ₙ δₙ ∘ h ∘ δₙ = h` at the live tower, obtained
from the level-agnostic theorem rather than proved again. -/
theorem real_end_defl_isLUB {h : realTower.Bilim → realTower.Bilim}
    (hh : ScottContinuous h) (x : realTower.Bilim) :
    IsLUB (Set.range fun n => realTower.defl n (h (realTower.defl n x))) (h x) :=
  EpPairTower.end_defl_isLUB realTower_isDcpo realTower_ins_scottContinuous hh x

end RealEpPairTower
