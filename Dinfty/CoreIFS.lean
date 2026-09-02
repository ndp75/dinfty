/-
  CoreIFS — abstract "internal IFS ⟹ gasket quotient map" framework (Theorem A).

  Extracted from `SierpinskiApplication.lean` on 2026-08-26 when `axiom PsiIso`
  was deleted (most likely false — see `Meta/Finding - PsiIso tower mismatch
  (2026-08-26).md` and `DBilimit_reflexive`). The concrete instantiation
  `dInftyCoreIFS` depended on the honest `σ_A/σ_B/σ_C : D∞ → D∞` that only the
  (false) iso `D∞ ≃ F(D∞)` could supply — with just the retract `(Psi, PsiInv)`
  those maps degenerate. This file keeps the abstract, tower-agnostic content
  (parametric over `Dinf`, `Gamma`) intact and Mathlib-only; it currently has
  no instance. Reusable if an honest internal IFS on `D∞` is ever constructed.
-/

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

universe u

section TheoremA

-- The three self-maps of `D_∞` induced, via `Ψ`, by `Φ`'s three copy-inclusions at every level (companion note §2.1: `σ_A,σ_B,σ_C`, the "internal IFS").
structure InternalIFS (Dinf : Type u) where
  sigmaA : Dinf → Dinf
  sigmaB : Dinf → Dinf
  sigmaC : Dinf → Dinf

-- `𝒦`, the Knaster–Tarski attractor of `{σ_A,σ_B,σ_C}` (companion note §2.1), realized here as its own carrier type (not a subset of `Dinf`, to sidestep threading closure-under-`σ_j` proof obligations through every downstream field
structure CoreIFS (Dinf Gamma : Type u) [TopologicalSpace Gamma] where
  Core : Type u
  topCore : TopologicalSpace Core
  sigmaA : Core → Core
  sigmaB : Core → Core
  sigmaC : Core → Core
  /-- the classical gasket IFS maps on `Γ` that `ρ` must intertwine
      `σ_A/B/C` with (companion note's coding map `π`'s own defining
      contractions) — abstract here, since their concrete Euclidean
      form (the "one elementary Euclidean fact" of the minimal citation
      set) is not needed for the assembly logic itself. -/
  fA : Gamma → Gamma
  fB : Gamma → Gamma
  fC : Gamma → Gamma

attribute [instance] CoreIFS.topCore

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma]

-- **Theorem A's full bundled data.** `rho` is the reading map (companion note §2.1: `ρ := π ∘ α⁻¹`); `equivariant` is Lemma EQ; `quotient_map` is Theorem QM (G1 — well-defined, continuous, open, surjective); `unique` is Theorem UN (G3)
class TheoremAData (K : CoreIFS Dinf Gamma) where
  rho : K.Core → Gamma
  equivariant :
    (∀ x, rho (K.sigmaA x) = K.fA (rho x)) ∧
    (∀ x, rho (K.sigmaB x) = K.fB (rho x)) ∧
    (∀ x, rho (K.sigmaC x) = K.fC (rho x))
  /-- Theorem QM: `ρ` is a well-defined, continuous, open, surjective
      map `(𝒦,τ_𝒦) → Γ` — i.e. a quotient map. `IsOpenMap`/`Continuous`
      are Mathlib's own topological predicates; well-definedness is
      already built into `rho`'s being a genuine total function
      `K.Core → Gamma`, per the companion note's own resolution (Lemma
      RD closes it as a single fixed decomposition rule, not a
      separate side condition on the map). -/
  quotient_map : Continuous rho ∧ Function.Surjective rho ∧ IsOpenMap rho
  /-- Theorem UN: `ρ` is the *unique* continuous `Ψ`-equivariant
      surjection `𝒦 → Γ`. -/
  unique : ∀ rho' : K.Core → Gamma, Continuous rho' → Function.Surjective rho' →
      (∀ x, rho' (K.sigmaA x) = K.fA (rho' x)) →
      (∀ x, rho' (K.sigmaB x) = K.fB (rho' x)) →
      (∀ x, rho' (K.sigmaC x) = K.fC (rho' x)) →
      rho' = rho

-- **Theorem A**, the assembly step (companion note §2.5): given the bundled data, `ρ` is exactly the unique continuous `Ψ`-equivariant surjection `(𝒦,τ_𝒦) → Γ` — a genuine `∃!` statement, not merely a repetition of the class fields
theorem theorem_A (K : CoreIFS Dinf Gamma) [TA : TheoremAData K] :
    ∃! rho : K.Core → Gamma,
      Continuous rho ∧ Function.Surjective rho ∧
      (∀ x, rho (K.sigmaA x) = K.fA (rho x)) ∧
      (∀ x, rho (K.sigmaB x) = K.fB (rho x)) ∧
      (∀ x, rho (K.sigmaC x) = K.fC (rho x)) := by
  refine ⟨TA.rho, ⟨TA.quotient_map.1, TA.quotient_map.2.1, TA.equivariant.1,
    TA.equivariant.2.1, TA.equivariant.2.2⟩, ?_⟩
  rintro rho' ⟨hc, hs, hA, hB, hC⟩
  exact TA.unique rho' hc hs hA hB hC

end TheoremA

section FixCharacterization

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma]

/-- `Fix f` — the fixed-point set of a self-map (companion note's
    `Fix(σ_j)`). Generic, not `Core`-specific. -/
def Fix {α : Type u} (f : α → α) : Set α := {x | f x = x}

-- The distinguished points G2's exact characterization is stated against: `Core`'s own `⊥`/`⊤` (`botC`/`topC` — named points, not assumed to come from a `Preorder Core` instance
structure FixPoints (K : CoreIFS Dinf Gamma) where
  botC : K.Core
  topC : K.Core
  m0 : K.Core
  xB : K.Core
  xC : K.Core
  yC : K.Core

variable {K : CoreIFS Dinf Gamma}

-- **G2, bundled**: Theorems ESCAPE / FSB / FSC, exactly — `Fix(σ_A) = {⊥}`, `Fix(σ_B) = {x_B, m₀}`, `Fix(σ_C) = {x_C, y_C, ⊤}`.
class FixData (P : FixPoints K) where
  fixA : Fix K.sigmaA = {P.botC}
  fixB : Fix K.sigmaB = {P.xB, P.m0}
  fixC : Fix K.sigmaC = {P.xC, P.yC, P.topC}
  xB_ne_m0 : P.xB ≠ P.m0
  xC_ne_yC : P.xC ≠ P.yC
  xC_ne_topC : P.xC ≠ P.topC
  yC_ne_topC : P.yC ≠ P.topC

-- **Assembly**: given `FixData`, `Fix(σ_A)`/`Fix(σ_B)`/`Fix(σ_C)` have exactly 1/2/3 elements
theorem fix_card (P : FixPoints K) [FD : FixData P] :
    (Fix K.sigmaA).ncard = 1 ∧ (Fix K.sigmaB).ncard = 2 ∧
    (Fix K.sigmaC).ncard = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FD.fixA, Set.ncard_singleton]
  · rw [FD.fixB, Set.ncard_pair FD.xB_ne_m0]
  · rw [FD.fixC]
    exact Set.ncard_eq_three.mpr
      ⟨P.xC, P.yC, P.topC, FD.xC_ne_yC, FD.xC_ne_topC, FD.yC_ne_topC, rfl⟩

end FixCharacterization

section ConnectingFixToRho

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma]

-- Any pair of equivariant maps (companion note's Lemma EQ shape, `f` the `D_∞`-side self-map, `g` its `Γ`-side counterpart) sends `Fix f` into `Fix g` — general, no IFS-specific content at all: if `f x = x` then `rho' x = rho' (f x) = g (rho' x)`, i.e.
theorem equivariant_fixes_fix {α β : Type u} {f : α → α} {g : β → β}
    {rho' : α → β} (heq : ∀ x, rho' (f x) = g (rho' x))
    {x : α} (hx : x ∈ Fix f) : rho' x ∈ Fix g := by
  have hfx : f x = x := hx
  have h1 : rho' (f x) = g (rho' x) := heq x
  rw [hfx] at h1
  exact h1.symm

-- The orbit of a basepoint under the internal IFS (companion note §2.1: `\{\sigma_w(\bot) : w\in\{A,B,C\}^{<\omega}\}`), as an inductive predicate rather than an explicit closure formula
inductive InOrbit {K : CoreIFS Dinf Gamma} (x0 : K.Core) : K.Core → Prop
  | base : InOrbit x0 x0
  | stepA {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaA y)
  | stepB {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaB y)
  | stepC {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaC y)

def Orbit {K : CoreIFS Dinf Gamma} (x0 : K.Core) : Set K.Core := {x | InOrbit x0 x}

-- Read off an `Orbit` element via the finite word (list of `Fin 3` direction symbols) that builds it, cons-recursively matching `InOrbit`'s own constructor shape
noncomputable def orbitWord {Dinf Gamma : Type u} [TopologicalSpace Gamma]
    (K : CoreIFS Dinf Gamma) (x0 : K.Core) : List (Fin 3) → K.Core
  | [] => x0
  | (i :: l) =>
      if i.val = 0 then K.sigmaA (orbitWord K x0 l)
      else if i.val = 1 then K.sigmaB (orbitWord K x0 l)
      else K.sigmaC (orbitWord K x0 l)

theorem orbit_subset_range_orbitWord {Dinf Gamma : Type u} [TopologicalSpace Gamma]
    {K : CoreIFS Dinf Gamma} (x0 : K.Core) :
    Orbit x0 ⊆ Set.range (orbitWord K x0) := by
  intro x hx
  induction hx with
  | base => exact ⟨[], rfl⟩
  | stepA _ ih =>
      obtain ⟨l, rfl⟩ := ih
      exact ⟨(0 : Fin 3) :: l, by simp [orbitWord]⟩
  | stepB _ ih =>
      obtain ⟨l, rfl⟩ := ih
      exact ⟨(1 : Fin 3) :: l, by simp [orbitWord]⟩
  | stepC _ ih =>
      obtain ⟨l, rfl⟩ := ih
      exact ⟨(2 : Fin 3) :: l, by simp [orbitWord]⟩

-- **Every `CoreIFS` orbit is countable** — generic, no `DBilimit`/ `PsiIso` content at all: it's the image of the countable type `List (Fin 3)` under `orbitWord`.
theorem orbit_countable {Dinf Gamma : Type u} [TopologicalSpace Gamma]
    {K : CoreIFS Dinf Gamma} (x0 : K.Core) : (Orbit x0).Countable :=
  (Set.countable_range (orbitWord K x0)).mono (orbit_subset_range_orbitWord x0)

variable {K : CoreIFS Dinf Gamma}

-- Two equivariant maps agreeing at the basepoint agree on the whole orbit — plain structural induction on `InOrbit`, no topology needed at this step (that's §8's `theoremA_unique_of_ingredients`, which adds density + continuity to extend from here to all of `Core`).
theorem agree_on_orbit {x0 : K.Core} {rho1 rho2 : K.Core → Gamma}
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hB1 : ∀ x, rho1 (K.sigmaB x) = K.fB (rho1 x))
    (hC1 : ∀ x, rho1 (K.sigmaC x) = K.fC (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x))
    (hB2 : ∀ x, rho2 (K.sigmaB x) = K.fB (rho2 x))
    (hC2 : ∀ x, rho2 (K.sigmaC x) = K.fC (rho2 x))
    (hbase : rho1 x0 = rho2 x0) :
    Set.EqOn rho1 rho2 (Orbit x0) := by
  intro x hx
  induction hx with
  | base => exact hbase
  | stepA _ ih => rw [hA1, hA2, ih]
  | stepB _ ih => rw [hB1, hB2, ih]
  | stepC _ ih => rw [hC1, hC2, ih]

-- **The basepoint is pinned.** Given `FixData` (Theorem ESCAPE: `Fix(σ_A) = \{⊥\}` exactly) and that `Fix(f_A)` is a subsingleton (the Banach-fixed-point uniqueness fact for the classical IFS's contraction `f_A`
theorem base_pin {P : FixPoints K} [FD : FixData P]
    (hFixA : Subsingleton (Fix K.fA)) {rho1 rho2 : K.Core → Gamma}
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x)) :
    rho1 P.botC = rho2 P.botC := by
  have hbot : P.botC ∈ Fix K.sigmaA := by rw [FD.fixA]; rfl
  have h1 : rho1 P.botC ∈ Fix K.fA := equivariant_fixes_fix hA1 hbot
  have h2 : rho2 P.botC ∈ Fix K.fA := equivariant_fixes_fix hA2 hbot
  have heq : (⟨rho1 P.botC, h1⟩ : Fix K.fA) = ⟨rho2 P.botC, h2⟩ := hFixA.elim _ _
  exact congrArg Subtype.val heq

-- **`TheoremAData.unique`, proved for real from named ingredients** (rather than left as an opaque field): `Fix(f_A)` a subsingleton (Banach uniqueness) + `𝒦`'s own density-of-orbit property (its literal defining equation
theorem theoremA_unique_of_ingredients {P : FixPoints K} [FD : FixData P]
    [T2Space Gamma] (hFixA : Subsingleton (Fix K.fA))
    (hDense : Dense (Orbit (K := K) P.botC))
    {rho1 rho2 : K.Core → Gamma}
    (hc1 : Continuous rho1) (hc2 : Continuous rho2)
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hB1 : ∀ x, rho1 (K.sigmaB x) = K.fB (rho1 x))
    (hC1 : ∀ x, rho1 (K.sigmaC x) = K.fC (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x))
    (hB2 : ∀ x, rho2 (K.sigmaB x) = K.fB (rho2 x))
    (hC2 : ∀ x, rho2 (K.sigmaC x) = K.fC (rho2 x)) :
    rho1 = rho2 := by
  have hbase : rho1 P.botC = rho2 P.botC := base_pin hFixA hA1 hA2
  have heqOn : Set.EqOn rho1 rho2 (Orbit (K := K) P.botC) :=
    agree_on_orbit hA1 hB1 hC1 hA2 hB2 hC2 hbase
  exact Continuous.ext_on hDense hc1 hc2 heqOn

end ConnectingFixToRho
