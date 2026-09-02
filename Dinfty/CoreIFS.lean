import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

universe u

section TheoremA

-- [D-0001] InternalIFS
structure InternalIFS (Dinf : Type u) where
  sigmaA : Dinf → Dinf
  sigmaB : Dinf → Dinf
  sigmaC : Dinf → Dinf

-- [D-0002] CoreIFS
structure CoreIFS (Dinf Gamma : Type u) [TopologicalSpace Gamma] where
  Core : Type u
  topCore : TopologicalSpace Core
  sigmaA : Core → Core
  sigmaB : Core → Core
  sigmaC : Core → Core
  fA : Gamma → Gamma
  fB : Gamma → Gamma
  fC : Gamma → Gamma

attribute [instance] CoreIFS.topCore

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma]

-- [D-0003] TheoremAData
class TheoremAData (K : CoreIFS Dinf Gamma) where
  rho : K.Core → Gamma
  equivariant :
    (∀ x, rho (K.sigmaA x) = K.fA (rho x)) ∧
    (∀ x, rho (K.sigmaB x) = K.fB (rho x)) ∧
    (∀ x, rho (K.sigmaC x) = K.fC (rho x))
  quotient_map : Continuous rho ∧ Function.Surjective rho ∧ IsOpenMap rho
  unique : ∀ rho' : K.Core → Gamma, Continuous rho' → Function.Surjective rho' →
      (∀ x, rho' (K.sigmaA x) = K.fA (rho' x)) →
      (∀ x, rho' (K.sigmaB x) = K.fB (rho' x)) →
      (∀ x, rho' (K.sigmaC x) = K.fC (rho' x)) →
      rho' = rho

-- [D-0004] theorem_A
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

-- [D-0005] Fix
def Fix {α : Type u} (f : α → α) : Set α := {x | f x = x}

-- [D-0006] FixPoints
structure FixPoints (K : CoreIFS Dinf Gamma) where
  botC : K.Core
  topC : K.Core
  m0 : K.Core
  xB : K.Core
  xC : K.Core
  yC : K.Core

variable {K : CoreIFS Dinf Gamma}

-- [D-0007] FixData
class FixData (P : FixPoints K) where
  fixA : Fix K.sigmaA = {P.botC}
  fixB : Fix K.sigmaB = {P.xB, P.m0}
  fixC : Fix K.sigmaC = {P.xC, P.yC, P.topC}
  xB_ne_m0 : P.xB ≠ P.m0
  xC_ne_yC : P.xC ≠ P.yC
  xC_ne_topC : P.xC ≠ P.topC
  yC_ne_topC : P.yC ≠ P.topC

-- [D-0008] fix_card
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

-- [D-0009] equivariant_fixes_fix
theorem equivariant_fixes_fix {α β : Type u} {f : α → α} {g : β → β}
    {rho' : α → β} (heq : ∀ x, rho' (f x) = g (rho' x))
    {x : α} (hx : x ∈ Fix f) : rho' x ∈ Fix g := by
  have hfx : f x = x := hx
  have h1 : rho' (f x) = g (rho' x) := heq x
  rw [hfx] at h1
  exact h1.symm

-- [D-0010] InOrbit
inductive InOrbit {K : CoreIFS Dinf Gamma} (x0 : K.Core) : K.Core → Prop
  | base : InOrbit x0 x0
  | stepA {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaA y)
  | stepB {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaB y)
  | stepC {y : K.Core} : InOrbit x0 y → InOrbit x0 (K.sigmaC y)

-- [D-0011] Orbit
def Orbit {K : CoreIFS Dinf Gamma} (x0 : K.Core) : Set K.Core := {x | InOrbit x0 x}

-- [D-0012] orbitWord
noncomputable def orbitWord {Dinf Gamma : Type u} [TopologicalSpace Gamma]
    (K : CoreIFS Dinf Gamma) (x0 : K.Core) : List (Fin 3) → K.Core
  | [] => x0
  | (i :: l) =>
      if i.val = 0 then K.sigmaA (orbitWord K x0 l)
      else if i.val = 1 then K.sigmaB (orbitWord K x0 l)
      else K.sigmaC (orbitWord K x0 l)

-- [D-0013] orbit_subset_range_orbitWord
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

-- [D-0014] orbit_countable
theorem orbit_countable {Dinf Gamma : Type u} [TopologicalSpace Gamma]
    {K : CoreIFS Dinf Gamma} (x0 : K.Core) : (Orbit x0).Countable :=
  (Set.countable_range (orbitWord K x0)).mono (orbit_subset_range_orbitWord x0)

variable {K : CoreIFS Dinf Gamma}

-- [D-0015] agree_on_orbit
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

-- [D-0016] base_pin
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

-- [D-0017] theoremA_unique_of_ingredients
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
