import Dinfty.NormalizedGlueMap

open GluingTowerLibrary SierpinskiApplication

-- [D-1366] §Local-continuity-of-s-morphism-action
open scoped Classical

universe u v

namespace GlueMapContinuity

open NormalizedGlueMap

-- [D-1367] §1-The-morphism-action-is-monotone
section Monotone

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']

-- [D-1368] baseMap_leGlue_of_le
theorem baseMap_leGlue_of_le (m' : P') {g g' : P →o P'} (hgg : g ≤ g')
    (x : GlueBase P) :
    leGlue m' (baseMap g x) (baseMap g' x) := by
  have hpt : ∀ a : P, g a ≤ g' a := fun a => OrderHom.le_def.mp hgg a
  cases x with
  | inl a =>
    exact ⟨Sum.inl (g a), self_mem_occs _ _, Sum.inl (g' a), self_mem_occs _ _, hpt a⟩
  | inr x =>
    cases x with
    | inl a =>
      exact ⟨Sum.inr (Sum.inl (g a)), self_mem_occs _ _,
             Sum.inr (Sum.inl (g' a)), self_mem_occs _ _, hpt a⟩
    | inr a =>
      exact ⟨Sum.inr (Sum.inr (g a)), self_mem_occs _ _,
             Sum.inr (Sum.inr (g' a)), self_mem_occs _ _, hpt a⟩

-- [D-1369] glueMap_le_of_le
theorem glueMap_le_of_le {m : P} {m' : P'} {g g' : P →o P'} (hgg : g ≤ g')
    (hginj : Function.Injective g) (hbot : g ⊥ = (⊥ : P')) (hmid : g m = m')
    (htop : g ⊤ = (⊤ : P')) (hm0 : m ≠ (⊥ : P))
    (hginj' : Function.Injective g') (hbot' : g' ⊥ = (⊥ : P')) (hmid' : g' m = m')
    (htop' : g' ⊤ = (⊤ : P')) (x : GlueCar (P := P) m) :
    glueMap g m m' hginj hbot hmid htop hm0 x
      ≤ glueMap g' m m' hginj' hbot' hmid' htop' hm0 x :=
  baseMap_leGlue_of_le m' hgg x.val

end Monotone

-- [D-1370] §2-Directed-families-over-a-finite-index-attain
section Attained

variable {α : Type u} [Preorder α] {ι : Type v} [Fintype ι] [Nonempty ι]

-- [D-1371] exists_greatest_of_directed
theorem exists_greatest_of_directed (f : ι → α) (hdir : Directed (· ≤ ·) f) :
    ∃ z : ι, ∀ i : ι, f i ≤ f z := by
  obtain ⟨z, hz⟩ := hdir.finset_le (Finset.univ : Finset ι)
  exact ⟨z, fun i => hz i (Finset.mem_univ i)⟩

end Attained

-- [D-1372] §3-Local-continuity-at-each-finite-level
section Continuity

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
variable {P' : Type u} [DecidableEq P'] [Lattice P'] [BoundedOrder P'] [Fintype P']
variable {ι : Type v} [Fintype ι] [Nonempty ι]

-- [D-1373] baseMap_directed_sup
theorem baseMap_directed_sup (m' : P') (g : ι → (P →o P'))
    (hdir : Directed (· ≤ ·) g) :
    ∃ z : ι, (∀ i : ι, g i ≤ g z) ∧
      ∀ (i : ι) (x : GlueBase P), leGlue m' (baseMap (g i) x) (baseMap (g z) x) := by
  obtain ⟨z, hz⟩ := exists_greatest_of_directed g hdir
  exact ⟨z, hz, fun i x => baseMap_leGlue_of_le m' (hz i) x⟩

-- [D-1374] glueMap_directed_sup
theorem glueMap_directed_sup {m : P} {m' : P'} (hm0 : m ≠ (⊥ : P))
    (g : ι → (P →o P')) (hdir : Directed (· ≤ ·) g)
    (hginj : ∀ i, Function.Injective (g i)) (hbot : ∀ i, (g i) ⊥ = (⊥ : P'))
    (hmid : ∀ i, (g i) m = m') (htop : ∀ i, (g i) ⊤ = (⊤ : P')) :
    ∃ z : ι, ∀ (i : ι) (x : GlueCar (P := P) m),
      glueMap (g i) m m' (hginj i) (hbot i) (hmid i) (htop i) hm0 x
        ≤ glueMap (g z) m m' (hginj z) (hbot z) (hmid z) (htop z) hm0 x := by
  obtain ⟨z, hz, _⟩ := baseMap_directed_sup (P := P) m' g hdir
  exact ⟨z, fun i x => baseMap_leGlue_of_le m' (hz i) x.val⟩

end Continuity

-- [D-1375] §4-The-tower-s-levels-are-finite-so-3-applies
section TowerLevels

open NormalizedGlueMap.NormalizedTower

-- [D-1376] triLevelFintype
noncomputable instance triLevelFintype (k : ℕ) : Fintype (triLevel k).carrier :=
  (triLevel k).fin

end TowerLevels

end GlueMapContinuity
