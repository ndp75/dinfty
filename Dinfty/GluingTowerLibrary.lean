import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Hom.Order
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.UniformSpace.Closeds
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.CompactlyGenerated.Basic
import Dinfty.ProdAut

open scoped Classical
open Relation

universe u

namespace GluingTowerLibrary

section GeneralLattice

variable {P : Type u} [Lattice P] [BoundedOrder P]

-- [D-0055] EndP
abbrev EndP (P : Type u) [Preorder P] := P →o P

-- [D-0056] inst-Preorder
instance : Preorder (EndP P) :=
  Preorder.lift (fun f => (f : P → P))

-- [D-0057] constHom
def constHom (x : P) : EndP P := ⟨fun _ => x, fun _ _ _ => le_refl x⟩

-- [D-0058] constHom_apply
omit [BoundedOrder P] in
@[simp] theorem constHom_apply (c x : P) : constHom c x = c := rfl

-- [D-0059] meetHom
def meetHom (c : P) : EndP P := ⟨fun x => x ⊓ c, fun _ _ hab => inf_le_inf_right c hab⟩

-- [D-0060] meetHom_apply
omit [BoundedOrder P] in
@[simp] theorem meetHom_apply (c x : P) : meetHom c x = x ⊓ c := rfl

-- [D-0061] Comp
def Comp (P : Type u) [Preorder P] (a : P) : Prop :=
  ∀ b : P, a ≤ b ∨ b ≤ a

-- [D-0062] bot_comp
theorem bot_comp : Comp P (⊥ : P) := fun _b => Or.inl bot_le

-- [D-0063] top_comp
theorem top_comp : Comp P (⊤ : P) := fun _b => Or.inr le_top

-- [D-0064] latticeDecLE
def latticeDecLE {P : Type u} [Lattice P] [DecidableEq P] :
    DecidableRel ((· ≤ ·) : P → P → Prop) :=
  fun a b => decidable_of_iff (a ⊔ b = b) sup_eq_right

-- [D-0065] JoinIrred
def JoinIrred (P : Type u) [Lattice P] [OrderBot P] (a : P) : Prop :=
  a ≠ ⊥ ∧ ∀ b c : P, a = b ⊔ c → a = b ∨ a = c

-- [D-0066] UniqueAtomCoatom
class UniqueAtomCoatom (P : Type u) [Lattice P] [BoundedOrder P] : Prop where
  unique_atom   : ∃! a : P, a ≠ ⊥ ∧ ∀ b : P, b ≠ ⊥ → a ≤ b
  unique_coatom : ∃! a : P, a ≠ ⊤ ∧ ∀ b : P, b ≠ ⊤ → b ≤ a

-- [D-0067] atomOf
noncomputable def atomOf (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : P :=
  (UniqueAtomCoatom.unique_atom (P := P)).choose

-- [D-0068] atomOf_ne_bot
theorem atomOf_ne_bot (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : atomOf P ≠ (⊥ : P) :=
  (UniqueAtomCoatom.unique_atom (P := P)).choose_spec.1.1

-- [D-0069] atomOf_le
theorem atomOf_le {P : Type u} [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]
    {b : P} (hb : b ≠ ⊥) : atomOf P ≤ b :=
  (UniqueAtomCoatom.unique_atom (P := P)).choose_spec.1.2 b hb

-- [D-0070] coatomOf
noncomputable def coatomOf (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : P :=
  (UniqueAtomCoatom.unique_coatom (P := P)).choose

-- [D-0071] coatomOf_ne_top
theorem coatomOf_ne_top (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : coatomOf P ≠ (⊤ : P) :=
  (UniqueAtomCoatom.unique_coatom (P := P)).choose_spec.1.1

-- [D-0072] coatomOf_le
theorem coatomOf_le {P : Type u} [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]
    {b : P} (hb : b ≠ ⊤) : b ≤ coatomOf P :=
  (UniqueAtomCoatom.unique_coatom (P := P)).choose_spec.1.2 b hb

-- [D-0073] atomOf_comparable
theorem atomOf_comparable (P : Type u) [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]
    (z : P) : z ≤ atomOf P ∨ atomOf P ≤ z := by
  rcases eq_or_ne z ⊥ with hz | hz
  · exact Or.inl (hz ▸ bot_le)
  · exact Or.inr (atomOf_le hz)

-- [D-0074] coatomOf_comparable
theorem coatomOf_comparable (P : Type u) [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]
    (z : P) : z ≤ coatomOf P ∨ coatomOf P ≤ z := by
  rcases eq_or_ne z ⊤ with hz | hz
  · exact Or.inr (hz ▸ le_top)
  · exact Or.inl (coatomOf_le hz)

-- [D-0075] inc_atomOf_eq_empty
theorem inc_atomOf_eq_empty (P : Type u) [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P] :
    {z : P | ¬ z ≤ atomOf P ∧ ¬ atomOf P ≤ z} = ∅ := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro hz1
  rcases atomOf_comparable P z with h | h
  · exact absurd h hz1
  · exact h

-- [D-0076] inc_coatomOf_eq_empty
theorem inc_coatomOf_eq_empty (P : Type u) [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P] :
    {z : P | ¬ z ≤ coatomOf P ∧ ¬ coatomOf P ≤ z} = ∅ := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro hz1
  rcases coatomOf_comparable P z with h | h
  · exact absurd h hz1
  · exact h

-- [D-0077] spikeHom
noncomputable def spikeHom (v : P) : EndP P :=
  ⟨fun x => if x = ⊤ then v else ⊥, by
    intro x y hxy
    by_cases hx : x = ⊤
    · have hy : y = ⊤ := le_antisymm le_top (hx ▸ hxy)
      simp [hx, hy]
    · by_cases hy : y = ⊤ <;> simp [hx, hy]⟩

-- [D-0078] cospikeHom
noncomputable def cospikeHom (v : P) : EndP P :=
  ⟨fun x => if x = ⊥ then v else ⊤, by
    intro x y hxy
    by_cases hy : y = ⊥
    · have hx : x = ⊥ := le_antisymm (hy ▸ hxy) bot_le
      simp [hx, hy]
    · by_cases hx : x = ⊥ <;> simp [hx, hy]⟩

-- [D-0079] spikeHom_apply_top
@[simp] theorem spikeHom_apply_top (v : P) : spikeHom v ⊤ = v := if_pos rfl

-- [D-0080] spikeHom_apply_of_ne
@[simp] theorem spikeHom_apply_of_ne (v : P) {x : P} (hx : x ≠ ⊤) :
    spikeHom v x = ⊥ := if_neg hx

-- [D-0081] cospikeHom_apply_bot
@[simp] theorem cospikeHom_apply_bot (v : P) : cospikeHom v ⊥ = v := if_pos rfl

-- [D-0082] cospikeHom_apply_of_ne
@[simp] theorem cospikeHom_apply_of_ne (v : P) {x : P} (hx : x ≠ ⊥) :
    cospikeHom v x = ⊤ := if_neg hx

-- [D-0083] spikeHom_atomOf_comp
theorem spikeHom_atomOf_comp [UniqueAtomCoatom P] :
    Comp (EndP P) (spikeHom (atomOf P)) := by
  intro g
  by_cases hg : g ⊤ = ⊥
  · right
    intro x
    rcases eq_or_ne x ⊤ with hx | hx
    · subst hx; simp [hg]
    · have : g x ≤ g ⊤ := g.mono le_top
      rw [hg, le_bot_iff] at this
      simp [hx, this]
  · left
    intro x
    rcases eq_or_ne x ⊤ with hx | hx
    · subst hx; simp [atomOf_le hg]
    · simp [hx]

-- [D-0084] cospikeHom_coatomOf_comp
theorem cospikeHom_coatomOf_comp [UniqueAtomCoatom P] :
    Comp (EndP P) (cospikeHom (coatomOf P)) := by
  intro g
  by_cases hg : g ⊥ = ⊤
  · left
    intro x
    rcases eq_or_ne x ⊥ with hx | hx
    · subst hx; simp [hg]
    · have : g ⊥ ≤ g x := g.mono bot_le
      rw [hg, top_le_iff] at this
      simp [hx, this]
  · right
    intro x
    rcases eq_or_ne x ⊥ with hx | hx
    · subst hx; simp [coatomOf_le hg]
    · simp [hx]

-- [D-0085] genreduce
theorem genreduce (P : Type u) [Lattice P] [BoundedOrder P] [Fintype P]
    [UniqueAtomCoatom P]
    (hCompP : ∀ b : P, Comp P b → b = ⊥ ∨ b = ⊤ ∨ b = atomOf P ∨ b = coatomOf P)
    (hAtomNe : atomOf P ≠ ⊤) (hCoatomNe : coatomOf P ≠ ⊥) :
    ∀ f : EndP P, Comp (EndP P) f →
      f = constHom (⊥ : P) ∨ f = constHom (⊤ : P) ∨
      f = spikeHom (atomOf P) ∨ f = cospikeHom (coatomOf P) := by
  have hbot_ne_top : (⊥ : P) ≠ ⊤ := by
    intro h
    apply atomOf_ne_bot P
    have h1 : atomOf P ≤ (⊤ : P) := le_top
    rw [← h] at h1
    exact le_bot_iff.mp h1
  intro f hf
  by_cases hconst : ∃ c : P, f = constHom c
  ·
    obtain ⟨c, hc⟩ := hconst
    have hcCompP : Comp P c := by
      intro c'
      rcases hf (constHom c') with h | h
      · left; have h1 := h ⊤; rw [hc] at h1; simpa using h1
      · right; have h1 := h ⊤; rw [hc] at h1; simpa using h1
    rcases hCompP c hcCompP with h | h | h | h
    · exact Or.inl (by rw [hc, h])
    · exact Or.inr (Or.inl (by rw [hc, h]))
    ·
      exfalso
      rcases hf (spikeHom (⊤ : P)) with hle | hle
      · have h1 := hle ⊥
        rw [hc] at h1
        simp only [constHom_apply, spikeHom_apply_of_ne _ hbot_ne_top] at h1
        exact atomOf_ne_bot P (h ▸ le_bot_iff.mp h1)
      · have h1 := hle ⊤
        rw [hc] at h1
        simp only [spikeHom_apply_top, constHom_apply] at h1
        exact hAtomNe (h ▸ top_le_iff.mp h1)
    ·
      exfalso
      rcases hf (cospikeHom (⊥ : P)) with hle | hle
      · have h1 := hle ⊥
        rw [hc] at h1
        simp only [constHom_apply, cospikeHom_apply_bot] at h1
        exact hCoatomNe (h ▸ le_bot_iff.mp h1)
      · have h1 := hle ⊤
        rw [hc] at h1
        simp only [cospikeHom_apply_of_ne _ hbot_ne_top.symm, constHom_apply] at h1
        exact coatomOf_ne_top P (h ▸ top_le_iff.mp h1)
  ·
    push Not at hconst
    set m : P := Finset.univ.inf (⇑f) with hmdef
    set M : P := Finset.univ.sup (⇑f) with hMdef
    have hle_M : ∀ x, f x ≤ M := fun x => Finset.le_sup (Finset.mem_univ x)
    have hm_le : ∀ x, m ≤ f x := fun x => Finset.inf_le (Finset.mem_univ x)
    have hcomp_c : ∀ c : P, M ≤ c ∨ c ≤ m := by
      intro c
      rcases hf (constHom c) with h | h
      · exact Or.inl (Finset.sup_le fun x _ => h x)
      · exact Or.inr (Finset.le_inf fun x _ => h x)
    have hcover : ∀ c : P, m < c → c < M → False := by
      intro c hmc hcM
      rcases hcomp_c c with h | h
      · exact absurd (lt_of_lt_of_le hcM h) (lt_irrefl c)
      · exact absurd (lt_of_lt_of_le hmc h) (lt_irrefl m)
    have hmem : ∀ x, f x = m ∨ f x = M := by
      intro x
      rcases eq_or_lt_of_le (hm_le x) with h | h
      · exact Or.inl h.symm
      rcases eq_or_lt_of_le (hle_M x) with h' | h'
      · exact Or.inr h'
      · exact absurd h' (fun h' => hcover (f x) h h')
    have hne : m ≠ M := by
      intro heq
      apply hconst m
      apply OrderHom.ext
      funext x
      rcases hmem x with h | h
      · simpa using h
      · simpa [heq] using h
    have hMattain : ∃ x, f x = M := by
      by_contra hcon
      push Not at hcon
      apply hconst m
      apply OrderHom.ext
      funext x
      rcases hmem x with h | h
      · simpa using h
      · exact absurd h (hcon x)
    have hmattain : ∃ x, f x = m := by
      by_contra hcon
      push Not at hcon
      apply hconst M
      apply OrderHom.ext
      funext x
      rcases hmem x with h | h
      · exact absurd h (hcon x)
      · simpa using h
    have hfTop : f ⊤ = M := by
      obtain ⟨x0, hx0⟩ := hMattain
      have h1 : f x0 ≤ f ⊤ := f.mono le_top
      rw [hx0] at h1
      exact le_antisymm (hle_M ⊤) h1
    have hfBot : f ⊥ = m := by
      obtain ⟨x0, hx0⟩ := hmattain
      have h1 : f ⊥ ≤ f x0 := f.mono bot_le
      rw [hx0] at h1
      exact le_antisymm h1 (hm_le ⊥)
    rcases eq_or_ne m ⊥ with hm | hm
    ·
      have hMne : M ≠ ⊥ := fun hMb => hne (hm.trans hMb.symm)
      have hMa : M = atomOf P := by
        rcases hcomp_c (atomOf P) with h | h
        · exact le_antisymm h (atomOf_le hMne)
        · exact absurd (le_bot_iff.mp (hm ▸ h)) (atomOf_ne_bot P)
      rcases eq_or_ne M ⊤ with hM | hM
      ·
        exact absurd (hMa.symm.trans hM) hAtomNe
      ·
        have hspiketop : f ≤ spikeHom (⊤ : P) := by
          rcases hf (spikeHom (⊤ : P)) with hle | hle
          · exact hle
          · exfalso
            have h1 := hle ⊤
            simp only [spikeHom_apply_top] at h1
            rw [hfTop, hMa] at h1
            exact hAtomNe (top_le_iff.mp h1)
        right; right; left
        apply OrderHom.ext
        funext x
        rcases eq_or_ne x ⊤ with hxT | hxT
        · subst hxT
          simp [hfTop, hMa]
        · have h2 := hspiketop x
          simp only [spikeHom_apply_of_ne _ hxT] at h2
          have hfx0 : f x = ⊥ := le_bot_iff.mp h2
          simp [hfx0, spikeHom_apply_of_ne _ hxT]
    · rcases eq_or_ne M ⊤ with hM | hM
      ·
        have hmne : m ≠ ⊤ := fun hmt => hne (hmt.trans hM.symm)
        have hmg : m = coatomOf P := by
          rcases hcomp_c (coatomOf P) with h | h
          · exact absurd (top_le_iff.mp (hM ▸ h)) (coatomOf_ne_top P)
          · exact le_antisymm (coatomOf_le hmne) h
        have hcospikebot : cospikeHom (⊥ : P) ≤ f := by
          rcases hf (cospikeHom (⊥ : P)) with hle | hle
          · exfalso
            have h1 := hle ⊥
            simp only [cospikeHom_apply_bot] at h1
            rw [hfBot, hmg] at h1
            exact hCoatomNe (le_bot_iff.mp h1)
          · exact hle
        right; right; right
        apply OrderHom.ext
        funext x
        rcases eq_or_ne x ⊥ with hx0 | hx0
        · subst hx0
          simp [hfBot, hmg]
        · have h2 := hcospikebot x
          simp only [cospikeHom_apply_of_ne _ hx0] at h2
          have hfx0 : f x = ⊤ := top_le_iff.mp h2
          simp [hfx0, cospikeHom_apply_of_ne _ hx0]
      ·
        exfalso
        have hUup : ∀ x y : P, f x = M → x ≤ y → f y = M := by
          intro x y hx hxy
          exact le_antisymm (hle_M y) (hx ▸ f.mono hxy)
        set g : EndP P :=
          ⟨fun x => if f x = M then ⊤ else ⊥, by
            intro x y hxy
            by_cases hx : f x = M
            · have hy : f y = M := hUup x y hx hxy
              simp [hx, hy]
            · by_cases hy : f y = M <;> simp [hx, hy]⟩ with hgdef
        obtain ⟨x0, hx0⟩ := hmattain
        obtain ⟨x1, hx1⟩ := hMattain
        have hgx0 : g x0 = ⊥ := by
          show (if f x0 = M then (⊤ : P) else ⊥) = ⊥
          rw [if_neg (hx0 ▸ hne)]
        have hgx1 : g x1 = ⊤ := by
          show (if f x1 = M then (⊤ : P) else ⊥) = ⊤
          rw [if_pos hx1]
        rcases hf g with hle | hle
        · have h1 := hle x0
          simp only [hx0, hgx0] at h1
          exact hm (le_bot_iff.mp h1)
        · have h1 := hle x1
          simp only [hgx1, hx1] at h1
          exact hM (top_le_iff.mp h1)

-- [D-0086] latticeOfFiniteSup
@[reducible]
noncomputable def latticeOfFiniteSup {α : Type u} [Fintype α] [DecidableEq α]
    (S : SemilatticeSup α) [OrderBot α] : Lattice α :=
  { S with
    inf := fun x y => (Finset.univ.filter (fun z => z ≤ x ∧ z ≤ y)).sup id
    inf_le_left := fun x y =>
      Finset.sup_le (fun z hz => (Finset.mem_filter.mp hz).2.1)
    inf_le_right := fun x y =>
      Finset.sup_le (fun z hz => (Finset.mem_filter.mp hz).2.2)
    le_inf := fun x y z hxy hxz =>
      Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxy, hxz⟩) }

-- [D-0087] endPBot_apply
@[simp] theorem endPBot_apply (x : P) : (⊥ : EndP P) x = (⊥ : P) := rfl
-- [D-0088] endPTop_apply
@[simp] theorem endPTop_apply (x : P) : (⊤ : EndP P) x = (⊤ : P) := rfl

-- [D-0089] endP_top_eq_constHom_top
theorem endP_top_eq_constHom_top : (⊤ : EndP P) = constHom (⊤ : P) := by
  ext x; simp [constHom_apply]

-- [D-0090] orderHomEquivSubtype
def orderHomEquivSubtype {α β : Type*} [Preorder α] [Preorder β] :
    (α →o β) ≃ {f : α → β // Monotone f} where
  toFun f := ⟨f, f.monotone⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-0091] orderHomDecidableLE
instance orderHomDecidableLE {α β : Type*} [Preorder α] [Preorder β] [Fintype α]
    [DecidableRel ((· ≤ ·) : β → β → Prop)] :
    DecidableRel ((· ≤ ·) : (α →o β) → (α →o β) → Prop) := fun f g =>
  decidable_of_iff (∀ x, f x ≤ g x) OrderHom.le_def.symm

-- [D-0092] decMonotone
instance decMonotone {α β : Type*} [Preorder α] [Preorder β] [Fintype α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] [DecidableRel ((· ≤ ·) : β → β → Prop)] :
    DecidablePred (Monotone : (α → β) → Prop) := fun f =>
  inferInstanceAs (Decidable (∀ x y, x ≤ y → f x ≤ f y))

-- [D-0093] endPFintype
instance endPFintype [Fintype P] [DecidableEq P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] : Fintype (EndP P) :=
  haveI _hpi : Fintype (P → P) := Pi.instFintype
  haveI _hsub : Fintype {f : P → P // Monotone f} := Subtype.fintype _
  Fintype.ofEquiv {f : P → P // Monotone f} orderHomEquivSubtype.symm

-- [D-0094] endPDecidableEq
instance endPDecidableEq [Fintype P] [DecidableEq P] : DecidableEq (EndP P) :=
  fun f g => decidable_of_iff ((f : P → P) = g) ⟨fun h => OrderHom.ext f g h, fun h => h ▸ rfl⟩

-- [D-0095] endPBoundedOrder
instance endPBoundedOrder : BoundedOrder (EndP P) := { OrderHom.orderTop, OrderHom.orderBot with }

-- [D-0096] endPDistribLatticeOfLinearOrder
instance endPDistribLatticeOfLinearOrder {Q : Type u} [LinearOrder Q] :
    DistribLattice (EndP Q) :=
  DistribLattice.ofInfSupLe (fun a b c => by
    rw [OrderHom.le_def]
    intro x
    show a x ⊓ (b x ⊔ c x) ≤ a x ⊓ b x ⊔ a x ⊓ c x
    exact inf_sup_le (α := Q))

-- [D-0097] endPId_apply
@[simp] theorem endPId_apply (x : P) : (OrderHom.id : EndP P) x = x := rfl

-- [D-0098] endPId_ne_bot
theorem endPId_ne_bot (hbt : (⊥ : P) ≠ ⊤) : (OrderHom.id : EndP P) ≠ ⊥ := by
  intro h
  have h1 := congrArg (fun f : EndP P => f ⊤) h
  simp only [endPId_apply, endPBot_apply] at h1
  exact hbt h1.symm

-- [D-0099] endPId_ne_top
theorem endPId_ne_top (hbt : (⊥ : P) ≠ ⊤) : (OrderHom.id : EndP P) ≠ ⊤ := by
  intro h
  have h1 := congrArg (fun f : EndP P => f ⊥) h
  simp only [endPId_apply, endPTop_apply] at h1
  exact hbt h1

-- [D-0100] endP_bot_ne_top
theorem endP_bot_ne_top (hbt : (⊥ : P) ≠ ⊤) : (⊥ : EndP P) ≠ (⊤ : EndP P) := by
  intro h
  have h1 := congrArg (fun f : EndP P => f ⊤) h
  simp only [endPBot_apply, endPTop_apply] at h1
  exact hbt h1

-- [D-0101] bot_ne_top_of_nontrivial
theorem bot_ne_top_of_nontrivial [Nontrivial P] : (⊥ : P) ≠ (⊤ : P) := by
  intro heq
  obtain ⟨a, b, hab⟩ := exists_pair_ne P
  have ha : a = (⊥ : P) := by
    have h1 : a ≤ (⊤ : P) := le_top
    rw [← heq] at h1
    exact le_antisymm h1 bot_le
  have hb : b = (⊥ : P) := by
    have h1 : b ≤ (⊤ : P) := le_top
    rw [← heq] at h1
    exact le_antisymm h1 bot_le
  exact hab (ha.trans hb.symm)

-- [D-0102] existsUnique_atom_of_least_nonzero
theorem existsUnique_atom_of_least_nonzero {α : Type u} [Lattice α] [BoundedOrder α]
    {a : α} (ha : a ≠ ⊥) (hle : ∀ b : α, b ≠ ⊥ → a ≤ b) :
    ∃! a' : α, a' ≠ ⊥ ∧ ∀ b : α, b ≠ ⊥ → a' ≤ b :=
  ⟨a, ⟨ha, hle⟩, fun a' ⟨ha', hle'⟩ => le_antisymm (hle' a ha) (hle a' ha')⟩

-- [D-0103] existsUnique_coatom_of_greatest_ne_top
theorem existsUnique_coatom_of_greatest_ne_top {α : Type u} [Lattice α] [BoundedOrder α]
    {a : α} (ha : a ≠ ⊤) (hle : ∀ b : α, b ≠ ⊤ → b ≤ a) :
    ∃! a' : α, a' ≠ ⊤ ∧ ∀ b : α, b ≠ ⊤ → b ≤ a' :=
  ⟨a, ⟨ha, hle⟩, fun a' ⟨ha', hle'⟩ => le_antisymm (hle a' ha') (hle' a ha)⟩

-- [D-0104] endPUniqueAtomCoatom
noncomputable instance endPUniqueAtomCoatom [UniqueAtomCoatom P] :
    UniqueAtomCoatom (EndP P) where
  unique_atom := by
    apply existsUnique_atom_of_least_nonzero (a := spikeHom (atomOf P))
    · intro h
      have h1 : spikeHom (atomOf P) (⊤ : P) = (⊥ : EndP P) ⊤ := congrArg (· ⊤) h
      simp only [spikeHom_apply_top] at h1
      exact atomOf_ne_bot P h1
    · intro f hf
      have hfTop : f ⊤ ≠ ⊥ := by
        intro hcon
        apply hf
        apply OrderHom.ext; funext x
        have hxle : f x ≤ f ⊤ := f.mono le_top
        rw [hcon, le_bot_iff] at hxle
        simpa using hxle
      intro x
      rcases eq_or_ne x ⊤ with hx | hx
      · subst hx; simpa using atomOf_le hfTop
      · simp [spikeHom_apply_of_ne _ hx]
  unique_coatom := by
    apply existsUnique_coatom_of_greatest_ne_top (a := cospikeHom (coatomOf P))
    · intro h
      have h1 : cospikeHom (coatomOf P) (⊥ : P) = (⊤ : EndP P) ⊥ := congrArg (· ⊥) h
      simp only [cospikeHom_apply_bot] at h1
      exact coatomOf_ne_top P h1
    · intro f hf
      have hfBot : f ⊥ ≠ ⊤ := by
        intro hcon
        apply hf
        apply OrderHom.ext; funext x
        have hxle : f ⊥ ≤ f x := f.mono bot_le
        rw [hcon, top_le_iff] at hxle
        simpa using hxle
      intro x
      rcases eq_or_ne x ⊥ with hx | hx
      · subst hx; simpa using coatomOf_le hfBot
      · simp [cospikeHom_apply_of_ne _ hx]

-- [D-0105] coatomOf_endP_eq_cospikeHom
theorem coatomOf_endP_eq_cospikeHom (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] :
    coatomOf (EndP P) = cospikeHom (coatomOf P) := by
  have huniq := (UniqueAtomCoatom.unique_coatom (P := EndP P)).choose_spec.2
  have hprop : cospikeHom (coatomOf P) ≠ (⊤ : EndP P) ∧
      ∀ b : EndP P, b ≠ ⊤ → b ≤ cospikeHom (coatomOf P) := by
    constructor
    · intro h
      have h1 : cospikeHom (coatomOf P) (⊥ : P) = (⊤ : EndP P) ⊥ := congrArg (· ⊥) h
      simp only [cospikeHom_apply_bot] at h1
      exact coatomOf_ne_top P h1
    · intro f hf
      have hfBot : f ⊥ ≠ ⊤ := by
        intro hcon
        apply hf
        apply OrderHom.ext; funext x
        have hxle : f ⊥ ≤ f x := f.mono bot_le
        rw [hcon, top_le_iff] at hxle
        simpa using hxle
      intro x
      rcases eq_or_ne x ⊥ with hx | hx
      · subst hx; simpa using coatomOf_le hfBot
      · simp [cospikeHom_apply_of_ne _ hx]
  exact (huniq (cospikeHom (coatomOf P)) hprop).symm

end GeneralLattice

section GraphProduct

-- [D-0106] Graph
structure Graph (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {a b}, adj a b → adj b a
  irrefl : ∀ a, ¬ adj a a

-- [D-0107] prodGraph
def prodGraph {V W : Type u} (G : Graph V) (H : Graph W) : Graph (V × W) where
  adj p q :=
    (p.1 = q.1 ∧ H.adj p.2 q.2) ∨ (p.2 = q.2 ∧ G.adj p.1 q.1)
  symm := by
    rintro ⟨v1, w1⟩ ⟨v2, w2⟩ (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl ⟨rfl, H.symm h⟩
    · exact Or.inr ⟨rfl, G.symm h⟩
  irrefl := by
    rintro ⟨v, w⟩ (⟨_, h⟩ | ⟨_, h⟩)
    · exact H.irrefl w h
    · exact G.irrefl v h

-- [D-0108] Graph.Connected
def Graph.Connected {V : Type u} (G : Graph V) : Prop :=
  ∀ a b : V, Relation.ReflTransGen G.adj a b

-- [D-0109] connected_no_isolated
theorem connected_no_isolated {V : Type u} (G : Graph V) (hconn : G.Connected)
    (a1 a2 : V) (hne : a1 ≠ a2) (v : V) : ∃ w, G.adj v w := by
  have hu : ∃ u, u ≠ v := by
    by_cases h : a1 = v
    · exact ⟨a2, by intro h2; exact hne (h.trans h2.symm)⟩
    · exact ⟨a1, h⟩
  obtain ⟨u, huv⟩ := hu
  rcases (hconn v u).cases_head with h | ⟨c, hvc, _⟩
  · exact absurd h.symm huv
  · exact ⟨c, hvc⟩

-- [D-0110] GraphPrime
def GraphPrime {V : Type u} (G : Graph V) : Prop :=
  ∀ {A B : Type u} (GA : Graph A) (GB : Graph B) (e : V ≃ A × B),
    (∀ v w, G.adj v w ↔ (prodGraph GA GB).adj (e v) (e w)) →
    GA.Connected → GB.Connected →
    (∃ a1 a2 : A, a1 ≠ a2) → (∃ b1 b2 : B, b1 ≠ b2) →
    False

-- [D-0111] hasse_prime_of_degree_one
theorem hasse_prime_of_degree_one {V : Type u} (G : Graph V)
    (v0 : V) (hdeg1 : ∀ w, G.adj v0 w → ∀ w', G.adj v0 w' → w = w')
    (_hnonempty : ∃ w, G.adj v0 w) :
    GraphPrime G := by
  intro A B GA GB e hadj hconnA hconnB hAnt hBnt
  obtain ⟨a1, a2, hAne⟩ := hAnt
  obtain ⟨b1, b2, hBne⟩ := hBnt
  set a0 := (e v0).1 with ha0def
  set b0 := (e v0).2 with hb0def
  obtain ⟨a', hAadj⟩ := connected_no_isolated GA hconnA a1 a2 hAne a0
  obtain ⟨b', hBadj⟩ := connected_no_isolated GB hconnB b1 b2 hBne b0
  have haa' : a' ≠ a0 := fun h => GA.irrefl a0 (h ▸ hAadj)
  set w1 := e.symm (a', b0) with hw1def
  set w2 := e.symm (a0, b') with hw2def
  have hw1ev : e w1 = (a', b0) := by rw [hw1def]; simp
  have hw2ev : e w2 = (a0, b') := by rw [hw2def]; simp
  have hev0 : e v0 = (a0, b0) := by rw [ha0def, hb0def]
  have hw1 : G.adj v0 w1 := by
    rw [hadj v0 w1, hev0, hw1ev]
    exact Or.inr ⟨rfl, hAadj⟩
  have hw2 : G.adj v0 w2 := by
    rw [hadj v0 w2, hev0, hw2ev]
    exact Or.inl ⟨rfl, hBadj⟩
  have hne : w1 ≠ w2 := by
    intro h
    apply haa'
    have heq : e w1 = e w2 := by rw [h]
    rw [hw1ev, hw2ev] at heq
    exact (Prod.mk.injEq .. ▸ heq).1
  exact hne (hdeg1 w1 hw1 w2 hw2)

end GraphProduct

section PhiConstruction

variable {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

-- [D-0112] GlueBase
abbrev GlueBase (P : Type u) := P ⊕ P ⊕ P

-- [D-0113] tagA
def tagA (x : P) : GlueBase P := Sum.inl x
-- [D-0114] tagB
def tagB (x : P) : GlueBase P := Sum.inr (Sum.inl x)
-- [D-0115] tagC
def tagC (x : P) : GlueBase P := Sum.inr (Sum.inr x)

-- [D-0116] canon
def canon (m : P) : GlueBase P → GlueBase P
  | Sum.inl x => Sum.inl x
  | Sum.inr (Sum.inl x) => if x = ⊥ then Sum.inl m else Sum.inr (Sum.inl x)
  | Sum.inr (Sum.inr x) =>
      if x = ⊥ then Sum.inl ⊤
      else if x = m then Sum.inr (Sum.inl ⊤)
      else Sum.inr (Sum.inr x)

-- [D-0117] canon_idem
theorem canon_idem (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : GlueBase P) :
    canon m (canon m x) = canon m x := by
  cases x with
  | inl x => rfl
  | inr x =>
    cases x with
    | inl x =>
      unfold canon
      by_cases hx : x = ⊥ <;> simp [hx, hm]
    | inr x =>
      unfold canon
      by_cases hx : x = ⊥
      · simp [hx]
      · by_cases hx' : x = m <;> simp [hx, hx', hm, hbt.symm]

-- [D-0118] GlueCar
def GlueCar (m : P) := {x : GlueBase P // canon m x = x}

-- [D-0119] inst-P
instance (m : P) : DecidableEq (GlueCar (P := P) m) := Subtype.instDecidableEq
-- [D-0120] inst-P
instance (m : P) : Fintype (GlueCar (P := P) m) := Subtype.fintype _

-- [D-0121] incl
def incl (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : GlueBase P) : GlueCar (P := P) m :=
  ⟨canon m x, canon_idem m hm hbt x⟩

-- [D-0122] glueCar_bot_ne_top
theorem glueCar_bot_ne_top (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    incl m hm hbt (Sum.inl ⊥) ≠ incl m hm hbt (Sum.inr (Sum.inr ⊤)) := by
  intro h
  have hv := congrArg Subtype.val h
  have h1 : canon m (Sum.inl (⊥ : P)) = Sum.inl ⊥ := rfl
  have h2 : canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr ⊤) := by
    simp only [canon]; rw [if_neg hbt.symm, if_neg hmt.symm]
  simp only [incl, h1, h2] at hv
  simp at hv

-- [D-0123] glueCar_nontrivial
theorem glueCar_nontrivial (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    Nontrivial (GlueCar (P := P) m) :=
  ⟨incl m hm hbt (Sum.inl ⊥), incl m hm hbt (Sum.inr (Sum.inr ⊤)), glueCar_bot_ne_top m hm hmt hbt⟩

-- [D-0124] rawRule
def rawRule (m : P) : GlueBase P → GlueBase P → Prop
  | Sum.inl x, Sum.inl y => x ≤ y
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => x ≤ y
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => x ≤ y
  | Sum.inl x, Sum.inr (Sum.inl _) => x ≤ m
  | Sum.inl _, Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr y) => m ≤ y
  | Sum.inr (Sum.inl _), Sum.inl _ => False
  | Sum.inr (Sum.inr _), Sum.inl _ => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => False

-- [D-0125] occs
def occs (m : P) : GlueBase P → List (GlueBase P)
  | Sum.inl x =>
      if x = m then [Sum.inl x, Sum.inr (Sum.inl ⊥)]
      else if x = ⊤ then [Sum.inl x, Sum.inr (Sum.inr ⊥)]
      else [Sum.inl x]
  | Sum.inr (Sum.inl x) =>
      if x = ⊤ then [Sum.inr (Sum.inl x), Sum.inr (Sum.inr m)]
      else [Sum.inr (Sum.inl x)]
  | Sum.inr (Sum.inr x) => [Sum.inr (Sum.inr x)]

-- [D-0126] self_mem_occs
theorem self_mem_occs (m : P) (x : GlueBase P) : x ∈ occs m x := by
  cases x with
  | inl x => simp only [occs]; split_ifs <;> simp
  | inr x => cases x with
    | inl x => simp only [occs]; split_ifs <;> simp
    | inr x => simp [occs]

-- [D-0127] leGlue
def leGlue (m : P) (x y : GlueBase P) : Prop :=
  ∃ u ∈ occs m x, ∃ v ∈ occs m y, rawRule m u v

-- [D-0128] decRawRule
instance decRawRule (m : P) [DecidableRel ((· ≤ ·) : P → P → Prop)] :
    DecidableRel (rawRule m)
  | Sum.inl x, Sum.inl y => inferInstanceAs (Decidable (x ≤ y))
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => inferInstanceAs (Decidable (x ≤ y))
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => inferInstanceAs (Decidable (x ≤ y))
  | Sum.inl x, Sum.inr (Sum.inl _) => inferInstanceAs (Decidable (x ≤ m))
  | Sum.inl _, Sum.inr (Sum.inr _) => isTrue trivial
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr y) => inferInstanceAs (Decidable (m ≤ y))
  | Sum.inr (Sum.inl _), Sum.inl _ => isFalse (fun h => h)
  | Sum.inr (Sum.inr _), Sum.inl _ => isFalse (fun h => h)
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => isFalse (fun h => h)

-- [D-0129] decLeGlue
instance decLeGlue (m : P) [DecidableRel ((· ≤ ·) : P → P → Prop)] :
    DecidableRel (leGlue m) := fun x y => by unfold leGlue; infer_instance

-- [D-0130] rawRule_trans
theorem rawRule_trans (m : P) {u v w : GlueBase P} (huv : rawRule m u v) (hvw : rawRule m v w) :
    rawRule m u w := by
  cases u with
  | inl x => cases v with
    | inl y => cases w with
      | inl z => exact le_trans huv hvw
      | inr z => cases z with
        | inl _ => exact le_trans huv hvw
        | inr _ => trivial
    | inr y => cases y with
      | inl _ => cases w with
        | inl _ => exact absurd hvw (by simp [rawRule])
        | inr z => cases z with
          | inl _ => exact huv
          | inr _ => trivial
      | inr _ => cases w with
        | inl _ => exact absurd hvw (by simp [rawRule])
        | inr z => cases z with
          | inl _ => exact absurd hvw (by simp [rawRule])
          | inr _ => trivial
  | inr x => cases x with
    | inl x => cases v with
      | inl _ => exact absurd huv (by simp [rawRule])
      | inr y => cases y with
        | inl y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRule])
          | inr z => cases z with
            | inl _ => exact le_trans huv hvw
            | inr _ => exact hvw
        | inr y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRule])
          | inr z => cases z with
            | inl _ => exact absurd hvw (by simp [rawRule])
            | inr _ => exact le_trans huv hvw
    | inr x => cases v with
      | inl _ => exact absurd huv (by simp [rawRule])
      | inr y => cases y with
        | inl _ => exact absurd huv (by simp [rawRule])
        | inr y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRule])
          | inr z => cases z with
            | inl _ => exact absurd hvw (by simp [rawRule])
            | inr _ => exact le_trans huv hvw

-- [D-0131] occs_canon_mem
theorem occs_canon_mem (m : P) (hm : m ≠ ⊥) {x : GlueBase P} (hxc : canon m x = x) :
    ∀ u ∈ occs m x, canon m u = x := by
  cases x with
  | inl vx =>
    intro u hu
    simp only [occs] at hu
    split_ifs at hu <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
      (first | obtain rfl | rfl := hu | subst hu) <;> simp_all [canon]
  | inr vx => cases vx with
    | inl vx =>
      intro u hu
      simp only [occs] at hu
      split_ifs at hu <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
        (first | obtain rfl | rfl := hu | subst hu) <;> simp_all [canon]
    | inr vx =>
      intro u hu
      simp only [occs, List.mem_singleton] at hu
      subst hu; exact hxc

-- [D-0132] leGlue_refl
theorem leGlue_refl (m : P) (x : GlueBase P) : leGlue m x x := by
  cases x with
  | inl x =>
    refine ⟨Sum.inl x, ?_, Sum.inl x, ?_, ?_⟩
    · simp only [occs]; split_ifs <;> simp
    · simp only [occs]; split_ifs <;> simp
    · show x ≤ x; exact le_refl x
  | inr x => cases x with
    | inl x =>
      refine ⟨Sum.inr (Sum.inl x), ?_, Sum.inr (Sum.inl x), ?_, ?_⟩
      · simp only [occs]; split_ifs <;> simp
      · simp only [occs]; split_ifs <;> simp
      · show x ≤ x; exact le_refl x
    | inr x =>
      refine ⟨Sum.inr (Sum.inr x), ?_, Sum.inr (Sum.inr x), ?_, ?_⟩
      · simp [occs]
      · simp [occs]
      · show x ≤ x; exact le_refl x

-- [D-0133] inst-P
instance (m : P) : LE (GlueCar (P := P) m) := ⟨fun x y => leGlue m x.1 y.1⟩

-- [D-0134] GlueCar.le_def
theorem GlueCar.le_def (m : P) (x y : GlueCar (P := P) m) : x ≤ y ↔ leGlue m x.1 y.1 := Iff.rfl

section GlueAntisymm
variable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
include hm hmt hbt

-- [D-0135] glue_antisymm
set_option maxHeartbeats 8000000 in
theorem glue_antisymm {x y : GlueBase P} (hxc : canon m x = x) (hyc : canon m y = y)
    (hxy : leGlue m x y) (hyx : leGlue m y x) : x = y := by
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  obtain ⟨u', hu', v', hv', hvu⟩ := hyx
  rcases x with vx | vx | vx <;> rcases y with vy | vy | vy <;>
    simp only [occs, canon] at hxc hyc hu hv hu' hv' ⊢ <;>
    split_ifs at hxc hyc hu hv hu' hv' <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      at hu hv hu' hv' <;>
    (first | obtain rfl | rfl := hu | subst hu) <;>
    (first | obtain rfl | rfl := hv | subst hv) <;>
    (first | obtain rfl | rfl := hu' | subst hu') <;>
    (first | obtain rfl | rfl := hv' | subst hv') <;>
    (try simp_all [rawRule]) <;>
    first
      | rfl
      | exact le_antisymm ‹_ ≤ _› ‹_ ≤ _›
      | exact absurd (le_antisymm huv hvu) (by assumption)
      | exact absurd (le_antisymm huv hvu).symm (by assumption)

-- [D-0136] glue_trans
set_option maxHeartbeats 8000000 in
theorem glue_trans {x y z : GlueBase P} (hxc : canon m x = x) (hyc : canon m y = y)
    (hzc : canon m z = z) (hxy : leGlue m x y) (hyz : leGlue m y z) : leGlue m x z := by
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  obtain ⟨v', hv', w, hw, hvw⟩ := hyz
  have hux : canon m u = x := occs_canon_mem m hm hxc u hu
  have hwz : canon m w = z := occs_canon_mem m hm hzc w hw
  have hu_mem := hu
  have hw_mem := hw
  rcases x with vx | vx | vx <;> rcases y with vy | vy | vy <;> rcases z with vz | vz | vz <;>
    simp only [occs, canon] at hxc hyc hzc hu hv hv' hw hux hwz <;>
    (try split_ifs at hxc hyc hzc hu hv hv' hw hux hwz) <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      at hu hv hv' hw <;>
    (first | obtain rfl | rfl := hu | subst hu) <;>
    (first | obtain rfl | rfl := hv | subst hv) <;>
    (first | obtain rfl | rfl := hv' | subst hv') <;>
    (first | obtain rfl | rfl := hw | subst hw) <;>
    first
      | (refine ⟨_, ?_, _, ?_, rawRule_trans m huv hvw⟩ <;> simp_all [occs] <;> done)
      | (refine ⟨_, ?_, _, ?_, rawRule_trans m huv (rawRule_trans m ?_ hvw)⟩
         · simp_all [occs]; done
         · simp_all [occs]; done
         · simp_all [rawRule]; done)
      | (refine ⟨_, ?_, _, ?_, rawRule_trans m (rawRule_trans m huv ?_) hvw⟩
         · simp_all [occs]; done
         · simp_all [occs]; done
         · simp_all [rawRule]; done)
      | (subst hux; refine ⟨_, ?_, _, ?_, hvw⟩ <;> simp_all [occs] <;> done)
      | (subst hwz; refine ⟨_, ?_, _, ?_, huv⟩ <;> simp_all [occs] <;> done)
      | (refine ⟨_, hu_mem, _, hw_mem, ?_⟩
         simp_all [rawRule] <;> exact le_trans ‹_ ≤ _› ‹_ ≤ _›)
      | (unfold leGlue; simp_all [occs, rawRule])
      | (subst_vars; exact leGlue_refl _ _)
      | fail "glue_trans: a transitivity case fell through. Do not let a fallback absorb it -- fix rawRule/occs or add the case."

-- [D-0137] glueCarPartialOrder
@[reducible]
def glueCarPartialOrder : PartialOrder (GlueCar (P := P) m) where
  le x y := leGlue m x.1 y.1
  le_refl x := leGlue_refl m x.1
  le_trans x y z := glue_trans m hm hmt hbt x.2 y.2 z.2
  le_antisymm x y hxy hyx := Subtype.ext (glue_antisymm m hm hmt hbt x.2 y.2 hxy hyx)

end GlueAntisymm

section PhiSkeleton

-- [D-0138] skelT
abbrev skelT (_m : P) : GlueBase P := Sum.inl ⊥
-- [D-0139] skelG1
abbrev skelG1 (m : P) : GlueBase P := Sum.inl m
-- [D-0140] skelG2
abbrev skelG2 (_m : P) : GlueBase P := Sum.inl ⊤
-- [D-0141] skelL
abbrev skelL (m : P) : GlueBase P := Sum.inr (Sum.inl m)
-- [D-0142] skelG3
abbrev skelG3 (_m : P) : GlueBase P := Sum.inr (Sum.inl ⊤)
-- [D-0143] skelR
abbrev skelR (_m : P) : GlueBase P := Sum.inr (Sum.inr ⊤)

-- [D-0144] iotaA
abbrev iotaA (_m : P) (x : P) : GlueBase P := Sum.inl x
-- [D-0145] iotaB
abbrev iotaB (m : P) (x : P) : GlueBase P := canon m (Sum.inr (Sum.inl x))
-- [D-0146] iotaC
abbrev iotaC (m : P) (x : P) : GlueBase P := canon m (Sum.inr (Sum.inr x))

-- [D-0147] iotaB_canon
theorem iotaB_canon (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) :
    canon m (iotaB m x) = iotaB m x := canon_idem m hm hbt (Sum.inr (Sum.inl x))

-- [D-0148] iotaC_canon
theorem iotaC_canon (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) :
    canon m (iotaC m x) = iotaC m x := canon_idem m hm hbt (Sum.inr (Sum.inr x))

-- [D-0149] skel_t_le_g1
theorem skel_t_le_g1 (m : P) : leGlue m (skelT m) (skelG1 m) :=
  ⟨skelT m, self_mem_occs m _, skelG1 m, self_mem_occs m _, bot_le⟩

-- [D-0150] skel_g1_le_g2
theorem skel_g1_le_g2 (m : P) : leGlue m (skelG1 m) (skelG2 m) :=
  ⟨skelG1 m, self_mem_occs m _, skelG2 m, self_mem_occs m _, le_top⟩

-- [D-0151] skel_g1_le_l
theorem skel_g1_le_l (m : P) : leGlue m (skelG1 m) (skelL m) :=
  ⟨skelG1 m, self_mem_occs m _, skelL m, self_mem_occs m _, le_refl m⟩

-- [D-0152] skel_l_le_g3
theorem skel_l_le_g3 (m : P) : leGlue m (skelL m) (skelG3 m) :=
  ⟨skelL m, self_mem_occs m _, skelG3 m, self_mem_occs m _, le_top⟩

-- [D-0153] skel_g3_le_r
theorem skel_g3_le_r (m : P) : leGlue m (skelG3 m) (skelR m) :=
  ⟨skelG3 m, self_mem_occs m _, skelR m, self_mem_occs m _, le_top⟩

-- [D-0154] skel_g2_le_g3
theorem skel_g2_le_g3 (m : P) : leGlue m (skelG2 m) (skelG3 m) := by
  refine ⟨skelG2 m, self_mem_occs m _, Sum.inr (Sum.inr m), ?_, ?_⟩
  · show Sum.inr (Sum.inr m) ∈ occs m (skelG3 m)
    simp only [occs]
    split_ifs <;> simp
  · trivial

-- [D-0155] skel_not_g2_le_l
theorem skel_not_g2_le_l (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) :
    ¬ leGlue m (skelG2 m) (skelL m) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hv' : v = skelL m := by
    show v = Sum.inr (Sum.inl m)
    have : occs m (Sum.inr (Sum.inl m)) = [Sum.inr (Sum.inl m)] := by
      simp only [occs]; rw [if_neg hmt]
    rw [this] at hv; simpa using hv
  subst hv'
  have hu' : u = skelG2 m ∨ u = Sum.inr (Sum.inr (⊥ : P)) := by
    show u = Sum.inl ⊤ ∨ u = Sum.inr (Sum.inr (⊥ : P))
    have : occs m (Sum.inl (⊤ : P)) = [Sum.inl ⊤, Sum.inr (Sum.inr (⊥ : P))] := by
      simp [occs, hmt.symm]
    rw [this] at hu; simpa using hu
  rcases hu' with hu' | hu' <;> subst hu'
  · exact hmt (le_antisymm le_top huv)
  · exact huv

-- [D-0156] skel_not_l_le_g2
theorem skel_not_l_le_g2 (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) :
    ¬ leGlue m (skelL m) (skelG2 m) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hu' : u = skelL m := by
    show u = Sum.inr (Sum.inl m)
    have : occs m (Sum.inr (Sum.inl m)) = [Sum.inr (Sum.inl m)] := by
      simp only [occs]; rw [if_neg hmt]
    rw [this] at hu; simpa using hu
  subst hu'
  have hv' : v = skelG2 m ∨ v = Sum.inr (Sum.inr (⊥ : P)) := by
    show v = Sum.inl ⊤ ∨ v = Sum.inr (Sum.inr (⊥ : P))
    have : occs m (Sum.inl (⊤ : P)) = [Sum.inl ⊤, Sum.inr (Sum.inr (⊥ : P))] := by
      simp [occs, hmt.symm]
    rw [this] at hv; simpa using hv
  rcases hv' with hv' | hv' <;> subst hv'
  · exact huv
  · exact hm (le_bot_iff.mp huv)

-- [D-0157] skel_t_ne_g1
theorem skel_t_ne_g1 (m : P) (hm : m ≠ ⊥) : skelT m ≠ skelG1 m := by
  simp only [skelT, skelG1]; exact fun h => hm (Sum.inl.inj h).symm

-- [D-0158] skel_g1_ne_g2
theorem skel_g1_ne_g2 (m : P) (hmt : m ≠ ⊤) : skelG1 m ≠ skelG2 m := by
  simp only [skelG1, skelG2]; exact fun h => hmt (Sum.inl.inj h)

-- [D-0159] skel_g1_ne_l
theorem skel_g1_ne_l (m : P) : skelG1 m ≠ skelL m := by
  simp [skelG1, skelL]

-- [D-0160] skel_g2_ne_g3
theorem skel_g2_ne_g3 (m : P) : skelG2 m ≠ skelG3 m := by
  simp [skelG2, skelG3]

-- [D-0161] skel_l_ne_g3
theorem skel_l_ne_g3 (m : P) (hmt : m ≠ ⊤) : skelL m ≠ skelG3 m := by
  simp only [skelL, skelG3]; exact fun h => hmt (Sum.inl.inj (Sum.inr.inj h))

-- [D-0162] skel_g3_ne_r
theorem skel_g3_ne_r (m : P) : skelG3 m ≠ skelR m := by
  simp [skelG3, skelR]

-- [D-0163] skelT_canon
theorem skelT_canon (m : P) : canon m (skelT m) = skelT m := rfl
-- [D-0164] skelG1_canon
theorem skelG1_canon (m : P) : canon m (skelG1 m) = skelG1 m := rfl
-- [D-0165] skelG2_canon
theorem skelG2_canon (m : P) : canon m (skelG2 m) = skelG2 m := rfl

-- [D-0166] skelL_canon
theorem skelL_canon (m : P) (hm : m ≠ ⊥) : canon m (skelL m) = skelL m := by
  show canon m (Sum.inr (Sum.inl m)) = Sum.inr (Sum.inl m)
  simp only [canon]; rw [if_neg hm]

-- [D-0167] skelG3_canon
theorem skelG3_canon (m : P) (hbt : (⊥ : P) ≠ ⊤) : canon m (skelG3 m) = skelG3 m := by
  show canon m (Sum.inr (Sum.inl (⊤ : P))) = Sum.inr (Sum.inl ⊤)
  simp only [canon]; rw [if_neg hbt.symm]

-- [D-0168] skelR_canon
theorem skelR_canon (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    canon m (skelR m) = skelR m := by
  show canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr ⊤)
  simp only [canon]; rw [if_neg hbt.symm, if_neg hmt.symm]

-- [D-0169] skel_not_ge_of_le_ne
theorem skel_not_ge_of_le_ne (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBase P} (hxc : canon m x = x) (hyc : canon m y = y)
    (hxy : leGlue m x y) (hne : x ≠ y) : ¬ leGlue m y x :=
  fun hyx => hne (glue_antisymm m hm hmt hbt hxc hyc hxy hyx)

-- [D-0170] skel_not_g3_le_g2
theorem skel_not_g3_le_g2 (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    ¬ leGlue m (skelG3 m) (skelG2 m) :=
  skel_not_ge_of_le_ne m hm hmt hbt (skelG2_canon m) (skelG3_canon m hbt)
    (skel_g2_le_g3 m) (skel_g2_ne_g3 m)

-- [D-0171] skel_dsi_copyA_le_g2
theorem skel_dsi_copyA_le_g2 (m : P) (v : P) : leGlue m (iotaA m v) (skelG2 m) :=
  ⟨iotaA m v, self_mem_occs m _, skelG2 m, self_mem_occs m _, le_top⟩

-- [D-0172] skel_dsi_copyC_g2_le
theorem skel_dsi_copyC_g2_le (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (v : P) :
    leGlue m (skelG2 m) (iotaC m v) := by
  by_cases hvb : v = ⊥
  · subst hvb
    have hiv : iotaC m (⊥ : P) = skelG2 m := by
      show canon m (Sum.inr (Sum.inr (⊥ : P))) = Sum.inl ⊤
      simp [canon]
    rw [hiv]; exact leGlue_refl m (skelG2 m)
  · by_cases hvm : v = m
    · obtain rfl := hvm.symm
      have hiv : iotaC m m = skelG3 m := by
        show canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤)
        simp [canon, hm]
      rw [hiv]; exact skel_g2_le_g3 m
    · have hiv : iotaC m v = Sum.inr (Sum.inr v) := by
        show canon m (Sum.inr (Sum.inr v)) = Sum.inr (Sum.inr v)
        simp only [canon]; rw [if_neg hvb, if_neg hvm]
      rw [hiv]
      exact ⟨skelG2 m, self_mem_occs m _, Sum.inr (Sum.inr v), self_mem_occs m _, trivial⟩

-- [D-0173] skel_dsi_copyA_not_g2_le
theorem skel_dsi_copyA_not_g2_le (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (v : P) (hv : v ≠ ⊤) : ¬ leGlue m (skelG2 m) (iotaA m v) := by
  by_cases hvm : v = m
  · obtain rfl := hvm.symm
    exact skel_not_ge_of_le_ne m hm hmt hbt (skelG1_canon m) (skelG2_canon m)
      (skel_g1_le_g2 m) (skel_g1_ne_g2 m hmt)
  · rintro ⟨u, hu, v', hv', huv⟩
    have hv''' : v' = Sum.inl v := by
      have : occs m (Sum.inl v) = [Sum.inl v] := by
        simp only [occs]; rw [if_neg hvm, if_neg hv]
      rw [this] at hv'; simpa using hv'
    subst hv'''
    have hu' : u = skelG2 m ∨ u = Sum.inr (Sum.inr (⊥ : P)) := by
      show u = Sum.inl ⊤ ∨ u = Sum.inr (Sum.inr (⊥ : P))
      have : occs m (Sum.inl (⊤ : P)) = [Sum.inl ⊤, Sum.inr (Sum.inr (⊥ : P))] := by
        simp [occs, hmt.symm]
      rw [this] at hu; simpa using hu
    rcases hu' with hu' | hu' <;> subst hu'
    · exact hv (le_antisymm le_top huv)
    · exact huv

-- [D-0174] skel_dsi_copyC_not_le_g2
theorem skel_dsi_copyC_not_le_g2 (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (v : P) (hv : v ≠ ⊥) : ¬ leGlue m (iotaC m v) (skelG2 m) := by
  by_cases hvm : v = m
  ·
    obtain rfl := hvm.symm
    have hiv : iotaC m m = skelG3 m := by
      show canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤)
      simp [canon, hm]
    rw [hiv]
    exact skel_not_g3_le_g2 m hm hmt hbt
  ·
    have hiv : iotaC m v = Sum.inr (Sum.inr v) := by
      show canon m (Sum.inr (Sum.inr v)) = Sum.inr (Sum.inr v)
      simp only [canon]; rw [if_neg hv, if_neg hvm]
    rw [hiv]
    rintro ⟨u, hu, v', hv', huv⟩
    have hu' : u = Sum.inr (Sum.inr v) := by
      have : occs m (Sum.inr (Sum.inr v)) = [Sum.inr (Sum.inr v)] := rfl
      rw [this] at hu; simpa using hu
    subst hu'
    have hv'' : v' = skelG2 m ∨ v' = Sum.inr (Sum.inr (⊥ : P)) := by
      show v' = Sum.inl ⊤ ∨ v' = Sum.inr (Sum.inr (⊥ : P))
      have : occs m (Sum.inl (⊤ : P)) = [Sum.inl ⊤, Sum.inr (Sum.inr (⊥ : P))] := by
        simp [occs, hmt.symm]
      rw [this] at hv'; simpa using hv'
    rcases hv'' with hv'' | hv'' <;> subst hv''
    · exact huv
    · exact hv (le_bot_iff.mp huv)

-- [D-0175] skel_dsi_copyB_incomp
theorem skel_dsi_copyB_incomp (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (v : P)
    (hvb : v ≠ ⊥) (hvt : v ≠ ⊤) :
    ¬ leGlue m (iotaB m v) (skelG2 m) ∧ ¬ leGlue m (skelG2 m) (iotaB m v) := by
  have hiv : iotaB m v = Sum.inr (Sum.inl v) := by
    show canon m (Sum.inr (Sum.inl v)) = Sum.inr (Sum.inl v)
    simp only [canon]; rw [if_neg hvb]
  have hoccs : occs m (Sum.inr (Sum.inl v)) = [Sum.inr (Sum.inl v)] := by
    simp only [occs]; rw [if_neg hvt]
  have hoccsg2 : occs m (Sum.inl (⊤ : P)) = [Sum.inl ⊤, Sum.inr (Sum.inr (⊥ : P))] := by
    simp [occs, hmt.symm]
  constructor
  · rintro ⟨u, hu, v', hv', huv⟩
    rw [hiv, hoccs] at hu
    have hu' : u = Sum.inr (Sum.inl v) := by simpa using hu
    subst hu'
    rw [hoccsg2] at hv'
    have hv'' : v' = skelG2 m ∨ v' = Sum.inr (Sum.inr (⊥ : P)) := by simpa using hv'
    rcases hv'' with hv'' | hv'' <;> subst hv''
    · exact huv
    · exact hm (le_bot_iff.mp huv)
  · rintro ⟨u, hu, v', hv', huv⟩
    rw [hoccsg2] at hu
    have hu' : u = skelG2 m ∨ u = Sum.inr (Sum.inr (⊥ : P)) := by simpa using hu
    rw [hiv, hoccs] at hv'
    have hv''' : v' = Sum.inr (Sum.inl v) := by simpa using hv'
    subst hv'''
    rcases hu' with hu' | hu' <;> subst hu'
    · exact hmt (le_antisymm le_top huv)
    · exact huv

-- [D-0176] occs_inl_mem
theorem occs_inl_mem (m : P) (x : P) {u : GlueBase P} (hu : u ∈ occs m (Sum.inl x)) :
    u = Sum.inl x ∨ (x = m ∧ u = Sum.inr (Sum.inl (⊥ : P))) ∨
      (x = ⊤ ∧ u = Sum.inr (Sum.inr (⊥ : P))) := by
  simp only [occs] at hu
  split_ifs at hu with h1 h2 <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inl ⟨h1, hu⟩)
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inr ⟨h2, hu⟩)
  · exact Or.inl hu

-- [D-0177] tagA_iso
theorem tagA_iso (m : P) (hm : m ≠ ⊥) (x y : P) :
    leGlue m (iotaA m x) (iotaA m y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases occs_inl_mem m x hu with hu' | ⟨hxm, hu'⟩ | ⟨hxt, hu'⟩ <;> subst hu' <;>
      rcases occs_inl_mem m y hv with hv' | ⟨hym, hv'⟩ | ⟨hyt, hv'⟩ <;> subst hv'
    · exact huv
    · obtain rfl := hym.symm; exact huv
    · subst hyt; exact le_top
    · exact huv.elim
    · obtain rfl := hxm.symm; obtain rfl := hym.symm; exact le_refl m
    · exact absurd (le_bot_iff.mp huv) hm
    · exact huv.elim
    · exact huv.elim
    · subst hxt; subst hyt; exact le_refl _
  · intro hxy
    exact ⟨iotaA m x, self_mem_occs m _, iotaA m y, self_mem_occs m _, hxy⟩

-- [D-0178] occs_iotaB_mem
theorem occs_iotaB_mem (m : P) (x : P) {u : GlueBase P} (hu : u ∈ occs m (iotaB m x)) :
    (x ≠ ⊥ ∧ x ≠ ⊤ ∧ u = Sum.inr (Sum.inl x)) ∨
    (x = ⊥ ∧ (u = Sum.inl m ∨ u = Sum.inr (Sum.inl (⊥ : P)))) ∨
    (x = ⊤ ∧ (u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m))) := by
  by_cases hxb : x = ⊥
  · subst hxb
    have hiv : iotaB m (⊥ : P) = Sum.inl m := by
      show canon m (Sum.inr (Sum.inl (⊥ : P))) = Sum.inl m
      simp [canon]
    rw [hiv] at hu
    have hoc : occs m (Sum.inl m) = [Sum.inl m, Sum.inr (Sum.inl (⊥ : P))] := by
      simp [occs]
    rw [hoc] at hu
    exact Or.inr (Or.inl ⟨rfl, by simpa using hu⟩)
  · have hiv : iotaB m x = Sum.inr (Sum.inl x) := by
      show canon m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x)
      simp only [canon]; rw [if_neg hxb]
    rw [hiv] at hu
    by_cases hxt : x = ⊤
    · subst hxt
      have hoc : occs m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by
        simp [occs]
      rw [hoc] at hu
      exact Or.inr (Or.inr ⟨rfl, by simpa using hu⟩)
    · have hoc : occs m (Sum.inr (Sum.inl x)) = [Sum.inr (Sum.inl x)] := by
        simp only [occs]; rw [if_neg hxt]
      rw [hoc] at hu
      exact Or.inl ⟨hxb, hxt, by simpa using hu⟩

-- [D-0179] tagB_iso
theorem tagB_iso (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    leGlue m (iotaB m x) (iotaB m y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases occs_iotaB_mem m x hu with ⟨hxb, hxt, hu'⟩ | ⟨hxb, hu' | hu'⟩ | ⟨hxt, hu' | hu'⟩ <;>
      subst hu' <;>
      rcases occs_iotaB_mem m y hv with ⟨hyb, hyt, hv'⟩ | ⟨hyb, hv' | hv'⟩ | ⟨hyt, hv' | hv'⟩ <;>
        subst hv'
    · exact huv
    · exact huv.elim
    · subst hyb; exact huv
    · subst hyt; exact huv
    · subst hyt; exact le_top
    · subst hxb; exact bot_le
    · subst hxb; subst hyb; exact le_refl _
    · subst hxb; subst hyb; exact le_refl _
    · subst hxb; subst hyt; exact bot_le
    · subst hxb; subst hyt; exact bot_le
    · subst hxb; exact huv
    · exact huv.elim
    · subst hxb; subst hyb; exact huv
    · subst hxb; subst hyt; exact huv
    · subst hxb; subst hyt; exact bot_le
    · subst hxt; exact huv
    · exact huv.elim
    · subst hxt; subst hyb; exact huv
    · subst hxt; subst hyt; exact huv
    · subst hxt; subst hyt; exact le_refl _
    · exact huv.elim
    · exact huv.elim
    · exact huv.elim
    · exact huv.elim
    · subst hxt; subst hyt; exact le_refl _
  · intro hxy
    by_cases hxb : x = ⊥
    · subst hxb
      have hix : iotaB m (⊥ : P) = Sum.inl m := by
        show canon m (Sum.inr (Sum.inl (⊥ : P))) = Sum.inl m
        simp [canon]
      rw [hix]
      by_cases hyb : y = ⊥
      · subst hyb
        rw [hix]
        exact ⟨Sum.inl m, self_mem_occs m _, Sum.inl m, self_mem_occs m _, le_refl m⟩
      · have hiy : iotaB m y = Sum.inr (Sum.inl y) := by
          show canon m (Sum.inr (Sum.inl y)) = Sum.inr (Sum.inl y)
          simp only [canon]; rw [if_neg hyb]
        rw [hiy]
        exact ⟨Sum.inl m, self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, le_refl m⟩
    · have hix : iotaB m x = Sum.inr (Sum.inl x) := by
        show canon m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x)
        simp only [canon]; rw [if_neg hxb]
      rw [hix]
      by_cases hyb : y = ⊥
      · subst hyb
        exact absurd (le_bot_iff.mp hxy) hxb
      · have hiy : iotaB m y = Sum.inr (Sum.inl y) := by
          show canon m (Sum.inr (Sum.inl y)) = Sum.inr (Sum.inl y)
          simp only [canon]; rw [if_neg hyb]
        rw [hiy]
        exact ⟨Sum.inr (Sum.inl x), self_mem_occs m _, Sum.inr (Sum.inl y),
          self_mem_occs m _, hxy⟩

-- [D-0180] occs_iotaC_mem
theorem occs_iotaC_mem (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (x : P) {u : GlueBase P}
    (hu : u ∈ occs m (iotaC m x)) :
    (x ≠ ⊥ ∧ x ≠ m ∧ u = Sum.inr (Sum.inr x)) ∨
    (x = ⊥ ∧ (u = Sum.inl (⊤ : P) ∨ u = Sum.inr (Sum.inr (⊥ : P)))) ∨
    (x = m ∧ (u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m))) := by
  by_cases hxb : x = ⊥
  · subst hxb
    have hiv : iotaC m (⊥ : P) = Sum.inl (⊤ : P) := by
      show canon m (Sum.inr (Sum.inr (⊥ : P))) = Sum.inl ⊤
      simp [canon]
    rw [hiv] at hu
    have hoc : occs m (Sum.inl (⊤ : P)) = [Sum.inl (⊤ : P), Sum.inr (Sum.inr (⊥ : P))] := by
      simp [occs, hmt.symm]
    rw [hoc] at hu
    exact Or.inr (Or.inl ⟨rfl, by simpa using hu⟩)
  · by_cases hxm : x = m
    · obtain rfl := hxm.symm
      have hiv : iotaC m m = Sum.inr (Sum.inl (⊤ : P)) := by
        show canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤)
        simp [canon, hm]
      rw [hiv] at hu
      have hoc : occs m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by
        simp [occs]
      rw [hoc] at hu
      exact Or.inr (Or.inr ⟨rfl, by simpa using hu⟩)
    · have hiv : iotaC m x = Sum.inr (Sum.inr x) := by
        show canon m (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr x)
        simp only [canon]; rw [if_neg hxb, if_neg hxm]
      rw [hiv] at hu
      have hoc : occs m (Sum.inr (Sum.inr x)) = [Sum.inr (Sum.inr x)] := rfl
      rw [hoc] at hu
      exact Or.inl ⟨hxb, hxm, by simpa using hu⟩

-- [D-0181] tagC_iso
theorem tagC_iso (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    leGlue m (iotaC m x) (iotaC m y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases occs_iotaC_mem m hm hmt x hu with ⟨hxb, hxm, hu'⟩ | ⟨hxb, hu' | hu'⟩ | ⟨hxm, hu' | hu'⟩ <;>
      subst hu' <;>
      rcases occs_iotaC_mem m hm hmt y hv with ⟨hyb, hym, hv'⟩ | ⟨hyb, hv' | hv'⟩ | ⟨hym, hv' | hv'⟩ <;>
        subst hv'
    · exact huv
    · exact huv.elim
    · subst hyb; exact huv
    · exact huv.elim
    · obtain rfl := hym.symm; exact huv
    · subst hxb; exact bot_le
    · subst hxb; subst hyb; exact le_refl _
    · subst hxb; subst hyb; exact le_refl _
    · subst hxb; obtain rfl := hym.symm; exact bot_le
    · subst hxb; obtain rfl := hym.symm; exact bot_le
    · subst hxb; exact huv
    · exact huv.elim
    · subst hxb; subst hyb; exact huv
    · exact huv.elim
    · subst hxb; obtain rfl := hym.symm; exact huv
    · obtain rfl := hxm.symm; exact huv
    · exact huv.elim
    · obtain rfl := hxm.symm; subst hyb; exact huv
    · obtain rfl := hxm.symm; obtain rfl := hym.symm; exact le_refl _
    · obtain rfl := hxm.symm; obtain rfl := hym.symm; exact huv
    · obtain rfl := hxm.symm; exact huv
    · exact huv.elim
    · obtain rfl := hxm.symm; subst hyb; exact huv
    · exact huv.elim
    · obtain rfl := hxm.symm; obtain rfl := hym.symm; exact huv
  · intro hxy
    have hCbot : iotaC m (⊥ : P) = Sum.inl (⊤ : P) := by
      show canon m (Sum.inr (Sum.inr (⊥ : P))) = Sum.inl ⊤
      simp [canon]
    have hCm : iotaC m m = Sum.inr (Sum.inl (⊤ : P)) := by
      show canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl ⊤)
      simp [canon, hm]
    have hbotOccs : Sum.inr (Sum.inr (⊥ : P)) ∈ occs m (Sum.inl (⊤ : P)) := by
      simp [occs, hmt.symm]
    have hmOccs : Sum.inr (Sum.inr m) ∈ occs m (Sum.inr (Sum.inl (⊤ : P))) := by
      simp [occs]
    by_cases hxb : x = ⊥
    · subst hxb
      rw [hCbot]
      by_cases hyb : y = ⊥
      · subst hyb; rw [hCbot]; exact leGlue_refl m (Sum.inl (⊤ : P))
      · by_cases hym : y = m
        · obtain rfl := hym.symm
          rw [hCm]
          exact ⟨Sum.inr (Sum.inr (⊥ : P)), hbotOccs, Sum.inr (Sum.inr m), hmOccs, hxy⟩
        · have hiy : iotaC m y = Sum.inr (Sum.inr y) := by
            show canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y)
            simp only [canon]; rw [if_neg hyb, if_neg hym]
          rw [hiy]
          exact ⟨Sum.inl (⊤ : P), self_mem_occs m _, Sum.inr (Sum.inr y),
            self_mem_occs m _, trivial⟩
    · by_cases hxm : x = m
      · obtain rfl := hxm.symm
        rw [hCm]
        by_cases hym : y = m
        · obtain rfl := hym.symm; rw [hCm]; exact leGlue_refl m (Sum.inr (Sum.inl (⊤ : P)))
        · by_cases hyb : y = ⊥
          · subst hyb
            rw [hCbot]
            exact ⟨Sum.inr (Sum.inr m), hmOccs, Sum.inr (Sum.inr (⊥ : P)), hbotOccs, hxy⟩
          · have hiy : iotaC m y = Sum.inr (Sum.inr y) := by
              show canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y)
              simp only [canon]; rw [if_neg hyb, if_neg hym]
            rw [hiy]
            exact ⟨Sum.inr (Sum.inl (⊤ : P)), self_mem_occs m _, Sum.inr (Sum.inr y),
              self_mem_occs m _, hxy⟩
      · have hix : iotaC m x = Sum.inr (Sum.inr x) := by
          show canon m (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr x)
          simp only [canon]; rw [if_neg hxb, if_neg hxm]
        rw [hix]
        by_cases hyb : y = ⊥
        · subst hyb
          rw [hCbot]
          exact ⟨Sum.inr (Sum.inr x), self_mem_occs m _, Sum.inr (Sum.inr (⊥ : P)),
            hbotOccs, hxy⟩
        · by_cases hym : y = m
          · obtain rfl := hym.symm
            rw [hCm]
            exact ⟨Sum.inr (Sum.inr x), self_mem_occs m _, Sum.inr (Sum.inr m), hmOccs, hxy⟩
          · have hiy : iotaC m y = Sum.inr (Sum.inr y) := by
              show canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y)
              simp only [canon]; rw [if_neg hyb, if_neg hym]
            rw [hiy]
            exact ⟨Sum.inr (Sum.inr x), self_mem_occs m _, Sum.inr (Sum.inr y),
              self_mem_occs m _, hxy⟩

-- [D-0182] iotaB_generic_eq
theorem iotaB_generic_eq (m x : P) (hxb : x ≠ ⊥) : iotaB m x = Sum.inr (Sum.inl x) := by
  show canon m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x)
  simp only [canon]; rw [if_neg hxb]

-- [D-0183] iotaC_generic_eq
theorem iotaC_generic_eq (m x : P) (hxb : x ≠ ⊥) (hxm : x ≠ m) :
    iotaC m x = Sum.inr (Sum.inr x) := by
  show canon m (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr x)
  simp only [canon]; rw [if_neg hxb, if_neg hxm]

-- [D-0184] occs_iotaA_generic
theorem occs_iotaA_generic (m x : P) (hxm : x ≠ m) (hxt : x ≠ ⊤) :
    occs m (iotaA m x) = [Sum.inl x] := by
  show occs m (Sum.inl x) = [Sum.inl x]
  simp only [occs]; rw [if_neg hxm, if_neg hxt]

-- [D-0185] occs_iotaB_generic
theorem occs_iotaB_generic (m x : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤) :
    occs m (iotaB m x) = [Sum.inr (Sum.inl x)] := by
  rw [iotaB_generic_eq m x hxb]
  simp only [occs]; rw [if_neg hxt]

-- [D-0186] occs_iotaC_generic
theorem occs_iotaC_generic (m x : P) (hxb : x ≠ ⊥) (hxm : x ≠ m) :
    occs m (iotaC m x) = [Sum.inr (Sum.inr x)] := by
  rw [iotaC_generic_eq m x hxb hxm]; rfl

-- [D-0187] leGlue_iotaA_iotaB_generic
theorem leGlue_iotaA_iotaB_generic (m x y : P) (hxm : x ≠ m) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hyt : y ≠ ⊤) :
    leGlue m (iotaA m x) (iotaB m y) ↔ x ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rw [occs_iotaA_generic m x hxm hxt] at hu
    rw [occs_iotaB_generic m y hyb hyt] at hv
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact huv
  · intro hxy
    refine ⟨Sum.inl x, ?_, Sum.inr (Sum.inl y), ?_, hxy⟩
    · rw [occs_iotaA_generic m x hxm hxt]; simp
    · rw [occs_iotaB_generic m y hyb hyt]; simp

-- [D-0188] leGlue_iotaA_iotaC_generic
theorem leGlue_iotaA_iotaC_generic (m x y : P) (hxm : x ≠ m) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hym : y ≠ m) :
    leGlue m (iotaA m x) (iotaC m y) := by
  refine ⟨Sum.inl x, ?_, Sum.inr (Sum.inr y), ?_, ?_⟩
  · rw [occs_iotaA_generic m x hxm hxt]; simp
  · rw [occs_iotaC_generic m y hyb hym]; simp
  · trivial

-- [D-0189] leGlue_iotaB_iotaC_generic
theorem leGlue_iotaB_iotaC_generic (m x y : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hym : y ≠ m) :
    leGlue m (iotaB m x) (iotaC m y) ↔ m ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rw [occs_iotaB_generic m x hxb hxt] at hu
    rw [occs_iotaC_generic m y hyb hym] at hv
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact huv
  · intro hmy
    refine ⟨Sum.inr (Sum.inl x), ?_, Sum.inr (Sum.inr y), ?_, hmy⟩
    · rw [occs_iotaB_generic m x hxb hxt]; simp
    · rw [occs_iotaC_generic m y hyb hym]; simp

-- [D-0190] not_leGlue_iotaB_iotaA_generic
theorem not_leGlue_iotaB_iotaA_generic (m x y : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤)
    (hym : y ≠ m) (hyt : y ≠ ⊤) :
    ¬ leGlue m (iotaB m x) (iotaA m y) := by
  rintro ⟨u, hu, v, hv, huv⟩
  rw [occs_iotaB_generic m x hxb hxt] at hu
  rw [occs_iotaA_generic m y hym hyt] at hv
  simp only [List.mem_singleton] at hu hv
  subst hu; subst hv
  exact huv.elim

-- [D-0191] not_leGlue_iotaC_iotaA_generic
theorem not_leGlue_iotaC_iotaA_generic (m x y : P) (hxb : x ≠ ⊥) (hxm : x ≠ m)
    (hym : y ≠ m) (hyt : y ≠ ⊤) :
    ¬ leGlue m (iotaC m x) (iotaA m y) := by
  rintro ⟨u, hu, v, hv, huv⟩
  rw [occs_iotaC_generic m x hxb hxm] at hu
  rw [occs_iotaA_generic m y hym hyt] at hv
  simp only [List.mem_singleton] at hu hv
  subst hu; subst hv
  exact huv.elim

-- [D-0192] not_leGlue_iotaC_iotaB_generic
theorem not_leGlue_iotaC_iotaB_generic (m x y : P) (hxb : x ≠ ⊥) (hxm : x ≠ m)
    (hyb : y ≠ ⊥) (hyt : y ≠ ⊤) :
    ¬ leGlue m (iotaC m x) (iotaB m y) := by
  rintro ⟨u, hu, v, hv, huv⟩
  rw [occs_iotaC_generic m x hxb hxm] at hu
  rw [occs_iotaB_generic m y hyb hyt] at hv
  simp only [List.mem_singleton] at hu hv
  subst hu; subst hv
  exact huv.elim

-- [D-0193] leGlue_iotaA_skelG1
theorem leGlue_iotaA_skelG1 (m x : P) (hxm : x ≤ m) : leGlue m (iotaA m x) (skelG1 m) :=
  ⟨iotaA m x, self_mem_occs m _, skelG1 m, self_mem_occs m _, hxm⟩

-- [D-0194] leGlue_skelG1_iotaB
theorem leGlue_skelG1_iotaB (m y : P) (hyb : y ≠ ⊥) (hyt : y ≠ ⊤) :
    leGlue m (skelG1 m) (iotaB m y) := by
  refine ⟨skelG1 m, self_mem_occs m _, iotaB m y, self_mem_occs m _, ?_⟩
  rw [iotaB_generic_eq m y hyb]
  show rawRule m (Sum.inl m) (Sum.inr (Sum.inl y))
  exact le_refl m

-- [D-0195] leGlue_iotaA_skelG2
theorem leGlue_iotaA_skelG2 (m x : P) : leGlue m (iotaA m x) (skelG2 m) :=
  ⟨iotaA m x, self_mem_occs m _, skelG2 m, self_mem_occs m _, le_top⟩

-- [D-0196] leGlue_skelG2_iotaC
theorem leGlue_skelG2_iotaC (m y : P) (hyb : y ≠ ⊥) (hym : y ≠ m) :
    leGlue m (skelG2 m) (iotaC m y) := by
  refine ⟨skelG2 m, self_mem_occs m _, iotaC m y, self_mem_occs m _, ?_⟩
  rw [iotaC_generic_eq m y hyb hym]
  show rawRule m (Sum.inl (⊤ : P)) (Sum.inr (Sum.inr y))
  trivial

-- [D-0197] leGlue_iotaB_skelG3
theorem leGlue_iotaB_skelG3 (m x : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤) :
    leGlue m (iotaB m x) (skelG3 m) := by
  refine ⟨iotaB m x, self_mem_occs m _, skelG3 m, self_mem_occs m _, ?_⟩
  rw [iotaB_generic_eq m x hxb]
  show rawRule m (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl (⊤ : P)))
  exact le_top

-- [D-0198] leGlue_skelG3_iotaC
theorem leGlue_skelG3_iotaC (m y : P) (hm : m ≠ ⊥) (hym : m ≤ y) :
    leGlue m (skelG3 m) (iotaC m y) := by
  have hyb : y ≠ ⊥ := fun h => hm (le_antisymm (h ▸ hym) bot_le)
  have hu : Sum.inr (Sum.inr m) ∈ occs m (skelG3 m) := by
    show Sum.inr (Sum.inr m) ∈ occs m (Sum.inr (Sum.inl (⊤ : P)))
    simp [occs]
  by_cases hym' : y = m
  · obtain rfl := hym'.symm
    have hiv : iotaC m m = skelG3 m := by
      show canon m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P))
      simp [canon, hm]
    rw [hiv]
    exact leGlue_refl m (skelG3 m)
  · rw [iotaC_generic_eq m y hyb hym']
    exact ⟨Sum.inr (Sum.inr m), hu, Sum.inr (Sum.inr y), self_mem_occs m _, hym⟩

-- [D-0199] generic_cross_copy_AB_factors
theorem generic_cross_copy_AB_factors (m x y : P) (hxm : x ≠ m) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hyt : y ≠ ⊤) (h : leGlue m (iotaA m x) (iotaB m y)) :
    leGlue m (iotaA m x) (skelG1 m) ∧ leGlue m (skelG1 m) (iotaB m y) ∧
      skelG1 m ≠ iotaA m x ∧ skelG1 m ≠ iotaB m y := by
  have hxm' : x ≤ m := (leGlue_iotaA_iotaB_generic m x y hxm hxt hyb hyt).mp h
  refine ⟨leGlue_iotaA_skelG1 m x hxm', leGlue_skelG1_iotaB m y hyb hyt, ?_, ?_⟩
  · show (Sum.inl m : GlueBase P) ≠ Sum.inl x
    intro heq
    injection heq with heq2
    exact hxm heq2.symm
  · rw [iotaB_generic_eq m y hyb]
    intro heq
    injection heq

-- [D-0200] generic_cross_copy_AC_factors
theorem generic_cross_copy_AC_factors (m x y : P) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hym : y ≠ m) :
    leGlue m (iotaA m x) (skelG2 m) ∧ leGlue m (skelG2 m) (iotaC m y) ∧
      skelG2 m ≠ iotaA m x ∧ skelG2 m ≠ iotaC m y := by
  refine ⟨leGlue_iotaA_skelG2 m x, leGlue_skelG2_iotaC m y hyb hym, ?_, ?_⟩
  · show (Sum.inl (⊤ : P)) ≠ Sum.inl x
    intro heq
    injection heq with heq2
    exact hxt heq2.symm
  · rw [iotaC_generic_eq m y hyb hym]
    intro heq
    injection heq

-- [D-0201] generic_cross_copy_BC_factors
theorem generic_cross_copy_BC_factors (m x y : P) (hm : m ≠ ⊥) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤)
    (hyb : y ≠ ⊥) (hym : y ≠ m) (h : leGlue m (iotaB m x) (iotaC m y)) :
    leGlue m (iotaB m x) (skelG3 m) ∧ leGlue m (skelG3 m) (iotaC m y) ∧
      skelG3 m ≠ iotaB m x ∧ skelG3 m ≠ iotaC m y := by
  have hmy : m ≤ y := (leGlue_iotaB_iotaC_generic m x y hxb hxt hyb hym).mp h
  refine ⟨leGlue_iotaB_skelG3 m x hxb hxt, leGlue_skelG3_iotaC m y hm hmy, ?_, ?_⟩
  · rw [iotaB_generic_eq m x hxb]
    show (Sum.inr (Sum.inl (⊤ : P)) : GlueBase P) ≠ Sum.inr (Sum.inl x)
    intro heq
    injection heq with heq2
    injection heq2 with heq3
    exact hxt heq3.symm
  · rw [iotaC_generic_eq m y hyb hym]
    intro heq
    injection heq with heq2
    injection heq2

-- [D-0202] not_leGlue_iotaB_iotaA_of_ne_bot
theorem not_leGlue_iotaB_iotaA_of_ne_bot (m x y : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (hxb : x ≠ ⊥) : ¬ leGlue m (iotaB m x) (iotaA m y) := by
  rintro ⟨u, hu, v, hv, huv⟩
  rcases occs_iotaB_mem m x hu with ⟨_, _, hu'⟩ | ⟨hxb', _⟩ | ⟨_, hu' | hu'⟩
  · subst hu'
    rcases occs_inl_mem m y hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
    · exact huv.elim
    · exact absurd (le_bot_iff.mp huv) hxb
    · exact absurd (le_bot_iff.mp huv) hm
  · exact absurd hxb' hxb
  · subst hu'
    rcases occs_inl_mem m y hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
    · exact huv.elim
    · exact hbt (le_antisymm huv bot_le).symm
    · exact absurd (le_bot_iff.mp huv) hm
  · subst hu'
    rcases occs_inl_mem m y hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
    · exact huv.elim
    · exact huv.elim
    · exact absurd (le_bot_iff.mp huv) hm

-- [D-0203] not_leGlue_iotaC_iotaA_of_ne_bot_ne_m
theorem not_leGlue_iotaC_iotaA_of_ne_bot_ne_m (m x y : P) (hm : m ≠ ⊥) (hxb : x ≠ ⊥)
    (hxm : x ≠ m) : ¬ leGlue m (iotaC m x) (iotaA m y) := by
  rintro ⟨u, hu, v, hv, huv⟩
  rw [occs_iotaC_generic m x hxb hxm] at hu
  simp only [List.mem_singleton] at hu
  subst hu
  rcases occs_inl_mem m y hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
  · exact huv.elim
  · exact huv.elim
  · exact absurd (le_bot_iff.mp huv) hxb

-- [D-0204] glueA
def glueA (m : P) (x : P) : GlueCar (P := P) m := ⟨Sum.inl x, rfl⟩

-- [D-0205] glueA_le_iff
theorem glueA_le_iff (m : P) (hm : m ≠ ⊥) (x y : P) : glueA m x ≤ glueA m y ↔ x ≤ y := by
  rw [GlueCar.le_def]; exact tagA_iso m hm x y

-- [D-0206] glueA_injective
theorem glueA_injective (m : P) {x y : P} (h : glueA m x = glueA m y) : x = y := by
  have hv : (Sum.inl x : GlueBase P) = Sum.inl y := congrArg Subtype.val h
  simpa using hv

-- [D-0207] glueA_lt_iff
theorem glueA_lt_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m x < glueA m y ↔ x < y := by
  letI := glueCarPartialOrder m hm hmt hbt
  constructor
  · intro h
    exact ((glueA_le_iff m hm x y).mp h.le).lt_of_ne
      (fun heq => h.ne (congrArg (glueA m) heq))
  · intro h
    exact ((glueA_le_iff m hm x y).mpr h.le).lt_of_ne
      (fun heq => h.ne (glueA_injective m heq))

end PhiSkeleton

section PhiSkeletonSanityChecks

-- [D-0208] example-leGlue
example : leGlue (1 : Fin 3) (skelT 1) (skelG1 (1 : Fin 3)) := by decide
-- [D-0209] example-leGlue
example : leGlue (1 : Fin 3) (skelG1 (1 : Fin 3)) (skelG2 1) := by decide
-- [D-0210] example-Fin
example : ¬ leGlue (1 : Fin 3) (skelG2 1) (skelL (1 : Fin 3)) := by decide
-- [D-0211] example-Fin
example : ¬ leGlue (1 : Fin 3) (skelL (1 : Fin 3)) (skelG2 1) := by decide
-- [D-0212] example-leGlue
example : leGlue (1 : Fin 3) (skelG2 1) (skelG3 (1 : Fin 3)) := by decide
-- [D-0213] example-leGlue
example : leGlue (1 : Fin 3) (skelG3 (1 : Fin 3)) (skelR 1) := by decide

-- [D-0214] example
noncomputable example :
    leGlue (OrderHom.id : Fin 3 →o Fin 3) (skelT OrderHom.id) (skelG1 (OrderHom.id : Fin 3 →o Fin 3)) := by
  decide
-- [D-0215] example
noncomputable example :
    ¬ leGlue (OrderHom.id : Fin 3 →o Fin 3) (skelG2 OrderHom.id) (skelL (OrderHom.id : Fin 3 →o Fin 3)) := by
  decide
-- [D-0216] example
noncomputable example :
    ¬ leGlue (OrderHom.id : Fin 3 →o Fin 3) (skelL OrderHom.id) (skelG2 (OrderHom.id : Fin 3 →o Fin 3)) := by
  decide

-- [D-0217] example-Fin
example : ∀ x y : Fin 3, leGlue (1 : Fin 3) (iotaA 1 x) (iotaA 1 y) ↔ x ≤ y := by decide
-- [D-0218] example-Fin
example : ∀ x y : Fin 3, leGlue (1 : Fin 3) (iotaB 1 x) (iotaB 1 y) ↔ x ≤ y := by decide
-- [D-0219] example-Fin
example : ∀ x y : Fin 3, leGlue (1 : Fin 3) (iotaC 1 x) (iotaC 1 y) ↔ x ≤ y := by decide

end PhiSkeletonSanityChecks

-- [D-0220] glueJoinRaw
def glueJoinRaw (m : P) : GlueBase P → GlueBase P → GlueBase P :=
  letI := latticeDecLE (P := P)
  fun a b => match a, b with
  | Sum.inl x1, Sum.inl x2 => Sum.inl (x1 ⊔ x2)
  | Sum.inr (Sum.inl x1), Sum.inr (Sum.inl x2) => Sum.inr (Sum.inl (x1 ⊔ x2))
  | Sum.inr (Sum.inr x1), Sum.inr (Sum.inr x2) => Sum.inr (Sum.inr (x1 ⊔ x2))
  | Sum.inl _, Sum.inr (Sum.inr x2) => Sum.inr (Sum.inr x2)
  | Sum.inr (Sum.inr x1), Sum.inl _ => Sum.inr (Sum.inr x1)
  | Sum.inl x1, Sum.inr (Sum.inl x2) =>
      if x1 ≤ m then Sum.inr (Sum.inl x2) else Sum.inr (Sum.inr m)
  | Sum.inr (Sum.inl x2), Sum.inl x1 =>
      if x1 ≤ m then Sum.inr (Sum.inl x2) else Sum.inr (Sum.inr m)
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr x2) =>
      if m ≤ x2 then Sum.inr (Sum.inr x2) else Sum.inr (Sum.inr (x2 ⊔ m))
  | Sum.inr (Sum.inr x2), Sum.inr (Sum.inl _) =>
      if m ≤ x2 then Sum.inr (Sum.inr x2) else Sum.inr (Sum.inr (x2 ⊔ m))

-- [D-0221] glueJoin
noncomputable def glueJoin (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x y : GlueCar (P := P) m) :
    GlueCar (P := P) m :=
  ⟨canon m (glueJoinRaw m x.1 y.1), canon_idem m hm hbt _⟩

-- [D-0222] rawRule_bot_left
theorem rawRule_bot_left (m : P) (v : GlueBase P) : rawRule m (Sum.inl ⊥) v := by
  cases v with
  | inl v => show (⊥ : P) ≤ v; exact bot_le
  | inr v => cases v with
    | inl v => show (⊥ : P) ≤ m; exact bot_le
    | inr _ => trivial

-- [D-0223] rawRule_top_right
theorem rawRule_top_right (m : P) (u : GlueBase P) : rawRule m u (Sum.inr (Sum.inr ⊤)) := by
  cases u with
  | inl _ => trivial
  | inr u => cases u with
    | inl u => show m ≤ (⊤ : P); exact le_top
    | inr u => show u ≤ (⊤ : P); exact le_top

-- [D-0224] mem_occs_canon
theorem mem_occs_canon (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (w : GlueBase P) :
    w ∈ occs m (canon m w) := by
  rcases w with x | x | x
  · simp only [canon]; exact self_mem_occs m (Sum.inl x)
  · simp only [canon]
    split_ifs with h
    · subst h; simp only [occs]; split_ifs <;> simp_all
    · exact self_mem_occs m (Sum.inr (Sum.inl x))
  · simp only [canon]
    split_ifs with h1 h2
    · subst h1; simp only [occs]; split_ifs <;> simp_all
    · subst h2; simp only [occs]; split_ifs <;> simp_all
    · exact self_mem_occs m (Sum.inr (Sum.inr x))

-- [D-0225] glueJoin_le_left
theorem glueJoin_le_left (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x y : GlueCar (P := P) m) : x ≤ ⟨(glueJoin m hm hbt x y).1, (glueJoin m hm hbt x y).2⟩ := by
  show leGlue m x.1 (canon m (glueJoinRaw m x.1 y.1))
  refine ⟨x.1, self_mem_occs m x.1, glueJoinRaw m x.1 y.1, mem_occs_canon m hm hmt hbt _, ?_⟩
  obtain ⟨vx, hxc⟩ := x
  obtain ⟨vy, hyc⟩ := y
  simp only
  rcases vx with x1 | x1 | x1 <;> rcases vy with y1 | y1 | y1 <;>
    simp only [glueJoinRaw] <;>
    (try split_ifs) <;>
    simp only [rawRule] <;>
    first
      | exact le_sup_left
      | exact le_sup_right
      | exact le_refl _
      | trivial
      | assumption

-- [D-0226] glueJoin_le_right
theorem glueJoin_le_right (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x y : GlueCar (P := P) m) : y ≤ ⟨(glueJoin m hm hbt x y).1, (glueJoin m hm hbt x y).2⟩ := by
  show leGlue m y.1 (canon m (glueJoinRaw m x.1 y.1))
  refine ⟨y.1, self_mem_occs m y.1, glueJoinRaw m x.1 y.1, mem_occs_canon m hm hmt hbt _, ?_⟩
  obtain ⟨vx, hxc⟩ := x
  obtain ⟨vy, hyc⟩ := y
  simp only
  rcases vx with x1 | x1 | x1 <;> rcases vy with y1 | y1 | y1 <;>
    simp only [glueJoinRaw] <;>
    (try split_ifs) <;>
    simp only [rawRule] <;>
    first
      | exact le_sup_left
      | exact le_sup_right
      | exact le_refl _
      | trivial
      | assumption

-- [D-0227] rawRule_join_le
theorem rawRule_join_le (m : P) {u v w : GlueBase P} (huw : rawRule m u w) (hvw : rawRule m v w) :
    rawRule m (glueJoinRaw m u v) w := by
  cases u with
  | inl x1 => cases v with
    | inl x2 =>
      simp only [glueJoinRaw]
      cases w with
      | inl _ => exact sup_le huw hvw
      | inr y => cases y with
        | inl _ => exact sup_le huw hvw
        | inr _ => trivial
    | inr y0 => cases y0 with
      | inl x2 =>
        simp only [glueJoinRaw]
        split_ifs with hx1
        · exact hvw
        · cases w with
          | inl _ => exact absurd hvw (by simp [rawRule])
          | inr y => cases y with
            | inl _ => exact absurd huw hx1
            | inr _ => exact hvw
      | inr x2 =>
        simp only [glueJoinRaw]
        exact hvw
  | inr x0 => cases x0 with
    | inl x1 => cases v with
      | inl x2 =>
        simp only [glueJoinRaw]
        split_ifs with hx2
        · exact huw
        · cases w with
          | inl _ => exact absurd huw (by simp [rawRule])
          | inr y => cases y with
            | inl _ => exact absurd hvw hx2
            | inr _ => exact huw
      | inr y0 => cases y0 with
        | inl x2 =>
          simp only [glueJoinRaw]
          cases w with
          | inl _ => exact absurd huw (by simp [rawRule])
          | inr y => cases y with
            | inl _ => exact sup_le huw hvw
            | inr _ => exact huw
        | inr x2 =>
          simp only [glueJoinRaw]
          split_ifs with hmx2
          · exact hvw
          · cases w with
            | inl _ => exact absurd hvw (by simp [rawRule])
            | inr y => cases y with
              | inl _ => exact absurd hvw (by simp [rawRule])
              | inr _ => exact sup_le hvw huw
    | inr x1 => cases v with
      | inl x2 =>
        simp only [glueJoinRaw]
        exact huw
      | inr y0 => cases y0 with
        | inl x2 =>
          simp only [glueJoinRaw]
          split_ifs with hmx1
          · exact huw
          · cases w with
            | inl _ => exact absurd huw (by simp [rawRule])
            | inr y => cases y with
              | inl _ => exact absurd huw (by simp [rawRule])
              | inr _ => exact sup_le huw hvw
        | inr x2 =>
          simp only [glueJoinRaw]
          cases w with
          | inl _ => exact absurd huw (by simp [rawRule])
          | inr y => cases y with
            | inl _ => exact absurd huw (by simp [rawRule])
            | inr _ => exact sup_le huw hvw

-- [D-0228] joinTarget
def joinTarget (m : P) : GlueBase P → GlueBase P
  | Sum.inl x =>
      if x = m then Sum.inr (Sum.inl ⊥)
      else if x = ⊤ then Sum.inr (Sum.inr ⊥)
      else Sum.inl x
  | Sum.inr (Sum.inl x) =>
      if x = ⊤ then Sum.inr (Sum.inr m) else Sum.inr (Sum.inl x)
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr x)

-- [D-0229] joinTarget_mem_occs
theorem joinTarget_mem_occs (m : P) (z : GlueBase P) : joinTarget m z ∈ occs m z := by
  cases z with
  | inl x => simp only [joinTarget, occs]; split_ifs <;> simp
  | inr x => cases x with
    | inl x => simp only [joinTarget, occs]; split_ifs <;> simp
    | inr x => simp [joinTarget, occs]

-- [D-0230] rawRule_self_dom
theorem rawRule_self_dom (m : P) {x : GlueBase P} {u q : GlueBase P}
    (hu : u ∈ occs m x) (huq : rawRule m u q) : rawRule m x q := by
  cases x with
  | inl vx =>
    simp only [occs] at hu
    split_ifs at hu <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
      (first | obtain rfl | rfl := hu | subst hu) <;>
      rcases q with y | y | y <;>
      simp_all [rawRule]
  | inr vx => cases vx with
    | inl vx =>
      simp only [occs] at hu
      split_ifs at hu <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
        (first | obtain rfl | rfl := hu | subst hu) <;>
        rcases q with y | y | y <;>
        simp_all [rawRule]
    | inr vx =>
      simp only [occs, List.mem_singleton] at hu
      subst hu
      exact huq

-- [D-0231] rawRule_joinTarget
theorem rawRule_joinTarget (m : P) {p z : GlueBase P} (hpz : leGlue m p z) :
    rawRule m p (joinTarget m z) := by
  obtain ⟨u, hu, w, hw, huw⟩ := hpz
  have hpw : rawRule m p w := rawRule_self_dom m hu huw
  cases z with
  | inl x1 =>
    simp only [occs] at hw
    simp only [joinTarget]
    split_ifs at hw ⊢ <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw <;>
      (first | obtain rfl | rfl := hw | subst hw) <;>
      rcases p with y | y | y <;>
      simp_all [rawRule]
  | inr x0 => cases x0 with
    | inl x1 =>
      simp only [occs] at hw
      simp only [joinTarget]
      split_ifs at hw ⊢ <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw <;>
        (first | obtain rfl | rfl := hw | subst hw) <;>
        rcases p with y | y | y <;>
        simp_all [rawRule]
    | inr x1 =>
      simp only [occs, joinTarget, List.mem_singleton] at hw
      subst hw
      exact hpw

-- [D-0232] le_glueJoin
theorem le_glueJoin (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x y z : GlueCar (P := P) m) : x ≤ z → y ≤ z →
    (⟨(glueJoin m hm hbt x y).1, (glueJoin m hm hbt x y).2⟩) ≤ z := by
  intro hxz hyz
  show leGlue m (canon m (glueJoinRaw m x.1 y.1)) z.1
  have hx' : rawRule m x.1 (joinTarget m z.1) :=
    rawRule_joinTarget m ((GlueCar.le_def m x z).mp hxz)
  have hy' : rawRule m y.1 (joinTarget m z.1) :=
    rawRule_joinTarget m ((GlueCar.le_def m y z).mp hyz)
  exact ⟨glueJoinRaw m x.1 y.1, mem_occs_canon m hm hmt hbt _,
    joinTarget m z.1, joinTarget_mem_occs m z.1, rawRule_join_le m hx' hy'⟩

-- [D-0233] glue_bot_eq
theorem glue_bot_eq (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    ∀ x : GlueCar (P := P) m, leGlue m (Sum.inl ⊥) x.1 := by
  intro x
  exact ⟨Sum.inl ⊥, self_mem_occs m _, x.1, self_mem_occs m x.1, rawRule_bot_left m x.1⟩

-- [D-0234] glue_top_eq
theorem glue_top_eq (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    ∀ x : GlueCar (P := P) m, leGlue m x.1 (canon m (Sum.inr (Sum.inr ⊤))) := by
  have hcanon : canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr (⊤ : P)) := by
    simp only [canon]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h1 hbt.symm | exact absurd h2 hmt.symm
  intro x
  rw [hcanon]
  exact ⟨x.1, self_mem_occs m x.1, Sum.inr (Sum.inr ⊤), self_mem_occs m _, rawRule_top_right m x.1⟩

section PhiLattice

-- [D-0235] glueSemilatticeSup
@[reducible]
noncomputable def glueSemilatticeSup (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    SemilatticeSup (GlueCar (P := P) m) :=
  { glueCarPartialOrder m hm hmt hbt with
    sup := fun x y => glueJoin m hm hbt x y
    le_sup_left := glueJoin_le_left m hm hmt hbt
    le_sup_right := glueJoin_le_right m hm hmt hbt
    sup_le := le_glueJoin m hm hmt hbt }

-- [D-0236] glueOrderBot
@[reducible]
noncomputable def glueOrderBot (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    OrderBot (GlueCar (P := P) m) :=
  letI := glueCarPartialOrder m hm hmt hbt
  { bot := incl m hm hbt (Sum.inl ⊥)
    bot_le := glue_bot_eq m hm hbt }

-- [D-0237] glueOrderTop
@[reducible]
noncomputable def glueOrderTop (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    OrderTop (GlueCar (P := P) m) :=
  letI := glueCarPartialOrder m hm hmt hbt
  { top := incl m hm hbt (Sum.inr (Sum.inr ⊤))
    le_top := glue_top_eq m hm hmt hbt }

-- [D-0238] glueLattice
@[reducible]
noncomputable def glueLattice (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    Lattice (GlueCar (P := P) m) :=
  letI := glueCarPartialOrder m hm hmt hbt
  letI hbot := glueOrderBot m hm hmt hbt
  @latticeOfFiniteSup (GlueCar (P := P) m) _ _ (glueSemilatticeSup m hm hmt hbt) hbot

-- [D-0239] glueBoundedOrder
@[reducible]
noncomputable def glueBoundedOrder (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    BoundedOrder (GlueCar (P := P) m) :=
  letI := glueCarPartialOrder m hm hmt hbt
  { glueOrderBot m hm hmt hbt, glueOrderTop m hm hmt hbt with }

-- [D-0240] glueUniqueAtomCoatom
noncomputable def glueUniqueAtomCoatom (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    [UniqueAtomCoatom P] (hnb : (⊥ : P) ≠ coatomOf P) (hcm : coatomOf P ≠ m) :
    @UniqueAtomCoatom (GlueCar (P := P) m) (glueLattice m hm hmt hbt) (glueBoundedOrder m hm hmt hbt) :=
  @UniqueAtomCoatom.mk (GlueCar (P := P) m) (glueLattice m hm hmt hbt) (glueBoundedOrder m hm hmt hbt)
    (@existsUnique_atom_of_least_nonzero (GlueCar (P := P) m) (glueLattice m hm hmt hbt)
        (glueBoundedOrder m hm hmt hbt) (incl m hm hbt (Sum.inl (atomOf P)))
      (by
        intro h
        apply atomOf_ne_bot P
        have hv := congrArg Subtype.val h
        simp only [incl, canon] at hv
        injection hv)
      (by
        intro b hb
        show leGlue m (Sum.inl (atomOf P)) b.1
        have hb1 : b.1 ≠ Sum.inl (⊥ : P) := by
          intro hcon
          apply hb
          apply Subtype.ext
          show b.1 = canon m (Sum.inl (⊥ : P))
          rw [hcon]; rfl
        rcases hbv : b.1 with y | y | y
        · refine ⟨Sum.inl (atomOf P), self_mem_occs m _, Sum.inl y, self_mem_occs m _, ?_⟩
          show atomOf P ≤ y
          exact atomOf_le fun hy0 => hb1 (hbv.trans (by rw [hy0]))
        · refine ⟨Sum.inl (atomOf P), self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, ?_⟩
          show atomOf P ≤ m; exact atomOf_le hm
        · refine ⟨Sum.inl (atomOf P), self_mem_occs m _, Sum.inr (Sum.inr y), self_mem_occs m _, ?_⟩
          trivial))
    (@existsUnique_coatom_of_greatest_ne_top (GlueCar (P := P) m) (glueLattice m hm hmt hbt)
        (glueBoundedOrder m hm hmt hbt) (incl m hm hbt (Sum.inr (Sum.inr (coatomOf P))))
      (by
        intro h
        apply coatomOf_ne_top P
        have hmem := mem_occs_canon m hm hmt hbt (Sum.inr (Sum.inr (coatomOf P)))
        have hv := congrArg Subtype.val h
        simp only [incl, glueBoundedOrder, glueOrderTop] at hv
        have htop : canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr (⊤ : P)) := by
          simp only [canon]
          split_ifs with h1 h2 <;> first | rfl | exact absurd h1 hbt.symm | exact absurd h2 hmt.symm
        have hv' : canon m (Sum.inr (Sum.inr (coatomOf P))) = Sum.inr (Sum.inr (⊤ : P)) :=
          hv.trans htop
        rw [hv'] at hmem
        simp only [occs, List.mem_singleton] at hmem
        injection hmem with hmem'
        injection hmem')
      (by
        intro b hb
        show leGlue m b.1 (canon m (Sum.inr (Sum.inr (coatomOf P))))
        rw [show canon m (Sum.inr (Sum.inr (coatomOf P))) = Sum.inr (Sum.inr (coatomOf P)) by
          simp only [canon]; rw [if_neg hnb.symm, if_neg hcm]]
        have hb1 : b.1 ≠ Sum.inr (Sum.inr (⊤ : P)) := by
          intro hcon
          apply hb
          apply Subtype.ext
          show b.1 = canon m (Sum.inr (Sum.inr (⊤ : P)))
          rw [hcon]
          simp only [canon]
          split_ifs with h1 h2 <;> first | rfl | exact absurd h1 hbt.symm | exact absurd h2 hmt.symm
        rcases hbv : b.1 with y | y | y
        · refine ⟨Sum.inl y, self_mem_occs m _, Sum.inr (Sum.inr (coatomOf P)), self_mem_occs m _, ?_⟩
          trivial
        · refine ⟨Sum.inr (Sum.inl y), self_mem_occs m _, Sum.inr (Sum.inr (coatomOf P)),
              self_mem_occs m _, ?_⟩
          show m ≤ coatomOf P; exact coatomOf_le hmt
        · refine ⟨Sum.inr (Sum.inr y), self_mem_occs m _, Sum.inr (Sum.inr (coatomOf P)),
              self_mem_occs m _, ?_⟩
          show y ≤ coatomOf P
          exact coatomOf_le fun hy0 => hb1 (hbv.trans (by rw [hy0]))))

end PhiLattice

end PhiConstruction

section PhiSanityChecks

-- [D-0241] example-card
example : Fintype.card (GlueCar (P := Fin 3) 1) = 6 := by decide
-- [D-0242] example-GlueCar
example : ∀ x y : GlueCar (P := Fin 3) 1,
    leGlue 1 x.1 y.1 → leGlue 1 y.1 x.1 → x = y := by decide
-- [D-0243] example-GlueCar
example : ∀ x y z : GlueCar (P := Fin 3) 1,
    leGlue 1 x.1 y.1 → leGlue 1 y.1 z.1 → leGlue 1 x.1 z.1 := by decide

-- [D-0244] example-card
example : Fintype.card (Fin 3 →o Fin 3) = 10 := by decide
-- [D-0245] example-card
noncomputable example : Fintype.card (GlueCar (P := Fin 3 →o Fin 3) (OrderHom.id)) = 27 := by
  decide
-- [D-0246] example
noncomputable example :
    ∀ x y : GlueCar (P := Fin 3 →o Fin 3) (OrderHom.id),
      leGlue OrderHom.id x.1 y.1 → leGlue OrderHom.id y.1 x.1 → x = y := by
  decide
-- [D-0247] example
noncomputable example :
    ∀ x y z : GlueCar (P := Fin 3 →o Fin 3) (OrderHom.id),
      leGlue OrderHom.id x.1 y.1 → leGlue OrderHom.id y.1 z.1 → leGlue OrderHom.id x.1 z.1 := by
  decide

-- [D-0248] example-card
example : Fintype.card (GlueCar (P := Fin 4) 2) = 9 := by decide
-- [D-0249] example-GlueCar
example : ∀ x y : GlueCar (P := Fin 4) 2,
    leGlue 2 x.1 y.1 → leGlue 2 y.1 x.1 → x = y := by decide
-- [D-0250] example-GlueCar
example : ∀ x y z : GlueCar (P := Fin 4) 2,
    leGlue 2 x.1 y.1 → leGlue 2 y.1 z.1 → leGlue 2 x.1 z.1 := by decide

end PhiSanityChecks

-- [D-0251] finThree_rigid
theorem finThree_rigid : Subsingleton (Fin 3 ≃o Fin 3) := by
  constructor
  intro f g
  have key : ∀ h : Fin 3 ≃o Fin 3, h 1 = 1 := by
    intro h
    have hb : h 0 = 0 := h.map_bot
    have ht : h 2 = 2 := h.map_top
    have h01 : h 1 ≠ 0 := fun hh => absurd (h.injective (hh.trans hb.symm)) (by decide)
    have h21 : h 1 ≠ 2 := fun hh => absurd (h.injective (hh.trans ht.symm)) (by decide)
    have keyv : ∀ v : Fin 3, v ≠ 0 → v ≠ 2 → v = 1 := by decide
    exact keyv (h 1) h01 h21
  apply OrderIso.ext
  funext x
  have hf0 : f 0 = 0 := f.map_bot
  have hf2 : f 2 = 2 := f.map_top
  have hg0 : g 0 = 0 := g.map_bot
  have hg2 : g 2 = 2 := g.map_top
  fin_cases x
  · exact hf0.trans hg0.symm
  · exact (key f).trans (key g).symm
  · exact hf2.trans hg2.symm

section JoinIrredInfra
variable {P : Type u} [Lattice P] [OrderBot P] [Fintype P] [DecidableEq P]

-- [D-0252] finite_lattice_eq_sup_joinIrreds
theorem finite_lattice_eq_sup_joinIrreds (a : P) :
    a = (Finset.univ.filter (fun q : P => JoinIrred P q ∧ q ≤ a)).sup id := by
  have hwf : WellFounded ((· < ·) : P → P → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  induction a using hwf.induction with
  | _ a ih =>
    by_cases hbot : a = ⊥
    · subst hbot
      have hempty :
          (Finset.univ.filter (fun q : P => JoinIrred P q ∧ q ≤ (⊥ : P))) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun q _ hq => hq.1.1 (le_bot_iff.mp hq.2))
      rw [hempty, Finset.sup_empty]
    · by_cases hji : JoinIrred P a
      · apply le_antisymm
        · exact Finset.le_sup (f := id)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hji, le_refl a⟩)
        · exact Finset.sup_le (fun q hq => (Finset.mem_filter.mp hq).2.2)
      · have hcontra : ¬ ∀ b c : P, a = b ⊔ c → a = b ∨ a = c :=
          fun hall => hji ⟨hbot, hall⟩
        push_neg at hcontra
        obtain ⟨b, c, habc, hab, hac⟩ := hcontra
        have hb_le : b ≤ a := by rw [habc]; exact le_sup_left
        have hc_le : c ≤ a := by rw [habc]; exact le_sup_right
        have hb_lt : b < a := lt_of_le_of_ne hb_le (fun heq => hab heq.symm)
        have hc_lt : c < a := lt_of_le_of_ne hc_le (fun heq => hac heq.symm)
        have hbeq := ih b hb_lt
        have hceq := ih c hc_lt
        have hsub_le :
            (Finset.univ.filter (fun q : P => JoinIrred P q ∧ q ≤ a)).sup id ≤ a :=
          Finset.sup_le (fun q hq => (Finset.mem_filter.mp hq).2.2)
        have hsupbc :
            b ⊔ c ≤ (Finset.univ.filter (fun q : P => JoinIrred P q ∧ q ≤ a)).sup id := by
          apply sup_le
          · rw [hbeq]
            exact Finset.sup_le (fun q hq => Finset.le_sup (f := id)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2.1,
                (Finset.mem_filter.mp hq).2.2.trans hb_le⟩))
          · rw [hceq]
            exact Finset.sup_le (fun q hq => Finset.le_sup (f := id)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2.1,
                (Finset.mem_filter.mp hq).2.2.trans hc_le⟩))
        have ha_le : a ≤ (Finset.univ.filter (fun q : P => JoinIrred P q ∧ q ≤ a)).sup id := by
          rwa [← habc] at hsupbc
        exact le_antisymm ha_le hsub_le

-- [D-0253] eq_of_joinIrred_le_iff
theorem eq_of_joinIrred_le_iff {a b : P}
    (h : ∀ q : P, JoinIrred P q → (q ≤ a ↔ q ≤ b)) : a = b := by
  apply le_antisymm
  · rw [finite_lattice_eq_sup_joinIrreds a]
    exact Finset.sup_le (fun q hq =>
      (h q (Finset.mem_filter.mp hq).2.1).mp (Finset.mem_filter.mp hq).2.2)
  · rw [finite_lattice_eq_sup_joinIrreds b]
    exact Finset.sup_le (fun q hq =>
      (h q (Finset.mem_filter.mp hq).2.1).mpr (Finset.mem_filter.mp hq).2.2)

-- [D-0254] orderIso_eq_id_of_fixes_joinIrred
theorem orderIso_eq_id_of_fixes_joinIrred {θ : P ≃o P}
    (hfix : ∀ q : P, JoinIrred P q → θ q = q) : ∀ a : P, θ a = a := by
  have hfix' : ∀ q : P, JoinIrred P q → θ.symm q = q := by
    intro q hq
    calc θ.symm q = θ.symm (θ q) := by rw [hfix q hq]
      _ = q := θ.symm_apply_apply q
  intro a
  apply eq_of_joinIrred_le_iff
  intro q hq
  constructor
  · intro hqθa
    have h1 : θ.symm q ≤ θ.symm (θ a) := θ.symm.monotone hqθa
    rwa [hfix' q hq, θ.symm_apply_apply] at h1
  · intro hqa
    have h1 : θ q ≤ θ a := θ.monotone hqa
    rwa [hfix q hq] at h1

-- [D-0255] orderIso_eq_of_joinIrred_eq
theorem orderIso_eq_of_joinIrred_eq {φ ψ : P ≃o P}
    (h : ∀ q : P, JoinIrred P q → φ q = ψ q) : φ = ψ := by
  have hfix : ∀ q : P, JoinIrred P q → (ψ.trans φ.symm) q = q := by
    intro q hq
    show φ.symm (ψ q) = q
    rw [← h q hq, φ.symm_apply_apply]
  have hid := orderIso_eq_id_of_fixes_joinIrred hfix
  apply OrderIso.ext
  funext a
  have ha : φ.symm (ψ a) = a := hid a
  have hb : φ (φ.symm (ψ a)) = φ a := congrArg φ ha
  rw [φ.apply_symm_apply] at hb
  exact hb.symm

end JoinIrredInfra

section GapMoves
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0256] Covers
def Covers {α : Type*} [Preorder α] (a b : α) : Prop :=
  a < b ∧ ∀ c, a < c → ¬ c < b

-- [D-0257] lowerAtBot
def lowerAtBot (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) : EndP P where
  toFun y := if y = ⊥ then w else f y
  monotone' := by
    intro y1 y2 hy
    by_cases h1 : y1 = ⊥
    · by_cases h2 : y2 = ⊥
      · rw [h1, h2]
      · show (if y1 = ⊥ then w else f y1) ≤ (if y2 = ⊥ then w else f y2)
        rw [if_pos h1, if_neg h2]
        calc w ≤ f ⊥ := hw_le
          _ ≤ f y2 := f.monotone (by rw [← h1]; exact hy)
    · by_cases h2 : y2 = ⊥
      · exact absurd (le_antisymm (by rw [← h2]; exact hy) bot_le) h1
      · show (if y1 = ⊥ then w else f y1) ≤ (if y2 = ⊥ then w else f y2)
        rw [if_neg h1, if_neg h2]
        exact f.monotone hy

-- [D-0258] raiseAtTop
def raiseAtTop (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') : EndP P where
  toFun y := if y = ⊤ then v' else f y
  monotone' := by
    intro y1 y2 hy
    by_cases h1 : y1 = ⊤
    · by_cases h2 : y2 = ⊤
      · rw [h1, h2]
      · exact absurd (le_antisymm (by rw [← h1]; exact hy) le_top).symm h2
    · by_cases h2 : y2 = ⊤
      · show (if y1 = ⊤ then v' else f y1) ≤ (if y2 = ⊤ then v' else f y2)
        rw [if_neg h1, if_pos h2]
        calc f y1 ≤ f ⊤ := f.monotone le_top
          _ ≤ v' := hv_ge
      · show (if y1 = ⊤ then v' else f y1) ≤ (if y2 = ⊤ then v' else f y2)
        rw [if_neg h1, if_neg h2]
        exact f.monotone hy

-- [D-0259] lowerAtBot_apply_bot
theorem lowerAtBot_apply_bot (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) :
    lowerAtBot f w hw_le ⊥ = w := by
  show (if (⊥ : P) = ⊥ then w else f ⊥) = w
  rw [if_pos rfl]

-- [D-0260] lowerAtBot_apply_ne
theorem lowerAtBot_apply_ne (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) {y : P} (hy : y ≠ ⊥) :
    lowerAtBot f w hw_le y = f y := by
  show (if y = ⊥ then w else f y) = f y
  rw [if_neg hy]

-- [D-0261] raiseAtTop_apply_top
theorem raiseAtTop_apply_top (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') :
    raiseAtTop f v' hv_ge ⊤ = v' := by
  show (if (⊤ : P) = ⊤ then v' else f ⊤) = v'
  rw [if_pos rfl]

-- [D-0262] raiseAtTop_apply_ne
theorem raiseAtTop_apply_ne (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') {y : P} (hy : y ≠ ⊤) :
    raiseAtTop f v' hv_ge y = f y := by
  show (if y = ⊤ then v' else f y) = f y
  rw [if_neg hy]

-- [D-0263] lowerAtBot_ne
theorem lowerAtBot_ne (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) (hne : w ≠ f ⊥) :
    lowerAtBot f w hw_le ≠ f := by
  intro heq
  apply hne
  have h1 : (lowerAtBot f w hw_le) ⊥ = f ⊥ := by rw [heq]
  rwa [lowerAtBot_apply_bot] at h1

-- [D-0264] lowerAtBot_le
theorem lowerAtBot_le (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) : lowerAtBot f w hw_le ≤ f := by
  rw [OrderHom.le_def]
  intro y
  by_cases hy : y = ⊥
  · rw [hy, lowerAtBot_apply_bot]; exact hw_le
  · rw [lowerAtBot_apply_ne f w hw_le hy]

-- [D-0265] lowerAtBot_lt
theorem lowerAtBot_lt (f : EndP P) (w : P) (hw_le : w ≤ f ⊥) (hlt : w < f ⊥) :
    lowerAtBot f w hw_le < f :=
  lt_of_le_of_ne (lowerAtBot_le f w hw_le) (lowerAtBot_ne f w hw_le hlt.ne)

-- [D-0266] raiseAtTop_ne
theorem raiseAtTop_ne (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') (hne : f ⊤ ≠ v') :
    f ≠ raiseAtTop f v' hv_ge := by
  intro heq
  apply hne
  have h1 : f ⊤ = (raiseAtTop f v' hv_ge) ⊤ := congrArg (· ⊤) heq
  rwa [raiseAtTop_apply_top] at h1

-- [D-0267] raiseAtTop_le
theorem raiseAtTop_le (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') : f ≤ raiseAtTop f v' hv_ge := by
  rw [OrderHom.le_def]
  intro y
  by_cases hy : y = ⊤
  · rw [hy, raiseAtTop_apply_top]; exact hv_ge
  · rw [raiseAtTop_apply_ne f v' hv_ge hy]

-- [D-0268] raiseAtTop_lt
theorem raiseAtTop_lt (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v') (hlt : f ⊤ < v') :
    f < raiseAtTop f v' hv_ge :=
  lt_of_le_of_ne (raiseAtTop_le f v' hv_ge) (raiseAtTop_ne f v' hv_ge hlt.ne)

-- [D-0269] covers_lowerAtBot
theorem covers_lowerAtBot (f : EndP P) (w : P) (hw_le : w ≤ f ⊥)
    (hcov : Covers w (f ⊥)) : Covers (lowerAtBot f w hw_le) f := by
  refine ⟨lowerAtBot_lt f w hw_le hcov.1, ?_⟩
  intro h hgh hhf
  have hle1 : ∀ y, lowerAtBot f w hw_le y ≤ h y := OrderHom.le_def.mp hgh.le
  have hle2 : ∀ y, h y ≤ f y := OrderHom.le_def.mp hhf.le
  have hagree : ∀ y, y ≠ ⊥ → h y = f y := by
    intro y hy
    have h1 := hle1 y
    rw [lowerAtBot_apply_ne f w hw_le hy] at h1
    exact le_antisymm (hle2 y) h1
  have hx0_1 : w ≤ h ⊥ := by
    have := hle1 ⊥
    rwa [lowerAtBot_apply_bot] at this
  have hx0_2 : h ⊥ ≤ f ⊥ := hle2 ⊥
  have hcase : h ⊥ = w ∨ h ⊥ = f ⊥ := by
    rcases eq_or_lt_of_le hx0_1 with heq | hlt
    · exact Or.inl heq.symm
    · right
      exact hx0_2.lt_or_eq.resolve_left (hcov.2 (h ⊥) hlt)
  rcases hcase with hc | hc
  · have heq : h = lowerAtBot f w hw_le := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = ⊥
      · rw [hy, hc, lowerAtBot_apply_bot]
      · rw [hagree y hy, lowerAtBot_apply_ne f w hw_le hy]
    rw [heq] at hgh
    exact lt_irrefl _ hgh
  · have heq : h = f := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = ⊥
      · rw [hy, hc]
      · exact hagree y hy
    rw [heq] at hhf
    exact lt_irrefl _ hhf

-- [D-0270] covers_raiseAtTop
theorem covers_raiseAtTop (f : EndP P) (v' : P) (hv_ge : f ⊤ ≤ v')
    (hcov : Covers (f ⊤) v') : Covers f (raiseAtTop f v' hv_ge) := by
  refine ⟨raiseAtTop_lt f v' hv_ge hcov.1, ?_⟩
  intro h hfh hhr
  have hle1 : ∀ y, f y ≤ h y := OrderHom.le_def.mp hfh.le
  have hle2 : ∀ y, h y ≤ raiseAtTop f v' hv_ge y := OrderHom.le_def.mp hhr.le
  have hagree : ∀ y, y ≠ ⊤ → h y = f y := by
    intro y hy
    have h2 := hle2 y
    rw [raiseAtTop_apply_ne f v' hv_ge hy] at h2
    exact le_antisymm h2 (hle1 y)
  have hx0_1 : h ⊤ ≤ v' := by
    have := hle2 ⊤
    rwa [raiseAtTop_apply_top] at this
  have hx0_2 : f ⊤ ≤ h ⊤ := hle1 ⊤
  have hcase : h ⊤ = f ⊤ ∨ h ⊤ = v' := by
    rcases eq_or_lt_of_le hx0_2 with heq | hlt
    · exact Or.inl heq.symm
    · right
      exact hx0_1.lt_or_eq.resolve_left (hcov.2 (h ⊤) hlt)
  rcases hcase with hc | hc
  · have heq : h = f := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = ⊤
      · rw [hy, hc]
      · exact hagree y hy
    rw [heq] at hfh
    exact lt_irrefl _ hfh
  · have heq : h = raiseAtTop f v' hv_ge := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = ⊤
      · rw [hy, hc, raiseAtTop_apply_top]
      · rw [hagree y hy, raiseAtTop_apply_ne f v' hv_ge hy]
    rw [heq] at hhr
    exact lt_irrefl _ hhr

-- [D-0271] gap1_second_cover
theorem gap1_second_cover (v w v' : P) (hbt : (⊥ : P) ≠ ⊤)
    (hw : Covers w v) (hv' : Covers v v') :
    ∃ g g2 : EndP P, Covers g (constHom v) ∧ Covers g g2 ∧ constHom v ≠ g2 := by
  have hw_le : w ≤ (constHom v : EndP P) ⊥ := by rw [constHom_apply]; exact hw.1.le
  have hcovw : Covers w ((constHom v : EndP P) ⊥) := by rw [constHom_apply]; exact hw
  set g : EndP P := lowerAtBot (constHom v) w hw_le with hgdef
  have hcov1 : Covers g (constHom v) := covers_lowerAtBot (constHom v) w hw_le hcovw
  have hg_top : g ⊤ = v := by
    rw [hgdef, lowerAtBot_apply_ne (constHom v) w hw_le hbt.symm, constHom_apply]
  have hv_ge : g ⊤ ≤ v' := by rw [hg_top]; exact hv'.1.le
  have hcovv' : Covers (g ⊤) v' := by rw [hg_top]; exact hv'
  set g2 : EndP P := raiseAtTop g v' hv_ge with hg2def
  have hcov2 : Covers g g2 := covers_raiseAtTop g v' hv_ge hcovv'
  refine ⟨g, g2, hcov1, hcov2, ?_⟩
  intro heq
  have h1 : (constHom v : EndP P) ⊤ = g2 ⊤ := by rw [heq]
  rw [constHom_apply, hg2def, raiseAtTop_apply_top] at h1
  exact hv'.1.ne h1

end GapMoves

section JConstruction
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0272] Graph.Hasse
def Graph.Hasse (P : Type u) [Preorder P] : Graph P where
  adj a b := Covers a b ∨ Covers b a
  symm := fun h => h.symm
  irrefl := fun a h => h.elim (fun hc => hc.1.ne rfl) (fun hc => hc.1.ne rfl)

-- [D-0273] decidableJoinIrred
noncomputable instance decidableJoinIrred : DecidablePred (JoinIrred P) :=
  Classical.decPred _

-- [D-0274] JSub
def JSub (P : Type u) [Lattice P] [OrderBot P] : Type u := {a : P // JoinIrred P a}

-- [D-0275] inst-Fintype
noncomputable instance : Fintype (JSub P) := Subtype.fintype _
-- [D-0276] inst-DecidableEq
noncomputable instance : DecidableEq (JSub P) := Classical.decEq _

-- [D-0277] stepMap
def stepMap (x q : P) : EndP P :=
  letI := latticeDecLE (P := P)
  { toFun := fun y => if q ≤ y then x else ⊥
    monotone' := by
      intro y z hyz
      by_cases hqy : q ≤ y
      · have hqz : q ≤ z := hqy.trans hyz
        simp only [if_pos hqy, if_pos hqz]; exact le_refl _
      · by_cases hqz : q ≤ z
        · simp only [if_neg hqy, if_pos hqz]; exact bot_le
        · simp only [if_neg hqy, if_neg hqz]; exact le_refl _ }

-- [D-0278] stepMap_apply_of_ge
@[simp] theorem stepMap_apply_of_ge (x q : P) {y : P} (h : q ≤ y) :
    stepMap x q y = x := if_pos h

-- [D-0279] stepMap_apply_of_not_ge
@[simp] theorem stepMap_apply_of_not_ge (x q : P) {y : P} (h : ¬ q ≤ y) :
    stepMap x q y = ⊥ := if_neg h

-- [D-0280] stepMap_apply_self
@[simp] theorem stepMap_apply_self (x q : P) : stepMap x q q = x :=
  stepMap_apply_of_ge x q le_rfl

end JConstruction

-- [D-0281] covers_prod_iff
theorem covers_prod_iff {P L : Type u} [PartialOrder P] [PartialOrder L]
    (a a' : P) (b b' : L) :
    Covers (a, b) (a', b') ↔
      (a = a' ∧ Covers b b') ∨ (b = b' ∧ Covers a a') := by
  have hlt_iff : ∀ (x1 : P) (y1 : L) (x2 : P) (y2 : L),
      (x1, y1) < (x2, y2) ↔ (x1 < x2 ∧ y1 ≤ y2) ∨ (x1 ≤ x2 ∧ y1 < y2) := by
    intro x1 y1 x2 y2
    rw [Prod.lt_iff]
  constructor
  · rintro ⟨hlt, hcov⟩
    have hle : a ≤ a' ∧ b ≤ b' := Prod.le_def.mp hlt.le
    have hne : (a, b) ≠ (a', b') := hlt.ne
    by_cases haeq : a = a'
    · subst haeq
      left
      refine ⟨rfl, ?_⟩
      have hbne : b ≠ b' := fun h => hne (by rw [h])
      have hblt : b < b' := lt_of_le_of_ne hle.2 hbne
      refine ⟨hblt, ?_⟩
      intro c2 hc1' hc2'
      exact hcov (a, c2) ((hlt_iff a b a c2).mpr (Or.inr ⟨le_refl a, hc1'⟩))
        ((hlt_iff a c2 a b').mpr (Or.inr ⟨le_refl a, hc2'⟩))
    · right
      have halt : a < a' := lt_of_le_of_ne hle.1 haeq
      have hbeq : b = b' := by
        by_contra hbne
        have hblt : b < b' := lt_of_le_of_ne hle.2 hbne
        exact hcov (a', b) ((hlt_iff a b a' b).mpr (Or.inl ⟨halt, le_refl b⟩))
          ((hlt_iff a' b a' b').mpr (Or.inr ⟨le_refl a', hblt⟩))
      refine ⟨hbeq, halt, ?_⟩
      intro c1 hc1' hc2'
      exact hcov (c1, b) ((hlt_iff a b c1 b).mpr (Or.inl ⟨hc1', le_refl b⟩))
        (by rw [← hbeq]; exact (hlt_iff c1 b a' b).mpr (Or.inl ⟨hc2', le_refl b⟩))
  · rintro (⟨haeq, hbcov⟩ | ⟨hbeq, hacov⟩)
    · subst haeq
      constructor
      · exact (hlt_iff a b a b').mpr (Or.inr ⟨le_refl a, hbcov.1⟩)
      · rintro ⟨c1, c2⟩ hc1 hc2
        rw [hlt_iff] at hc1 hc2
        rcases hc1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
          rcases hc2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact lt_irrefl a (h1a.trans h2a)
        · exact lt_irrefl a (h1a.trans_le h2a)
        · exact lt_irrefl a (h1a.trans_lt h2a)
        · exact hbcov.2 c2 h1b h2b
    · subst hbeq
      constructor
      · exact (hlt_iff a b a' b).mpr (Or.inl ⟨hacov.1, le_refl b⟩)
      · rintro ⟨c1, c2⟩ hc1 hc2
        rw [hlt_iff] at hc1 hc2
        rcases hc1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
          rcases hc2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact hacov.2 c1 h1a h2a
        · exact lt_irrefl b (h1b.trans_lt h2b)
        · exact lt_irrefl b (h1b.trans_le h2b)
        · exact lt_irrefl b (h1b.trans h2b)

section StepMapCharacterization
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0282] stepMap_join
theorem stepMap_join (x1 x2 q : P) :
    (stepMap x1 q : EndP P) ⊔ stepMap x2 q = stepMap (x1 ⊔ x2) q := by
  apply OrderHom.ext
  funext y
  show (stepMap x1 q : EndP P) y ⊔ (stepMap x2 q : EndP P) y = (stepMap (x1 ⊔ x2) q : EndP P) y
  by_cases hqy : q ≤ y
  · rw [stepMap_apply_of_ge x1 q hqy, stepMap_apply_of_ge x2 q hqy, stepMap_apply_of_ge (x1 ⊔ x2) q hqy]
  · rw [stepMap_apply_of_not_ge x1 q hqy, stepMap_apply_of_not_ge x2 q hqy,
        stepMap_apply_of_not_ge (x1 ⊔ x2) q hqy, sup_idem]

-- [D-0283] exists_mem_eq_of_joinIrred_sup
theorem exists_mem_eq_of_joinIrred_sup {L : Type*} [Lattice L] [OrderBot L]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → L) {a : L}
    (ha : JoinIrred L a) (heq : a = s.sup g) : ∃ i ∈ s, a = g i := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sup_empty] at heq; exact absurd heq ha.1
  | insert i t hi ih =>
      rw [Finset.sup_insert] at heq
      rcases ha.2 (g i) (t.sup g) heq with h | h
      · exact ⟨i, Finset.mem_insert_self i t, h⟩
      · obtain ⟨j, hjt, hj⟩ := ih h
        exact ⟨j, Finset.mem_insert_of_mem hjt, hj⟩

-- [D-0284] endP_finset_sup_apply
theorem endP_finset_sup_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → EndP P) (y : P) :
    (s.sup g) y = s.sup (fun i => g i y) := by
  induction s using Finset.induction with
  | empty => rfl
  | insert i t hi ih =>
      rw [Finset.sup_insert, Finset.sup_insert,
          show (g i ⊔ t.sup g) y = g i y ⊔ (t.sup g) y from rfl, ih]

-- [D-0285] endP_stepMap_sup_eq_self
theorem endP_stepMap_sup_eq_self (f : EndP P) :
    f = Finset.univ.sup (fun p => (stepMap (f p) p : EndP P)) := by
  apply OrderHom.ext
  funext y
  rw [endP_finset_sup_apply]
  apply le_antisymm
  · calc f y = (stepMap (f y) y : EndP P) y := (stepMap_apply_self (f y) y).symm
      _ ≤ Finset.univ.sup (fun p => (stepMap (f p) p : EndP P) y) :=
          Finset.le_sup (f := fun p => (stepMap (f p) p : EndP P) y) (Finset.mem_univ y)
  · apply Finset.sup_le
    intro p _
    by_cases hpy : p ≤ y
    · rw [stepMap_apply_of_ge (f p) p hpy]
      exact f.monotone hpy
    · rw [stepMap_apply_of_not_ge (f p) p hpy]
      exact bot_le

-- [D-0286] joinIrred_endP_iff_exists_stepMap
theorem joinIrred_endP_iff_exists_stepMap (f : EndP P) :
    JoinIrred (EndP P) f ↔ ∃ x q : P, JoinIrred P x ∧ f = stepMap x q := by
  constructor
  · intro hf
    obtain ⟨p, -, hp⟩ := exists_mem_eq_of_joinIrred_sup Finset.univ
      (fun p => (stepMap (f p) p : EndP P)) hf (endP_stepMap_sup_eq_self f)
    refine ⟨f p, p, ⟨?_, ?_⟩, hp⟩
    · intro hbot
      apply hf.1
      rw [hp, hbot]
      apply OrderHom.ext; funext y
      by_cases hqy : p ≤ y
      · rw [stepMap_apply_of_ge (⊥ : P) p hqy, endPBot_apply]
      · rw [stepMap_apply_of_not_ge (⊥ : P) p hqy, endPBot_apply]
    · intro b c hbc
      have heq2 : f = stepMap b p ⊔ stepMap c p := by rw [stepMap_join, ← hbc, ← hp]
      rcases hf.2 (stepMap b p) (stepMap c p) heq2 with h | h
      · left
        have h1 : f p = (stepMap b p : EndP P) p := by rw [h]
        rwa [stepMap_apply_self] at h1
      · right
        have h1 : f p = (stepMap c p : EndP P) p := by rw [h]
        rwa [stepMap_apply_self] at h1
  · rintro ⟨x, q, hx, hfeq⟩
    constructor
    · intro hbot
      apply hx.1
      have h1 : (stepMap x q : EndP P) q = (⊥ : EndP P) q := by rw [← hfeq, hbot]
      rwa [stepMap_apply_self, endPBot_apply] at h1
    · intro g h heq
      have heval : g q ⊔ h q = x := by
        have h1 : (g ⊔ h) q = (stepMap x q : EndP P) q := by rw [← heq, hfeq]
        rw [stepMap_apply_self] at h1
        exact h1
      rcases hx.2 (g q) (h q) heval.symm with hgq | hhq
      · left
        apply OrderHom.ext; funext y
        show f y = g y
        rw [hfeq]
        have hgle : g ≤ (stepMap x q : EndP P) := by rw [← hfeq]; rw [heq]; exact le_sup_left
        by_cases hqy : q ≤ y
        · have hub := OrderHom.le_def.mp hgle y
          rw [stepMap_apply_of_ge x q hqy] at hub
          have hlb : x ≤ g y := by
            calc x = g q := hgq
              _ ≤ g y := g.monotone hqy
          rw [stepMap_apply_of_ge x q hqy]
          exact le_antisymm hlb hub
        · rw [stepMap_apply_of_not_ge x q hqy]
          have hub := OrderHom.le_def.mp hgle y
          rw [stepMap_apply_of_not_ge x q hqy] at hub
          exact le_antisymm bot_le hub
      · right
        apply OrderHom.ext; funext y
        show f y = h y
        rw [hfeq]
        have hhle : h ≤ (stepMap x q : EndP P) := by rw [← hfeq]; rw [heq]; exact le_sup_right
        by_cases hqy : q ≤ y
        · have hub := OrderHom.le_def.mp hhle y
          rw [stepMap_apply_of_ge x q hqy] at hub
          have hlb : x ≤ h y := by
            calc x = h q := hhq
              _ ≤ h y := h.monotone hqy
          rw [stepMap_apply_of_ge x q hqy]
          exact le_antisymm hlb hub
        · rw [stepMap_apply_of_not_ge x q hqy]
          have hub := OrderHom.le_def.mp hhle y
          rw [stepMap_apply_of_not_ge x q hqy] at hub
          exact le_antisymm bot_le hub

-- [D-0287] stepMap_inj_of_ne_bot
theorem stepMap_inj_of_ne_bot {x x' q q' : P} (hx : x ≠ ⊥) (hx' : x' ≠ ⊥)
    (heq : (stepMap x q : EndP P) = stepMap x' q') : x = x' ∧ q = q' := by
  have h1 : (stepMap x q : EndP P) q = (stepMap x' q' : EndP P) q := by rw [heq]
  rw [stepMap_apply_self] at h1
  have hq'q : q' ≤ q := by
    by_contra hcon
    rw [stepMap_apply_of_not_ge x' q' hcon] at h1
    exact hx h1
  rw [stepMap_apply_of_ge x' q' hq'q] at h1
  have h2 : (stepMap x q : EndP P) q' = (stepMap x' q' : EndP P) q' := by rw [heq]
  rw [stepMap_apply_self] at h2
  have hqq' : q ≤ q' := by
    by_contra hcon
    rw [stepMap_apply_of_not_ge x q hcon] at h2
    exact hx' h2.symm
  exact ⟨h1, le_antisymm hqq' hq'q⟩

-- [D-0288] stepMap_le_stepMap_iff
theorem stepMap_le_stepMap_iff {x x2 q q2 : P} (hx : x ≠ ⊥) :
    (stepMap x q : EndP P) ≤ stepMap x2 q2 ↔ x ≤ x2 ∧ q2 ≤ q := by
  constructor
  · intro hle
    have h1 : (stepMap x q : EndP P) q = x := stepMap_apply_self x q
    have h2 := OrderHom.le_def.mp hle q
    rw [h1] at h2
    have hq2q : q2 ≤ q := by
      by_contra hcon
      rw [stepMap_apply_of_not_ge x2 q2 hcon] at h2
      exact hx (le_bot_iff.mp h2)
    rw [stepMap_apply_of_ge x2 q2 hq2q] at h2
    exact ⟨h2, hq2q⟩
  · rintro ⟨hxx2, hq2q⟩
    rw [OrderHom.le_def]
    intro y
    by_cases hqy : q ≤ y
    · have hq2y : q2 ≤ y := hq2q.trans hqy
      rw [stepMap_apply_of_ge x q hqy, stepMap_apply_of_ge x2 q2 hq2y]
      exact hxx2
    · rw [stepMap_apply_of_not_ge x q hqy]
      exact bot_le

-- [D-0289] jiWitnessX
noncomputable def jiWitnessX (f : EndP P) (hf : JoinIrred (EndP P) f) : P :=
  ((joinIrred_endP_iff_exists_stepMap f).mp hf).choose

-- [D-0290] jiWitnessQ
noncomputable def jiWitnessQ (f : EndP P) (hf : JoinIrred (EndP P) f) : P :=
  (((joinIrred_endP_iff_exists_stepMap f).mp hf).choose_spec).choose

-- [D-0291] jiWitness_spec
theorem jiWitness_spec (f : EndP P) (hf : JoinIrred (EndP P) f) :
    JoinIrred P (jiWitnessX f hf) ∧ f = stepMap (jiWitnessX f hf) (jiWitnessQ f hf) :=
  (((joinIrred_endP_iff_exists_stepMap f).mp hf).choose_spec).choose_spec

-- [D-0292] jiEquiv
noncomputable def jiEquiv :
    P × {x : P // JoinIrred P x} ≃ {f : EndP P // JoinIrred (EndP P) f} where
  toFun := fun (q, x) =>
    ⟨stepMap x.1 q, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x.1, q, x.2, rfl⟩⟩
  invFun := fun f => (jiWitnessQ f.1 f.2, ⟨jiWitnessX f.1 f.2, (jiWitness_spec f.1 f.2).1⟩)
  left_inv := by
    rintro ⟨q, x, hx⟩
    have hspec := jiWitness_spec (stepMap x q)
      ((joinIrred_endP_iff_exists_stepMap _).mpr ⟨x, q, hx, rfl⟩)
    have hinj := stepMap_inj_of_ne_bot hx.1 hspec.1.1 hspec.2
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨hinj.2.symm, hinj.1.symm⟩
  right_inv := by
    rintro ⟨f, hf⟩
    have hspec := jiWitness_spec f hf
    apply Subtype.ext
    show stepMap (jiWitnessX f hf) (jiWitnessQ f hf) = f
    exact hspec.2.symm

end StepMapCharacterization

section JICovers
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0293] stepMap_ne_iff
theorem stepMap_ne_iff {x x2 q q2 : P} (hx : x ≠ ⊥) (hx2 : x2 ≠ ⊥) :
    (stepMap x q : EndP P) ≠ stepMap x2 q2 ↔ x ≠ x2 ∨ q ≠ q2 := by
  constructor
  · intro hne
    by_contra hcon
    push_neg at hcon
    exact hne (by rw [hcon.1, hcon.2])
  · rintro (h | h) heq
    · exact h (stepMap_inj_of_ne_bot hx hx2 heq).1
    · exact h (stepMap_inj_of_ne_bot hx hx2 heq).2

-- [D-0294] stepMap_lt_iff
theorem stepMap_lt_iff {x x2 q q2 : P} (hx : x ≠ ⊥) (hx2 : x2 ≠ ⊥) :
    (stepMap x q : EndP P) < stepMap x2 q2 ↔ (x < x2 ∧ q2 ≤ q) ∨ (x ≤ x2 ∧ q2 < q) := by
  rw [lt_iff_le_and_ne, stepMap_le_stepMap_iff hx, stepMap_ne_iff hx hx2]
  constructor
  · rintro ⟨⟨hxx2, hq2q⟩, hxne | hqne⟩
    · exact Or.inl ⟨lt_of_le_of_ne hxx2 hxne, hq2q⟩
    · exact Or.inr ⟨hxx2, lt_of_le_of_ne hq2q (Ne.symm hqne)⟩
  · rintro (⟨hxlt, hq2q⟩ | ⟨hxle, hq2lt⟩)
    · exact ⟨⟨hxlt.le, hq2q⟩, Or.inl hxlt.ne⟩
    · exact ⟨⟨hxle, hq2lt.le⟩, Or.inr hq2lt.ne.symm⟩

-- [D-0295] stepMap_ji_covers_iff
theorem stepMap_ji_covers_iff {x x2 q q2 : P} (hx : JoinIrred P x) (hx2 : JoinIrred P x2) :
    Covers (⟨stepMap x q, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x, q, hx, rfl⟩⟩ :
              {f : EndP P // JoinIrred (EndP P) f})
           ⟨stepMap x2 q2, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x2, q2, hx2, rfl⟩⟩ ↔
    (x = x2 ∧ Covers q2 q) ∨ (q = q2 ∧ Covers (⟨x, hx⟩ : {x : P // JoinIrred P x}) ⟨x2, hx2⟩) := by
  constructor
  · rintro ⟨hlt, hcov⟩
    have hlt' : (stepMap x q : EndP P) < stepMap x2 q2 := hlt
    rw [stepMap_lt_iff hx.1 hx2.1] at hlt'
    by_cases hxeq : x = x2
    · subst hxeq
      left
      refine ⟨rfl, ?_, ?_⟩
      · rcases hlt' with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h (lt_irrefl x)
        · exact h
      · intro c hc1 hc2
        apply hcov ⟨stepMap x c, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x, c, hx, rfl⟩⟩
        · show (stepMap x q : EndP P) < stepMap x c
          rw [stepMap_lt_iff hx.1 hx.1]; right; exact ⟨le_refl x, hc2⟩
        · show (stepMap x c : EndP P) < stepMap x q2
          rw [stepMap_lt_iff hx.1 hx.1]; right; exact ⟨le_refl x, hc1⟩
    · right
      have hxx2 : x < x2 := by
        rcases hlt' with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact lt_of_le_of_ne h hxeq
      have hq2q : q2 ≤ q := by
        rcases hlt' with ⟨_, h⟩ | ⟨_, h⟩
        · exact h
        · exact h.le
      have hqeq : q = q2 := by
        by_contra hqne
        have hq2ltq : q2 < q := lt_of_le_of_ne hq2q (Ne.symm hqne)
        apply hcov ⟨stepMap x2 q, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x2, q, hx2, rfl⟩⟩
        · show (stepMap x q : EndP P) < stepMap x2 q
          rw [stepMap_lt_iff hx.1 hx2.1]; left; exact ⟨hxx2, le_refl q⟩
        · show (stepMap x2 q : EndP P) < stepMap x2 q2
          rw [stepMap_lt_iff hx2.1 hx2.1]; right; exact ⟨le_refl x2, hq2ltq⟩
      refine ⟨hqeq, hxx2, ?_⟩
      intro c hc1 hc2
      apply hcov ⟨stepMap c.1 q, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨c.1, q, c.2, rfl⟩⟩
      · show (stepMap x q : EndP P) < stepMap c.1 q
        rw [stepMap_lt_iff hx.1 c.2.1]; left; exact ⟨hc1, le_refl q⟩
      · show (stepMap c.1 q : EndP P) < stepMap x2 q2
        rw [stepMap_lt_iff c.2.1 hx2.1]; left; exact ⟨hc2, hqeq.symm.le⟩
  · rintro (⟨hxeq, hcovq⟩ | ⟨hqeq, hcovx⟩)
    · subst hxeq
      constructor
      · show (stepMap x q : EndP P) < stepMap x q2
        rw [stepMap_lt_iff hx.1 hx.1]; right; exact ⟨le_refl x, hcovq.1⟩
      · rintro ⟨c1, hc1ji⟩ hc1 hc2
        obtain ⟨c1x, c1q, hc1x, hc1eq⟩ := (joinIrred_endP_iff_exists_stepMap c1).mp hc1ji
        subst hc1eq
        have hc1' : (stepMap x q : EndP P) < stepMap c1x c1q := hc1
        have hc2' : (stepMap c1x c1q : EndP P) < stepMap x q2 := hc2
        rw [stepMap_lt_iff hx.1 hc1x.1] at hc1'
        rw [stepMap_lt_iff hc1x.1 hx.1] at hc2'
        rcases hc1' with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
          rcases hc2' with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact lt_irrefl x (h1a.trans h2a)
        · exact lt_irrefl x (h1a.trans_le h2a)
        · exact lt_irrefl x (h1a.trans_lt h2a)
        · exact hcovq.2 c1q h2b h1b
    · subst hqeq
      constructor
      · show (stepMap x q : EndP P) < stepMap x2 q
        rw [stepMap_lt_iff hx.1 hx2.1]; left; exact ⟨hcovx.1, le_refl q⟩
      · rintro ⟨c1, hc1ji⟩ hc1 hc2
        obtain ⟨c1x, c1q, hc1x, hc1eq⟩ := (joinIrred_endP_iff_exists_stepMap c1).mp hc1ji
        subst hc1eq
        have hc1' : (stepMap x q : EndP P) < stepMap c1x c1q := hc1
        have hc2' : (stepMap c1x c1q : EndP P) < stepMap x2 q := hc2
        rw [stepMap_lt_iff hx.1 hc1x.1] at hc1'
        rw [stepMap_lt_iff hc1x.1 hx2.1] at hc2'
        rcases hc1' with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
          rcases hc2' with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact hcovx.2 ⟨c1x, hc1x⟩ h1a h2a
        · exact lt_irrefl q (h2b.trans_le h1b)
        · exact lt_irrefl q (h2b.trans_lt h1b)
        · exact lt_irrefl q (h2b.trans h1b)

end JICovers

section LemmaMCL
variable {P L : Type u} [Fintype P] [DecidableEq P] [PartialOrder P] [Lattice L] [OrderBot L]

-- [D-0296] joinBelow
noncomputable def joinBelow (f : P → L) (x : P) : L :=
  (Finset.univ.filter (fun y => y < x)).sup f

-- [D-0297] le_joinBelow
theorem le_joinBelow (f : P → L) {x y : P} (hy : y < x) : f y ≤ joinBelow f x :=
  Finset.le_sup (f := f) (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)

-- [D-0298] joinBelow_le
theorem joinBelow_le (f : P → L) {x : P} {v : L} (h : ∀ y, y < x → f y ≤ v) :
    joinBelow f x ≤ v :=
  Finset.sup_le (fun y hy => h y (Finset.mem_filter.mp hy).2)

-- [D-0299] updateAt
def updateAt (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) : P →o L where
  toFun y := if y = x0 then v else f y
  monotone' := by
    intro y1 y2 hy
    by_cases h1 : y1 = x0
    · by_cases h2 : y2 = x0
      · rw [h1, h2]
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_pos h1, if_neg h2]
        have hlt : x0 < y2 := by
          rw [h1] at hy
          exact lt_of_le_of_ne hy (Ne.symm h2)
        calc v ≤ f x0 := hv_le
          _ ≤ f y2 := f.monotone hlt.le
    · by_cases h2 : y2 = x0
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_neg h1, if_pos h2]
        have hlt : y1 < x0 := by
          rw [h2] at hy
          exact lt_of_le_of_ne hy h1
        calc f y1 ≤ joinBelow f x0 := le_joinBelow f hlt
          _ ≤ v := hv_ge
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_neg h1, if_neg h2]
        exact f.monotone hy

-- [D-0300] updateAt_apply_self
theorem updateAt_apply_self (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) : updateAt f x0 v hv_le hv_ge x0 = v := by
  show (if x0 = x0 then v else f x0) = v
  rw [if_pos rfl]

-- [D-0301] updateAt_apply_ne
theorem updateAt_apply_ne (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) {y : P} (hy : y ≠ x0) :
    updateAt f x0 v hv_le hv_ge y = f y := by
  show (if y = x0 then v else f y) = f y
  rw [if_neg hy]

-- [D-0302] updateAt_ne
theorem updateAt_ne (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) (hne : v ≠ f x0) :
    updateAt f x0 v hv_le hv_ge ≠ f := by
  intro heq
  apply hne
  have h1 : (updateAt f x0 v hv_le hv_ge) x0 = f x0 := by rw [heq]
  rwa [updateAt_apply_self] at h1

-- [D-0303] updateAt_le
theorem updateAt_le (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) : updateAt f x0 v hv_le hv_ge ≤ f := by
  rw [OrderHom.le_def]
  intro y
  by_cases hy : y = x0
  · rw [hy, updateAt_apply_self]; exact hv_le
  · rw [updateAt_apply_ne f x0 v hv_le hv_ge hy]

-- [D-0304] updateAt_lt
theorem updateAt_lt (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) (hlt : v < f x0) :
    updateAt f x0 v hv_le hv_ge < f :=
  lt_of_le_of_ne (updateAt_le f x0 v hv_le hv_ge) (updateAt_ne f x0 v hv_le hv_ge hlt.ne)

-- [D-0305] covers_updateAt
theorem covers_updateAt (f : P →o L) (x0 : P) (v : L) (hv_le : v ≤ f x0)
    (hv_ge : joinBelow f x0 ≤ v) (hcov : Covers v (f x0)) :
    Covers (updateAt f x0 v hv_le hv_ge) f := by
  refine ⟨updateAt_lt f x0 v hv_le hv_ge hcov.1, ?_⟩
  intro h hgh hhf
  have hle1 : ∀ y, updateAt f x0 v hv_le hv_ge y ≤ h y := OrderHom.le_def.mp hgh.le
  have hle2 : ∀ y, h y ≤ f y := OrderHom.le_def.mp hhf.le
  have hagree : ∀ y, y ≠ x0 → h y = f y := by
    intro y hy
    have h1 := hle1 y
    rw [updateAt_apply_ne f x0 v hv_le hv_ge hy] at h1
    exact le_antisymm (hle2 y) h1
  have hx0_1 : v ≤ h x0 := by
    have := hle1 x0
    rwa [updateAt_apply_self] at this
  have hx0_2 : h x0 ≤ f x0 := hle2 x0
  have hcase : h x0 = v ∨ h x0 = f x0 := by
    rcases eq_or_lt_of_le hx0_1 with heq | hlt
    · exact Or.inl heq.symm
    · right
      exact hx0_2.lt_or_eq.resolve_left (hcov.2 (h x0) hlt)
  rcases hcase with hc | hc
  · have heq : h = updateAt f x0 v hv_le hv_ge := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = x0
      · rw [hy, hc, updateAt_apply_self]
      · rw [hagree y hy, updateAt_apply_ne f x0 v hv_le hv_ge hy]
    rw [heq] at hgh
    exact lt_irrefl _ hgh
  · have heq : h = f := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = x0
      · rw [hy, hc]
      · exact hagree y hy
    rw [heq] at hhf
    exact lt_irrefl _ hhf

-- [D-0306] exists_updateAt_of_covers
theorem exists_updateAt_of_covers (f g : P →o L) (hcov : Covers g f) :
    ∃ x0 v, ∃ (hv_le : v ≤ f x0) (hv_ge : joinBelow f x0 ≤ v),
      g = updateAt f x0 v hv_le hv_ge ∧ Covers v (f x0) := by
  have hgf_le : ∀ y, g y ≤ f y := OrderHom.le_def.mp hcov.1.le
  set X : Finset P := Finset.univ.filter (fun y => g y < f y) with hXdef
  have hX_ne : X.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hcov.1.ne
    apply OrderHom.ext
    funext y
    have h1 : g y ≤ f y := hgf_le y
    have h2 : ¬ g y < f y := by
      intro hlt
      have hmem : y ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hlt⟩
      rw [hempty] at hmem
      simp at hmem
    exact h1.lt_or_eq.resolve_left h2
  obtain ⟨x0, hx0_mem, hx0_max⟩ := Finset.exists_maximal hX_ne
  have hx0_lt : g x0 < f x0 := (Finset.mem_filter.mp hx0_mem).2
  have hmono : Monotone (fun y => if y = x0 then f x0 else g y) := by
    intro y1 y2 hy
    by_cases h1 : y1 = x0
    · by_cases h2 : y2 = x0
      · rw [h1, h2]
      · show (if y1 = x0 then f x0 else g y1) ≤ (if y2 = x0 then f x0 else g y2)
        rw [if_pos h1, if_neg h2]
        have hlt2 : x0 < y2 := by
          rw [h1] at hy
          exact lt_of_le_of_ne hy (Ne.symm h2)
        have hy2notX : y2 ∉ X := fun hmem =>
          absurd (hlt2.trans_le (hx0_max hmem hlt2.le)) (lt_irrefl x0)
        have hgy2 : g y2 = f y2 := by
          have h3 : g y2 ≤ f y2 := hgf_le y2
          have h4 : ¬ g y2 < f y2 := fun hc =>
            hy2notX (Finset.mem_filter.mpr ⟨Finset.mem_univ y2, hc⟩)
          exact h3.lt_or_eq.resolve_left h4
        rw [hgy2]
        exact f.monotone hlt2.le
    · show (if y1 = x0 then f x0 else g y1) ≤ (if y2 = x0 then f x0 else g y2)
      by_cases h2 : y2 = x0
      · rw [if_neg h1, if_pos h2]
        have hlt1 : y1 < x0 := by
          rw [h2] at hy
          exact lt_of_le_of_ne hy h1
        calc g y1 ≤ f y1 := hgf_le y1
          _ ≤ f x0 := f.monotone hlt1.le
      · rw [if_neg h1, if_neg h2]
        exact g.monotone hy
  set h : P →o L := ⟨fun y => if y = x0 then f x0 else g y, hmono⟩ with hhdef
  have hh_apply_x0 : h x0 = f x0 := by
    show (if x0 = x0 then f x0 else g x0) = f x0
    rw [if_pos rfl]
  have hh_apply_ne : ∀ y, y ≠ x0 → h y = g y := by
    intro y hy
    show (if y = x0 then f x0 else g y) = g y
    rw [if_neg hy]
  have hgh_le : ∀ y, g y ≤ h y := by
    intro y
    by_cases hy : y = x0
    · rw [hy, hh_apply_x0]; exact hx0_lt.le
    · rw [hh_apply_ne y hy]
  have hhf_le : ∀ y, h y ≤ f y := by
    intro y
    by_cases hy : y = x0
    · rw [hy, hh_apply_x0]
    · rw [hh_apply_ne y hy]; exact hgf_le y
  have hgh_ne : g ≠ h := by
    intro heq
    have h1 : g x0 = h x0 := by rw [heq]
    rw [hh_apply_x0] at h1
    exact hx0_lt.ne h1
  have hgh_lt : g < h := lt_of_le_of_ne (OrderHom.le_def.mpr hgh_le) hgh_ne
  have hhf_le' : h ≤ f := OrderHom.le_def.mpr hhf_le
  have hhf_eq : h = f := by
    by_cases hne : h = f
    · exact hne
    · exact absurd (lt_of_le_of_ne hhf_le' hne) (hcov.2 h hgh_lt)
  have hagree : ∀ y, y ≠ x0 → g y = f y := by
    intro y hy
    have h1 : h y = f y := by rw [hhf_eq]
    rw [hh_apply_ne y hy] at h1
    exact h1
  have hv_le : g x0 ≤ f x0 := hx0_lt.le
  have hv_ge : joinBelow f x0 ≤ g x0 := by
    apply joinBelow_le
    intro y hy
    rw [← hagree y (ne_of_lt hy)]
    exact g.monotone hy.le
  refine ⟨x0, g x0, hv_le, hv_ge, ?_, ?_⟩
  · apply OrderHom.ext
    funext y
    by_cases hy : y = x0
    · rw [hy, updateAt_apply_self]
    · rw [hagree y hy, updateAt_apply_ne f x0 (g x0) hv_le hv_ge hy]
  · refine ⟨hx0_lt, ?_⟩
    intro c hc1 hc2
    have hmono' : Monotone (fun y => if y = x0 then c else g y) := by
      intro y1 y2 hy
      by_cases h1 : y1 = x0
      · by_cases h2 : y2 = x0
        · rw [h1, h2]
        · show (if y1 = x0 then c else g y1) ≤ (if y2 = x0 then c else g y2)
          rw [if_pos h1, if_neg h2]
          have hlt2 : x0 < y2 := by
            rw [h1] at hy
            exact lt_of_le_of_ne hy (Ne.symm h2)
          rw [hagree y2 (Ne.symm (ne_of_lt hlt2))]
          exact hc2.le.trans (f.monotone hlt2.le)
      · by_cases h2 : y2 = x0
        · show (if y1 = x0 then c else g y1) ≤ (if y2 = x0 then c else g y2)
          rw [if_neg h1, if_pos h2]
          have hlt1 : y1 < x0 := by
            rw [h2] at hy
            exact lt_of_le_of_ne hy h1
          calc g y1 ≤ g x0 := g.monotone hlt1.le
            _ ≤ c := hc1.le
        · show (if y1 = x0 then c else g y1) ≤ (if y2 = x0 then c else g y2)
          rw [if_neg h1, if_neg h2]
          exact g.monotone hy
    set g' : P →o L := ⟨fun y => if y = x0 then c else g y, hmono'⟩ with hg'def
    have hg'_apply_x0 : g' x0 = c := by
      show (if x0 = x0 then c else g x0) = c
      rw [if_pos rfl]
    have hg'_apply_ne : ∀ y, y ≠ x0 → g' y = g y := by
      intro y hy
      show (if y = x0 then c else g y) = g y
      rw [if_neg hy]
    have hgg'_le : ∀ y, g y ≤ g' y := by
      intro y
      by_cases hy : y = x0
      · rw [hy, hg'_apply_x0]; exact hc1.le
      · rw [hg'_apply_ne y hy]
    have hg'f_le : ∀ y, g' y ≤ f y := by
      intro y
      by_cases hy : y = x0
      · rw [hy, hg'_apply_x0]; exact hc2.le
      · rw [hg'_apply_ne y hy]; exact hgf_le y
    have hgg'_ne : g ≠ g' := by
      intro heq
      have h1 : g x0 = g' x0 := by rw [heq]
      rw [hg'_apply_x0] at h1
      exact hc1.ne h1
    have hg'f_ne : g' ≠ f := by
      intro heq
      have h1 : g' x0 = f x0 := by rw [heq]
      rw [hg'_apply_x0] at h1
      exact hc2.ne h1
    have hgg'_lt : g < g' := lt_of_le_of_ne (OrderHom.le_def.mpr hgg'_le) hgg'_ne
    have hg'f_lt : g' < f := lt_of_le_of_ne (OrderHom.le_def.mpr hg'f_le) hg'f_ne
    exact hcov.2 g' hgg'_lt hg'f_lt

-- [D-0307] covers_iff_exists_updateAt
theorem covers_iff_exists_updateAt (f g : P →o L) :
    Covers g f ↔ ∃ x0 v, ∃ (hv_le : v ≤ f x0) (hv_ge : joinBelow f x0 ≤ v),
      g = updateAt f x0 v hv_le hv_ge ∧ Covers v (f x0) := by
  constructor
  · exact exists_updateAt_of_covers f g
  · rintro ⟨x0, v, hv_le, hv_ge, hgeq, hvcov⟩
    rw [hgeq]
    exact covers_updateAt f x0 v hv_le hv_ge hvcov

-- [D-0308] joinBelow_le_self
theorem joinBelow_le_self (f : P →o L) (x : P) : joinBelow f x ≤ f x :=
  joinBelow_le f (fun y hy => f.monotone hy.le)

-- [D-0309] exists_covBy_ge
theorem exists_covBy_ge {Q : Type u} [Fintype Q] [PartialOrder Q] {a b : Q}
    (hab : a < b) : ∃ w, Covers w b ∧ a ≤ w := by
  classical
  set S : Finset Q := Finset.univ.filter (fun x => a ≤ x ∧ x < b) with hSdef
  have hS_ne : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_refl a, hab⟩⟩
  obtain ⟨w, hw_mem, hw_max⟩ := Finset.exists_maximal hS_ne
  obtain ⟨_, hwa, hwb⟩ := Finset.mem_filter.mp hw_mem
  refine ⟨w, ⟨hwb, ?_⟩, hwa⟩
  intro c hwc hcb
  have hac : a ≤ c := le_trans hwa hwc.le
  have hcS : c ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac, hcb⟩
  exact absurd (hwc.trans_le (hw_max hcS hwc.le)) (lt_irrefl w)

-- [D-0310] forced_eq_joinBelow_of_unique_cover
theorem forced_eq_joinBelow_of_unique_cover [Fintype L] (f g : P →o L)
    (hgcov : Covers g f) (huniq : ∀ g', Covers g' f → g' = g) :
    ∃ x0 v, ∃ (hv_le : v ≤ f x0) (hv_ge : joinBelow f x0 ≤ v),
      g = updateAt f x0 v hv_le hv_ge ∧ Covers v (f x0) ∧
        ∀ x, x ≠ x0 → f x = joinBelow f x := by
  obtain ⟨x0, v, hv_le, hv_ge, hgeq, hvcov⟩ := exists_updateAt_of_covers f g hgcov
  refine ⟨x0, v, hv_le, hv_ge, hgeq, hvcov, ?_⟩
  intro x hx
  by_contra hne
  have hle : joinBelow f x ≤ f x := joinBelow_le_self f x
  have hlt : joinBelow f x < f x := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨w, hwcov, hw_ge⟩ := exists_covBy_ge hlt
  have hw_le : w ≤ f x := hwcov.1.le
  have hg2 : Covers (updateAt f x w hw_le hw_ge) f := covers_updateAt f x w hw_le hw_ge hwcov
  have heq := huniq _ hg2
  rw [hgeq] at heq
  have hcontra : (updateAt f x w hw_le hw_ge) x = (updateAt f x0 v hv_le hv_ge) x := by
    rw [heq]
  rw [updateAt_apply_self, updateAt_apply_ne f x0 v hv_le hv_ge hx] at hcontra
  rw [hcontra] at hwcov
  exact lt_irrefl _ hwcov.1

end LemmaMCL

section LemmaMCLUp
variable {P L : Type u} [Fintype P] [DecidableEq P] [PartialOrder P] [Lattice L] [OrderTop L]

-- [D-0311] meetAbove
noncomputable def meetAbove (f : P → L) (x : P) : L :=
  (Finset.univ.filter (fun y => x < y)).inf f

-- [D-0312] meetAbove_le
theorem meetAbove_le (f : P → L) {x y : P} (hy : x < y) : meetAbove f x ≤ f y :=
  Finset.inf_le (f := f) (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)

-- [D-0313] le_meetAbove
theorem le_meetAbove (f : P → L) {x : P} {v : L} (h : ∀ y, x < y → v ≤ f y) :
    v ≤ meetAbove f x :=
  Finset.le_inf (fun y hy => h y (Finset.mem_filter.mp hy).2)

-- [D-0314] updateAtUp
def updateAtUp (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) : P →o L where
  toFun y := if y = x0 then v else f y
  monotone' := by
    intro y1 y2 hy
    by_cases h1 : y1 = x0
    · by_cases h2 : y2 = x0
      · rw [h1, h2]
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_pos h1, if_neg h2]
        have hlt : x0 < y2 := by
          rw [h1] at hy
          exact lt_of_le_of_ne hy (Ne.symm h2)
        calc v ≤ meetAbove f x0 := hv_le
          _ ≤ f y2 := meetAbove_le f hlt
    · by_cases h2 : y2 = x0
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_neg h1, if_pos h2]
        have hlt : y1 < x0 := by
          rw [h2] at hy
          exact lt_of_le_of_ne hy h1
        calc f y1 ≤ f x0 := f.monotone hlt.le
          _ ≤ v := hv_ge
      · show (if y1 = x0 then v else f y1) ≤ (if y2 = x0 then v else f y2)
        rw [if_neg h1, if_neg h2]
        exact f.monotone hy

-- [D-0315] updateAtUp_apply_self
theorem updateAtUp_apply_self (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) : updateAtUp f x0 v hv_ge hv_le x0 = v := by
  show (if x0 = x0 then v else f x0) = v
  rw [if_pos rfl]

-- [D-0316] updateAtUp_apply_ne
theorem updateAtUp_apply_ne (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) {y : P} (hy : y ≠ x0) :
    updateAtUp f x0 v hv_ge hv_le y = f y := by
  show (if y = x0 then v else f y) = f y
  rw [if_neg hy]

-- [D-0317] updateAtUp_ne
theorem updateAtUp_ne (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) (hne : v ≠ f x0) :
    updateAtUp f x0 v hv_ge hv_le ≠ f := by
  intro heq
  apply hne
  have h1 : (updateAtUp f x0 v hv_ge hv_le) x0 = f x0 := by rw [heq]
  rwa [updateAtUp_apply_self] at h1

-- [D-0318] updateAtUp_ge
theorem updateAtUp_ge (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) : f ≤ updateAtUp f x0 v hv_ge hv_le := by
  rw [OrderHom.le_def]
  intro y
  by_cases hy : y = x0
  · rw [hy, updateAtUp_apply_self]; exact hv_ge
  · rw [updateAtUp_apply_ne f x0 v hv_ge hv_le hy]

-- [D-0319] updateAtUp_gt
theorem updateAtUp_gt (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) (hlt : f x0 < v) :
    f < updateAtUp f x0 v hv_ge hv_le :=
  lt_of_le_of_ne (updateAtUp_ge f x0 v hv_ge hv_le)
    (updateAtUp_ne f x0 v hv_ge hv_le hlt.ne').symm

-- [D-0320] covers_updateAtUp
theorem covers_updateAtUp (f : P →o L) (x0 : P) (v : L) (hv_ge : f x0 ≤ v)
    (hv_le : v ≤ meetAbove f x0) (hcov : Covers (f x0) v) :
    Covers f (updateAtUp f x0 v hv_ge hv_le) := by
  refine ⟨updateAtUp_gt f x0 v hv_ge hv_le hcov.1, ?_⟩
  intro h hfh hhu
  have hle1 : ∀ y, f y ≤ h y := OrderHom.le_def.mp hfh.le
  have hle2 : ∀ y, h y ≤ updateAtUp f x0 v hv_ge hv_le y := OrderHom.le_def.mp hhu.le
  have hagree : ∀ y, y ≠ x0 → h y = f y := by
    intro y hy
    have h2 := hle2 y
    rw [updateAtUp_apply_ne f x0 v hv_ge hv_le hy] at h2
    exact le_antisymm h2 (hle1 y)
  have hx0_1 : h x0 ≤ v := by
    have := hle2 x0
    rwa [updateAtUp_apply_self] at this
  have hx0_2 : f x0 ≤ h x0 := hle1 x0
  have hcase : h x0 = f x0 ∨ h x0 = v := by
    rcases eq_or_lt_of_le hx0_2 with heq | hlt
    · exact Or.inl heq.symm
    · right
      exact hx0_1.lt_or_eq.resolve_left (hcov.2 (h x0) hlt)
  rcases hcase with hc | hc
  · have heq : h = f := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = x0
      · rw [hy, hc]
      · exact hagree y hy
    rw [heq] at hfh
    exact lt_irrefl _ hfh
  · have heq : h = updateAtUp f x0 v hv_ge hv_le := by
      apply OrderHom.ext
      funext y
      by_cases hy : y = x0
      · rw [hy, hc, updateAtUp_apply_self]
      · rw [hagree y hy, updateAtUp_apply_ne f x0 v hv_ge hv_le hy]
    rw [heq] at hhu
    exact lt_irrefl _ hhu

-- [D-0321] exists_updateAtUp_of_covers
theorem exists_updateAtUp_of_covers (f h : P →o L) (hcov : Covers f h) :
    ∃ x0 v, ∃ (hv_ge : f x0 ≤ v) (hv_le : v ≤ meetAbove f x0),
      h = updateAtUp f x0 v hv_ge hv_le ∧ Covers (f x0) v := by
  have hfh_le : ∀ y, f y ≤ h y := OrderHom.le_def.mp hcov.1.le
  set Y : Finset P := Finset.univ.filter (fun y => f y < h y) with hYdef
  have hY_ne : Y.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hcov.1.ne
    apply OrderHom.ext
    funext y
    have h1 : f y ≤ h y := hfh_le y
    have h2 : ¬ f y < h y := by
      intro hlt
      have hmem : y ∈ Y := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hlt⟩
      rw [hempty] at hmem
      simp at hmem
    exact h1.lt_or_eq.resolve_left h2
  obtain ⟨x0, hx0_mem, hx0_min⟩ := Finset.exists_minimal hY_ne
  have hx0_lt : f x0 < h x0 := (Finset.mem_filter.mp hx0_mem).2
  have hmono : Monotone (fun y => if y = x0 then f x0 else h y) := by
    intro y1 y2 hy
    by_cases h1 : y1 = x0
    · by_cases h2 : y2 = x0
      · rw [h1, h2]
      · show (if y1 = x0 then f x0 else h y1) ≤ (if y2 = x0 then f x0 else h y2)
        rw [if_pos h1, if_neg h2]
        have hlt2 : x0 < y2 := by
          rw [h1] at hy
          exact lt_of_le_of_ne hy (Ne.symm h2)
        calc f x0 ≤ f y2 := f.monotone hlt2.le
          _ ≤ h y2 := hfh_le y2
    · show (if y1 = x0 then f x0 else h y1) ≤ (if y2 = x0 then f x0 else h y2)
      by_cases h2 : y2 = x0
      · rw [if_neg h1, if_pos h2]
        have hlt1 : y1 < x0 := by
          rw [h2] at hy
          exact lt_of_le_of_ne hy h1
        have hy1notY : y1 ∉ Y := fun hmem =>
          absurd (hlt1.trans_le (hx0_min hmem hlt1.le)) (lt_irrefl y1)
        have hhy1 : h y1 = f y1 := by
          have h3 : f y1 ≤ h y1 := hfh_le y1
          have h4 : ¬ f y1 < h y1 := fun hc =>
            hy1notY (Finset.mem_filter.mpr ⟨Finset.mem_univ y1, hc⟩)
          exact (h3.lt_or_eq.resolve_left h4).symm
        rw [hhy1]
        exact f.monotone hlt1.le
      · rw [if_neg h1, if_neg h2]
        exact h.monotone hy
  set g : P →o L := ⟨fun y => if y = x0 then f x0 else h y, hmono⟩ with hgdef
  have hg_apply_x0 : g x0 = f x0 := by
    show (if x0 = x0 then f x0 else h x0) = f x0
    rw [if_pos rfl]
  have hg_apply_ne : ∀ y, y ≠ x0 → g y = h y := by
    intro y hy
    show (if y = x0 then f x0 else h y) = h y
    rw [if_neg hy]
  have hgh_le : ∀ y, g y ≤ h y := by
    intro y
    by_cases hy : y = x0
    · rw [hy, hg_apply_x0]; exact hx0_lt.le
    · rw [hg_apply_ne y hy]
  have hfg_le : ∀ y, f y ≤ g y := by
    intro y
    by_cases hy : y = x0
    · rw [hy, hg_apply_x0]
    · rw [hg_apply_ne y hy]; exact hfh_le y
  have hgh_ne : g ≠ h := by
    intro heq
    have h1 : g x0 = h x0 := by rw [heq]
    rw [hg_apply_x0] at h1
    exact hx0_lt.ne h1
  have hgh_lt : g < h := lt_of_le_of_ne (OrderHom.le_def.mpr hgh_le) hgh_ne
  have hfg_le' : f ≤ g := OrderHom.le_def.mpr hfg_le
  have hfg_eq : f = g := by
    by_cases hne : f = g
    · exact hne
    · exact absurd hgh_lt (hcov.2 g (lt_of_le_of_ne hfg_le' hne))
  have hagree : ∀ y, y ≠ x0 → h y = f y := by
    intro y hy
    have h1 : g y = h y := hg_apply_ne y hy
    rw [← hfg_eq] at h1
    exact h1.symm
  have hv_ge : f x0 ≤ h x0 := hx0_lt.le
  have hv_le : h x0 ≤ meetAbove f x0 := by
    apply le_meetAbove
    intro y hy
    rw [← hagree y (ne_of_lt hy).symm]
    exact h.monotone hy.le
  refine ⟨x0, h x0, hv_ge, hv_le, ?_, ?_⟩
  · apply OrderHom.ext
    funext y
    by_cases hy : y = x0
    · rw [hy, updateAtUp_apply_self]
    · rw [hagree y hy, updateAtUp_apply_ne f x0 (h x0) hv_ge hv_le hy]
  · refine ⟨hx0_lt, ?_⟩
    intro c hc1 hc2
    have hmono' : Monotone (fun y => if y = x0 then c else h y) := by
      intro y1 y2 hy
      by_cases h1 : y1 = x0
      · by_cases h2 : y2 = x0
        · rw [h1, h2]
        · show (if y1 = x0 then c else h y1) ≤ (if y2 = x0 then c else h y2)
          rw [if_pos h1, if_neg h2]
          have hlt2 : x0 < y2 := by
            rw [h1] at hy
            exact lt_of_le_of_ne hy (Ne.symm h2)
          calc c ≤ h x0 := hc2.le
            _ ≤ h y2 := h.monotone hlt2.le
      · by_cases h2 : y2 = x0
        · show (if y1 = x0 then c else h y1) ≤ (if y2 = x0 then c else h y2)
          rw [if_neg h1, if_pos h2]
          have hlt1 : y1 < x0 := by
            rw [h2] at hy
            exact lt_of_le_of_ne hy h1
          rw [hagree y1 h1]
          calc f y1 ≤ f x0 := f.monotone hlt1.le
            _ ≤ c := hc1.le
        · show (if y1 = x0 then c else h y1) ≤ (if y2 = x0 then c else h y2)
          rw [if_neg h1, if_neg h2]
          exact h.monotone hy
    set h' : P →o L := ⟨fun y => if y = x0 then c else h y, hmono'⟩ with hh'def
    have hh'_apply_x0 : h' x0 = c := by
      show (if x0 = x0 then c else h x0) = c
      rw [if_pos rfl]
    have hh'_apply_ne : ∀ y, y ≠ x0 → h' y = h y := by
      intro y hy
      show (if y = x0 then c else h y) = h y
      rw [if_neg hy]
    have hfh'_le : ∀ y, f y ≤ h' y := by
      intro y
      by_cases hy : y = x0
      · rw [hy, hh'_apply_x0]; exact hc1.le
      · rw [hh'_apply_ne y hy]; exact hfh_le y
    have hh'h_le : ∀ y, h' y ≤ h y := by
      intro y
      by_cases hy : y = x0
      · rw [hy, hh'_apply_x0]; exact hc2.le
      · rw [hh'_apply_ne y hy]
    have hfh'_ne : f ≠ h' := by
      intro heq
      have h1 : f x0 = h' x0 := by rw [heq]
      rw [hh'_apply_x0] at h1
      exact hc1.ne h1
    have hh'h_ne : h' ≠ h := by
      intro heq
      have h1 : h' x0 = h x0 := by rw [heq]
      rw [hh'_apply_x0] at h1
      exact hc2.ne h1
    have hfh'_lt : f < h' := lt_of_le_of_ne (OrderHom.le_def.mpr hfh'_le) hfh'_ne
    have hh'h_lt : h' < h := lt_of_le_of_ne (OrderHom.le_def.mpr hh'h_le) hh'h_ne
    exact hcov.2 h' hfh'_lt hh'h_lt

-- [D-0322] covers_iff_exists_updateAtUp
theorem covers_iff_exists_updateAtUp (f h : P →o L) :
    Covers f h ↔ ∃ x0 v, ∃ (hv_ge : f x0 ≤ v) (hv_le : v ≤ meetAbove f x0),
      h = updateAtUp f x0 v hv_ge hv_le ∧ Covers (f x0) v := by
  constructor
  · exact exists_updateAtUp_of_covers f h
  · rintro ⟨x0, v, hv_ge, hv_le, hheq, hvcov⟩
    rw [hheq]
    exact covers_updateAtUp f x0 v hv_ge hv_le hvcov

-- [D-0323] self_le_meetAbove
theorem self_le_meetAbove (f : P →o L) (x : P) : f x ≤ meetAbove f x :=
  le_meetAbove f (fun y hy => f.monotone hy.le)

-- [D-0324] exists_covBy_le
theorem exists_covBy_le {Q : Type u} [Fintype Q] [PartialOrder Q] {a b : Q}
    (hab : a < b) : ∃ w, Covers a w ∧ w ≤ b := by
  classical
  set S : Finset Q := Finset.univ.filter (fun x => a < x ∧ x ≤ b) with hSdef
  have hS_ne : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab, le_refl b⟩⟩
  obtain ⟨w, hw_mem, hw_min⟩ := Finset.exists_minimal hS_ne
  obtain ⟨_, hwa, hwb⟩ := Finset.mem_filter.mp hw_mem
  refine ⟨w, ⟨hwa, ?_⟩, hwb⟩
  intro c hac hcw
  have hcb : c ≤ b := le_trans hcw.le hwb
  have hcS : c ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac, hcb⟩
  exact absurd (hcw.trans_le (hw_min hcS hcw.le)) (lt_irrefl c)

-- [D-0325] forced_eq_meetAbove_of_unique_cover
theorem forced_eq_meetAbove_of_unique_cover [Fintype L] (f h : P →o L)
    (hhcov : Covers f h) (huniq : ∀ h', Covers f h' → h' = h) :
    ∃ x0 v, ∃ (hv_ge : f x0 ≤ v) (hv_le : v ≤ meetAbove f x0),
      h = updateAtUp f x0 v hv_ge hv_le ∧ Covers (f x0) v ∧
        ∀ x, x ≠ x0 → f x = meetAbove f x := by
  obtain ⟨x0, v, hv_ge, hv_le, hheq, hvcov⟩ := exists_updateAtUp_of_covers f h hhcov
  refine ⟨x0, v, hv_ge, hv_le, hheq, hvcov, ?_⟩
  intro x hx
  by_contra hne
  have hle : f x ≤ meetAbove f x := self_le_meetAbove f x
  have hlt : f x < meetAbove f x := lt_of_le_of_ne hle hne
  obtain ⟨w, hwcov, hw_le⟩ := exists_covBy_le hlt
  have hw_ge : f x ≤ w := hwcov.1.le
  have hh2 : Covers f (updateAtUp f x w hw_ge hw_le) := covers_updateAtUp f x w hw_ge hw_le hwcov
  have heq := huniq _ hh2
  rw [hheq] at heq
  have hcontra : (updateAtUp f x w hw_ge hw_le) x = (updateAtUp f x0 v hv_ge hv_le) x := by
    rw [heq]
  rw [updateAtUp_apply_self, updateAtUp_apply_ne f x0 v hv_ge hv_le hx] at hcontra
  rw [hcontra] at hwcov
  exact lt_irrefl _ hwcov.1

end LemmaMCLUp

section DcnmiFact1
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0326] fact1_forced_bot
theorem fact1_forced_bot (f : EndP P) (p : P)
    (hforced : ∀ x, x ≠ p → f x = joinBelow f x) :
    ∀ x, ¬ p ≤ x → f x = ⊥ := by
  have hwf : WellFounded ((· < ·) : P → P → Prop) := Finite.wellFounded_of_trans_of_irrefl _
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    intro hx
    have hxne : x ≠ p := by
      intro h
      apply hx
      rw [h]
    rw [hforced x hxne]
    apply le_antisymm
    · apply joinBelow_le
      intro y hy
      have hyne : ¬ p ≤ y := fun hy0 => hx (hy0.trans hy.le)
      rw [ih y hy hyne]
    · exact bot_le

-- [D-0327] fact2_forced_top
theorem fact2_forced_top (f : EndP P) (p : P)
    (hforced : ∀ x, x ≠ p → f x = meetAbove f x) :
    ∀ x, ¬ x ≤ p → f x = ⊤ := by
  have hwf : WellFounded ((· > ·) : P → P → Prop) := Finite.wellFounded_of_trans_of_irrefl _
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    intro hx
    have hxne : x ≠ p := by
      intro h
      apply hx
      rw [h]
    rw [hforced x hxne]
    apply le_antisymm
    · exact le_top
    · apply le_meetAbove
      intro y hy
      have hyne : ¬ y ≤ p := fun hy0 => hx (hy.le.trans hy0)
      rw [ih y hy hyne]

-- [D-0328] comp_of_same_witness
theorem comp_of_same_witness (f : EndP P) (p : P) (hbt : (⊥ : P) ≠ ⊤)
    (hforced_down : ∀ x, x ≠ p → f x = joinBelow f x)
    (hforced_up : ∀ x, x ≠ p → f x = meetAbove f x) :
    Comp P p := by
  have hdown := fact1_forced_bot f p hforced_down
  have hup := fact2_forced_top f p hforced_up
  intro x
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnpx, hnxp⟩ := hcon
  have h1 : f x = ⊥ := hdown x hnpx
  have h2 : f x = ⊤ := hup x hnxp
  rw [h1] at h2
  exact hbt h2

end DcnmiFact1

section DcnmiSameGeneral
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0329] coatomOf_covers_top
theorem coatomOf_covers_top : Covers (coatomOf P) (⊤ : P) := by
  refine ⟨lt_of_le_of_ne le_top (coatomOf_ne_top P), ?_⟩
  intro c hc1 hc2
  exact absurd (hc1.trans_le (coatomOf_le hc2.ne)) (lt_irrefl _)

-- [D-0330] atomOf_covers_bot
theorem atomOf_covers_bot : Covers (⊥ : P) (atomOf P) := by
  refine ⟨lt_of_le_of_ne bot_le (Ne.symm (atomOf_ne_bot P)), ?_⟩
  intro c hc1 hc2
  exact absurd (hc2.trans_le (atomOf_le hc1.ne')) (lt_irrefl _)

-- [D-0331] joinBelow_eq_forced
theorem joinBelow_eq_forced (f : EndP P) (p : P) (hp : Comp P p)
    (hdown : ∀ y, ¬ p ≤ y → f y = ⊥) {x : P} (hx : Covers p x) :
    joinBelow f x = f p := by
  apply le_antisymm
  · apply joinBelow_le
    intro y hy
    have hyp : y ≤ p := by
      rcases hp y with hpy | hyp'
      · rcases eq_or_lt_of_le hpy with heq | hlt
        · exact le_of_eq heq.symm
        · exact absurd hy (hx.2 y hlt)
      · exact hyp'
    rcases eq_or_lt_of_le hyp with heq | hlt
    · exact le_of_eq (congrArg f heq)
    · rw [hdown y (fun hle => absurd (hlt.trans_le hle) (lt_irrefl y))]
      exact bot_le
  · exact le_joinBelow f hx.1

-- [D-0332] meetAbove_eq_forced
theorem meetAbove_eq_forced (f : EndP P) (p : P) (hp : Comp P p)
    (hup : ∀ y, ¬ y ≤ p → f y = ⊤) {x : P} (hx : Covers x p) :
    meetAbove f x = f p := by
  apply le_antisymm
  · exact meetAbove_le f hx.1
  · apply le_meetAbove
    intro y hy
    have hyp : p ≤ y := by
      rcases hp y with hpy | hyp'
      · exact hpy
      · rcases eq_or_lt_of_le hyp' with heq | hlt
        · exact le_of_eq heq.symm
        · exact absurd hlt (hx.2 y hy)
    rcases eq_or_lt_of_le hyp with heq | hlt
    · exact le_of_eq (congrArg f heq)
    · rw [hup y (fun hle => absurd (hlt.trans_le hle) (lt_irrefl p))]
      exact le_top

-- [D-0333] dcnmi_same_general
theorem dcnmi_same_general
    (f : EndP P) (hbt : (⊥ : P) ≠ ⊤) (p : P)
    (g : EndP P) (hgcov : Covers g f) (hguniq : ∀ g', Covers g' f → g' = g)
    (hgp : ∀ x0 v hv_le hv_ge, g = updateAt f x0 v hv_le hv_ge → x0 = p)
    (h : EndP P) (hhcov : Covers f h) (hhuniq : ∀ h', Covers f h' → h' = h)
    (hhp : ∀ x0 v hv_ge hv_le, h = updateAtUp f x0 v hv_ge hv_le → x0 = p) :
    False := by
  obtain ⟨x0, v, hv_le, hv_ge, hgeq, hvcov, hforced_down⟩ :=
    forced_eq_joinBelow_of_unique_cover f g hgcov hguniq
  have hx0p : x0 = p := hgp x0 v hv_le hv_ge hgeq
  subst x0
  obtain ⟨x1, w, hv_ge', hv_le', hheq, hwcov, hforced_up⟩ :=
    forced_eq_meetAbove_of_unique_cover f h hhcov hhuniq
  have hx1p : x1 = p := hhp x1 w hv_ge' hv_le' hheq
  subst x1
  have hp : Comp P p := comp_of_same_witness f p hbt hforced_down hforced_up
  have hdown : ∀ x, ¬ p ≤ x → f x = ⊥ := fact1_forced_bot f p hforced_down
  have hup : ∀ x, ¬ x ≤ p → f x = ⊤ := fact2_forced_top f p hforced_up
  by_cases hpt : p = (⊤ : P)
  ·
    by_cases hmb : f p = (⊥ : P)
    · rw [hmb] at hvcov
      exact absurd (hvcov.1.trans_le bot_le) (lt_irrefl _)
    · have hx_ne_p : (coatomOf P) ≠ p := by rw [hpt]; exact coatomOf_ne_top P
      have hfx : f (coatomOf P) = ⊥ := by
        apply hdown
        rw [hpt]
        intro hc
        exact coatomOf_ne_top P (le_antisymm le_top hc)
      have hcovp : Covers (coatomOf P) p := by rw [hpt]; exact coatomOf_covers_top
      have hma : meetAbove f (coatomOf P) = f p := meetAbove_eq_forced f p hp hup hcovp
      have hge2 : f (coatomOf P) ≤ atomOf P := by rw [hfx]; exact bot_le
      have hle2 : atomOf P ≤ meetAbove f (coatomOf P) := by
        rw [hma]; exact atomOf_le hmb
      have hcov2 : Covers (f (coatomOf P)) (atomOf P) := by
        rw [hfx]; exact atomOf_covers_bot
      have hh2 : Covers f (updateAtUp f (coatomOf P) (atomOf P) hge2 hle2) :=
        covers_updateAtUp f (coatomOf P) (atomOf P) hge2 hle2 hcov2
      have heq2 := hhuniq _ hh2
      rw [hheq] at heq2
      have hcontra : (updateAtUp f (coatomOf P) (atomOf P) hge2 hle2) (coatomOf P) =
          (updateAtUp f p w hv_ge' hv_le') (coatomOf P) := by rw [heq2]
      rw [updateAtUp_apply_self, updateAtUp_apply_ne f p w hv_ge' hv_le' hx_ne_p] at hcontra
      exact atomOf_ne_bot P (hcontra.trans hfx)
  ·
    by_cases hmt : f p = (⊤ : P)
    · rw [hmt] at hwcov
      exact absurd (hwcov.1.trans_le le_top) (lt_irrefl _)
    · have hplt : p < (⊤ : P) := lt_of_le_of_ne le_top hpt
      obtain ⟨x, hxcov, _⟩ := exists_covBy_le hplt
      have hx_ne_p : x ≠ p := hxcov.1.ne'
      have hfx : f x = ⊤ := by
        apply hup
        intro hc
        exact hxcov.1.ne (le_antisymm hc hxcov.1.le).symm
      have hjb : joinBelow f x = f p := joinBelow_eq_forced f p hp hdown hxcov
      have hle3 : coatomOf P ≤ f x := by rw [hfx]; exact le_top
      have hge3 : joinBelow f x ≤ coatomOf P := by
        rw [hjb]; exact coatomOf_le hmt
      have hcov3 : Covers (coatomOf P) (f x) := by
        rw [hfx]; exact coatomOf_covers_top
      have hg2 : Covers (updateAt f x (coatomOf P) hle3 hge3) f :=
        covers_updateAt f x (coatomOf P) hle3 hge3 hcov3
      have heq3 := hguniq _ hg2
      rw [hgeq] at heq3
      have hcontra : (updateAt f x (coatomOf P) hle3 hge3) x =
          (updateAt f p v hv_le hv_ge) x := by rw [heq3]
      rw [updateAt_apply_self, updateAt_apply_ne f p v hv_le hv_ge hx_ne_p] at hcontra
      exact coatomOf_ne_top P (hcontra.trans hfx)

end DcnmiSameGeneral

section Sig1BreakGeneric
variable {P L : Type u} [Fintype P] [DecidableEq P] [PartialOrder P] [Lattice L] [BoundedOrder L]

-- [D-0334] meetAbove_eq_of_agree_off
theorem meetAbove_eq_of_agree_off (f g : P → L) (x0 : P)
    (hagree : ∀ y, y ≠ x0 → g y = f y) {x : P} (hx : ¬ x < x0) :
    meetAbove g x = meetAbove f x := by
  unfold meetAbove
  apply Finset.inf_congr rfl
  intro y hy
  apply hagree
  rintro rfl
  exact hx (Finset.mem_filter.mp hy).2

-- [D-0335] joinBelow_eq_of_agree_off
theorem joinBelow_eq_of_agree_off (f g : P → L) (x0 : P)
    (hagree : ∀ y, y ≠ x0 → g y = f y) {x : P} (hx : ¬ x0 < x) :
    joinBelow g x = joinBelow f x := by
  unfold joinBelow
  apply Finset.sup_congr rfl
  intro y hy
  apply hagree
  rintro rfl
  exact hx (Finset.mem_filter.mp hy).2

-- [D-0336] second_upcover_of_ne_witness
theorem second_upcover_of_ne_witness
    (f : P →o L) (p0 : P) (v0 : L) (hv_le0 : v0 ≤ f p0) (hv_ge0 : joinBelow f p0 ≤ v0)
    (p1 : P) (w1 : L) (hv_ge1 : f p1 ≤ w1) (hv_le1 : w1 ≤ meetAbove f p1)
    (hcov1 : Covers (f p1) w1)
    (hp1p0 : p1 ≠ p0) (hnlt : ¬ p1 < p0) :
    ∃ h2, Covers (updateAt f p0 v0 hv_le0 hv_ge0) h2 ∧ h2 ≠ f := by
  have hagree : ∀ y, y ≠ p0 → (updateAt f p0 v0 hv_le0 hv_ge0) y = f y := fun y hy =>
    updateAt_apply_ne f p0 v0 hv_le0 hv_ge0 hy
  have hgp1 : (updateAt f p0 v0 hv_le0 hv_ge0) p1 = f p1 := hagree p1 hp1p0
  have hma : meetAbove (updateAt f p0 v0 hv_le0 hv_ge0) p1 = meetAbove f p1 :=
    meetAbove_eq_of_agree_off f (updateAt f p0 v0 hv_le0 hv_ge0) p0 hagree hnlt
  have hv_ge1' : (updateAt f p0 v0 hv_le0 hv_ge0) p1 ≤ w1 := by rw [hgp1]; exact hv_ge1
  have hv_le1' : w1 ≤ meetAbove (updateAt f p0 v0 hv_le0 hv_ge0) p1 := by
    rw [hma]; exact hv_le1
  have hcov1' : Covers ((updateAt f p0 v0 hv_le0 hv_ge0) p1) w1 := by
    rw [hgp1]; exact hcov1
  refine ⟨updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 w1 hv_ge1' hv_le1', ?_, ?_⟩
  · exact covers_updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 w1 hv_ge1' hv_le1' hcov1'
  · intro heq
    have h1 : (updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 w1 hv_ge1' hv_le1') p1 = f p1 := by
      rw [heq]
    rw [updateAtUp_apply_self] at h1
    exact hcov1.1.ne h1.symm

end Sig1BreakGeneric

section AcPin
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0337] eq_coatomOf_of_covers_top
theorem eq_coatomOf_of_covers_top {v : P} (h : Covers v (⊤ : P)) : v = coatomOf P := by
  have hvne : v ≠ (⊤ : P) := h.1.ne
  have hle : v ≤ coatomOf P := coatomOf_le hvne
  have hcoatomlt : coatomOf P < (⊤ : P) := lt_of_le_of_ne le_top (coatomOf_ne_top P)
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  · exact absurd hcoatomlt (h.2 (coatomOf P) hlt)

-- [D-0338] eq_atomOf_of_covers_bot
theorem eq_atomOf_of_covers_bot {w : P} (h : Covers (⊥ : P) w) : w = atomOf P := by
  have hwne : w ≠ (⊥ : P) := h.1.ne'
  have hle : atomOf P ≤ w := atomOf_le hwne
  have hatomlt : (⊥ : P) < atomOf P := lt_of_le_of_ne bot_le (Ne.symm (atomOf_ne_bot P))
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq.symm
  · exact absurd hlt (h.2 (atomOf P) hatomlt)

-- [D-0339] ac_pin_second_upcover
theorem ac_pin_second_upcover
    (f : EndP P) (hnb : (⊥ : P) ≠ coatomOf P)
    (p0 v0 : P) (hv_le0 : v0 ≤ f p0) (hv_ge0 : joinBelow f p0 ≤ v0)
    (hcov0 : Covers v0 (f p0))
    (hforced_down : ∀ x, x ≠ p0 → f x = joinBelow f x)
    (p1 : P) (hforced_up : ∀ x, x ≠ p1 → f x = meetAbove f x)
    (hnp01 : ¬ p0 ≤ p1) :
    ∃ h2, Covers (updateAt f p0 v0 hv_le0 hv_ge0) h2 ∧ h2 ≠ f := by
  have hdown : ∀ x, ¬ p0 ≤ x → f x = ⊥ := fact1_forced_bot f p0 hforced_down
  have hup : ∀ x, ¬ x ≤ p1 → f x = ⊤ := fact2_forced_top f p1 hforced_up
  have hp1 : f p1 = ⊥ := hdown p1 hnp01
  have hp0 : f p0 = ⊤ := hup p0 hnp01
  have hp1p0 : p1 ≠ p0 := by
    intro h
    apply hnp01
    rw [h]
  have hcovtop : Covers v0 (⊤ : P) := by rw [← hp0]; exact hcov0
  have hv0 : v0 = coatomOf P := eq_coatomOf_of_covers_top hcovtop
  have hgp1 : (updateAt f p0 v0 hv_le0 hv_ge0) p1 = ⊥ := by
    rw [updateAt_apply_ne f p0 v0 hv_le0 hv_ge0 hp1p0]
    exact hp1
  have hbound : ∀ y, p1 < y → atomOf P ≤ (updateAt f p0 v0 hv_le0 hv_ge0) y := by
    intro y hy
    by_cases hyp0 : y = p0
    · rw [hyp0, updateAt_apply_self, hv0]
      exact atomOf_le (Ne.symm hnb)
    · rw [updateAt_apply_ne f p0 v0 hv_le0 hv_ge0 hyp0]
      have hynp1 : ¬ y ≤ p1 := fun hle => absurd (hy.trans_le hle) (lt_irrefl p1)
      rw [hup y hynp1]
      exact le_top
  have hma : atomOf P ≤ meetAbove (updateAt f p0 v0 hv_le0 hv_ge0) p1 :=
    le_meetAbove (updateAt f p0 v0 hv_le0 hv_ge0) hbound
  have hge : (updateAt f p0 v0 hv_le0 hv_ge0) p1 ≤ atomOf P := by rw [hgp1]; exact bot_le
  have hcov1 : Covers ((updateAt f p0 v0 hv_le0 hv_ge0) p1) (atomOf P) := by
    rw [hgp1]; exact atomOf_covers_bot
  refine ⟨updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 (atomOf P) hge hma, ?_, ?_⟩
  · exact covers_updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 (atomOf P) hge hma hcov1
  · intro heq
    have h1 : (updateAtUp (updateAt f p0 v0 hv_le0 hv_ge0) p1 (atomOf P) hge hma) p1 = f p1 := by
      rw [heq]
    rw [updateAtUp_apply_self] at h1
    rw [hp1] at h1
    exact atomOf_ne_bot P h1

-- [D-0340] sig1break_p0_ne_p1_second_upcover
theorem sig1break_p0_ne_p1_second_upcover
    (f : EndP P) (hnb : (⊥ : P) ≠ coatomOf P)
    (p0 v0 : P) (hv_le0 : v0 ≤ f p0) (hv_ge0 : joinBelow f p0 ≤ v0)
    (hcov0 : Covers v0 (f p0)) (hforced_down : ∀ x, x ≠ p0 → f x = joinBelow f x)
    (p1 w1 : P) (hv_ge1 : f p1 ≤ w1) (hv_le1 : w1 ≤ meetAbove f p1)
    (hcov1 : Covers (f p1) w1) (hforced_up : ∀ x, x ≠ p1 → f x = meetAbove f x)
    (hp01 : p0 ≠ p1) :
    ∃ h2, Covers (updateAt f p0 v0 hv_le0 hv_ge0) h2 ∧ h2 ≠ f := by
  by_cases hle : p0 ≤ p1
  · have hlt : p0 < p1 := lt_of_le_of_ne hle hp01
    exact second_upcover_of_ne_witness f p0 v0 hv_le0 hv_ge0 p1 w1 hv_ge1 hv_le1 hcov1
      hp01.symm (fun hc => absurd (hlt.trans hc) (lt_irrefl p0))
  · exact ac_pin_second_upcover f hnb p0 v0 hv_le0 hv_ge0 hcov0 hforced_down p1 hforced_up hle

end AcPin

-- [D-0341] reflTransGen_symm_of_symm
theorem reflTransGen_symm_of_symm {α : Type*} {r : α → α → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hac hcb ih => exact Relation.ReflTransGen.head (hsymm _ _ hcb) ih

section HasseConnected
variable {P : Type u} [Fintype P] [Lattice P] [BoundedOrder P]

-- [D-0342] hasse_connects_to_top
theorem hasse_connects_to_top (a : P) :
    Relation.ReflTransGen (Graph.Hasse P).adj a (⊤ : P) := by
  have hwf : WellFounded (fun a b : P => b < a) := Finite.wellFounded_of_trans_of_irrefl _
  induction a using hwf.induction with
  | _ a ih =>
    by_cases hatop : a = ⊤
    · rw [hatop]
    · obtain ⟨w, hcov, hwtop⟩ := exists_covBy_le (lt_of_le_of_ne le_top hatop)
      have hadj : (Graph.Hasse P).adj a w := Or.inl hcov
      exact Relation.ReflTransGen.head hadj (ih w hcov.1)

-- [D-0343] hasse_connected_of_lattice
theorem hasse_connected_of_lattice : (Graph.Hasse P).Connected := by
  intro a b
  have ha := hasse_connects_to_top a
  have hb := hasse_connects_to_top b
  have hb' := reflTransGen_symm_of_symm (fun x y h => (Graph.Hasse P).symm h) hb
  exact ha.trans hb'

end HasseConnected

section JHWiring
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0344] hasse_bot_degree_one
theorem hasse_bot_degree_one :
    ∀ w, (Graph.Hasse P).adj (⊥ : P) w → ∀ w', (Graph.Hasse P).adj (⊥ : P) w' → w = w' := by
  intro w hw w' hw'
  have hw2 : Covers (⊥ : P) w := hw.resolve_right (fun h => absurd h.1 (not_lt_bot))
  have hw2' : Covers (⊥ : P) w' := hw'.resolve_right (fun h => absurd h.1 (not_lt_bot))
  rw [eq_atomOf_of_covers_bot hw2, eq_atomOf_of_covers_bot hw2']

-- [D-0345] hasse_bot_nonempty
theorem hasse_bot_nonempty : ∃ w, (Graph.Hasse P).adj (⊥ : P) w :=
  ⟨atomOf P, Or.inl atomOf_covers_bot⟩

-- [D-0346] hasse_P_prime
theorem hasse_P_prime : GraphPrime (Graph.Hasse P) :=
  hasse_prime_of_degree_one (Graph.Hasse P) ⊥ hasse_bot_degree_one hasse_bot_nonempty

end JHWiring

-- [D-0347] card_joinIrred_lt
theorem card_joinIrred_lt {P : Type u} [Fintype P] [Lattice P] [BoundedOrder P] :
    Fintype.card {x : P // JoinIrred P x} < Fintype.card P :=
  Fintype.card_subtype_lt (show ¬ JoinIrred P (⊥ : P) from fun h => h.1 rfl)

section JIAdj
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0348] jiEquiv_adj_iff
theorem jiEquiv_adj_iff (p1 p2 : P × {x : P // JoinIrred P x}) :
    (Graph.Hasse {f : EndP P // JoinIrred (EndP P) f}).adj (jiEquiv p1) (jiEquiv p2) ↔
    (prodGraph (Graph.Hasse P) (Graph.Hasse {x : P // JoinIrred P x})).adj p1 p2 := by
  obtain ⟨q1, x1v, hx1⟩ := p1
  obtain ⟨q2, x2v, hx2⟩ := p2
  have h1 := stepMap_ji_covers_iff hx1 hx2 (q := q1) (q2 := q2)
  have h2 := stepMap_ji_covers_iff hx2 hx1 (q := q2) (q2 := q1)
  constructor
  · rintro (hc | hc)
    · have hc' : Covers (⟨stepMap x1v q1, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x1v,q1,hx1,rfl⟩⟩ :
          {f : EndP P // JoinIrred (EndP P) f})
          ⟨stepMap x2v q2, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x2v,q2,hx2,rfl⟩⟩ := hc
      rw [h1] at hc'
      rcases hc' with ⟨hxeq, hcov⟩ | ⟨hqeq, hcov⟩
      · exact Or.inr ⟨Subtype.ext hxeq, Or.inr hcov⟩
      · exact Or.inl ⟨hqeq, Or.inl hcov⟩
    · have hc' : Covers (⟨stepMap x2v q2, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x2v,q2,hx2,rfl⟩⟩ :
          {f : EndP P // JoinIrred (EndP P) f})
          ⟨stepMap x1v q1, (joinIrred_endP_iff_exists_stepMap _).mpr ⟨x1v,q1,hx1,rfl⟩⟩ := hc
      rw [h2] at hc'
      rcases hc' with ⟨hxeq, hcov⟩ | ⟨hqeq, hcov⟩
      · exact Or.inr ⟨Subtype.ext hxeq.symm, Or.inl hcov⟩
      · exact Or.inl ⟨hqeq.symm, Or.inr hcov⟩
  · rintro (⟨hqeq, hcov | hcov⟩ | ⟨hxeq, hcov | hcov⟩)
    · exact Or.inl (h1.mpr (Or.inr ⟨hqeq, hcov⟩))
    · exact Or.inr (h2.mpr (Or.inr ⟨hqeq.symm, hcov⟩))
    · exact Or.inr (h2.mpr (Or.inl ⟨(Subtype.ext_iff.mp hxeq).symm, hcov⟩))
    · exact Or.inl (h1.mpr (Or.inl ⟨Subtype.ext_iff.mp hxeq, hcov⟩))

end JIAdj

-- [D-0349] row_col_rel_iso
theorem row_col_rel_iso {A B : Type*} [Nonempty A] [Nonempty B]
    (leA : A → A → Prop) (leB : B → B → Prop)
    (hAref : ∀ a, leA a a) (hBref : ∀ b, leB b b)
    (φ : A × B ≃ A × B)
    (hφord : ∀ v w : A × B, (leA v.1 w.1 ∧ leB v.2 w.2) ↔
        (leA (φ v).1 (φ w).1 ∧ leB (φ v).2 (φ w).2))
    (γA : A ≃ A) (γB : B ≃ B) (hdecomp : ∀ p, φ p = (γA p.1, γB p.2)) :
    (∀ a1 a2 : A, leA a1 a2 ↔ leA (γA a1) (γA a2)) ∧
    (∀ b1 b2 : B, leB b1 b2 ↔ leB (γB b1) (γB b2)) := by
  constructor
  · intro a1 a2
    obtain ⟨b0⟩ := ‹Nonempty B›
    have h1 := hφord (a1, b0) (a2, b0)
    rw [hdecomp (a1, b0), hdecomp (a2, b0)] at h1
    simpa [hBref] using h1
  · intro b1 b2
    obtain ⟨a0⟩ := ‹Nonempty A›
    have h1 := hφord (a0, b1) (a0, b2)
    rw [hdecomp (a0, b1), hdecomp (a0, b2)] at h1
    simpa [hAref] using h1

section JIOrder
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0350] jiEquiv_le_iff
theorem jiEquiv_le_iff (p1 p2 : P × {x : P // JoinIrred P x}) :
    jiEquiv p1 ≤ jiEquiv p2 ↔ p1.2.1 ≤ p2.2.1 ∧ p2.1 ≤ p1.1 := by
  obtain ⟨q1, x1v, hx1⟩ := p1
  obtain ⟨q2, x2v, hx2⟩ := p2
  exact stepMap_le_stepMap_iff hx1.1

end JIOrder

section JHOrderLevelFull
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]
  [Nonempty {x : P // JoinIrred P x}]

-- [D-0351] joinIrred_atomOf
theorem joinIrred_atomOf : JoinIrred P (atomOf P) := by
  refine ⟨atomOf_ne_bot P, ?_⟩
  intro b c hbc
  by_cases hb : b = ⊥
  · right; rw [hb, bot_sup_eq] at hbc; exact hbc
  · left
    have h1 : b ≤ atomOf P := by rw [hbc]; exact le_sup_left
    exact le_antisymm (atomOf_le hb) h1

-- [D-0352] instOrderBotJI
noncomputable instance instOrderBotJI :
    OrderBot {x : P // JoinIrred P x} where
  bot := ⟨atomOf P, joinIrred_atomOf⟩
  bot_le := fun x => atomOf_le x.2.1

-- [D-0353] isAtomic_of_finite
theorem isAtomic_of_finite {α : Type*} [PartialOrder α] [Finite α] [OrderBot α] :
    IsAtomic α :=
  isAtomic_of_orderBot_wellFounded_lt (Finite.wellFounded_of_trans_of_irrefl _)

-- [D-0354] inst-IsAtomic
noncomputable instance : IsAtomic {x : P // JoinIrred P x} :=
  isAtomic_of_finite

-- [D-0355] inst-IsAtomic
noncomputable instance : IsAtomic (Pᵒᵈ) := isAtomic_of_finite

-- [D-0356] isAtom_toDual_coatomOf
theorem isAtom_toDual_coatomOf :
    IsAtom (α := Pᵒᵈ) (OrderDual.toDual (coatomOf P)) := by
  constructor
  · intro h; exact coatomOf_ne_top P (congrArg OrderDual.ofDual h)
  · intro b hb
    have hb' : coatomOf P < OrderDual.ofDual b := hb
    show b = OrderDual.toDual (⊤ : P)
    by_contra hbt
    have hne : OrderDual.ofDual b ≠ (⊤ : P) := fun hc => hbt (congrArg OrderDual.toDual hc)
    exact absurd (lt_of_lt_of_le hb' (coatomOf_le hne)) (lt_irrefl _)

-- [D-0357] toDual_atom_unique
theorem toDual_atom_unique (k : Pᵒᵈ) (hk : IsAtom k) :
    k = OrderDual.toDual (coatomOf P) := by
  have hkt : OrderDual.ofDual k ≠ (⊤ : P) := fun h => hk.1 (congrArg OrderDual.toDual h)
  rcases eq_or_lt_of_le (coatomOf_le hkt) with h | h
  · exact congrArg OrderDual.toDual h
  · exact absurd (congrArg OrderDual.ofDual (hk.2 (OrderDual.toDual (coatomOf P)) h))
      (coatomOf_ne_top P)

-- [D-0358] jiOrderIso
noncomputable def jiOrderIso :
    (Pᵒᵈ × {x : P // JoinIrred P x}) ≃o {f : EndP P // JoinIrred (EndP P) f} where
  toFun p := jiEquiv (OrderDual.ofDual p.1, p.2)
  invFun f := (OrderDual.toDual (jiEquiv.symm f).1, (jiEquiv.symm f).2)
  left_inv p := by
    have h := jiEquiv.symm_apply_apply (OrderDual.ofDual p.1, p.2)
    simp only [h]; rfl
  right_inv f := by
    show jiEquiv ((jiEquiv.symm f).1, (jiEquiv.symm f).2) = f
    exact jiEquiv.apply_symm_apply f
  map_rel_iff' := by
    intro p q
    show (jiEquiv (OrderDual.ofDual p.1, p.2) : {f : EndP P // JoinIrred (EndP P) f})
        ≤ jiEquiv (OrderDual.ofDual q.1, q.2) ↔ _
    rw [jiEquiv_le_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

-- [D-0359] jh_free
theorem jh_free
    (φ : {f : EndP P // JoinIrred (EndP P) f} ≃ {f : EndP P // JoinIrred (EndP P) f})
    (hφord : ∀ v w, v ≤ w ↔ φ v ≤ φ w) :
    ∃ (γA : P ≃ P) (γB : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x}),
      (∀ a1 a2, a1 ≤ a2 ↔ γA a1 ≤ γA a2) ∧
      (∀ b1 b2, b1 ≤ b2 ↔ γB b1 ≤ γB b2) ∧
      (∀ p : P × {x : P // JoinIrred P x}, φ (jiEquiv p) = jiEquiv (γA p.1, γB p.2)) := by
  classical
  let Φ : {f : EndP P // JoinIrred (EndP P) f} ≃o {f : EndP P // JoinIrred (EndP P) f} :=
    { toEquiv := φ, map_rel_iff' := fun {v w} => (hφord v w).symm }
  let Ψ : (Pᵒᵈ × {x : P // JoinIrred P x}) ≃o (Pᵒᵈ × {x : P // JoinIrred P x}) :=
    (jiOrderIso.trans Φ).trans jiOrderIso.symm
  have hposJ : 0 < Fintype.card {x : P // JoinIrred P x} :=
    Fintype.card_pos_iff.mpr ⟨(⊥ : {x : P // JoinIrred P x})⟩
  have hsizeJ : Fintype.card {x : P // JoinIrred P x} < Fintype.card (Pᵒᵈ) := card_joinIrred_lt
  have hdec := ProdAut.prod_decomposition_of_card (A := Pᵒᵈ)
    isAtom_toDual_coatomOf toDual_atom_unique hposJ hsizeJ Ψ
  have hdec' := ProdAut.prod_decomposition_of_card (A := Pᵒᵈ)
    isAtom_toDual_coatomOf toDual_atom_unique hposJ hsizeJ Ψ.symm
  set fA : Pᵒᵈ → Pᵒᵈ := fun a => (Ψ (a, ⊥)).1 with hfA
  set fB : {x : P // JoinIrred P x} → {x : P // JoinIrred P x} :=
    fun b => (Ψ ((⊥ : Pᵒᵈ), b)).2 with hfB
  set gA : Pᵒᵈ → Pᵒᵈ := fun a => (Ψ.symm (a, ⊥)).1 with hgA
  set gB : {x : P // JoinIrred P x} → {x : P // JoinIrred P x} :=
    fun b => (Ψ.symm ((⊥ : Pᵒᵈ), b)).2 with hgB
  have hΨ : ∀ a b, Ψ (a, b) = (fA a, fB b) := fun a b => hdec a b
  have hΨ' : ∀ a b, Ψ.symm (a, b) = (gA a, gB b) := fun a b => hdec' a b
  have hAA : ∀ a, gA (fA a) = a := by
    intro a
    have h := Ψ.symm_apply_apply (a, (⊥ : {x : P // JoinIrred P x}))
    rw [hΨ a ⊥, hΨ' (fA a) (fB ⊥)] at h
    exact congrArg Prod.fst h
  have hAA' : ∀ a, fA (gA a) = a := by
    intro a
    have h := Ψ.apply_symm_apply (a, (⊥ : {x : P // JoinIrred P x}))
    rw [hΨ' a ⊥, hΨ (gA a) (gB ⊥)] at h
    exact congrArg Prod.fst h
  have hBB : ∀ b, gB (fB b) = b := by
    intro b
    have h := Ψ.symm_apply_apply ((⊥ : Pᵒᵈ), b)
    rw [hΨ ⊥ b, hΨ' (fA ⊥) (fB b)] at h
    exact congrArg Prod.snd h
  have hBB' : ∀ b, fB (gB b) = b := by
    intro b
    have h := Ψ.apply_symm_apply ((⊥ : Pᵒᵈ), b)
    rw [hΨ' ⊥ b, hΨ (gA ⊥) (gB b)] at h
    exact congrArg Prod.snd h
  refine ⟨⟨fA, gA, hAA, hAA'⟩, ⟨fB, gB, hBB, hBB'⟩, ?_, ?_, ?_⟩
  · intro a1 a2
    have h := Ψ.map_rel_iff (a := (a2, (⊥ : {x : P // JoinIrred P x}))) (b := (a1, ⊥))
    rw [hΨ a2 ⊥, hΨ a1 ⊥] at h
    constructor
    · intro hle
      exact (h.mpr ⟨hle, le_rfl⟩).1
    · intro hle
      exact (h.mp ⟨hle, le_rfl⟩).1
  · intro b1 b2
    have h := Ψ.map_rel_iff (a := ((⊥ : Pᵒᵈ), b1)) (b := (⊥, b2))
    rw [hΨ ⊥ b1, hΨ ⊥ b2] at h
    show b1 ≤ b2 ↔ fB b1 ≤ fB b2
    exact ⟨fun hle => (h.mpr ⟨le_rfl, hle⟩).2, fun hle => (h.mp ⟨le_rfl, hle⟩).2⟩
  · rintro ⟨q, x⟩
    have h : Ψ (OrderDual.toDual q, x) = (fA (OrderDual.toDual q), fB x) := hΨ _ _
    have h2 : jiOrderIso (Ψ (OrderDual.toDual q, x)) = φ (jiEquiv (q, x)) := by
      show jiOrderIso (jiOrderIso.symm (Φ (jiOrderIso (OrderDual.toDual q, x)))) = _
      rw [jiOrderIso.apply_symm_apply]
      rfl
    rw [h] at h2
    exact h2.symm

-- [D-0360] jh_product_order_level_full
theorem jh_product_order_level_full
    (hBconn : (Graph.Hasse {x : P // JoinIrred P x}).Connected)
    (φ : {f : EndP P // JoinIrred (EndP P) f} ≃ {f : EndP P // JoinIrred (EndP P) f})
    (hφadj : ∀ v w, (Graph.Hasse {f : EndP P // JoinIrred (EndP P) f}).adj v w ↔
        (Graph.Hasse {f : EndP P // JoinIrred (EndP P) f}).adj (φ v) (φ w))
    (hφord : ∀ v w, v ≤ w ↔ φ v ≤ φ w) :
    ∃ (γA : P ≃ P) (γB : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x}),
      (∀ a1 a2, a1 ≤ a2 ↔ γA a1 ≤ γA a2) ∧
      (∀ b1 b2, b1 ≤ b2 ↔ γB b1 ≤ γB b2) ∧
      (∀ p : P × {x : P // JoinIrred P x}, φ (jiEquiv p) = jiEquiv (γA p.1, γB p.2)) :=
  jh_free φ hφord

end JHOrderLevelFull

section PhiHat
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0361] stepMap_bot
theorem stepMap_bot (q : P) : (stepMap (⊥ : P) q : EndP P) = ⊥ := by
  apply OrderHom.ext; funext y
  by_cases hqy : q ≤ y
  · rw [stepMap_apply_of_ge (⊥ : P) q hqy, endPBot_apply]
  · rw [stepMap_apply_of_not_ge (⊥ : P) q hqy, endPBot_apply]

-- [D-0362] stepMap_finset_sup
theorem stepMap_finset_sup {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → P) (q : P) :
    (stepMap (s.sup f) q : EndP P) = s.sup (fun i => (stepMap (f i) q : EndP P)) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sup_empty]; exact stepMap_bot q
  | insert i t hi ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih, stepMap_join]

-- [D-0363] orderIso_finset_sup
theorem orderIso_finset_sup {L : Type*} [Lattice L] [OrderBot L] {ι : Type*} [DecidableEq ι]
    (Ψ : L ≃o L) (s : Finset ι) (f : ι → L) :
    Ψ (s.sup f) = s.sup (fun i => Ψ (f i)) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sup_empty]; exact OrderIso.map_bot Ψ
  | insert i t hi ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Ψ.map_sup, ih]

-- [D-0364] tauHat
noncomputable def tauHat (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x}) (v : P) : P :=
  (Finset.univ.filter (fun x : P => JoinIrred P x ∧ x ≤ v)).sup
    (fun x => if hx : JoinIrred P x then (τ ⟨x, hx⟩).1 else ⊥)

-- [D-0365] tauHat_monotone
theorem tauHat_monotone (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x}) :
    Monotone (tauHat τ) := by
  intro v1 v2 hv
  apply Finset.sup_le
  intro x hx
  apply Finset.le_sup (f := fun x => if hx : JoinIrred P x then (τ ⟨x, hx⟩).1 else ⊥)
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.trans hv⟩

-- [D-0366] phi_hat_vertical_general
theorem phi_hat_vertical_general
    (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x})
    (Ψ : EndP P ≃o EndP P)
    (hvert : ∀ (x : P) (hx : JoinIrred P x) (q : P), Ψ (stepMap x q) = stepMap (τ ⟨x, hx⟩).1 q)
    (v q : P) :
    Ψ (stepMap v q) = stepMap (tauHat τ v) q := by
  have hveq : (stepMap v q : EndP P) =
      (Finset.univ.filter (fun x : P => JoinIrred P x ∧ x ≤ v)).sup
        (fun x => (stepMap x q : EndP P)) := by
    conv_lhs => rw [finite_lattice_eq_sup_joinIrreds v]
    rw [stepMap_finset_sup]
    apply Finset.sup_congr rfl
    intro x _
    rfl
  rw [hveq, orderIso_finset_sup]
  unfold tauHat
  rw [stepMap_finset_sup]
  apply Finset.sup_congr rfl
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [dif_pos hx.2.1, hvert x hx.2.1 q]

-- [D-0367] phi_hat_closed_form
theorem phi_hat_closed_form
    (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x})
    (Ψ : EndP P ≃o EndP P)
    (hvert : ∀ (x : P) (hx : JoinIrred P x) (q : P), Ψ (stepMap x q) = stepMap (τ ⟨x, hx⟩).1 q)
    (g : EndP P) (y : P) :
    Ψ g y = tauHat τ (g y) := by
  have hg : g = Finset.univ.sup (fun q => (stepMap (g q) q : EndP P)) := endP_stepMap_sup_eq_self g
  have hΨg : Ψ g = Finset.univ.sup (fun q => (stepMap (tauHat τ (g q)) q : EndP P)) := by
    conv_lhs => rw [hg]
    rw [orderIso_finset_sup]
    apply Finset.sup_congr rfl
    intro q _
    exact phi_hat_vertical_general τ Ψ hvert (g q) q
  rw [hΨg, endP_finset_sup_apply]
  apply le_antisymm
  · apply Finset.sup_le
    intro q _
    by_cases hqy : q ≤ y
    · rw [stepMap_apply_of_ge (tauHat τ (g q)) q hqy]
      exact tauHat_monotone τ (g.monotone hqy)
    · rw [stepMap_apply_of_not_ge (tauHat τ (g q)) q hqy]
      exact bot_le
  · calc tauHat τ (g y) = (stepMap (tauHat τ (g y)) y : EndP P) y := (stepMap_apply_self _ y).symm
      _ ≤ Finset.univ.sup (fun q => (stepMap (tauHat τ (g q)) q : EndP P) y) :=
          Finset.le_sup (f := fun q => (stepMap (tauHat τ (g q)) q : EndP P) y) (Finset.mem_univ y)

-- [D-0368] tauHat_injective
theorem tauHat_injective
    (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x})
    (Ψ : EndP P ≃o EndP P)
    (hvert : ∀ (x : P) (hx : JoinIrred P x) (q : P), Ψ (stepMap x q) = stepMap (τ ⟨x, hx⟩).1 q) :
    Function.Injective (tauHat τ) := by
  intro p1 p2 heq
  have h1 : Ψ (constHom p1 : EndP P) = Ψ (constHom p2 : EndP P) := by
    apply OrderHom.ext; funext y
    have e1 := phi_hat_closed_form τ Ψ hvert (constHom p1) y
    have e2 := phi_hat_closed_form τ Ψ hvert (constHom p2) y
    rw [constHom_apply] at e1 e2
    rw [e1, e2, heq]
  have h2 : (constHom p1 : EndP P) = constHom p2 := Ψ.injective h1
  have h3 : (constHom p1 : EndP P) ⊥ = (constHom p2 : EndP P) ⊥ := by rw [h2]
  rwa [constHom_apply, constHom_apply] at h3

-- [D-0369] tauHat_le_iff
theorem tauHat_le_iff
    (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x})
    (Ψ : EndP P ≃o EndP P)
    (hvert : ∀ (x : P) (hx : JoinIrred P x) (q : P), Ψ (stepMap x q) = stepMap (τ ⟨x, hx⟩).1 q)
    (v v' : P) :
    tauHat τ v ≤ tauHat τ v' ↔ v ≤ v' := by
  have hcv : Ψ (constHom v : EndP P) = constHom (tauHat τ v) := by
    apply OrderHom.ext; funext y
    rw [phi_hat_closed_form τ Ψ hvert (constHom v) y, constHom_apply, constHom_apply]
  have hcv' : Ψ (constHom v' : EndP P) = constHom (tauHat τ v') := by
    apply OrderHom.ext; funext y
    rw [phi_hat_closed_form τ Ψ hvert (constHom v') y, constHom_apply, constHom_apply]
  constructor
  · intro h
    have h1 : (constHom (tauHat τ v) : EndP P) ≤ constHom (tauHat τ v') := by
      rw [OrderHom.le_def]; intro y; rw [constHom_apply, constHom_apply]; exact h
    rw [← hcv, ← hcv'] at h1
    have h2 := Ψ.le_iff_le.mp h1
    have h3 := OrderHom.le_def.mp h2 (⊥ : P)
    rwa [constHom_apply, constHom_apply] at h3
  · intro h; exact tauHat_monotone τ h

end PhiHat

-- [D-0370] HasUniqueDownCover
def HasUniqueDownCover {α : Type*} [Preorder α] (b : α) : Prop :=
  ∃ a, Covers a b ∧ ∀ a', Covers a' b → a' = a

-- [D-0371] HasUniqueUpCover
def HasUniqueUpCover {α : Type*} [Preorder α] (a : α) : Prop :=
  ∃ b, Covers a b ∧ ∀ b', Covers a b' → b' = b

-- [D-0372] not_hasUniqueUpCover_of_second
theorem not_hasUniqueUpCover_of_second {α : Type*} [Preorder α] {a b : α}
    (hab : Covers a b) {b2 : α} (hb2 : Covers a b2) (hne : b2 ≠ b) :
    ¬ HasUniqueUpCover a := by
  rintro ⟨c, _, huniq⟩
  exact hne ((huniq b2 hb2).trans (huniq b hab).symm)

-- [D-0373] not_hasUniqueDownCover_of_second
theorem not_hasUniqueDownCover_of_second {α : Type*} [Preorder α] {a b : α}
    (hab : Covers a b) {a2 : α} (ha2 : Covers a2 b) (hne : a2 ≠ a) :
    ¬ HasUniqueDownCover b := by
  rintro ⟨c, _, huniq⟩
  exact hne ((huniq a2 ha2).trans (huniq a hab).symm)

-- [D-0374] hasUniqueUpCover_of_covers_top
theorem hasUniqueUpCover_of_covers_top {α : Type*} [PartialOrder α] [OrderTop α] {b : α}
    (h : Covers b (⊤ : α)) : HasUniqueUpCover b :=
  ⟨⊤, h, fun c hc => by
    by_contra hne
    exact h.2 c hc.1 (lt_top_iff_ne_top.mpr hne)⟩

section Sig1BreakAssembled
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0375] hasUniqueDownCover_top
theorem hasUniqueDownCover_top : HasUniqueDownCover (⊤ : P) :=
  ⟨coatomOf P, coatomOf_covers_top, fun a' ha' => eq_coatomOf_of_covers_top ha'⟩

-- [D-0376] hasUniqueUpCover_bot
theorem hasUniqueUpCover_bot : HasUniqueUpCover (⊥ : P) :=
  ⟨atomOf P, atomOf_covers_bot, fun b' hb' => eq_atomOf_of_covers_bot hb'⟩

-- [D-0377] updateAt_witness_eq_of_covers
theorem updateAt_witness_eq_of_covers (f : EndP P) {x0 x0' : P} {v v' : P}
    (hv_le : v ≤ f x0) (hv_ge : joinBelow f x0 ≤ v)
    (hv_le' : v' ≤ f x0') (hv_ge' : joinBelow f x0' ≤ v') (hcov' : Covers v' (f x0'))
    (heq : updateAt f x0 v hv_le hv_ge = updateAt f x0' v' hv_le' hv_ge') :
    x0 = x0' := by
  by_contra hne
  have h1 : (updateAt f x0 v hv_le hv_ge) x0' = f x0' :=
    updateAt_apply_ne f x0 v hv_le hv_ge (Ne.symm hne)
  have h2 : (updateAt f x0' v' hv_le' hv_ge') x0' = v' := updateAt_apply_self f x0' v' hv_le' hv_ge'
  rw [heq, h2] at h1
  exact hcov'.1.ne h1

-- [D-0378] updateAtUp_witness_eq_of_covers
theorem updateAtUp_witness_eq_of_covers (f : EndP P) {x0 x0' : P} {v v' : P}
    (hv_ge : f x0 ≤ v) (hv_le : v ≤ meetAbove f x0)
    (hv_ge' : f x0' ≤ v') (hv_le' : v' ≤ meetAbove f x0') (hcov' : Covers (f x0') v')
    (heq : updateAtUp f x0 v hv_ge hv_le = updateAtUp f x0' v' hv_ge' hv_le') :
    x0 = x0' := by
  by_contra hne
  have h1 : (updateAtUp f x0 v hv_ge hv_le) x0' = f x0' :=
    updateAtUp_apply_ne f x0 v hv_ge hv_le (Ne.symm hne)
  have h2 : (updateAtUp f x0' v' hv_ge' hv_le') x0' = v' := updateAtUp_apply_self f x0' v' hv_ge' hv_le'
  rw [heq, h2] at h1
  exact hcov'.1.ne h1.symm

-- [D-0379] deg11_down_cover_not_uniqueUpCover
theorem deg11_down_cover_not_uniqueUpCover
    (hbt : (⊥ : P) ≠ ⊤) (hnb : (⊥ : P) ≠ coatomOf P)
    (f : EndP P) (hdc : HasUniqueDownCover f) (huc : HasUniqueUpCover f)
    (g : EndP P) (hgcov : Covers g f) :
    ¬ HasUniqueUpCover g := by
  obtain ⟨g0, hg0cov, hguniq0⟩ := hdc
  have hgeq0 : g = g0 := hguniq0 g hgcov
  have hguniq : ∀ a', Covers a' f → a' = g :=
    fun a' ha' => (hguniq0 a' ha').trans hgeq0.symm
  obtain ⟨h, hhcov, hhuniq⟩ := huc
  obtain ⟨p0, v0, hv_le0, hv_ge0, hgeq, hcov0, hforced_down⟩ :=
    forced_eq_joinBelow_of_unique_cover f g hgcov hguniq
  obtain ⟨p1, w1, hv_ge1, hv_le1, hheq, hcov1, hforced_up⟩ :=
    forced_eq_meetAbove_of_unique_cover f h hhcov hhuniq
  by_cases hp01 : p0 = p1
  · exfalso
    have hgp : ∀ x0 v hv_le hv_ge, g = updateAt f x0 v hv_le hv_ge → x0 = p0 := by
      intro x0 v hv_le hv_ge heq2
      exact updateAt_witness_eq_of_covers f hv_le hv_ge hv_le0 hv_ge0 hcov0 (heq2.symm.trans hgeq)
    have hhp : ∀ x0 v hv_ge hv_le, h = updateAtUp f x0 v hv_ge hv_le → x0 = p0 := by
      intro x0 v hv_ge hv_le heq2
      rw [hp01]
      exact updateAtUp_witness_eq_of_covers f hv_ge hv_le hv_ge1 hv_le1 hcov1 (heq2.symm.trans hheq)
    exact dcnmi_same_general f hbt p0 g hgcov hguniq hgp h hhcov hhuniq hhp
  · rw [hgeq]
    obtain ⟨h2, hcov_h2, hne⟩ := sig1break_p0_ne_p1_second_upcover f hnb p0 v0 hv_le0 hv_ge0 hcov0
      hforced_down p1 w1 hv_ge1 hv_le1 hcov1 hforced_up hp01
    have hcov_gf : Covers (updateAt f p0 v0 hv_le0 hv_ge0) f := by rw [← hgeq]; exact hgcov
    exact not_hasUniqueUpCover_of_second hcov_gf hcov_h2 hne

-- [D-0380] deg11_down_cover_not_covers_top
theorem deg11_down_cover_not_covers_top
    (hbt : (⊥ : P) ≠ ⊤) (hnb : (⊥ : P) ≠ coatomOf P)
    (f : EndP P) (hdc : HasUniqueDownCover f) (huc : HasUniqueUpCover f)
    (g : EndP P) (hgcov : Covers g f) :
    ¬ Covers g (⊤ : EndP P) := fun hcovtop =>
  deg11_down_cover_not_uniqueUpCover hbt hnb f hdc huc g hgcov
    (hasUniqueUpCover_of_covers_top hcovtop)

end Sig1BreakAssembled
section CoversGlueA
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0381] covers_glueA_of_covers
theorem covers_glueA_of_covers (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x' x : P)
    (hcov : Covers x' x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueA m x') (glueA m x) := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine ⟨(glueA_lt_iff m hm hmt hbt x' x).mpr hcov.1, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w | w | w
  · have hc1' : x' < w := (glueA_lt_iff m hm hmt hbt x' w).mp hc1
    have hc2' : w < x := (glueA_lt_iff m hm hmt hbt w x).mp hc2
    exact hcov.2 w hc1' hc2'
  · have hwb : w ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hle : leGlue m (iotaB m w) (iotaA m x) := by
      show leGlue m (iotaB m w) (Sum.inl x)
      rw [iotaB_generic_eq m w hwb]; exact hc2.le
    exact not_leGlue_iotaB_iotaA_of_ne_bot m w x hm hbt hwb hle
  · have hwb : w ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hwm : w ≠ m := by
      rintro rfl
      simp [canon, hwb] at hcvfix
    have hle : leGlue m (iotaC m w) (iotaA m x) := by
      show leGlue m (iotaC m w) (Sum.inl x)
      rw [iotaC_generic_eq m w hwb hwm]; exact hc2.le
    exact not_leGlue_iotaC_iotaA_of_ne_bot_ne_m m w x hm hwb hwm hle

-- [D-0382] covers_glueA_shape
theorem covers_glueA_shape (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x : P)
    (g : GlueCar (P := P) m)
    (hgcov : letI := glueCarPartialOrder m hm hmt hbt; Covers g (glueA m x)) :
    ∃ x', g = glueA m x' ∧ Covers x' x := by
  letI := glueCarPartialOrder m hm hmt hbt
  obtain ⟨cv, hcvfix⟩ := g
  rcases cv with w | w | w
  · refine ⟨w, rfl, (glueA_lt_iff m hm hmt hbt w x).mp hgcov.1, ?_⟩
    intro y hy1 hy2
    exact hgcov.2 (glueA m y) ((glueA_lt_iff m hm hmt hbt w y).mpr hy1)
      ((glueA_lt_iff m hm hmt hbt y x).mpr hy2)
  · exfalso
    have hwb : w ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hle : leGlue m (iotaB m w) (iotaA m x) := by
      show leGlue m (iotaB m w) (Sum.inl x)
      rw [iotaB_generic_eq m w hwb]; exact hgcov.1.le
    exact not_leGlue_iotaB_iotaA_of_ne_bot m w x hm hbt hwb hle
  · exfalso
    have hwb : w ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hwm : w ≠ m := by
      rintro rfl
      simp [canon, hwb] at hcvfix
    have hle : leGlue m (iotaC m w) (iotaA m x) := by
      show leGlue m (iotaC m w) (Sum.inl x)
      rw [iotaC_generic_eq m w hwb hwm]; exact hgcov.1.le
    exact not_leGlue_iotaC_iotaA_of_ne_bot_ne_m m w x hm hwb hwm hle

-- [D-0383] hasUniqueDownCover_glueA_iff
theorem hasUniqueDownCover_glueA_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : P) :
    letI := glueCarPartialOrder m hm hmt hbt
    HasUniqueDownCover (glueA m x) ↔ HasUniqueDownCover x := by
  letI := glueCarPartialOrder m hm hmt hbt
  constructor
  · rintro ⟨g, hgcov, hguniq⟩
    obtain ⟨x', hgeq, hx'cov⟩ := covers_glueA_shape m hm hmt hbt x g hgcov
    refine ⟨x', hx'cov, fun a' ha' => ?_⟩
    have heq := hguniq (glueA m a') (covers_glueA_of_covers m hm hmt hbt a' x ha')
    rw [hgeq] at heq
    exact glueA_injective m heq
  · rintro ⟨a, hacov, hauniq⟩
    refine ⟨glueA m a, covers_glueA_of_covers m hm hmt hbt a x hacov, fun g' hg'cov => ?_⟩
    obtain ⟨x', hgeq, hx'cov⟩ := covers_glueA_shape m hm hmt hbt x g' hg'cov
    rw [hgeq, hauniq x' hx'cov]

-- [D-0384] hasUniqueDownCover_glueA_top_iff
theorem hasUniqueDownCover_glueA_top_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    HasUniqueDownCover (glueA m (⊤ : P)) ↔ HasUniqueDownCover (⊤ : P) :=
  hasUniqueDownCover_glueA_iff m hm hmt hbt ⊤

end CoversGlueA

section GlueBTransfer
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0385] glueB
def glueB (m : P) (x : P) (hx : x ≠ ⊥) : GlueCar (P := P) m :=
  ⟨Sum.inr (Sum.inl x), by simp only [canon]; rw [if_neg hx]⟩

-- [D-0386] glueB_injective
theorem glueB_injective (m : P) {x y : P} (hx : x ≠ ⊥) (hy : y ≠ ⊥)
    (h : glueB m x hx = glueB m y hy) : x = y := by
  have hv : (Sum.inr (Sum.inl x) : GlueBase P) = Sum.inr (Sum.inl y) := congrArg Subtype.val h
  simpa using hv

-- [D-0387] glueL
def glueL (m : P) (hm : m ≠ ⊥) : GlueCar (P := P) m := glueB m m hm

-- [D-0388] leGlue_tagA_skelL_iff
theorem leGlue_tagA_skelL_iff (m w : P) (hmt : m ≠ ⊤) :
    leGlue m (Sum.inl w) (skelL m) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsL : occs m (skelL m) = [skelL m] := by
      simp only [occs, skelL]; rw [if_neg hmt]
    rw [hoccsL] at hv
    have hv' : v = skelL m := by simpa using hv
    subst hv'
    rcases occs_inl_mem m w hu with hu' | ⟨hwm, hu'⟩ | ⟨hwt, hu'⟩ <;> subst hu'
    · exact huv
    · exact le_of_eq hwm
    · exact huv.elim
  · intro hwle
    exact ⟨Sum.inl w, self_mem_occs m _, skelL m, self_mem_occs m _, hwle⟩

-- [D-0389] leGlue_tagB_skelL_iff
theorem leGlue_tagB_skelL_iff (m w : P) (hmt : m ≠ ⊤) (hwb : w ≠ ⊥) :
    leGlue m (Sum.inr (Sum.inl w)) (skelL m) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsL : occs m (skelL m) = [skelL m] := by
      simp only [occs, skelL]; rw [if_neg hmt]
    rw [hoccsL] at hv
    have hv' : v = skelL m := by simpa using hv
    subst hv'
    rw [← iotaB_generic_eq m w hwb] at hu
    rcases occs_iotaB_mem m w hu with ⟨_, _, hu'⟩ | ⟨hwb', _⟩ | ⟨hwt, hu' | hu'⟩
    · subst hu'; exact huv
    · exact absurd hwb' hwb
    · subst hwt; subst hu'; exact huv
    · subst hwt; subst hu'; exact huv.elim
  · intro hwle
    exact ⟨Sum.inr (Sum.inl w), self_mem_occs m _, skelL m, self_mem_occs m _, hwle⟩

-- [D-0390] not_leGlue_tagC_skelL
theorem not_leGlue_tagC_skelL (m w : P) (hmt : m ≠ ⊤) :
    ¬ leGlue m (Sum.inr (Sum.inr w)) (skelL m) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hoccsL : occs m (skelL m) = [skelL m] := by
    simp only [occs, skelL]; rw [if_neg hmt]
  rw [hoccsL] at hv
  have hv' : v = skelL m := by simpa using hv
  subst hv'
  have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs] using hu
  subst hu'
  exact huv.elim

-- [D-0391] leGlue_tagB_tagB_imp
theorem leGlue_tagB_tagB_imp (m w w' : P) (hwt : w ≠ ⊤)
    (h : leGlue m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inl w'))) : w ≤ w' := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  have hoccsw : occs m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
    simp only [occs]; rw [if_neg hwt]
  rw [hoccsw] at hu
  have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
  subst hu'
  by_cases hw't : w' = ⊤
  · subst hw't; exact le_top
  · have hoccsw' : occs m (Sum.inr (Sum.inl w')) = [Sum.inr (Sum.inl w')] := by
      simp only [occs]; rw [if_neg hw't]
    rw [hoccsw'] at hv
    have hv' : v = Sum.inr (Sum.inl w') := by simpa using hv
    subst hv'
    exact huv

-- [D-0392] not_leGlue_tagB_tagA
theorem not_leGlue_tagB_tagA (m w w' : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (hw : w ≠ ⊥) :
    ¬ leGlue m (Sum.inr (Sum.inl w)) (Sum.inl w') := by
  rintro ⟨u, hu, v, hv, huv⟩
  by_cases hwt : w = ⊤
  · subst hwt
    have hoccsw : occs m (Sum.inr (Sum.inl (⊤ : P))) =
        [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by simp [occs]
    rw [hoccsw] at hu
    have hu' : u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m) := by simpa using hu
    rcases hu' with hu' | hu'
    · subst hu'
      rcases occs_inl_mem m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
      · subst hv'; exact huv.elim
      · subst hv'; exact hbt (le_antisymm huv bot_le).symm
      · subst hv'; exact hm (le_bot_iff.mp huv)
    · subst hu'
      rcases occs_inl_mem m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
      · subst hv'; exact huv.elim
      · subst hv'; exact huv.elim
      · subst hv'; exact hm (le_bot_iff.mp huv)
  · have hoccsw : occs m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
      simp only [occs]; rw [if_neg hwt]
    rw [hoccsw] at hu
    have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
    subst hu'
    rcases occs_inl_mem m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
    · subst hv'; exact huv.elim
    · subst hv'; exact hw (le_bot_iff.mp huv)
    · subst hv'; exact hm (le_bot_iff.mp huv)

-- [D-0393] covers_glueB_of_covers
theorem covers_glueB_of_covers (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (w : P) (hw : w ≠ ⊥) (hwcov : Covers w m) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueB m w hw) (glueL m hm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hle : glueB m w hw ≤ glueL m hm := by
    rw [GlueCar.le_def]; exact (leGlue_tagB_skelL_iff m w hmt hw).mpr hwcov.1.le
  have hne : glueB m w hw ≠ glueL m hm :=
    fun heq => hwcov.1.ne (glueB_injective m hw hm heq)
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w' | w' | w'
  · exact not_leGlue_tagB_tagA m w w' hm hbt hw hc1.le
  · have hwt : w ≠ ⊤ := (hwcov.1.trans_le le_top).ne
    have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hww' : w ≤ w' := leGlue_tagB_tagB_imp m w w' hwt hc1.le
    have hw'm : w' ≤ m := (leGlue_tagB_skelL_iff m w' hmt hw'b).mp hc2.le
    have hw'ne : w' ≠ w := by
      rintro rfl
      exact hc1.ne rfl
    have hw'm' : w' ≠ m := by
      rintro rfl
      exact hc2.ne rfl
    exact hwcov.2 w' (hww'.lt_of_ne (Ne.symm hw'ne)) (hw'm.lt_of_ne hw'm')
  · exact not_leGlue_tagC_skelL m w' hmt hc2.le

-- [D-0394] covers_glueA_m_of_covers_bot
theorem covers_glueA_m_of_covers_bot (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hbot : Covers (⊥ : P) m) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueA m m) (glueL m hm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hle : glueA m m ≤ glueL m hm := by
    rw [GlueCar.le_def]; exact (leGlue_tagA_skelL_iff m m hmt).mpr le_rfl
  have hne : glueA m m ≠ glueL m hm := by
    intro heq
    have hv : (Sum.inl m : GlueBase P) = Sum.inr (Sum.inl m) := congrArg Subtype.val heq
    exact absurd hv (by simp)
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w' | w' | w'
  · have hmw'' : m < w' := (glueA_lt_iff m hm hmt hbt m w').mp hc1
    have hw'm : w' ≤ m := (leGlue_tagA_skelL_iff m w' hmt).mp hc2.le
    exact absurd (hmw''.trans_le hw'm) (lt_irrefl m)
  · have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hw'm : w' ≤ m := (leGlue_tagB_skelL_iff m w' hmt hw'b).mp hc2.le
    have hw'm' : w' ≠ m := by
      rintro rfl
      exact hc2.ne rfl
    have hbotw' : (⊥ : P) < w' := lt_of_le_of_ne bot_le (Ne.symm hw'b)
    exact hbot.2 w' hbotw' (hw'm.lt_of_ne hw'm')
  · exact not_leGlue_tagC_skelL m w' hmt hc2.le

-- [D-0395] leGlue_tagA_tagB_of_le
theorem leGlue_tagA_tagB_of_le (m x y : P) (hxm : x ≤ m) :
    leGlue m (Sum.inl x) (Sum.inr (Sum.inl y)) :=
  ⟨Sum.inl x, self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, hxm⟩

-- [D-0396] glueA_lt_glueB_of_le
theorem glueA_lt_glueB_of_le (m x y : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hxm : x ≤ m) (hy : y ≠ ⊥) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m x < glueB m y hy := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueA, glueB] at hv)
  rw [GlueCar.le_def]; exact leGlue_tagA_tagB_of_le m x y hxm

-- [D-0397] glueB_lt_glueB_of_lt
theorem glueB_lt_glueB_of_lt (m x y : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hxy : x < y) (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueB m x hx < glueB m y hy := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => hxy.ne (glueB_injective m hx hy heq))
  rw [GlueCar.le_def]
  exact ⟨Sum.inr (Sum.inl x), self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, hxy.le⟩

-- [D-0398] glueB_lt_skelL_of_lt
theorem glueB_lt_skelL_of_lt (m z : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hzm : z < m) (hzb : z ≠ ⊥) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueB m z hzb < glueL m hm := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => hzm.ne (glueB_injective m hzb hm heq))
  rw [GlueCar.le_def]; exact (leGlue_tagB_skelL_iff m z hmt hzb).mpr hzm.le

-- [D-0399] glueA_m_lt_glueL
theorem glueA_m_lt_glueL (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m m < glueL m hm := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueA, glueL, glueB] at hv)
  rw [GlueCar.le_def]; exact (leGlue_tagA_skelL_iff m m hmt).mpr le_rfl

-- [D-0400] covers_glueL_shape
theorem covers_glueL_shape (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (g : GlueCar (P := P) m)
    (hgcov : letI := glueCarPartialOrder m hm hmt hbt; Covers g (glueL m hm)) :
    (g = glueA m m ∧ Covers (⊥ : P) m) ∨
    (∃ w, ∃ hw : w ≠ ⊥, g = glueB m w hw ∧ Covers w m) := by
  letI := glueCarPartialOrder m hm hmt hbt
  obtain ⟨cv, hcvfix⟩ := g
  rcases cv with w' | w' | w'
  · have hw'm : w' ≤ m := (leGlue_tagA_skelL_iff m w' hmt).mp hgcov.1.le
    have hw'eq : w' = m := by
      by_contra hne
      have hw'lt : w' < m := hw'm.lt_of_ne hne
      exact hgcov.2 (glueA m m) ((glueA_lt_iff m hm hmt hbt w' m).mpr hw'lt)
        (glueA_m_lt_glueL m hm hmt hbt)
    refine Or.inl ⟨Subtype.ext (congrArg Sum.inl hw'eq), lt_of_le_of_ne bot_le (Ne.symm hm),
      fun z hz hzm => ?_⟩
    have hzb : z ≠ ⊥ := hz.ne'
    exact hgcov.2 (glueB m z hzb)
      (glueA_lt_glueB_of_le m w' z hm hmt hbt (le_of_eq hw'eq) hzb)
      (glueB_lt_skelL_of_lt m z hm hmt hbt hzm hzb)
  · have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hw'm : w' ≤ m := (leGlue_tagB_skelL_iff m w' hmt hw'b).mp hgcov.1.le
    have hw'm' : w' ≠ m := fun heq => hgcov.1.ne (by subst heq; rfl)
    refine Or.inr ⟨w', hw'b, rfl, hw'm.lt_of_ne hw'm', fun z hz hzm => ?_⟩
    have hzb : z ≠ ⊥ := (lt_of_le_of_lt bot_le hz).ne'
    exact hgcov.2 (glueB m z hzb) (glueB_lt_glueB_of_lt m w' z hm hmt hbt hz hw'b hzb)
      (glueB_lt_skelL_of_lt m z hm hmt hbt hzm hzb)
  · exact absurd hgcov.1.le (not_leGlue_tagC_skelL m w' hmt)

-- [D-0401] hasUniqueDownCover_glueL_iff
theorem hasUniqueDownCover_glueL_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    HasUniqueDownCover (glueL m hm) ↔ HasUniqueDownCover m := by
  letI := glueCarPartialOrder m hm hmt hbt
  constructor
  · rintro ⟨g0, hg0cov, hg0uniq⟩
    rcases covers_glueL_shape m hm hmt hbt g0 hg0cov with
      ⟨hg0eq, hbot⟩ | ⟨w0, hw0b, hg0eq, hw0cov⟩
    · refine ⟨⊥, hbot, fun w hw => ?_⟩
      by_contra hwb
      have hcov := covers_glueB_of_covers m hm hmt hbt w hwb hw
      have heq := hg0uniq (glueB m w hwb) hcov
      rw [hg0eq] at heq
      have hv := congrArg Subtype.val heq
      simp [glueA, glueB] at hv
    · refine ⟨w0, hw0cov, fun w hw => ?_⟩
      by_cases hwb : w = ⊥
      · subst hwb
        have hcov := covers_glueA_m_of_covers_bot m hm hmt hbt hw
        have heq := hg0uniq (glueA m m) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueB] at hv
      · have hcov := covers_glueB_of_covers m hm hmt hbt w hwb hw
        have heq := hg0uniq (glueB m w hwb) hcov
        rw [hg0eq] at heq
        exact glueB_injective m hwb hw0b heq
  · rintro ⟨w0, hw0cov, hw0uniq⟩
    by_cases hw0b : w0 = ⊥
    · subst hw0b
      refine ⟨glueA m m, covers_glueA_m_of_covers_bot m hm hmt hbt hw0cov, fun g hgcov => ?_⟩
      rcases covers_glueL_shape m hm hmt hbt g hgcov with
        ⟨hgeq, _⟩ | ⟨w, hwb, hgeq, hwcov⟩
      · exact hgeq
      · exact absurd (hw0uniq w hwcov) hwb
    · refine ⟨glueB m w0 hw0b, covers_glueB_of_covers m hm hmt hbt w0 hw0b hw0cov,
        fun g hgcov => ?_⟩
      rcases covers_glueL_shape m hm hmt hbt g hgcov with
        ⟨hgeq, hbot⟩ | ⟨w, hwb, hgeq, hwcov⟩
      · exact absurd (hw0uniq ⊥ hbot).symm hw0b
      · have hweq : w = w0 := hw0uniq w hwcov
        subst hweq
        rw [hgeq]

end GlueBTransfer

section GlueBGeneral
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0402] leGlue_tagA_tagB_iff
theorem leGlue_tagA_tagB_iff (m w y : P) (hyt : y ≠ ⊤) :
    leGlue m (Sum.inl w) (Sum.inr (Sum.inl y)) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsy : occs m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
      simp only [occs]; rw [if_neg hyt]
    rw [hoccsy] at hv
    have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
    subst hv'
    rcases occs_inl_mem m w hu with hu' | ⟨hwm, hu'⟩ | ⟨hwt, hu'⟩ <;> subst hu'
    · exact huv
    · exact le_of_eq hwm
    · exact huv.elim
  · intro hwle
    exact ⟨Sum.inl w, self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, hwle⟩

-- [D-0403] leGlue_tagB_tagB_iff
theorem leGlue_tagB_tagB_iff (m w y : P) (hyt : y ≠ ⊤) (hwb : w ≠ ⊥) :
    leGlue m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inl y)) ↔ w ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsy : occs m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
      simp only [occs]; rw [if_neg hyt]
    rw [hoccsy] at hv
    have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
    subst hv'
    rw [← iotaB_generic_eq m w hwb] at hu
    rcases occs_iotaB_mem m w hu with ⟨_, _, hu'⟩ | ⟨hwb', _⟩ | ⟨hwt, hu' | hu'⟩
    · subst hu'; exact huv
    · exact absurd hwb' hwb
    · subst hwt; subst hu'; exact huv
    · subst hwt; subst hu'; exact huv.elim
  · intro hwle
    exact ⟨Sum.inr (Sum.inl w), self_mem_occs m _, Sum.inr (Sum.inl y), self_mem_occs m _, hwle⟩

-- [D-0404] not_leGlue_tagC_tagB
theorem not_leGlue_tagC_tagB (m w y : P) (hyt : y ≠ ⊤) :
    ¬ leGlue m (Sum.inr (Sum.inr w)) (Sum.inr (Sum.inl y)) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hoccsy : occs m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
    simp only [occs]; rw [if_neg hyt]
  rw [hoccsy] at hv
  have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
  subst hv'
  have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs] using hu
  subst hu'
  exact huv.elim

-- [D-0405] glueA_m_lt_glueB
theorem glueA_m_lt_glueB (m x : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hx : x ≠ ⊥) (hxt : x ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m m < glueB m x hx := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueA, glueB] at hv)
  rw [GlueCar.le_def]; exact (leGlue_tagA_tagB_iff m m x hxt).mpr le_rfl

-- [D-0406] covers_glueB_of_covers_gen
theorem covers_glueB_of_covers_gen (m x : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hx : x ≠ ⊥) (hxt : x ≠ ⊤)
    (w : P) (hw : w ≠ ⊥) (hwcov : Covers w x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueB m w hw) (glueB m x hx) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hle : glueB m w hw ≤ glueB m x hx := by
    rw [GlueCar.le_def]; exact (leGlue_tagB_tagB_iff m w x hxt hw).mpr hwcov.1.le
  have hne : glueB m w hw ≠ glueB m x hx :=
    fun heq => hwcov.1.ne (glueB_injective m hw hx heq)
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w' | w' | w'
  · exact not_leGlue_tagB_tagA m w w' hm hbt hw hc1.le
  · have hwt : w ≠ ⊤ := (hwcov.1.trans_le le_top).ne
    have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hww' : w ≤ w' := leGlue_tagB_tagB_imp m w w' hwt hc1.le
    have hw'x : w' ≤ x := (leGlue_tagB_tagB_iff m w' x hxt hw'b).mp hc2.le
    have hw'ne : w' ≠ w := by
      rintro rfl
      exact hc1.ne rfl
    have hw'x' : w' ≠ x := by
      rintro rfl
      exact hc2.ne rfl
    exact hwcov.2 w' (hww'.lt_of_ne (Ne.symm hw'ne)) (hw'x.lt_of_ne hw'x')
  · exact not_leGlue_tagC_tagB m w' x hxt hc2.le

-- [D-0407] covers_glueA_m_of_covers_bot_gen
theorem covers_glueA_m_of_covers_bot_gen (m x : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hx : x ≠ ⊥) (hxt : x ≠ ⊤)
    (hbot : Covers (⊥ : P) x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueA m m) (glueB m x hx) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hle : glueA m m ≤ glueB m x hx := by
    rw [GlueCar.le_def]; exact (leGlue_tagA_tagB_iff m m x hxt).mpr le_rfl
  have hne : glueA m m ≠ glueB m x hx := by
    intro heq
    have hv : (Sum.inl m : GlueBase P) = Sum.inr (Sum.inl x) := congrArg Subtype.val heq
    exact absurd hv (by simp)
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w' | w' | w'
  · have hmw'' : m < w' := (glueA_lt_iff m hm hmt hbt m w').mp hc1
    have hw'm : w' ≤ m := (leGlue_tagA_tagB_iff m w' x hxt).mp hc2.le
    exact absurd (hmw''.trans_le hw'm) (lt_irrefl m)
  · have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hw'x : w' ≤ x := (leGlue_tagB_tagB_iff m w' x hxt hw'b).mp hc2.le
    have hw'x' : w' ≠ x := by
      rintro rfl
      exact hc2.ne rfl
    have hbotw' : (⊥ : P) < w' := lt_of_le_of_ne bot_le (Ne.symm hw'b)
    exact hbot.2 w' hbotw' (hw'x.lt_of_ne hw'x')
  · exact not_leGlue_tagC_tagB m w' x hxt hc2.le

-- [D-0408] covers_glueB_shape_gen
theorem covers_glueB_shape_gen (m x : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hx : x ≠ ⊥) (hxt : x ≠ ⊤)
    (g : GlueCar (P := P) m)
    (hgcov : letI := glueCarPartialOrder m hm hmt hbt; Covers g (glueB m x hx)) :
    (g = glueA m m ∧ Covers (⊥ : P) x) ∨
    (∃ w, ∃ hw : w ≠ ⊥, g = glueB m w hw ∧ Covers w x) := by
  letI := glueCarPartialOrder m hm hmt hbt
  obtain ⟨cv, hcvfix⟩ := g
  rcases cv with w' | w' | w'
  · have hw'm : w' ≤ m := (leGlue_tagA_tagB_iff m w' x hxt).mp hgcov.1.le
    have hw'eq : w' = m := by
      by_contra hne
      have hw'lt : w' < m := hw'm.lt_of_ne hne
      exact hgcov.2 (glueA m m) ((glueA_lt_iff m hm hmt hbt w' m).mpr hw'lt)
        (glueA_m_lt_glueB m x hm hmt hbt hx hxt)
    refine Or.inl ⟨Subtype.ext (congrArg Sum.inl hw'eq), lt_of_le_of_ne bot_le (Ne.symm hx),
      fun z hz hzx => ?_⟩
    have hzb : z ≠ ⊥ := hz.ne'
    exact hgcov.2 (glueB m z hzb)
      (glueA_lt_glueB_of_le m w' z hm hmt hbt (le_of_eq hw'eq) hzb)
      (glueB_lt_glueB_of_lt m z x hm hmt hbt hzx hzb hx)
  · have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hw'x : w' ≤ x := (leGlue_tagB_tagB_iff m w' x hxt hw'b).mp hgcov.1.le
    have hw'x' : w' ≠ x := fun heq => hgcov.1.ne (by subst heq; rfl)
    refine Or.inr ⟨w', hw'b, rfl, hw'x.lt_of_ne hw'x', fun z hz hzx => ?_⟩
    have hzb : z ≠ ⊥ := (lt_of_le_of_lt bot_le hz).ne'
    exact hgcov.2 (glueB m z hzb) (glueB_lt_glueB_of_lt m w' z hm hmt hbt hz hw'b hzb)
      (glueB_lt_glueB_of_lt m z x hm hmt hbt hzx hzb hx)
  · exact absurd hgcov.1.le (not_leGlue_tagC_tagB m w' x hxt)

-- [D-0409] hasUniqueDownCover_glueB_iff_gen
theorem hasUniqueDownCover_glueB_iff_gen (m x : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hx : x ≠ ⊥) (hxt : x ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    HasUniqueDownCover (glueB m x hx) ↔ HasUniqueDownCover x := by
  letI := glueCarPartialOrder m hm hmt hbt
  constructor
  · rintro ⟨g0, hg0cov, hg0uniq⟩
    rcases covers_glueB_shape_gen m x hm hmt hbt hx hxt g0 hg0cov with
      ⟨hg0eq, hbot⟩ | ⟨w0, hw0b, hg0eq, hw0cov⟩
    · refine ⟨⊥, hbot, fun w hw => ?_⟩
      by_contra hwb
      have hcov := covers_glueB_of_covers_gen m x hm hmt hbt hx hxt w hwb hw
      have heq := hg0uniq (glueB m w hwb) hcov
      rw [hg0eq] at heq
      have hv := congrArg Subtype.val heq
      simp [glueA, glueB] at hv
    · refine ⟨w0, hw0cov, fun w hw => ?_⟩
      by_cases hwb : w = ⊥
      · subst hwb
        have hcov := covers_glueA_m_of_covers_bot_gen m x hm hmt hbt hx hxt hw
        have heq := hg0uniq (glueA m m) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueB] at hv
      · have hcov := covers_glueB_of_covers_gen m x hm hmt hbt hx hxt w hwb hw
        have heq := hg0uniq (glueB m w hwb) hcov
        rw [hg0eq] at heq
        exact glueB_injective m hwb hw0b heq
  · rintro ⟨w0, hw0cov, hw0uniq⟩
    by_cases hw0b : w0 = ⊥
    · subst hw0b
      refine ⟨glueA m m, covers_glueA_m_of_covers_bot_gen m x hm hmt hbt hx hxt hw0cov,
        fun g hgcov => ?_⟩
      rcases covers_glueB_shape_gen m x hm hmt hbt hx hxt g hgcov with
        ⟨hgeq, _⟩ | ⟨w, hwb, hgeq, hwcov⟩
      · exact hgeq
      · exact absurd (hw0uniq w hwcov) hwb
    · refine ⟨glueB m w0 hw0b, covers_glueB_of_covers_gen m x hm hmt hbt hx hxt w0 hw0b hw0cov,
        fun g hgcov => ?_⟩
      rcases covers_glueB_shape_gen m x hm hmt hbt hx hxt g hgcov with
        ⟨hgeq, hbot⟩ | ⟨w, hwb, hgeq, hwcov⟩
      · exact absurd (hw0uniq ⊥ hbot).symm hw0b
      · have hweq : w = w0 := hw0uniq w hwcov
        subst hweq
        rw [hgeq]

end GlueBGeneral

section GlueCGeneral
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0410] leGlue_tagA_tagC
theorem leGlue_tagA_tagC (m w y : P) :
    leGlue m (Sum.inl w) (Sum.inr (Sum.inr y)) :=
  ⟨Sum.inl w, self_mem_occs m _, Sum.inr (Sum.inr y), self_mem_occs m _, trivial⟩

-- [D-0411] leGlue_tagB_tagC_iff
theorem leGlue_tagB_tagC_iff (m w y : P) :
    leGlue m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inr y)) ↔ m ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hv' : v = Sum.inr (Sum.inr y) := by simpa [occs] using hv
    subst hv'
    by_cases hwt : w = ⊤
    · subst hwt
      have hoc : occs m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by simp [occs]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m) := by simpa using hu
      rcases hu' with hu' | hu' <;> subst hu' <;> exact huv
    · have hoc : occs m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
        simp only [occs]; rw [if_neg hwt]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
      subst hu'
      exact huv
  · intro hmy
    exact ⟨Sum.inr (Sum.inl w), self_mem_occs m _, Sum.inr (Sum.inr y), self_mem_occs m _, hmy⟩

-- [D-0412] leGlue_tagC_tagC_iff
theorem leGlue_tagC_tagC_iff (m x y : P) :
    leGlue m (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inr y)) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr x) := by simpa [occs] using hu
    have hv' : v = Sum.inr (Sum.inr y) := by simpa [occs] using hv
    subst hu'; subst hv'
    exact huv
  · intro hxy
    exact ⟨_, self_mem_occs m _, _, self_mem_occs m _, hxy⟩

-- [D-0413] leGlue_tagC_tagB_top_iff
theorem leGlue_tagC_tagB_top_iff (m w' : P) :
    leGlue m (Sum.inr (Sum.inr w')) (Sum.inr (Sum.inl (⊤ : P))) ↔ w' ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr w') := by simpa [occs] using hu
    subst hu'
    have hv' : v = Sum.inr (Sum.inl (⊤ : P)) ∨ v = Sum.inr (Sum.inr m) := by simpa [occs] using hv
    rcases hv' with hv' | hv'
    · subst hv'; exact huv.elim
    · subst hv'; exact huv
  · intro hw'm
    exact ⟨Sum.inr (Sum.inr w'), self_mem_occs m _, Sum.inr (Sum.inr m), by simp [occs], hw'm⟩

-- [D-0414] glueC
def glueC (m : P) (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) : GlueCar (P := P) m :=
  ⟨Sum.inr (Sum.inr x), by simp only [canon]; rw [if_neg hx, if_neg hxm]⟩

-- [D-0415] glueC_injective
theorem glueC_injective (m : P) {x y : P} (hx : x ≠ ⊥) (hxm : x ≠ m) (hy : y ≠ ⊥) (hym : y ≠ m)
    (h : glueC m x hx hxm = glueC m y hy hym) : x = y := by
  have hv : (Sum.inr (Sum.inr x) : GlueBase P) = Sum.inr (Sum.inr y) := congrArg Subtype.val h
  simpa using hv

variable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)

-- [D-0416] glueA_top_lt_glueC
theorem glueA_top_lt_glueC (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m ⊤ < glueC m x hx hxm := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueA, glueC] at hv)
  rw [GlueCar.le_def]; exact leGlue_tagA_tagC m ⊤ x

-- [D-0417] glueB_top_lt_glueC_of_le
theorem glueB_top_lt_glueC_of_le (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) (hmx : m ≤ x) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueB m ⊤ (hbt ∘ Eq.symm) < glueC m x hx hxm := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueB, glueC] at hv)
  rw [GlueCar.le_def]; exact (leGlue_tagB_tagC_iff m ⊤ x).mpr hmx

-- [D-0418] glueC_lt_glueC_of_lt
theorem glueC_lt_glueC_of_lt (w x : P) (hw : w ≠ ⊥) (hwm : w ≠ m) (hx : x ≠ ⊥) (hxm : x ≠ m)
    (hwx : w < x) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueC m w hw hwm < glueC m x hx hxm := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => hwx.ne (glueC_injective m hw hwm hx hxm heq))
  rw [GlueCar.le_def]; exact (leGlue_tagC_tagC_iff m w x).mpr hwx.le

-- [D-0419] glueA_top_lt_glueB_top
theorem glueA_top_lt_glueB_top :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m ⊤ < glueB m ⊤ (hbt ∘ Eq.symm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine lt_of_le_of_ne ?_ (fun heq => by
    have hv := congrArg Subtype.val heq; simp [glueA, glueB] at hv)
  rw [GlueCar.le_def]
  have hocc : Sum.inr (Sum.inr m) ∈ occs m (Sum.inr (Sum.inl (⊤ : P))) := by simp [occs]
  exact ⟨Sum.inl ⊤, self_mem_occs m _, Sum.inr (Sum.inr m), hocc, trivial⟩

-- [D-0420] covers_glueA_top_of_covers_bot_gen
theorem covers_glueA_top_of_covers_bot_gen (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m)
    (hbot : Covers (⊥ : P) x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueA m (⊤ : P)) (glueC m x hx hxm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine ⟨glueA_top_lt_glueC m hm hmt hbt x hx hxm, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w'' | w'' | w''
  · have hlt : (⊤ : P) < w'' := (glueA_lt_iff m hm hmt hbt ⊤ w'').mp hc1
    exact absurd (hlt.trans_le le_top) (lt_irrefl _)
  · have hmx : ¬ (m ≤ x) := by
      intro hmx'
      rcases hmx'.lt_or_eq with hlt | heq
      · exact hbot.2 m (lt_of_le_of_ne bot_le (Ne.symm hm)) hlt
      · exact hxm heq.symm
    exact hmx ((leGlue_tagB_tagC_iff m w'' x).mp hc2.le)
  · have hw''le : w'' ≤ x := (leGlue_tagC_tagC_iff m w'' x).mp hc2.le
    have hw''ne : w'' ≠ x := fun heq => hc2.ne (by subst heq; rfl)
    have hw''x : w'' < x := lt_of_le_of_ne hw''le hw''ne
    have hw''b : w'' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    exact hbot.2 w'' (lt_of_le_of_ne bot_le (Ne.symm hw''b)) hw''x

-- [D-0421] covers_glueB_top_of_covers_gen
theorem covers_glueB_top_of_covers_gen (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) (hcov : Covers m x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueB m (⊤ : P) (hbt ∘ Eq.symm)) (glueC m x hx hxm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  refine ⟨glueB_top_lt_glueC_of_le m hm hmt hbt x hx hxm hcov.1.le, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w'' | w'' | w''
  · exact not_leGlue_tagB_tagA m ⊤ w'' hm hbt (Ne.symm hbt) hc1.le
  · by_cases hw''t : w'' = ⊤
    · subst hw''t
      exact lt_irrefl _ hc1
    · have := (leGlue_tagB_tagB_iff m ⊤ w'' hw''t (Ne.symm hbt)).mp hc1.le
      exact absurd (le_antisymm le_top this) hw''t
  · have hw''m : w'' ≠ m := by
      intro heq
      have hw''bot : w'' ≠ ⊥ := by rw [heq]; exact hm
      have hcanon : canon m (Sum.inr (Sum.inr w'')) = Sum.inr (Sum.inl (⊤ : P)) := by
        simp only [canon]; rw [if_neg hw''bot, if_pos heq]
      rw [hcanon] at hcvfix
      exact absurd hcvfix (by simp)
    have hmw'' : m ≤ w'' := (leGlue_tagB_tagC_iff m ⊤ w'').mp hc1.le
    have hw''le : w'' ≤ x := (leGlue_tagC_tagC_iff m w'' x).mp hc2.le
    have hw''ne : w'' ≠ x := fun heq => hc2.ne (by subst heq; rfl)
    have hw''x : w'' < x := lt_of_le_of_ne hw''le hw''ne
    have hmw''lt : m < w'' := lt_of_le_of_ne hmw'' (Ne.symm hw''m)
    exact hcov.2 w'' hmw''lt hw''x

-- [D-0422] covers_glueC_of_covers_gen
theorem covers_glueC_of_covers_gen (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m)
    (w : P) (hw : w ≠ ⊥) (hwm : w ≠ m) (hwcov : Covers w x) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueC m w hw hwm) (glueC m x hx hxm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hle : glueC m w hw hwm ≤ glueC m x hx hxm := by
    rw [GlueCar.le_def]; exact (leGlue_tagC_tagC_iff m w x).mpr hwcov.1.le
  have hne : glueC m w hw hwm ≠ glueC m x hx hxm :=
    fun heq => hwcov.1.ne (glueC_injective m hw hwm hx hxm heq)
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro c hc1 hc2
  obtain ⟨cv, hcvfix⟩ := c
  rcases cv with w' | w' | w'
  · obtain ⟨u, hu, v, hv, huv⟩ := hc1.le
    have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs, glueC] using hu
    subst hu'
    rcases occs_inl_mem m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
    · exact huv.elim
    · exact huv.elim
    · exact hw (le_bot_iff.mp huv)
  · obtain ⟨u, hu, v, hv, huv⟩ := hc1.le
    have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs, glueC] using hu
    subst hu'
    by_cases hw't : w' = ⊤
    · subst hw't
      have hv' : v = Sum.inr (Sum.inl (⊤ : P)) ∨ v = Sum.inr (Sum.inr m) := by simpa [occs] using hv
      rcases hv' with hv' | hv'
      · subst hv'; exact huv.elim
      · subst hv'
        have hmx : m ≤ x := (leGlue_tagB_tagC_iff m ⊤ x).mp hc2.le
        have hwlt : w < m := lt_of_le_of_ne huv hwm
        exact absurd (lt_of_le_of_ne hmx (Ne.symm hxm)) (hwcov.2 m hwlt)
    · have hv' : v = Sum.inr (Sum.inl w') := by simpa [occs, hw't] using hv
      subst hv'
      exact huv.elim
  · have hw'w : w ≤ w' := (leGlue_tagC_tagC_iff m w w').mp hc1.le
    have hw'x : w' ≤ x := (leGlue_tagC_tagC_iff m w' x).mp hc2.le
    have hw'wne : w' ≠ w := fun heq => hc1.ne (by subst heq; rfl)
    have hw'xne : w' ≠ x := fun heq => hc2.ne (by subst heq; rfl)
    exact hwcov.2 w' (hw'w.lt_of_ne (Ne.symm hw'wne)) (hw'x.lt_of_ne hw'xne)

-- [D-0423] covers_glueC_shape_gen
theorem covers_glueC_shape_gen (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m)
    (g : GlueCar (P := P) m)
    (hgcov : letI := glueCarPartialOrder m hm hmt hbt; Covers g (glueC m x hx hxm)) :
    (g = glueA m (⊤ : P) ∧ Covers (⊥ : P) x) ∨
    (g = glueB m (⊤ : P) (hbt ∘ Eq.symm) ∧ Covers m x) ∨
    (∃ w, ∃ hw : w ≠ ⊥, ∃ hwm : w ≠ m, g = glueC m w hw hwm ∧ Covers w x) := by
  letI := glueCarPartialOrder m hm hmt hbt
  obtain ⟨cv, hcvfix⟩ := g
  rcases cv with w' | w' | w'
  · have hw'eq : w' = ⊤ := by
      by_contra hne
      have hw'lt : w' < ⊤ := lt_of_le_of_ne le_top hne
      exact hgcov.2 (glueA m ⊤) ((glueA_lt_iff m hm hmt hbt w' ⊤).mpr hw'lt)
        (glueA_top_lt_glueC m hm hmt hbt x hx hxm)
    subst hw'eq
    refine Or.inl ⟨rfl, lt_of_le_of_ne bot_le (Ne.symm hx), fun z hz hzx => ?_⟩
    by_cases hzm : z = m
    · exact hgcov.2 (glueB m ⊤ (hbt ∘ Eq.symm)) (glueA_top_lt_glueB_top m hm hmt hbt)
        (glueB_top_lt_glueC_of_le m hm hmt hbt x hx hxm (hzm ▸ hzx.le))
    · exact hgcov.2 (glueC m z hz.ne' hzm) (glueA_top_lt_glueC m hm hmt hbt z hz.ne' hzm)
        (glueC_lt_glueC_of_lt m hm hmt hbt z x hz.ne' hzm hx hxm hzx)
  · have hw't : w' = ⊤ := by
      by_contra hne
      have hw'lt : w' < ⊤ := lt_of_le_of_ne le_top hne
      have hmx : m ≤ x := (leGlue_tagB_tagC_iff m w' x).mp hgcov.1.le
      exact hgcov.2 (glueB m ⊤ (hbt ∘ Eq.symm))
        (lt_of_le_of_ne
          (by rw [GlueCar.le_def]
              exact ⟨Sum.inr (Sum.inl w'), self_mem_occs m _,
                Sum.inr (Sum.inl (⊤ : P)), self_mem_occs m _, hw'lt.le⟩)
          (fun heq => hne (by have hv := congrArg Subtype.val heq; simpa [glueB] using hv)))
        (glueB_top_lt_glueC_of_le m hm hmt hbt x hx hxm hmx)
    subst hw't
    refine Or.inr (Or.inl ⟨rfl, ?_, fun z hz hzx => ?_⟩)
    · have hmx : m ≤ x := (leGlue_tagB_tagC_iff m ⊤ x).mp hgcov.1.le
      exact lt_of_le_of_ne hmx (Ne.symm hxm)
    · have hzm : z ≠ m := hz.ne'
      have hmbot : (⊥ : P) < m := lt_of_le_of_ne bot_le (Ne.symm hm)
      have hzb : z ≠ ⊥ := (hmbot.trans hz).ne'
      exact hgcov.2 (glueC m z hzb hzm)
        (lt_of_le_of_ne
          (by rw [GlueCar.le_def]; exact (leGlue_tagB_tagC_iff m ⊤ z).mpr hz.le)
          (fun heq => by have hv := congrArg Subtype.val heq; simp [glueC] at hv))
        (glueC_lt_glueC_of_lt m hm hmt hbt z x hzb hzm hx hxm hzx)
  · have hw'b : w' ≠ ⊥ := by
      rintro rfl
      simp [canon] at hcvfix
    have hw'm : w' ≠ m := by
      intro heq
      have hw'bot : w' ≠ ⊥ := hw'b
      have hcanon : canon m (Sum.inr (Sum.inr w')) = Sum.inr (Sum.inl (⊤ : P)) := by
        simp only [canon]; rw [if_neg hw'bot, if_pos heq]
      rw [hcanon] at hcvfix
      exact absurd hcvfix (by simp)
    have hw'x : w' ≤ x := (leGlue_tagC_tagC_iff m w' x).mp hgcov.1.le
    have hw'xne : w' ≠ x := fun heq => hgcov.1.ne (by subst heq; rfl)
    refine Or.inr (Or.inr ⟨w', hw'b, hw'm, rfl, hw'x.lt_of_ne hw'xne, fun z hz hzx => ?_⟩)
    by_cases hzm : z = m
    · exact hgcov.2 (glueB m (⊤ : P) (hbt ∘ Eq.symm))
        (lt_of_le_of_ne
          (by rw [GlueCar.le_def]; exact (leGlue_tagC_tagB_top_iff m w').mpr (hzm ▸ hz.le))
          (fun heq => by have hv := congrArg Subtype.val heq; simp [glueB] at hv))
        (glueB_top_lt_glueC_of_le m hm hmt hbt x hx hxm (hzm ▸ hzx.le))
    · have hzw' : z ≠ w' := hz.ne'
      have hw'bot : (⊥ : P) < w' := lt_of_le_of_ne bot_le (Ne.symm hw'b)
      have hzb : z ≠ ⊥ := (hw'bot.trans hz).ne'
      exact hgcov.2 (glueC m z hzb hzm)
        (glueC_lt_glueC_of_lt m hm hmt hbt w' z hw'b hw'm hzb hzm hz)
        (glueC_lt_glueC_of_lt m hm hmt hbt z x hzb hzm hx hxm hzx)

-- [D-0424] hasUniqueDownCover_glueC_iff_gen
theorem hasUniqueDownCover_glueC_iff_gen (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) :
    letI := glueCarPartialOrder m hm hmt hbt
    HasUniqueDownCover (glueC m x hx hxm) ↔ HasUniqueDownCover x := by
  letI := glueCarPartialOrder m hm hmt hbt
  constructor
  · rintro ⟨g0, hg0cov, hg0uniq⟩
    rcases covers_glueC_shape_gen m hm hmt hbt x hx hxm g0 hg0cov with
      ⟨hg0eq, hbot⟩ | ⟨hg0eq, hmcov⟩ | ⟨w0, hw0b, hw0m, hg0eq, hw0cov⟩
    · refine ⟨⊥, hbot, fun w hw => ?_⟩
      by_contra hwb
      by_cases hwm : w = m
      · have hcov := covers_glueB_top_of_covers_gen m hm hmt hbt x hx hxm (hwm ▸ hw)
        have heq := hg0uniq (glueB m ⊤ (hbt ∘ Eq.symm)) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueB] at hv
      · have hcov := covers_glueC_of_covers_gen m hm hmt hbt x hx hxm w hwb hwm hw
        have heq := hg0uniq (glueC m w hwb hwm) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueC] at hv
    · refine ⟨m, hmcov, fun w hw => ?_⟩
      by_contra hwm'
      by_cases hwb : w = ⊥
      · have hcov := covers_glueA_top_of_covers_bot_gen m hm hmt hbt x hx hxm (hwb ▸ hw)
        have heq := hg0uniq (glueA m ⊤) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueB] at hv
      · have hcov := covers_glueC_of_covers_gen m hm hmt hbt x hx hxm w hwb hwm' hw
        have heq := hg0uniq (glueC m w hwb hwm') hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueB, glueC] at hv
    · refine ⟨w0, hw0cov, fun w hw => ?_⟩
      by_cases hwb : w = ⊥
      · have hcov := covers_glueA_top_of_covers_bot_gen m hm hmt hbt x hx hxm (hwb ▸ hw)
        have heq := hg0uniq (glueA m ⊤) hcov
        rw [hg0eq] at heq
        have hv := congrArg Subtype.val heq
        simp [glueA, glueC] at hv
      · by_cases hwm' : w = m
        · have hcov := covers_glueB_top_of_covers_gen m hm hmt hbt x hx hxm (hwm' ▸ hw)
          have heq := hg0uniq (glueB m ⊤ (hbt ∘ Eq.symm)) hcov
          rw [hg0eq] at heq
          have hv := congrArg Subtype.val heq
          simp [glueB, glueC] at hv
        · have hcov := covers_glueC_of_covers_gen m hm hmt hbt x hx hxm w hwb hwm' hw
          have heq := hg0uniq (glueC m w hwb hwm') hcov
          rw [hg0eq] at heq
          exact glueC_injective m hwb hwm' hw0b hw0m heq
  · rintro ⟨w0, hw0cov, hw0uniq⟩
    by_cases hw0b : w0 = ⊥
    · refine ⟨glueA m ⊤, covers_glueA_top_of_covers_bot_gen m hm hmt hbt x hx hxm (hw0b ▸ hw0cov),
        fun g hgcov => ?_⟩
      rcases covers_glueC_shape_gen m hm hmt hbt x hx hxm g hgcov with
        ⟨hgeq, _⟩ | ⟨hgeq, hmcov⟩ | ⟨w, hwb, hwm', hgeq, hwcov⟩
      · exact hgeq
      · exact absurd (hw0b ▸ hw0uniq m hmcov : m = ⊥) hm
      · exact absurd (hw0b ▸ hw0uniq w hwcov : w = ⊥) hwb
    · by_cases hw0m : w0 = m
      · refine ⟨glueB m ⊤ (hbt ∘ Eq.symm),
          covers_glueB_top_of_covers_gen m hm hmt hbt x hx hxm (hw0m ▸ hw0cov), fun g hgcov => ?_⟩
        rcases covers_glueC_shape_gen m hm hmt hbt x hx hxm g hgcov with
          ⟨hgeq, hbot⟩ | ⟨hgeq, _⟩ | ⟨w, hwb, hwm', hgeq, hwcov⟩
        · exact absurd (hw0m ▸ hw0uniq ⊥ hbot : (⊥ : P) = m) (Ne.symm hm)
        · exact hgeq
        · exact absurd (hw0m ▸ hw0uniq w hwcov : w = m) hwm'
      · refine ⟨glueC m w0 hw0b hw0m,
          covers_glueC_of_covers_gen m hm hmt hbt x hx hxm w0 hw0b hw0m hw0cov, fun g hgcov => ?_⟩
        rcases covers_glueC_shape_gen m hm hmt hbt x hx hxm g hgcov with
          ⟨hgeq, hbot⟩ | ⟨hgeq, hmcov⟩ | ⟨w, hwb, hwm', hgeq, hwcov⟩
        · exact absurd (hw0uniq ⊥ hbot).symm hw0b
        · exact absurd (hw0uniq m hmcov).symm hw0m
        · have hweq : w = w0 := hw0uniq w hwcov
          subst hweq
          rw [hgeq]

end GlueCGeneral

section JoinIrredCoverConnect
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [OrderBot P]

-- [D-0425] joinIrred_of_hasUniqueDownCover
theorem joinIrred_of_hasUniqueDownCover {a : P} (h : HasUniqueDownCover a) :
    JoinIrred P a := by
  obtain ⟨g0, hg0cov, hg0uniq⟩ := h
  have hbot_lt : (⊥ : P) < a := lt_of_le_of_lt bot_le hg0cov.1
  refine ⟨hbot_lt.ne', fun b c habc => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hab', hac'⟩ := hcon
  have hb_le : b ≤ a := by rw [habc]; exact le_sup_left
  have hc_le : c ≤ a := by rw [habc]; exact le_sup_right
  have hb_lt : b < a := lt_of_le_of_ne hb_le (Ne.symm hab')
  have hc_lt : c < a := lt_of_le_of_ne hc_le (Ne.symm hac')
  obtain ⟨wb, hwbcov, hwb_ge⟩ := exists_covBy_ge hb_lt
  obtain ⟨wc, hwccov, hwc_ge⟩ := exists_covBy_ge hc_lt
  have hb_g0 : b ≤ g0 := by rw [hg0uniq wb hwbcov] at hwb_ge; exact hwb_ge
  have hc_g0 : c ≤ g0 := by rw [hg0uniq wc hwccov] at hwc_ge; exact hwc_ge
  have ha_g0 : a ≤ g0 := by rw [habc]; exact sup_le hb_g0 hc_g0
  exact hg0cov.1.ne (le_antisymm hg0cov.1.le ha_g0)

-- [D-0426] hasUniqueDownCover_of_joinIrred
theorem hasUniqueDownCover_of_joinIrred {a : P} (h : JoinIrred P a) :
    HasUniqueDownCover a := by
  obtain ⟨hab, hji⟩ := h
  have hbot_lt : (⊥ : P) < a := lt_of_le_of_ne bot_le (Ne.symm hab)
  obtain ⟨w0, hw0cov, -⟩ := exists_covBy_ge hbot_lt
  refine ⟨w0, hw0cov, fun w1 hw1cov => ?_⟩
  by_contra hne01
  have hle : w0 ⊔ w1 ≤ a := sup_le hw0cov.1.le hw1cov.1.le
  have hne_eq : w0 ⊔ w1 ≠ a := by
    intro heq
    rcases hji w0 w1 heq.symm with h | h
    · exact hw0cov.1.ne h.symm
    · exact hw1cov.1.ne h.symm
  have hlt : w0 ⊔ w1 < a := lt_of_le_of_ne hle hne_eq
  by_cases h0 : w0 = w0 ⊔ w1
  · by_cases h1 : w1 = w0 ⊔ w1
    · exact hne01 (h1.trans h0.symm)
    · have hlt1 : w1 < w0 ⊔ w1 := lt_of_le_of_ne le_sup_right h1
      exact absurd hlt (hw1cov.2 _ hlt1)
  · have hlt0 : w0 < w0 ⊔ w1 := lt_of_le_of_ne le_sup_left h0
    exact absurd hlt (hw0cov.2 _ hlt0)

-- [D-0427] hasUniqueDownCover_iff_joinIrred
theorem hasUniqueDownCover_iff_joinIrred (a : P) : HasUniqueDownCover a ↔ JoinIrred P a :=
  ⟨joinIrred_of_hasUniqueDownCover, hasUniqueDownCover_of_joinIrred⟩

end JoinIrredCoverConnect

section GlueAJoinIrred
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0428] joinIrred_glueA_of_joinIrred
theorem joinIrred_glueA_of_joinIrred (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : P) (hx : JoinIrred P x) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderBot m hm hmt hbt
    letI := glueLattice m hm hmt hbt
    JoinIrred (GlueCar (P := P) m) (glueA m x) := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderBot m hm hmt hbt
  letI := glueLattice m hm hmt hbt
  exact (hasUniqueDownCover_iff_joinIrred (glueA m x)).mp
    ((hasUniqueDownCover_glueA_iff m hm hmt hbt x).mpr
      ((hasUniqueDownCover_iff_joinIrred x).mpr hx))

-- [D-0429] glueA_ne_top
theorem glueA_ne_top (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x : P) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderTop m hm hmt hbt
    glueA m x ≠ (⊤ : GlueCar (P := P) m) := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderTop m hm hmt hbt
  have htop : (⊤ : GlueCar (P := P) m) = incl m hm hbt (Sum.inr (Sum.inr ⊤)) := rfl
  rw [htop]
  intro heq
  have hv := congrArg Subtype.val heq
  have h2 : canon m (Sum.inr (Sum.inr (⊤ : P))) = Sum.inr (Sum.inr ⊤) := by
    simp only [canon]; rw [if_neg hbt.symm, if_neg hmt.symm]
  simp only [glueA, incl, h2] at hv
  exact absurd hv Sum.inl_ne_inr

end GlueAJoinIrred

section GlueBCJoinIrred
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0430] joinIrred_glueB_iff
theorem joinIrred_glueB_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : P) (hx : x ≠ ⊥) (hxt : x ≠ ⊤) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderBot m hm hmt hbt
    letI := glueLattice m hm hmt hbt
    JoinIrred (GlueCar (P := P) m) (glueB m x hx) ↔ JoinIrred P x := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderBot m hm hmt hbt
  letI := glueLattice m hm hmt hbt
  rw [← hasUniqueDownCover_iff_joinIrred, ← hasUniqueDownCover_iff_joinIrred]
  exact hasUniqueDownCover_glueB_iff_gen m x hm hmt hbt hx hxt

-- [D-0431] joinIrred_glueC_iff
theorem joinIrred_glueC_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m) :
    letI := glueCarPartialOrder m hm hmt hbt
    letI := glueOrderBot m hm hmt hbt
    letI := glueLattice m hm hmt hbt
    JoinIrred (GlueCar (P := P) m) (glueC m x hx hxm) ↔ JoinIrred P x := by
  letI := glueCarPartialOrder m hm hmt hbt
  letI := glueOrderBot m hm hmt hbt
  letI := glueLattice m hm hmt hbt
  rw [← hasUniqueDownCover_iff_joinIrred, ← hasUniqueDownCover_iff_joinIrred]
  exact hasUniqueDownCover_glueC_iff_gen m hm hmt hbt x hx hxm

end GlueBCJoinIrred

section Gap1Closed
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0432] joinBelow_constHom_eq
theorem joinBelow_constHom_eq (v : P) {x0 : P} (hx0 : x0 ≠ ⊥) :
    joinBelow (constHom v : EndP P) x0 = v := by
  apply le_antisymm
  · exact joinBelow_le (constHom v : EndP P) (fun y _ => le_of_eq (constHom_apply v y))
  · have hbot : (⊥ : P) < x0 := lt_of_le_of_ne bot_le (Ne.symm hx0)
    have h := le_joinBelow (constHom v : EndP P) hbot
    rwa [constHom_apply] at h

-- [D-0433] covers_constHom_iff_lowerAtBot
theorem covers_constHom_iff_lowerAtBot (v : P) (g : EndP P) :
    Covers g (constHom v) ↔
      ∃ w, ∃ hw_le : w ≤ (constHom v : EndP P) ⊥, g = lowerAtBot (constHom v) w hw_le ∧
        Covers w ((constHom v : EndP P) ⊥) := by
  constructor
  · intro hcov
    obtain ⟨x0, w, hw_le, hw_ge, hgeq, hwcov⟩ := exists_updateAt_of_covers (constHom v) g hcov
    have hx0_bot : x0 = ⊥ := by
      by_contra hne
      have heq : joinBelow (constHom v : EndP P) x0 = v := joinBelow_constHom_eq v hne
      rw [heq] at hw_ge
      have hwv : w < v := by
        have hlt := hwcov.1
        rwa [constHom_apply] at hlt
      exact absurd (hwv.trans_le hw_ge) (lt_irrefl w)
    subst hx0_bot
    refine ⟨w, hw_le, ?_, hwcov⟩
    rw [hgeq]
    apply OrderHom.ext
    funext y
    by_cases hy : y = ⊥
    · rw [hy, updateAt_apply_self, lowerAtBot_apply_bot]
    · rw [updateAt_apply_ne (constHom v) ⊥ w hw_le hw_ge hy,
        lowerAtBot_apply_ne (constHom v) w hw_le hy]
  · rintro ⟨w, hw_le, hgeq, hwcov⟩
    rw [hgeq]
    exact covers_lowerAtBot (constHom v) w hw_le hwcov

-- [D-0434] hasUniqueDownCover_constHom_iff
theorem hasUniqueDownCover_constHom_iff (v : P) :
    HasUniqueDownCover (constHom v : EndP P) ↔ HasUniqueDownCover v := by
  constructor
  · rintro ⟨g0, hg0cov, hg0uniq⟩
    obtain ⟨w0, hw0_le, hg0eq, hw0cov⟩ := (covers_constHom_iff_lowerAtBot v g0).mp hg0cov
    refine ⟨w0, hw0cov, fun w1 hw1cov => ?_⟩
    have hw1_le : w1 ≤ (constHom v : EndP P) ⊥ := by rw [constHom_apply]; exact hw1cov.1.le
    have heq := hg0uniq (lowerAtBot (constHom v) w1 hw1_le)
      ((covers_constHom_iff_lowerAtBot v _).mpr ⟨w1, hw1_le, rfl, hw1cov⟩)
    rw [hg0eq] at heq
    have h2 := congrArg (fun f : EndP P => f (⊥ : P)) heq
    simpa [lowerAtBot_apply_bot] using h2
  · rintro ⟨w0, hw0cov, hw0uniq⟩
    have hw0_le : w0 ≤ (constHom v : EndP P) ⊥ := by rw [constHom_apply]; exact hw0cov.1.le
    refine ⟨lowerAtBot (constHom v) w0 hw0_le,
      (covers_constHom_iff_lowerAtBot v _).mpr ⟨w0, hw0_le, rfl, hw0cov⟩, fun g' hg'cov => ?_⟩
    obtain ⟨w1, hw1_le, hg'eq, hw1cov⟩ := (covers_constHom_iff_lowerAtBot v g').mp hg'cov
    have hweq : w1 = w0 := hw0uniq w1 hw1cov
    subst hweq
    rw [hg'eq]

-- [D-0435] gap1_down_cover_has_second_up_cover
theorem gap1_down_cover_has_second_up_cover (v v' : P) (hbt : (⊥ : P) ≠ ⊤)
    (hv' : Covers v v') (g : EndP P) (hg : Covers g (constHom v)) :
    ∃ g2 : EndP P, Covers g g2 ∧ constHom v ≠ g2 := by
  obtain ⟨w, hw_le, hgeq, hwcov⟩ := (covers_constHom_iff_lowerAtBot v g).mp hg
  subst hgeq
  have hg_top : lowerAtBot (constHom v) w hw_le ⊤ = v := by
    rw [lowerAtBot_apply_ne (constHom v) w hw_le hbt.symm, constHom_apply]
  have hv_ge : lowerAtBot (constHom v) w hw_le ⊤ ≤ v' := by rw [hg_top]; exact hv'.1.le
  have hcovv' : Covers (lowerAtBot (constHom v) w hw_le ⊤) v' := by rw [hg_top]; exact hv'
  refine ⟨raiseAtTop (lowerAtBot (constHom v) w hw_le) v' hv_ge,
    covers_raiseAtTop _ v' hv_ge hcovv', ?_⟩
  intro heq
  have h1 : (constHom v : EndP P) ⊤ =
      raiseAtTop (lowerAtBot (constHom v) w hw_le) v' hv_ge ⊤ := congrArg (fun f => f ⊤) heq
  rw [constHom_apply, raiseAtTop_apply_top] at h1
  exact hv'.1.ne h1

end Gap1Closed

section IdDownCover
variable {L : Type u} [Fintype L] [DecidableEq L] [Lattice L] [BoundedOrder L]

-- [D-0436] covers_id_updateAt_of_joinIrred
theorem covers_id_updateAt_of_joinIrred (x0 : L) (hx0 : JoinIrred L x0) :
    ∃ v0, v0 < x0 ∧ ∃ (hv_le : v0 ≤ (OrderHom.id : EndP L) x0)
      (hv_ge : joinBelow (OrderHom.id : EndP L) x0 ≤ v0),
      Covers (updateAt (OrderHom.id : EndP L) x0 v0 hv_le hv_ge) (OrderHom.id : EndP L) := by
  obtain ⟨v0, hv0cov, hv0uniq⟩ := (hasUniqueDownCover_iff_joinIrred x0).mpr hx0
  have hv_le : v0 ≤ (OrderHom.id : EndP L) x0 := hv0cov.1.le
  have hv_ge : joinBelow (OrderHom.id : EndP L) x0 ≤ v0 := by
    apply joinBelow_le
    intro y hy
    obtain ⟨w, hwcov, hyw⟩ := exists_covBy_ge hy
    rw [hv0uniq w hwcov] at hyw
    exact hyw
  exact ⟨v0, hv0cov.1, hv_le, hv_ge, covers_updateAt _ x0 v0 hv_le hv_ge hv0cov⟩

-- [D-0437] not_hasUniqueDownCover_id_of_ne
theorem not_hasUniqueDownCover_id_of_ne (x1 x2 : L) (hx1 : JoinIrred L x1)
    (hx2 : JoinIrred L x2) (hne : x1 ≠ x2) :
    ¬ HasUniqueDownCover (OrderHom.id : EndP L) := by
  obtain ⟨v1, hv1lt, hv1le, hv1ge, hcov1⟩ := covers_id_updateAt_of_joinIrred x1 hx1
  obtain ⟨v2, hv2lt, hv2le, hv2ge, hcov2⟩ := covers_id_updateAt_of_joinIrred x2 hx2
  refine not_hasUniqueDownCover_of_second hcov1 hcov2 (fun heq => ?_)
  have h1 : (updateAt (OrderHom.id : EndP L) x2 v2 hv2le hv2ge) x1 =
      (updateAt (OrderHom.id : EndP L) x1 v1 hv1le hv1ge) x1 := by rw [heq]
  rw [updateAt_apply_ne (OrderHom.id : EndP L) x2 v2 hv2le hv2ge hne, updateAt_apply_self] at h1
  exact hv1lt.ne' h1

end IdDownCover

section G2Pin
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0438] §copy-embeddings-as-total-maps-P-GlueCar-m
-- [D-0439] glueBt
def glueBt (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) : GlueCar (P := P) m :=
  ⟨iotaB m x, iotaB_canon m hm hbt x⟩

-- [D-0440] glueCt
def glueCt (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) : GlueCar (P := P) m :=
  ⟨iotaC m x, iotaC_canon m hm hbt x⟩

-- [D-0441] unA
def unA : GlueBase P → P
  | Sum.inl x => x
  | Sum.inr (Sum.inl _) => ⊥
  | Sum.inr (Sum.inr _) => ⊥

-- [D-0442] unB
def unB : GlueBase P → P
  | Sum.inl _ => ⊥
  | Sum.inr (Sum.inl x) => x
  | Sum.inr (Sum.inr _) => ⊤

-- [D-0443] unC
def unC (m : P) : GlueBase P → P
  | Sum.inl _ => ⊥
  | Sum.inr (Sum.inl _) => m
  | Sum.inr (Sum.inr x) => x

-- [D-0444] unA_glueA
theorem unA_glueA (m x : P) : unA (glueA m x).1 = x := rfl

-- [D-0445] unB_glueBt
theorem unB_glueBt (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) :
    unB (glueBt m hm hbt x).1 = x := by
  by_cases hxb : x = ⊥
  · subst hxb
    show unB (iotaB m (⊥ : P)) = (⊥ : P)
    rw [show iotaB m (⊥ : P) = Sum.inl m from by simp [canon]]
    rfl
  · show unB (iotaB m x) = x
    rw [iotaB_generic_eq m x hxb]
    rfl

-- [D-0446] unC_glueCt
theorem unC_glueCt (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : P) :
    unC m (glueCt m hm hbt x).1 = x := by
  by_cases hxb : x = ⊥
  · subst hxb
    show unC m (iotaC m (⊥ : P)) = (⊥ : P)
    rw [show iotaC m (⊥ : P) = Sum.inl (⊤ : P) from by simp [canon]]
    rfl
  · by_cases hxm : x = m
    · show unC m (iotaC m x) = x
      rw [show iotaC m x = Sum.inr (Sum.inl (⊤ : P)) from by simp [canon, hxb, hxm, hm]]
      exact hxm.symm
    · show unC m (iotaC m x) = x
      rw [iotaC_generic_eq m x hxb hxm]
      rfl

-- [D-0447] glueBt_le_iff
theorem glueBt_le_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    glueBt m hm hbt x ≤ glueBt m hm hbt y ↔ x ≤ y := by
  rw [GlueCar.le_def]; exact tagB_iso m hm hmt hbt x y

-- [D-0448] glueCt_le_iff
theorem glueCt_le_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    glueCt m hm hbt x ≤ glueCt m hm hbt y ↔ x ≤ y := by
  rw [GlueCar.le_def]; exact tagC_iso m hm hmt hbt x y

-- [D-0449] §canonicity-extraction
-- [D-0450] canon_inr_inl_ne_bot
theorem canon_inr_inl_ne_bot (m w : P)
    (h : canon m (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w)) : w ≠ ⊥ := by
  intro hw; subst hw; simp only [canon] at h; split_ifs at h <;> simp at h

-- [D-0451] canon_inr_inr_ne
theorem canon_inr_inr_ne (m w : P)
    (h : canon m (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w)) : w ≠ ⊥ ∧ w ≠ m := by
  constructor
  · intro hw; subst hw; simp only [canon] at h; split_ifs at h <;> simp at h
  · intro hw; subst hw; simp only [canon] at h; split_ifs at h <;> simp at h

-- [D-0452] occs_inr_inl_mem
theorem occs_inr_inl_mem (m w : P) {t : GlueBase P} (ht : t ∈ occs m (Sum.inr (Sum.inl w))) :
    t = Sum.inr (Sum.inl w) ∨ (w = ⊤ ∧ t = Sum.inr (Sum.inr m)) := by
  simp only [occs] at ht
  split_ifs at ht with hw <;> simp at ht <;> tauto

-- [D-0453] occs_inr_inr_mem
theorem occs_inr_inr_mem (m w : P) {t : GlueBase P} (ht : t ∈ occs m (Sum.inr (Sum.inr w))) :
    t = Sum.inr (Sum.inr w) := by
  simp only [occs] at ht; simpa using ht

-- [D-0454] occs_inr_inl_ne_top
theorem occs_inr_inl_ne_top (m x : P) (hxt : x ≠ ⊤) {t : GlueBase P}
    (ht : t ∈ occs m (Sum.inr (Sum.inl x))) : t = Sum.inr (Sum.inl x) := by
  simp only [occs] at ht; rw [if_neg hxt] at ht; simpa using ht

-- [D-0455] §shape-lemmas
-- [D-0456] le_tagA_shape
theorem le_tagA_shape (m : P) (hm : m ≠ ⊥) (x : P) {z : GlueBase P}
    (hzc : canon m z = z) (hz : leGlue m z (Sum.inl x)) :
    ∃ y, y ≤ x ∧ z = Sum.inl y := by
  obtain ⟨u, hu, v, hv, huv⟩ := hz
  rcases z with w | w | w
  · refine ⟨w, ?_, rfl⟩
    rcases occs_inl_mem m w hu with hu' | ⟨hwm, hu'⟩ | ⟨hwt, hu'⟩ <;> subst hu' <;>
      rcases occs_inl_mem m x hv with hv' | ⟨hxm, hv'⟩ | ⟨hxt, hv'⟩ <;> subst hv' <;>
      first
        | exact huv
        | exact huv.elim
        | (rw [hxt]; exact le_top)
        | (rw [hxm]; exact huv)
        | (rw [hwm, hxm])
  · exfalso
    have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hzc
    rcases occs_inr_inl_mem m w hu with hu' | ⟨_, hu'⟩ <;> subst hu' <;>
      rcases occs_inl_mem m x hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv' <;>
      first
        | exact huv
        | exact hwb (le_bot_iff.mp huv)
        | exact hm (le_bot_iff.mp huv)
  · exfalso
    have hwb : (canon_inr_inr_ne m w hzc).1 = (canon_inr_inr_ne m w hzc).1 := rfl
    have hwb' : w ≠ ⊥ := (canon_inr_inr_ne m w hzc).1
    have hu' := occs_inr_inr_mem m w hu
    subst hu'
    rcases occs_inl_mem m x hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv' <;>
      first
        | exact huv
        | exact hwb' (le_bot_iff.mp huv)

-- [D-0457] tagA_top_le_shape
theorem tagA_top_le_shape (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {z : GlueBase P} (hzc : canon m z = z) (hz : leGlue m (Sum.inl (⊤ : P)) z) :
    ∃ y, z = iotaC m y := by
  rcases z with w | w | w
  · by_cases hwt : w = ⊤
    · refine ⟨⊥, ?_⟩
      rw [hwt]
      show Sum.inl (⊤ : P) = canon m (Sum.inr (Sum.inr (⊥ : P)))
      simp [canon]
    · exact absurd hz (skel_dsi_copyA_not_g2_le m hm hmt hbt w hwt)
  · have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hzc
    by_cases hwt : w = ⊤
    · refine ⟨m, ?_⟩
      rw [hwt]
      show Sum.inr (Sum.inl (⊤ : P)) = canon m (Sum.inr (Sum.inr m))
      simp [canon, hm]
    · exfalso
      rw [← iotaB_generic_eq m w hwb] at hz
      exact (skel_dsi_copyB_incomp m hm hmt w hwb hwt).2 hz
  · obtain ⟨hwb, hwm⟩ := canon_inr_inr_ne m w hzc
    exact ⟨w, (iotaC_generic_eq m w hwb hwm).symm⟩

-- [D-0458] le_tagB_shape
theorem le_tagB_shape (m : P) (hm : m ≠ ⊥) (x : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤)
    {z : GlueBase P} (hzc : canon m z = z) (hz : leGlue m z (Sum.inr (Sum.inl x))) :
    (∃ y, y ≤ m ∧ z = Sum.inl y) ∨ (∃ y, y ≤ x ∧ y ≠ ⊥ ∧ z = Sum.inr (Sum.inl y)) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hz
  have hvv := occs_inr_inl_ne_top m x hxt hv
  subst hvv
  rcases z with w | w | w
  · left
    refine ⟨w, ?_, rfl⟩
    rcases occs_inl_mem m w hu with hu' | ⟨hwm, hu'⟩ | ⟨_, hu'⟩ <;> subst hu'
    · exact huv
    · exact le_of_eq hwm
    · exact huv.elim
  · right
    have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hzc
    refine ⟨w, ?_, hwb, rfl⟩
    rcases occs_inr_inl_mem m w hu with hu' | ⟨_, hu'⟩ <;> subst hu'
    · exact huv
    · exact huv.elim
  · exfalso
    have hu' := occs_inr_inr_mem m w hu
    subst hu'
    exact huv

-- [D-0459] tagB_le_shape
theorem tagB_le_shape (m : P) (hm : m ≠ ⊥) (x : P) (hxb : x ≠ ⊥) (hxt : x ≠ ⊤)
    {z : GlueBase P} (hzc : canon m z = z) (hz : leGlue m (Sum.inr (Sum.inl x)) z) :
    (∃ y, x ≤ y ∧ z = Sum.inr (Sum.inl y)) ∨
      (∃ y, m ≤ y ∧ y ≠ m ∧ z = Sum.inr (Sum.inr y)) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hz
  have huu := occs_inr_inl_ne_top m x hxt hu
  subst huu
  rcases z with w | w | w
  · exfalso
    rcases occs_inl_mem m w hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
    · exact huv
    · exact hxb (le_bot_iff.mp huv)
    · exact hm (le_bot_iff.mp huv)
  · left
    refine ⟨w, ?_, rfl⟩
    rcases occs_inr_inl_mem m w hv with hv' | ⟨hwt, hv'⟩ <;> subst hv'
    · exact huv
    · rw [hwt]; exact le_top
  · right
    obtain ⟨hwb, hwm⟩ := canon_inr_inr_ne m w hzc
    have hv' := occs_inr_inr_mem m w hv
    subst hv'
    exact ⟨w, huv, hwm, rfl⟩

-- [D-0460] incomp_g2_shape
theorem incomp_g2_shape (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {z : GlueBase P} (hzc : canon m z = z)
    (h1 : ¬ leGlue m z (Sum.inl (⊤ : P))) (h2 : ¬ leGlue m (Sum.inl (⊤ : P)) z) :
    ∃ y, y ≠ ⊥ ∧ y ≠ ⊤ ∧ z = Sum.inr (Sum.inl y) := by
  rcases z with w | w | w
  · exact absurd (skel_dsi_copyA_le_g2 m w) h1
  · have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hzc
    by_cases hwt : w = ⊤
    · exfalso; apply h2; rw [hwt]; exact skel_g2_le_g3 m
    · exact ⟨w, hwb, hwt, rfl⟩
  · exfalso
    exact h2 ⟨Sum.inl ⊤, self_mem_occs m _, Sum.inr (Sum.inr w), self_mem_occs m _, trivial⟩

-- [D-0461] tagA_le_tagC
theorem tagA_le_tagC (m y w : P) : leGlue m (Sum.inl y) (Sum.inr (Sum.inr w)) :=
  ⟨Sum.inl y, self_mem_occs m _, Sum.inr (Sum.inr w), self_mem_occs m _, trivial⟩

-- [D-0462] tagA_le_g3
theorem tagA_le_g3 (m y : P) : leGlue m (Sum.inl y) (Sum.inr (Sum.inl (⊤ : P))) := by
  refine ⟨Sum.inl y, self_mem_occs m _, Sum.inr (Sum.inr m), ?_, trivial⟩
  simp [occs]

-- [D-0463] §two-purely-P-level-counting-facts
-- [D-0464] ncard_down_add_strict_up_lt
theorem ncard_down_add_strict_up_lt (m p : P) (hp1 : ¬ p ≤ m) (hp2 : ¬ m ≤ p) :
    ({y : P | y ≤ m}).ncard + ({y : P | m ≤ y ∧ y ≠ m}).ncard + 1 ≤ Nat.card P := by
  have hdisj : Disjoint ({y : P | y ≤ m}) ({y : P | m ≤ y ∧ y ≠ m}) := by
    rw [Set.disjoint_left]
    rintro y hy1 ⟨hy2, hy3⟩
    exact hy3 (le_antisymm hy1 hy2)
  have hpn : p ∉ ({y : P | y ≤ m}) ∪ ({y : P | m ≤ y ∧ y ≠ m}) := by
    rintro (h | ⟨h, _⟩)
    · exact hp1 h
    · exact hp2 h
  have hle := Set.ncard_le_ncard
    (Set.subset_univ (insert p (({y : P | y ≤ m}) ∪ ({y : P | m ≤ y ∧ y ≠ m}))))
    (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hpn (Set.toFinite _),
      Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_univ] at hle
  exact hle

-- [D-0465] ncard_strict_down_add_up_le
theorem ncard_strict_down_add_up_le (x : P) (hxb : x ≠ ⊥) :
    ({y : P | y ≤ x ∧ y ≠ ⊥}).ncard + ({y : P | x ≤ y}).ncard ≤ Nat.card P := by
  have hinter : ({y : P | y ≤ x ∧ y ≠ ⊥}) ∩ ({y : P | x ≤ y}) = {x} := by
    ext y
    constructor
    · rintro ⟨⟨hy1, _⟩, hy3⟩; exact le_antisymm hy1 hy3
    · rintro rfl; exact ⟨⟨le_refl _, hxb⟩, le_refl _⟩
  have hbn : (⊥ : P) ∉ ({y : P | y ≤ x ∧ y ≠ ⊥}) ∪ ({y : P | x ≤ y}) := by
    rintro (⟨_, h⟩ | h)
    · exact h rfl
    · exact hxb (le_bot_iff.mp h)
  have hle := Set.ncard_le_ncard
    (Set.subset_univ (insert (⊥ : P) (({y : P | y ≤ x ∧ y ≠ ⊥}) ∪ ({y : P | x ≤ y}))))
    (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hbn (Set.toFinite _), Set.ncard_univ] at hle
  have hsum := Set.ncard_union_add_ncard_inter
    ({y : P | y ≤ x ∧ y ≠ ⊥}) ({y : P | x ≤ y})
  rw [hinter, Set.ncard_singleton] at hsum
  omega

-- [D-0466] §down-sets-up-sets-in-P
-- [D-0467] gDown
def gDown (m : P) (z : GlueCar (P := P) m) : Set (GlueCar (P := P) m) := {w | w ≤ z}
-- [D-0468] gUp
def gUp (m : P) (z : GlueCar (P := P) m) : Set (GlueCar (P := P) m) := {w | z ≤ w}

-- [D-0469] gDown_ncard_map
theorem gDown_ncard_map (m : P) (φ : GlueCar (P := P) m ≃o GlueCar (P := P) m)
    (z : GlueCar (P := P) m) : (gDown m (φ z)).ncard = (gDown m z).ncard := by
  have himg : gDown m (φ z) = φ '' gDown m z := by
    ext w
    simp only [gDown, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      have h2 : φ (φ.symm w) ≤ φ z := by rw [φ.apply_symm_apply]; exact h
      exact φ.le_iff_le.mp h2
    · rintro ⟨w', hw', rfl⟩; exact φ.le_iff_le.mpr hw'
  rw [himg]; exact Set.ncard_image_of_injective _ φ.injective

-- [D-0470] gUp_ncard_map
theorem gUp_ncard_map (m : P) (φ : GlueCar (P := P) m ≃o GlueCar (P := P) m)
    (z : GlueCar (P := P) m) : (gUp m (φ z)).ncard = (gUp m z).ncard := by
  have himg : gUp m (φ z) = φ '' gUp m z := by
    ext w
    simp only [gUp, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      have h2 : φ z ≤ φ (φ.symm w) := by rw [φ.apply_symm_apply]; exact h
      exact φ.le_iff_le.mp h2
    · rintro ⟨w', hw', rfl⟩; exact φ.le_iff_le.mpr hw'
  rw [himg]; exact Set.ncard_image_of_injective _ φ.injective

-- [D-0471] gDown_glueA
theorem gDown_glueA (m : P) (hm : m ≠ ⊥) (x : P) :
    gDown m (glueA m x) = (glueA m) '' {y : P | y ≤ x} := by
  ext w
  simp only [gDown, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨y, hyx, hy⟩ := le_tagA_shape m hm x w.2 h
    exact ⟨y, hyx, Subtype.ext hy.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact (glueA_le_iff m hm y x).mpr hy

-- [D-0472] glueA_inj
theorem glueA_inj (m : P) : Function.Injective (glueA m) := fun _ _ h => glueA_injective m h

-- [D-0473] glueCt_inj
theorem glueCt_inj (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    Function.Injective (glueCt m hm hbt) := by
  intro a b h
  rw [← unC_glueCt m hm hbt a, ← unC_glueCt m hm hbt b, h]

-- [D-0474] glueBt_inj
theorem glueBt_inj (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    Function.Injective (glueBt m hm hbt) := by
  intro a b h
  rw [← unB_glueBt m hm hbt a, ← unB_glueBt m hm hbt b, h]

-- [D-0475] gDown_g2_ncard
theorem gDown_g2_ncard (m : P) (hm : m ≠ ⊥) :
    (gDown m (glueA m ⊤)).ncard = Nat.card P := by
  rw [gDown_glueA m hm ⊤,
      Set.ncard_image_of_injective _ (glueA_inj m),
      show ({y : P | y ≤ ⊤}) = Set.univ from Set.eq_univ_of_forall (fun _ => le_top),
      Set.ncard_univ]

-- [D-0476] gUp_g2_ncard_ge
theorem gUp_g2_ncard_ge (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    Nat.card P ≤ (gUp m (glueA m ⊤)).ncard := by
  have hsub : Set.range (glueCt m hm hbt) ⊆ gUp m (glueA m ⊤) := by
    rintro _ ⟨y, rfl⟩
    exact skel_dsi_copyC_g2_le m hm hmt hbt y
  calc Nat.card P = (Set.range (glueCt m hm hbt)).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ (glueCt_inj m hm hbt),
            Set.ncard_univ]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

-- [D-0477] §the-pinning-theorem
-- [D-0478] glue_g2_unique
theorem glue_g2_unique (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (p : P) (hp1 : ¬ p ≤ m) (hp2 : ¬ m ≤ p) (z : GlueCar (P := P) m)
    (hdn : (gDown m z).ncard = Nat.card P)
    (hup : Nat.card P ≤ (gUp m z).ncard) :
    z = glueA m ⊤ := by
  obtain ⟨zv, hzc⟩ := z
  rcases zv with x | x | x
  ·
    have hcard : ({y : P | y ≤ x}).ncard = Nat.card P := by
      rw [← Set.ncard_image_of_injective _ (glueA_inj m), ← gDown_glueA m hm x]
      exact hdn
    have huniv : ({y : P | y ≤ x}) = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, hcard]
    have htop : (⊤ : P) ∈ ({y : P | y ≤ x}) := by rw [huniv]; trivial
    have hx : x = ⊤ := le_antisymm le_top htop
    subst hx
    rfl
  ·
    exfalso
    have hxb : x ≠ ⊥ := canon_inr_inl_ne_bot m x hzc
    by_cases hxt : x = ⊤
    ·
      subst hxt
      have hsub : Set.range (glueA m) ⊆ gDown m ⟨Sum.inr (Sum.inl (⊤ : P)), hzc⟩ := by
        rintro _ ⟨y, rfl⟩
        exact tagA_le_g3 m y
      have hnot : (⟨Sum.inr (Sum.inl (⊤ : P)), hzc⟩ : GlueCar (P := P) m) ∉
          Set.range (glueA m) := by
        rintro ⟨y, hy⟩
        have hv := congrArg Subtype.val hy
        simp only [glueA] at hv
        exact absurd hv (by simp)
      have hne : Set.range (glueA m) ≠ gDown m ⟨Sum.inr (Sum.inl (⊤ : P)), hzc⟩ := by
        intro heq
        exact hnot (by rw [heq]; exact leGlue_refl m _)
      have hlt := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        (Set.toFinite _)
      rw [← Set.image_univ, Set.ncard_image_of_injective _ (glueA_inj m),
          Set.ncard_univ, hdn] at hlt
      omega
    ·
      have hD : gDown m ⟨Sum.inr (Sum.inl x), hzc⟩ ⊆
          ((glueA m) '' {y : P | y ≤ m}) ∪
            ((glueBt m hm hbt) '' {y : P | y ≤ x ∧ y ≠ ⊥}) := by
        intro w hw
        rcases le_tagB_shape m hm x hxb hxt w.2 hw with ⟨y, hy, hwy⟩ | ⟨y, hy1, hy2, hwy⟩
        · exact Or.inl ⟨y, hy, Subtype.ext hwy.symm⟩
        · refine Or.inr ⟨y, ⟨hy1, hy2⟩, Subtype.ext ?_⟩
          show iotaB m y = w.1
          rw [iotaB_generic_eq m y hy2]; exact hwy.symm
      have hU : gUp m ⟨Sum.inr (Sum.inl x), hzc⟩ ⊆
          ((glueBt m hm hbt) '' {y : P | x ≤ y}) ∪
            ((glueCt m hm hbt) '' {y : P | m ≤ y ∧ y ≠ m}) := by
        intro w hw
        rcases tagB_le_shape m hm x hxb hxt w.2 hw with ⟨y, hy, hwy⟩ | ⟨y, hy1, hy2, hwy⟩
        · refine Or.inl ⟨y, hy, Subtype.ext ?_⟩
          show iotaB m y = w.1
          have hyb : y ≠ ⊥ := fun h => hxb (le_bot_iff.mp (h ▸ hy))
          rw [iotaB_generic_eq m y hyb]; exact hwy.symm
        · refine Or.inr ⟨y, ⟨hy1, hy2⟩, Subtype.ext ?_⟩
          show iotaC m y = w.1
          have hyb : y ≠ ⊥ := fun h => hm (le_bot_iff.mp (h ▸ hy1))
          rw [iotaC_generic_eq m y hyb hy2]; exact hwy.symm
      have c1 : Nat.card P ≤
          ({y : P | y ≤ m}).ncard + ({y : P | y ≤ x ∧ y ≠ ⊥}).ncard := by
        calc Nat.card P = (gDown m ⟨Sum.inr (Sum.inl x), hzc⟩).ncard := hdn.symm
          _ ≤ (((glueA m) '' {y : P | y ≤ m}) ∪
                ((glueBt m hm hbt) '' {y : P | y ≤ x ∧ y ≠ ⊥})).ncard :=
              Set.ncard_le_ncard hD (Set.toFinite _)
          _ ≤ ((glueA m) '' {y : P | y ≤ m}).ncard +
                ((glueBt m hm hbt) '' {y : P | y ≤ x ∧ y ≠ ⊥}).ncard :=
              Set.ncard_union_le _ _
          _ ≤ ({y : P | y ≤ m}).ncard + ({y : P | y ≤ x ∧ y ≠ ⊥}).ncard :=
              Nat.add_le_add (Set.ncard_image_le (Set.toFinite _))
                (Set.ncard_image_le (Set.toFinite _))
      have c2 : Nat.card P ≤
          ({y : P | x ≤ y}).ncard + ({y : P | m ≤ y ∧ y ≠ m}).ncard := by
        calc Nat.card P ≤ (gUp m ⟨Sum.inr (Sum.inl x), hzc⟩).ncard := hup
          _ ≤ (((glueBt m hm hbt) '' {y : P | x ≤ y}) ∪
                ((glueCt m hm hbt) '' {y : P | m ≤ y ∧ y ≠ m})).ncard :=
              Set.ncard_le_ncard hU (Set.toFinite _)
          _ ≤ ((glueBt m hm hbt) '' {y : P | x ≤ y}).ncard +
                ((glueCt m hm hbt) '' {y : P | m ≤ y ∧ y ≠ m}).ncard :=
              Set.ncard_union_le _ _
          _ ≤ ({y : P | x ≤ y}).ncard + ({y : P | m ≤ y ∧ y ≠ m}).ncard :=
              Nat.add_le_add (Set.ncard_image_le (Set.toFinite _))
                (Set.ncard_image_le (Set.toFinite _))
      have c3 := ncard_down_add_strict_up_lt m p hp1 hp2
      have c4 := ncard_strict_down_add_up_le x hxb
      omega
  ·
    exfalso
    obtain ⟨hxb, hxm⟩ := canon_inr_inr_ne m x hzc
    have hsub : Set.range (glueA m) ⊆ gDown m ⟨Sum.inr (Sum.inr x), hzc⟩ := by
      rintro _ ⟨y, rfl⟩
      exact tagA_le_tagC m y x
    have hnot : (⟨Sum.inr (Sum.inr x), hzc⟩ : GlueCar (P := P) m) ∉
        Set.range (glueA m) := by
      rintro ⟨y, hy⟩
      have hv := congrArg Subtype.val hy
      simp only [glueA] at hv
      exact absurd hv (by simp)
    have hne : Set.range (glueA m) ≠ gDown m ⟨Sum.inr (Sum.inr x), hzc⟩ := by
      intro heq
      exact hnot (by rw [heq]; exact leGlue_refl m _)
    have hlt := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      (Set.toFinite _)
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (glueA_inj m),
        Set.ncard_univ, hdn] at hlt
    omega

-- [D-0479] glue_g2_pinned
theorem glue_g2_pinned (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (p : P) (hp1 : ¬ p ≤ m) (hp2 : ¬ m ≤ p)
    (φ : GlueCar (P := P) m ≃o GlueCar (P := P) m) :
    φ (glueA m ⊤) = glueA m ⊤ := by
  refine glue_g2_unique m hm hmt hbt p hp1 hp2 _ ?_ ?_
  · rw [gDown_ncard_map]; exact gDown_g2_ncard m hm
  · rw [gUp_ncard_map]; exact gUp_g2_ncard_ge m hm hmt hbt

-- [D-0480] §the-UP-TRANSFER-assembly
-- [D-0481] glue_copy_fixed
theorem glue_copy_fixed (m : P) (hAut : Subsingleton (P ≃o P))
    (ι : P → GlueCar (P := P) m) (un : GlueCar (P := P) m → P)
    (hun : ∀ x, un (ι x) = x)
    (hι : ∀ x y, ι x ≤ ι y ↔ x ≤ y)
    (φ : GlueCar (P := P) m ≃o GlueCar (P := P) m)
    (hfwd : ∀ x, ∃ y, φ (ι x) = ι y)
    (hbwd : ∀ x, ∃ y, φ.symm (ι x) = ι y) :
    ∀ x, φ (ι x) = ι x := by
  have hinj : Function.Injective ι := by
    intro a b h; rw [← hun a, ← hun b, h]
  have hf : ∀ x, ι (un (φ (ι x))) = φ (ι x) := by
    intro x; obtain ⟨y, hy⟩ := hfwd x; rw [hy, hun]
  have hg : ∀ x, ι (un (φ.symm (ι x))) = φ.symm (ι x) := by
    intro x; obtain ⟨y, hy⟩ := hbwd x; rw [hy, hun]
  have hgf : ∀ x, un (φ.symm (ι (un (φ (ι x))))) = x := by
    intro x; apply hinj; rw [hg, hf, φ.symm_apply_apply]
  have hfg : ∀ x, un (φ (ι (un (φ.symm (ι x))))) = x := by
    intro x; apply hinj; rw [hf, hg, φ.apply_symm_apply]
  have hmono : ∀ x y, un (φ (ι x)) ≤ un (φ (ι y)) ↔ x ≤ y := by
    intro x y; rw [← hι, hf, hf, φ.le_iff_le, hι]
  let e : P ≃o P :=
    { toFun := fun x => un (φ (ι x))
      invFun := fun x => un (φ.symm (ι x))
      left_inv := hgf
      right_inv := hfg
      map_rel_iff' := fun {a b} => hmono a b }
  intro x
  have he : e = OrderIso.refl P := hAut.elim e (OrderIso.refl P)
  have hx : un (φ (ι x)) = x := by
    have h2 : e x = (OrderIso.refl P) x := by rw [he]
    exact h2
  rw [← hf x, hx]

-- [D-0482] glue_rigid_of_incomparable
theorem glue_rigid_of_incomparable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hAut : Subsingleton (P ≃o P)) (p : P) (hp1 : ¬ p ≤ m) (hp2 : ¬ m ≤ p) :
    Subsingleton (GlueCar (P := P) m ≃o GlueCar (P := P) m) := by
  have key : ∀ (φ : GlueCar (P := P) m ≃o GlueCar (P := P) m)
      (z : GlueCar (P := P) m), φ z = z := by
    intro φ
    have hg2 : φ (glueA m ⊤) = glueA m ⊤ := glue_g2_pinned m hm hmt hbt p hp1 hp2 φ
    have hg2' : φ.symm (glueA m ⊤) = glueA m ⊤ :=
      glue_g2_pinned m hm hmt hbt p hp1 hp2 φ.symm
    have hA : ∀ x, φ (glueA m x) = glueA m x := by
      refine glue_copy_fixed m hAut (glueA m) (fun w => unA w.1) (fun x => rfl)
        (fun x y => glueA_le_iff m hm x y) φ ?_ ?_
      · intro x
        have h1 : φ (glueA m x) ≤ glueA m ⊤ := by
          rw [← hg2]; exact φ.le_iff_le.mpr (skel_dsi_copyA_le_g2 m x)
        obtain ⟨y, _, hy⟩ := le_tagA_shape m hm ⊤ (φ (glueA m x)).2 h1
        exact ⟨y, Subtype.ext hy⟩
      · intro x
        have h1 : φ.symm (glueA m x) ≤ glueA m ⊤ := by
          rw [← hg2']; exact φ.symm.le_iff_le.mpr (skel_dsi_copyA_le_g2 m x)
        obtain ⟨y, _, hy⟩ := le_tagA_shape m hm ⊤ (φ.symm (glueA m x)).2 h1
        exact ⟨y, Subtype.ext hy⟩
    have hC : ∀ x, φ (glueCt m hm hbt x) = glueCt m hm hbt x := by
      refine glue_copy_fixed m hAut (glueCt m hm hbt) (fun w => unC m w.1)
        (unC_glueCt m hm hbt) (fun x y => glueCt_le_iff m hm hmt hbt x y) φ ?_ ?_
      · intro x
        have h1 : glueA m ⊤ ≤ φ (glueCt m hm hbt x) := by
          rw [← hg2]; exact φ.le_iff_le.mpr (skel_dsi_copyC_g2_le m hm hmt hbt x)
        obtain ⟨y, hy⟩ := tagA_top_le_shape m hm hmt hbt (φ (glueCt m hm hbt x)).2 h1
        exact ⟨y, Subtype.ext hy⟩
      · intro x
        have h1 : glueA m ⊤ ≤ φ.symm (glueCt m hm hbt x) := by
          rw [← hg2']; exact φ.symm.le_iff_le.mpr (skel_dsi_copyC_g2_le m hm hmt hbt x)
        obtain ⟨y, hy⟩ := tagA_top_le_shape m hm hmt hbt (φ.symm (glueCt m hm hbt x)).2 h1
        exact ⟨y, Subtype.ext hy⟩
    have hg1 : glueBt m hm hbt (⊥ : P) = glueA m m := by
      apply Subtype.ext
      show iotaB m (⊥ : P) = Sum.inl m
      simp [canon]
    have hg3 : glueBt m hm hbt (⊤ : P) = glueCt m hm hbt m := by
      apply Subtype.ext
      show iotaB m (⊤ : P) = iotaC m m
      rw [iotaB_generic_eq m ⊤ (Ne.symm hbt),
          show iotaC m m = Sum.inr (Sum.inl (⊤ : P)) from by simp [canon, hm]]
    have hBfwd : ∀ (ψ : GlueCar (P := P) m ≃o GlueCar (P := P) m),
        ψ (glueA m ⊤) = glueA m ⊤ →
        (∀ x, ψ (glueA m x) = glueA m x) →
        (∀ x, ψ (glueCt m hm hbt x) = glueCt m hm hbt x) →
        ∀ x, ∃ y, ψ (glueBt m hm hbt x) = glueBt m hm hbt y := by
      intro ψ hψ2 hψA hψC x
      by_cases hxb : x = ⊥
      · subst hxb
        exact ⟨⊥, by rw [hg1, hψA]⟩
      · by_cases hxt : x = ⊤
        · subst hxt
          exact ⟨⊤, by rw [hg3, hψC]⟩
        · have hi := skel_dsi_copyB_incomp m hm hmt x hxb hxt
          have h1 : ¬ (ψ (glueBt m hm hbt x) ≤ glueA m ⊤) := by
            rw [← hψ2]; intro hcon; exact hi.1 (ψ.le_iff_le.mp hcon)
          have h2 : ¬ (glueA m ⊤ ≤ ψ (glueBt m hm hbt x)) := by
            rw [← hψ2]; intro hcon; exact hi.2 (ψ.le_iff_le.mp hcon)
          obtain ⟨y, hyb, _, hy⟩ :=
            incomp_g2_shape m hm hmt hbt (ψ (glueBt m hm hbt x)).2 h1 h2
          refine ⟨y, Subtype.ext ?_⟩
          show (ψ (glueBt m hm hbt x)).1 = iotaB m y
          rw [hy, iotaB_generic_eq m y hyb]
    have hCsymm : ∀ x, φ.symm (glueCt m hm hbt x) = glueCt m hm hbt x := by
      intro x
      have h := congrArg φ.symm (hC x)
      rw [φ.symm_apply_apply] at h
      exact h.symm
    have hAsymm : ∀ x, φ.symm (glueA m x) = glueA m x := by
      intro x
      have h := congrArg φ.symm (hA x)
      rw [φ.symm_apply_apply] at h
      exact h.symm
    have hB : ∀ x, φ (glueBt m hm hbt x) = glueBt m hm hbt x := by
      refine glue_copy_fixed m hAut (glueBt m hm hbt) (fun w => unB w.1)
        (unB_glueBt m hm hbt) (fun x y => glueBt_le_iff m hm hmt hbt x y) φ
        (hBfwd φ hg2 hA hC) (hBfwd φ.symm hg2' hAsymm hCsymm)
    intro z
    obtain ⟨zv, hzc⟩ := z
    rcases zv with x | x | x
    · exact hA x
    · have hxb : x ≠ ⊥ := canon_inr_inl_ne_bot m x hzc
      have hz : (⟨Sum.inr (Sum.inl x), hzc⟩ : GlueCar (P := P) m) = glueBt m hm hbt x := by
        apply Subtype.ext
        show Sum.inr (Sum.inl x) = iotaB m x
        rw [iotaB_generic_eq m x hxb]
      rw [hz]; exact hB x
    · obtain ⟨hxb, hxm⟩ := canon_inr_inr_ne m x hzc
      have hz : (⟨Sum.inr (Sum.inr x), hzc⟩ : GlueCar (P := P) m) = glueCt m hm hbt x := by
        apply Subtype.ext
        show Sum.inr (Sum.inr x) = iotaC m x
        rw [iotaC_generic_eq m x hxb hxm]
      rw [hz]; exact hC x
  exact ⟨fun a b => OrderIso.ext (funext (fun z => by rw [key a z, key b z]))⟩

end G2Pin

-- [D-0483] GluingTower
class GluingTower (D : ℕ → Type u)
    (_Hlat : ∀ k, Lattice (D k)) (_Hbdd : ∀ k, BoundedOrder (D k))
    (_Hfin : ∀ k, Fintype (D k)) where
  uac : ∀ k, UniqueAtomCoatom (D k)
  base0_rigid : Subsingleton (D 0 ≃o D 0)
  base1_rigid : Subsingleton (D 1 ≃o D 1)

-- [D-0484] GluingTowerUp
class GluingTowerUp (D : ℕ → Type u) [∀ k, Lattice (D k)]
    [∀ k, BoundedOrder (D k)] : Prop where
  up_transfer : ∀ k, Subsingleton (EndP (D k) ≃o EndP (D k)) →
    Subsingleton (D (k+1) ≃o D (k+1))

-- [D-0485] GluingTowerDown
class GluingTowerDown (D : ℕ → Type u) [∀ k, Lattice (D k)]
    [∀ k, BoundedOrder (D k)] : Prop where
  down_transfer : ∀ k, Subsingleton (D k ≃o D k) →
    Subsingleton (EndP (D k) ≃o EndP (D k))

-- [D-0486] connected_of_le_subtype
theorem connected_of_le_subtype {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
    (S : α → Prop) [DecidablePred S] :
    ∀ (n : ℕ) (a b : {x : α // S x}), (a : α) ≤ (b : α) →
      (Finset.univ.filter (fun c : {x : α // S x} => (a : α) < c.1 ∧ c.1 < (b : α))).card ≤ n →
      Relation.ReflTransGen (Graph.Hasse {x : α // S x}).adj a b := by
  intro n
  induction n with
  | zero =>
    intro a b hab hcard
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hab' : a = b := Subtype.ext heq
      rw [hab']
    · have hnone : ∀ c : {x : α // S x}, ¬ ((a : α) < c.1 ∧ c.1 < (b : α)) := by
        intro c hc
        have hmem : c ∈ Finset.univ.filter (fun c : {x : α // S x} => (a : α) < c.1 ∧ c.1 < (b : α)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩
        have := Finset.card_pos.mpr ⟨c, hmem⟩
        omega
      have hadj : (Graph.Hasse {x : α // S x}).adj a b :=
        Or.inl ⟨hlt, fun c hc1 hc2 => hnone c ⟨hc1, hc2⟩⟩
      exact Relation.ReflTransGen.single hadj
  | succ n ih =>
    intro a b hab hcard
    set T := Finset.univ.filter (fun c : {x : α // S x} => (a : α) < c.1 ∧ c.1 < (b : α)) with hTdef
    rcases T.eq_empty_or_nonempty with hempty | ⟨c, hcmem⟩
    · rcases eq_or_lt_of_le hab with heq | hlt
      · have hab' : a = b := Subtype.ext heq
        rw [hab']
      · have hnone : ∀ c : {x : α // S x}, ¬ ((a : α) < c.1 ∧ c.1 < (b : α)) := by
          intro c hc
          have hmem : c ∈ T := by
            rw [hTdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩
          rw [hempty] at hmem
          simp at hmem
        have hadj : (Graph.Hasse {x : α // S x}).adj a b :=
          Or.inl ⟨hlt, fun c hc1 hc2 => hnone c ⟨hc1, hc2⟩⟩
        exact Relation.ReflTransGen.single hadj
    · have hcmem' : (a : α) < c.1 ∧ c.1 < (b : α) := by
        have := hcmem
        simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      have hac : Relation.ReflTransGen (Graph.Hasse {x : α // S x}).adj a c := by
        apply ih a c hcmem'.1.le
        have hsub : (Finset.univ.filter (fun d : {x : α // S x} => (a : α) < d.1 ∧ d.1 < c.1)) ⊆
            T \ {c} := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [hTdef]
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          exact ⟨⟨hd.1, hd.2.trans hcmem'.2⟩, fun heq => (heq ▸ hd.2).ne rfl⟩
        calc (Finset.univ.filter (fun d : {x : α // S x} => (a : α) < d.1 ∧ d.1 < c.1)).card
            ≤ (T \ {c}).card := Finset.card_le_card hsub
          _ ≤ T.card - 1 := by rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hcmem)]; simp
          _ ≤ n := by omega
      have hcb : Relation.ReflTransGen (Graph.Hasse {x : α // S x}).adj c b := by
        apply ih c b hcmem'.2.le
        have hsub : (Finset.univ.filter (fun d : {x : α // S x} => c.1 < d.1 ∧ (d : α) < (b : α))) ⊆
            T \ {c} := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [hTdef]
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          exact ⟨⟨hcmem'.1.trans hd.1, hd.2⟩, fun heq => (heq ▸ hd.1).ne' rfl⟩
        calc (Finset.univ.filter (fun d : {x : α // S x} => c.1 < d.1 ∧ (d : α) < (b : α))).card
            ≤ (T \ {c}).card := Finset.card_le_card hsub
          _ ≤ T.card - 1 := by rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hcmem)]; simp
          _ ≤ n := by omega
      exact hac.trans hcb

-- [D-0487] connected_of_le_subtype'
theorem connected_of_le_subtype' {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
    (S : α → Prop) [DecidablePred S] (a b : {x : α // S x}) (hab : (a : α) ≤ (b : α)) :
    Relation.ReflTransGen (Graph.Hasse {x : α // S x}).adj a b :=
  connected_of_le_subtype S _ a b hab le_rfl

section JConnHub
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0488] atomOf_hasUniqueDownCover
theorem atomOf_hasUniqueDownCover : HasUniqueDownCover (atomOf P) :=
  ⟨⊥, atomOf_covers_bot, fun a' ha' => by
    by_contra hne
    have hbot_lt : (⊥ : P) < a' := lt_of_le_of_ne bot_le (Ne.symm hne)
    exact atomOf_covers_bot.2 a' hbot_lt ha'.1⟩

variable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)

-- [D-0489] hasse_hasUniqueDownCover_glueCar_connected
theorem hasse_hasUniqueDownCover_glueCar_connected :
    letI := glueCarPartialOrder m hm hmt hbt
    (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).Connected := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hub1_udc : HasUniqueDownCover (glueA m (⊤ : P)) :=
    (hasUniqueDownCover_glueA_iff m hm hmt hbt (⊤ : P)).mpr hasUniqueDownCover_top
  have hub2_udc : HasUniqueDownCover (glueA m (atomOf P)) :=
    (hasUniqueDownCover_glueA_iff m hm hmt hbt (atomOf P)).mpr atomOf_hasUniqueDownCover
  have hub2_le_hub1 : glueA m (atomOf P) ≤ glueA m (⊤ : P) :=
    (glueA_le_iff m hm (atomOf P) (⊤ : P)).mpr le_top
  have hub2pt_to_hub1 :
      Relation.ReflTransGen (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).adj
        (⟨glueA m (atomOf P), hub2_udc⟩ : {f : GlueCar (P := P) m // HasUniqueDownCover f})
        ⟨glueA m (⊤ : P), hub1_udc⟩ :=
    connected_of_le_subtype' HasUniqueDownCover _ _ hub2_le_hub1
  suffices h : ∀ g : {f : GlueCar (P := P) m // HasUniqueDownCover f},
      Relation.ReflTransGen (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).adj
        g ⟨glueA m (⊤ : P), hub1_udc⟩ by
    intro a b
    exact (h a).trans
      (reflTransGen_symm_of_symm
        (fun x y hxy => (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).symm hxy)
        (h b))
  rintro ⟨gc, hg_udc⟩
  obtain ⟨cv, hcvfix⟩ := gc
  rcases cv with w | w | w
  ·
    have hle : glueA m w ≤ glueA m (⊤ : P) := (glueA_le_iff m hm w (⊤ : P)).mpr le_top
    exact connected_of_le_subtype' HasUniqueDownCover _ _ hle
  ·
    have hwb : w ≠ ⊥ := by rintro rfl; simp [canon] at hcvfix
    have hle : glueA m (atomOf P) ≤ glueB m w hwb := by
      rw [GlueCar.le_def]
      exact ⟨Sum.inl (atomOf P), self_mem_occs m _, Sum.inr (Sum.inl w), self_mem_occs m _,
        atomOf_le hm⟩
    have hstep : Relation.ReflTransGen
        (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).adj
        (⟨glueA m (atomOf P), hub2_udc⟩ : {f : GlueCar (P := P) m // HasUniqueDownCover f})
        ⟨glueB m w hwb, hg_udc⟩ :=
      connected_of_le_subtype' HasUniqueDownCover _ _ hle
    exact (reflTransGen_symm_of_symm
        (fun x y hxy => (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).symm hxy)
        hstep).trans hub2pt_to_hub1
  ·
    have hwb : w ≠ ⊥ := by rintro rfl; simp [canon] at hcvfix
    have hwm : w ≠ m := by
      rintro rfl
      simp [canon, hwb] at hcvfix
    have hle : glueA m (⊤ : P) ≤ glueC m w hwb hwm := by
      rw [GlueCar.le_def]
      exact leGlue_tagA_tagC m ⊤ w
    have hstep : Relation.ReflTransGen
        (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).adj
        (⟨glueA m (⊤ : P), hub1_udc⟩ : {f : GlueCar (P := P) m // HasUniqueDownCover f})
        ⟨glueC m w hwb hwm, hg_udc⟩ :=
      connected_of_le_subtype' HasUniqueDownCover _ _ hle
    exact reflTransGen_symm_of_symm
        (fun x y hxy => (Graph.Hasse {f : GlueCar (P := P) m // HasUniqueDownCover f}).symm hxy)
        hstep

end JConnHub

-- [D-0490] connected_of_pointwise_iff
theorem connected_of_pointwise_iff {α : Type*} [PartialOrder α]
    (S1 S2 : α → Prop) (h : ∀ a, S1 a ↔ S2 a) :
    (Graph.Hasse {x : α // S1 x}).Connected → (Graph.Hasse {x : α // S2 x}).Connected := by
  have heq : S1 = S2 := funext (fun a => propext (h a))
  subst heq
  exact id

-- [D-0491] covers_orderIso
theorem covers_orderIso {L M : Type*} [Preorder L] [Preorder M] (Ψ : L ≃o M) {a b : L}
    (h : Covers a b) : Covers (Ψ a) (Ψ b) := by
  refine ⟨Ψ.strictMono h.1, ?_⟩
  intro c hac hcb
  have h1 : a < Ψ.symm c := by
    have := Ψ.symm.strictMono hac
    simpa using this
  have h2 : Ψ.symm c < b := by
    have := Ψ.symm.strictMono hcb
    simpa using this
  exact h.2 (Ψ.symm c) h1 h2

-- [D-0492] joinIrred_orderIso
theorem joinIrred_orderIso {L M : Type*} [Lattice L] [OrderBot L] [Lattice M] [OrderBot M]
    (Ψ : L ≃o M) {a : L} (ha : JoinIrred L a) : JoinIrred M (Ψ a) := by
  refine ⟨fun h => ha.1 (Ψ.injective (h.trans (OrderIso.map_bot Ψ).symm)), ?_⟩
  intro b c hbc
  have h2 : a = Ψ.symm b ⊔ Ψ.symm c := by
    apply Ψ.injective
    rw [Ψ.map_sup, Ψ.apply_symm_apply, Ψ.apply_symm_apply]
    exact hbc
  rcases ha.2 _ _ h2 with h | h
  · left; rw [h, Ψ.apply_symm_apply]
  · right; rw [h, Ψ.apply_symm_apply]

section TauHatJI
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0493] tauHat_eq_of_joinIrred
theorem tauHat_eq_of_joinIrred (τ : {x : P // JoinIrred P x} ≃ {x : P // JoinIrred P x})
    (hτord : ∀ b1 b2 : {x : P // JoinIrred P x}, b1 ≤ b2 ↔ τ b1 ≤ τ b2)
    (v : P) (hv : JoinIrred P v) : tauHat τ v = (τ ⟨v, hv⟩).1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hxJI, hxle⟩ := hx
    rw [dif_pos hxJI]
    exact (hτord ⟨x, hxJI⟩ ⟨v, hv⟩).mp hxle
  · have hmem : v ∈ Finset.univ.filter (fun x : P => JoinIrred P x ∧ x ≤ v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv, le_refl v⟩
    have hle := Finset.le_sup (f := fun x => if hx : JoinIrred P x then (τ ⟨x, hx⟩).1 else ⊥) hmem
    rwa [dif_pos hv] at hle

end TauHatJI

-- [D-0494] aut_D_k_trivial
theorem aut_D_k_trivial
    (D : ℕ → Type u) [∀ k, Lattice (D k)] [∀ k, BoundedOrder (D k)]
    [GluingTowerUp D] [GluingTowerDown D]
    (base : Subsingleton (D 0 ≃o D 0)) :
    ∀ k, Subsingleton (D k ≃o D k) := by
  intro k
  induction k with
  | zero => exact base
  | succ n ih =>
      have hEnd : Subsingleton (EndP (D n) ≃o EndP (D n)) :=
        GluingTowerDown.down_transfer n ih
      exact GluingTowerUp.up_transfer n hEnd

-- [D-0495] aut_D_infinity_trivial
theorem aut_D_infinity_trivial
    (Dinfty : Type u) [Lattice Dinfty] [BoundedOrder Dinfty]
    (D : ℕ → Type u) [∀ k, Lattice (D k)] [∀ k, BoundedOrder (D k)]
    [GluingTowerUp D] [GluingTowerDown D]
    (base : Subsingleton (D 0 ≃o D 0))
    (colimit_compat :
      Subsingleton (Dinfty ≃o Dinfty) ↔ ∀ k, Subsingleton (D k ≃o D k)) :
    Subsingleton (Dinfty ≃o Dinfty) :=
  colimit_compat.mpr (aut_D_k_trivial D base)

-- [D-0496] constHom_le_iff
theorem constHom_le_iff {P : Type u} [Lattice P] [BoundedOrder P] (c d : P) :
    (constHom c : EndP P) ≤ constHom d ↔ c ≤ d := by
  constructor
  · intro h
    have h1 := OrderHom.le_def.mp h (⊥ : P)
    rwa [constHom_apply, constHom_apply] at h1
  · intro h
    rw [OrderHom.le_def]
    intro y
    rwa [constHom_apply, constHom_apply]

-- [D-0497] constHom_injective
theorem constHom_injective {P : Type u} [Lattice P] [BoundedOrder P] :
    Function.Injective (constHom (P := P)) := by
  intro c d h
  exact le_antisymm ((constHom_le_iff c d).mp h.le) ((constHom_le_iff d c).mp h.ge)

-- [D-0498] meetHom_le_iff
theorem meetHom_le_iff {P : Type u} [Lattice P] [BoundedOrder P] (c d : P) :
    (meetHom c : EndP P) ≤ meetHom d ↔ c ≤ d := by
  constructor
  · intro h
    have h1 := OrderHom.le_def.mp h (⊤ : P)
    simpa using h1
  · intro h
    rw [OrderHom.le_def]
    intro y
    simpa using inf_le_inf_left y h

-- [D-0499] meetHom_injective
theorem meetHom_injective {P : Type u} [Lattice P] [BoundedOrder P] :
    Function.Injective (meetHom (P := P)) := by
  intro c d h
  exact le_antisymm ((meetHom_le_iff c d).mp h.le) ((meetHom_le_iff d c).mp h.ge)

-- [D-0500] meetHom_top
@[simp] theorem meetHom_top {P : Type u} [Lattice P] [BoundedOrder P] :
    (meetHom (⊤ : P) : EndP P) = OrderHom.id := by
  ext x; simp [meetHom_apply]

-- [D-0501] meetHom_bot
@[simp] theorem meetHom_bot {P : Type u} [Lattice P] [BoundedOrder P] :
    (meetHom (⊥ : P) : EndP P) = constHom ⊥ := by
  ext x; simp [meetHom_apply]

section EpPairProjection

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0502] pGen
noncomputable def pGen (w : GlueCar (P := EndP L) (OrderHom.id)) : L :=
  match w.1 with
  | Sum.inl f => f (⊥ : L)
  | Sum.inr (Sum.inl f) => if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)
  | Sum.inr (Sum.inr _) => (⊤ : L)

-- [D-0503] pGen_section
theorem pGen_section (x : L) :
    pGen (glueA (OrderHom.id : EndP L) (constHom x)) = x := by
  show (constHom x : EndP L) ⊥ = x
  rw [constHom_apply]

-- [D-0504] not_leGlue_tagC_tagA
theorem not_leGlue_tagC_tagA {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
    (m w x : P) (hw : w ≠ ⊥) :
    ¬ leGlue m (Sum.inr (Sum.inr w)) (Sum.inl x) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs] using hu
  subst hu'
  rcases occs_inl_mem m x hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
  · exact huv.elim
  · exact huv.elim
  · exact hw (le_bot_iff.mp huv)

-- [D-0505] le_glueA_imp_glueA_shaped
theorem le_glueA_imp_glueA_shaped {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    [Fintype P] (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    (z : GlueCar (P := P) m) (x : P) (hz : leGlue m z.1 (Sum.inl x)) :
    ∃ w, z.1 = Sum.inl w := by
  obtain ⟨zv, hzc⟩ := z
  rcases zv with w | w | w
  · exact ⟨w, rfl⟩
  · exfalso
    have hw : w ≠ ⊥ := by rintro rfl; simp [canon, hm] at hzc
    exact not_leGlue_tagB_tagA m w x hm hbt hw hz
  · exfalso
    have hw : w ≠ ⊥ := by rintro rfl; simp [canon] at hzc
    exact not_leGlue_tagC_tagA m w x hw hz

-- [D-0506] glueA_sup
theorem glueA_sup {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    letI := glueLattice m hm hmt hbt
    glueA m x ⊔ glueA m y = glueA m (x ⊔ y) := by
  letI := glueLattice m hm hmt hbt
  apply Subtype.ext
  show canon m (glueJoinRaw m (Sum.inl x) (Sum.inl y)) = Sum.inl (x ⊔ y)
  simp [glueJoinRaw, canon]

-- [D-0507] glueA_inf
theorem glueA_inf {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (x y : P) :
    letI := glueLattice m hm hmt hbt
    glueA m x ⊓ glueA m y = glueA m (x ⊓ y) := by
  letI := glueLattice m hm hmt hbt
  have hxy1 : leGlue m (glueA m x ⊓ glueA m y).1 (Sum.inl x) :=
    (GlueCar.le_def m (glueA m x ⊓ glueA m y) (glueA m x)).mp inf_le_left
  obtain ⟨w, hw⟩ := le_glueA_imp_glueA_shaped m hm hbt (glueA m x ⊓ glueA m y) x hxy1
  have heq : glueA m x ⊓ glueA m y = glueA m w := Subtype.ext hw
  have hwx : glueA m w ≤ glueA m x := by rw [← heq]; exact inf_le_left
  have hwy : glueA m w ≤ glueA m y := by rw [← heq]; exact inf_le_right
  have hwx' : w ≤ x := (glueA_le_iff m hm w x).mp hwx
  have hwy' : w ≤ y := (glueA_le_iff m hm w y).mp hwy
  apply le_antisymm
  · rw [heq]; exact (glueA_le_iff m hm w (x ⊓ y)).mpr (le_inf hwx' hwy')
  · exact le_inf ((glueA_le_iff m hm (x ⊓ y) x).mpr inf_le_left)
      ((glueA_le_iff m hm (x ⊓ y) y).mpr inf_le_right)

-- [D-0508] glueA_bot
theorem glueA_bot {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueLattice m hm hmt hbt
    letI := glueBoundedOrder m hm hmt hbt
    glueA m (⊥ : P) = ⊥ := by
  letI := glueLattice m hm hmt hbt
  letI := glueBoundedOrder m hm hmt hbt
  rfl

-- [D-0509] joinIrred_glueA_iff
theorem joinIrred_glueA_iff {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    [Fintype P] (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (v : P) :
    letI := glueLattice m hm hmt hbt
    letI := glueBoundedOrder m hm hmt hbt
    JoinIrred (GlueCar (P := P) m) (glueA m v) ↔ JoinIrred P v := by
  letI := glueLattice m hm hmt hbt
  letI := glueBoundedOrder m hm hmt hbt
  constructor
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hv0 => hne (hv0 ▸ glueA_bot m hm hmt hbt), fun b c hbc => ?_⟩
    have hsplit' := hsplit (glueA m b) (glueA m c) (by rw [glueA_sup m hm hmt hbt, hbc])
    rcases hsplit' with h | h
    · exact Or.inl (glueA_injective m h)
    · exact Or.inr (glueA_injective m h)
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hv0 => hne (glueA_injective m (hv0.trans (glueA_bot m hm hmt hbt).symm)),
      fun b c hbc => ?_⟩
    have hble : b ≤ glueA m v := hbc ▸ le_sup_left
    have hcle : c ≤ glueA m v := hbc ▸ le_sup_right
    obtain ⟨b', hb'⟩ := le_glueA_imp_glueA_shaped m hm hbt b v ((GlueCar.le_def m b (glueA m v)).mp hble)
    obtain ⟨c', hc'⟩ := le_glueA_imp_glueA_shaped m hm hbt c v ((GlueCar.le_def m c (glueA m v)).mp hcle)
    have hbeq : b = glueA m b' := Subtype.ext hb'
    have hceq : c = glueA m c' := Subtype.ext hc'
    have hv_eq : glueA m v = glueA m (b' ⊔ c') := by
      rw [hbc, hbeq, hceq, glueA_sup m hm hmt hbt]
    have hv_split : v = b' ⊔ c' := glueA_injective m hv_eq
    rcases hsplit b' c' hv_split with h | h
    · exact Or.inl (by rw [h]; exact hbeq.symm)
    · exact Or.inr (by rw [h]; exact hceq.symm)

-- [D-0510] constHom_sup
theorem constHom_sup {P : Type u} [Lattice P] [BoundedOrder P] (c d : P) :
    (constHom c : EndP P) ⊔ constHom d = constHom (c ⊔ d) := by
  ext x; simp [constHom_apply]

-- [D-0511] constHom_inf
theorem constHom_inf {P : Type u} [Lattice P] [BoundedOrder P] (c d : P) :
    (constHom c : EndP P) ⊓ constHom d = constHom (c ⊓ d) := by
  ext x; simp [constHom_apply]

-- [D-0512] leGlue_tagA_tagB_top
theorem leGlue_tagA_tagB_top {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]
    (m w : P) : leGlue m (Sum.inl w) (Sum.inr (Sum.inl (⊤ : P))) := by
  refine ⟨Sum.inl w, self_mem_occs m _, Sum.inr (Sum.inr m), ?_, trivial⟩
  simp [occs]

-- [D-0513] ne_bot_of_canon_tagB
theorem ne_bot_of_canon_tagB {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    (m f : P) (hwv : canon m (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl f)) : f ≠ ⊥ := by
  intro hfb
  rw [canon, if_pos hfb] at hwv
  exact (Sum.inl_ne_inr) hwv

-- [D-0514] ne_bot_of_canon_tagC
theorem ne_bot_of_canon_tagC {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    (m f : P) (hwv : canon m (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr f)) : f ≠ ⊥ := by
  intro hfb
  rw [canon, if_pos hfb] at hwv
  exact (Sum.inl_ne_inr) hwv

-- [D-0515] pGen_deflation
theorem pGen_deflation (w : GlueCar (P := EndP L) (OrderHom.id)) :
    leGlue (OrderHom.id : EndP L) (Sum.inl (constHom (pGen w) : EndP L)) w.1 := by
  obtain ⟨wv, hwv⟩ := w
  rcases wv with f | f | f
  · show leGlue (OrderHom.id : EndP L) (Sum.inl (constHom (f (⊥ : L)) : EndP L)) (Sum.inl f)
    refine ⟨Sum.inl (constHom (f (⊥ : L))), self_mem_occs _ _, Sum.inl f, self_mem_occs _ _, ?_⟩
    show (constHom (f (⊥ : L)) : EndP L) ≤ f
    rw [OrderHom.le_def]
    intro z
    rw [constHom_apply]
    exact f.monotone bot_le
  · show leGlue (OrderHom.id : EndP L)
        (Sum.inl (constHom (if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)) : EndP L))
        (Sum.inr (Sum.inl f))
    by_cases hft : f = (⊤ : EndP L)
    · rw [if_pos hft, hft]
      exact leGlue_tagA_tagB_top (OrderHom.id : EndP L) (constHom (⊤ : L))
    · rw [if_neg hft]
      exact (leGlue_tagA_tagB_iff (OrderHom.id : EndP L) (constHom (⊥ : L)) f hft).mpr (by
        rw [OrderHom.le_def]; intro z; rw [constHom_apply]; exact bot_le)
  · show leGlue (OrderHom.id : EndP L) (Sum.inl (constHom (⊤ : L) : EndP L)) (Sum.inr (Sum.inr f))
    exact ⟨Sum.inl (constHom (⊤ : L)), self_mem_occs _ _, Sum.inr (Sum.inr f), self_mem_occs _ _, trivial⟩

-- [D-0516] pGen_monotone
theorem pGen_monotone (hm : (OrderHom.id : EndP L) ≠ ⊥) (hbt : (⊥ : EndP L) ≠ (⊤ : EndP L))
    (w w' : GlueCar (P := EndP L) (OrderHom.id))
    (hle : w ≤ w') : pGen w ≤ pGen w' := by
  rw [GlueCar.le_def] at hle
  obtain ⟨wv, hwv⟩ := w
  obtain ⟨wv', hwv'⟩ := w'
  simp only at hle
  rcases wv with f | f | f <;> rcases wv' with f' | f' | f'
  ·
    show f (⊥ : L) ≤ f' (⊥ : L)
    have h : f ≤ f' := (tagA_iso (OrderHom.id : EndP L) hm f f').mp hle
    exact (OrderHom.le_def.mp h) ⊥
  ·
    show f (⊥ : L) ≤ (if f' = (⊤ : EndP L) then (⊤ : L) else (⊥ : L))
    by_cases hf't : f' = (⊤ : EndP L)
    · rw [if_pos hf't]; exact le_top
    · rw [if_neg hf't]
      have hfm : f ≤ (OrderHom.id : EndP L) :=
        (leGlue_tagA_tagB_iff (OrderHom.id : EndP L) f f' hf't).mp hle
      exact OrderHom.le_def.mp hfm ⊥
  ·
    show f (⊥ : L) ≤ (⊤ : L)
    exact le_top
  ·
    exact absurd hle (not_leGlue_tagB_tagA (OrderHom.id : EndP L) f f' hm hbt
      (ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hwv))
  ·
    show (if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)) ≤
        (if f' = (⊤ : EndP L) then (⊤ : L) else (⊥ : L))
    by_cases hf't : f' = (⊤ : EndP L)
    · rw [if_pos hf't]; exact le_top
    · have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB _ f hwv
      have hfle : f ≤ f' := (leGlue_tagB_tagB_iff (OrderHom.id : EndP L) f f' hf't hfb).mp hle
      have hfne : f ≠ (⊤ : EndP L) := fun hfT => hf't (top_le_iff.mp (hfT ▸ hfle))
      rw [if_neg hfne, if_neg hf't]
  ·
    show (if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)) ≤ (⊤ : L)
    exact le_top
  ·
    exact absurd hle (not_leGlue_tagC_tagA (OrderHom.id : EndP L) f f'
      (ne_bot_of_canon_tagC (OrderHom.id : EndP L) f hwv))
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · show (⊤ : L) ≤ (if f' = (⊤ : EndP L) then (⊤ : L) else (⊥ : L))
      rw [if_pos hf't]
    · exact absurd hle (not_leGlue_tagC_tagB (OrderHom.id : EndP L) f f' hf't)
  ·
    show (⊤ : L) ≤ (⊤ : L)
    exact le_refl _

end EpPairProjection

-- [D-0517] pGen_top
theorem pGen_top {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]
    (hm : (OrderHom.id : EndP L) ≠ ⊥) (hmt : (OrderHom.id : EndP L) ≠ ⊤)
    (hbt : (⊥ : EndP L) ≠ (⊤ : EndP L)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) hm hmt hbt
    letI := glueOrderTop (OrderHom.id : EndP L) hm hmt hbt
    pGen (⊤ : GlueCar (P := EndP L) OrderHom.id) = (⊤ : L) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm hmt hbt
  letI := glueOrderTop (OrderHom.id : EndP L) hm hmt hbt
  have hval : (⊤ : GlueCar (P := EndP L) OrderHom.id).1
      = canon (OrderHom.id : EndP L) (Sum.inr (Sum.inr (⊤ : EndP L))) := rfl
  have hcanon : canon (OrderHom.id : EndP L) (Sum.inr (Sum.inr (⊤ : EndP L)))
      = Sum.inr (Sum.inr (⊤ : EndP L)) := by
    simp only [canon]
    split_ifs with h1 h2
    · exact absurd h1 hbt.symm
    · exact absurd h2 hmt.symm
    · rfl
  show pGen (⊤ : GlueCar (P := EndP L) OrderHom.id) = (⊤ : L)
  unfold pGen
  rw [hval, hcanon]

section DBilimitDcpo

-- [D-0518] directedOn_exists_greatest_of_finite
theorem directedOn_exists_greatest_of_finite {α : Type u} [Preorder α] {T : Set α}
    (hfin : T.Finite) (hne : T.Nonempty) (hdir : DirectedOn (· ≤ ·) T) :
    ∃ t ∈ T, ∀ s ∈ T, s ≤ t := by
  obtain ⟨t, ht⟩ := hfin.exists_maximal hne
  refine ⟨t, ht.1, fun s hs => ?_⟩
  obtain ⟨c, hc, hsc, htc⟩ := hdir s hs t ht.1
  exact hsc.trans (ht.2 hc htc)

-- [D-0519] monotone_sSup_image_of_finite_directed
theorem monotone_sSup_image_of_finite_directed {α β : Type u} [CompleteLattice α]
    [CompleteLattice β] {f : α → β} (hf : Monotone f) {T : Set α} (hfin : T.Finite)
    (hne : T.Nonempty) (hdir : DirectedOn (· ≤ ·) T) :
    f (sSup T) = sSup (f '' T) := by
  obtain ⟨t, htT, ht⟩ := directedOn_exists_greatest_of_finite hfin hne hdir
  have hsup : sSup T = t := le_antisymm (sSup_le ht) (le_sSup htT)
  rw [hsup]
  refine le_antisymm (le_sSup ⟨t, htT, rfl⟩) (sSup_le ?_)
  rintro _ ⟨s, hs, rfl⟩
  exact hf (ht s hs)

-- [D-0520] monotone_scottContinuous_of_finite
theorem monotone_scottContinuous_of_finite {α : Type u} [CompleteLattice α] [Finite α]
    {f : α → α} (hf : Monotone f) : ScottContinuous f := by
  intro S hSne hSdir a haLUB
  have haSup : a = sSup S := haLUB.unique (isLUB_sSup S)
  subst haSup
  rw [monotone_sSup_image_of_finite_directed hf (Set.toFinite S) hSne hSdir]
  exact isLUB_sSup _

-- [D-0521] monotone_scottContinuous_of_finite_dom
theorem monotone_scottContinuous_of_finite_dom {α : Type u} {β : Type v}
    [PartialOrder α] [Finite α] [Preorder β] {f : α → β} (hf : Monotone f) :
    ScottContinuous f := by
  intro S hSne hSdir a haLUB
  obtain ⟨t, htS, htmax⟩ := directedOn_exists_greatest_of_finite (Set.toFinite S) hSne hSdir
  have htLUB : IsLUB S t := ⟨fun s hs => htmax s hs, fun z hz => hz htS⟩
  have hat : a = t := haLUB.unique htLUB
  rw [hat]
  constructor
  · rintro _ ⟨s, hs, rfl⟩; exact hf (htmax s hs)
  · rintro z hz; exact hz ⟨t, htS, rfl⟩

end DBilimitDcpo

-- [D-0522] ScottEndP
def ScottEndP (α : Type*) [Preorder α] : Type _ := {F : α →o α // ScottContinuous (F : α → α)}

-- [D-0523] directedOn_image_of_monotone
theorem directedOn_image_of_monotone {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) {T : Set α} (hdir : DirectedOn (· ≤ ·) T) :
    DirectedOn (· ≤ ·) (f '' T) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
  exact ⟨f z, ⟨z, hz, rfl⟩, hf hxz, hf hyz⟩

section PhiConstructionGen

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-0524] GlueBaseGen
abbrev GlueBaseGen (P : Type u) := P ⊕ P ⊕ P

-- [D-0525] canonGen
def canonGen (m : P) : GlueBaseGen P → GlueBaseGen P
  | Sum.inl x => Sum.inl x
  | Sum.inr (Sum.inl x) => if x = ⊥ then Sum.inl m else Sum.inr (Sum.inl x)
  | Sum.inr (Sum.inr x) =>
      if x = ⊥ then Sum.inl ⊤
      else if x = m then Sum.inr (Sum.inl ⊤)
      else Sum.inr (Sum.inr x)

-- [D-0526] canonGen_idem
theorem canonGen_idem (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (x : GlueBaseGen P) :
    canonGen m (canonGen m x) = canonGen m x := by
  cases x with
  | inl x => rfl
  | inr x =>
    cases x with
    | inl x =>
      unfold canonGen
      by_cases hx : x = ⊥ <;> simp [hx, hm]
    | inr x =>
      unfold canonGen
      by_cases hx : x = ⊥
      · simp [hx]
      · by_cases hx' : x = m <;> simp [hx, hx', hm, hbt.symm]

-- [D-0527] GlueCarGen
def GlueCarGen (m : P) := {x : GlueBaseGen P // canonGen m x = x}

-- [D-0528] rawRuleGen
def rawRuleGen (m : P) : GlueBaseGen P → GlueBaseGen P → Prop
  | Sum.inl x, Sum.inl y => x ≤ y
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => x ≤ y
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => x ≤ y
  | Sum.inl x, Sum.inr (Sum.inl _) => x ≤ m
  | Sum.inl _, Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr y) => m ≤ y
  | Sum.inr (Sum.inl _), Sum.inl _ => False
  | Sum.inr (Sum.inr _), Sum.inl _ => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => False

-- [D-0529] occsGen
def occsGen (m : P) : GlueBaseGen P → List (GlueBaseGen P)
  | Sum.inl x =>
      if x = m then [Sum.inl x, Sum.inr (Sum.inl ⊥)]
      else if x = ⊤ then [Sum.inl x, Sum.inr (Sum.inr ⊥)]
      else [Sum.inl x]
  | Sum.inr (Sum.inl x) =>
      if x = ⊤ then [Sum.inr (Sum.inl x), Sum.inr (Sum.inr m)]
      else [Sum.inr (Sum.inl x)]
  | Sum.inr (Sum.inr x) => [Sum.inr (Sum.inr x)]

-- [D-0530] leGlueGen
def leGlueGen (m : P) (x y : GlueBaseGen P) : Prop :=
  ∃ u ∈ occsGen m x, ∃ v ∈ occsGen m y, rawRuleGen m u v

-- [D-0531] rawRuleGen_trans
theorem rawRuleGen_trans (m : P) {u v w : GlueBaseGen P} (huv : rawRuleGen m u v)
    (hvw : rawRuleGen m v w) : rawRuleGen m u w := by
  cases u with
  | inl x => cases v with
    | inl y => cases w with
      | inl z => exact le_trans huv hvw
      | inr z => cases z with
        | inl _ => exact le_trans huv hvw
        | inr _ => trivial
    | inr y => cases y with
      | inl _ => cases w with
        | inl _ => exact absurd hvw (by simp [rawRuleGen])
        | inr z => cases z with
          | inl _ => exact huv
          | inr _ => trivial
      | inr _ => cases w with
        | inl _ => exact absurd hvw (by simp [rawRuleGen])
        | inr z => cases z with
          | inl _ => exact absurd hvw (by simp [rawRuleGen])
          | inr _ => trivial
  | inr x => cases x with
    | inl x => cases v with
      | inl _ => exact absurd huv (by simp [rawRuleGen])
      | inr y => cases y with
        | inl y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRuleGen])
          | inr z => cases z with
            | inl _ => exact le_trans huv hvw
            | inr _ => exact hvw
        | inr y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRuleGen])
          | inr z => cases z with
            | inl _ => exact absurd hvw (by simp [rawRuleGen])
            | inr _ => exact le_trans huv hvw
    | inr x => cases v with
      | inl _ => exact absurd huv (by simp [rawRuleGen])
      | inr y => cases y with
        | inl _ => exact absurd huv (by simp [rawRuleGen])
        | inr y => cases w with
          | inl _ => exact absurd hvw (by simp [rawRuleGen])
          | inr z => cases z with
            | inl _ => exact absurd hvw (by simp [rawRuleGen])
            | inr _ => exact le_trans huv hvw

-- [D-0532] occsGen_canon_mem
theorem occsGen_canon_mem (m : P) (hm : m ≠ ⊥) {x : GlueBaseGen P} (hxc : canonGen m x = x) :
    ∀ u ∈ occsGen m x, canonGen m u = x := by
  cases x with
  | inl vx =>
    intro u hu
    simp only [occsGen] at hu
    split_ifs at hu <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
      (first | obtain rfl | rfl := hu | subst hu) <;> simp_all [canonGen]
  | inr vx => cases vx with
    | inl vx =>
      intro u hu
      simp only [occsGen] at hu
      split_ifs at hu <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu <;>
        (first | obtain rfl | rfl := hu | subst hu) <;> simp_all [canonGen]
    | inr vx =>
      intro u hu
      simp only [occsGen, List.mem_singleton] at hu
      subst hu; exact hxc

-- [D-0533] leGlueGen_refl
theorem leGlueGen_refl (m : P) (x : GlueBaseGen P) : leGlueGen m x x := by
  cases x with
  | inl x =>
    refine ⟨Sum.inl x, ?_, Sum.inl x, ?_, ?_⟩
    · simp only [occsGen]; split_ifs <;> simp
    · simp only [occsGen]; split_ifs <;> simp
    · show x ≤ x; exact le_refl x
  | inr x => cases x with
    | inl x =>
      refine ⟨Sum.inr (Sum.inl x), ?_, Sum.inr (Sum.inl x), ?_, ?_⟩
      · simp only [occsGen]; split_ifs <;> simp
      · simp only [occsGen]; split_ifs <;> simp
      · show x ≤ x; exact le_refl x
    | inr x =>
      refine ⟨Sum.inr (Sum.inr x), ?_, Sum.inr (Sum.inr x), ?_, ?_⟩
      · simp [occsGen]
      · simp [occsGen]
      · show x ≤ x; exact le_refl x

-- [D-0534] inst-P
instance (m : P) : LE (GlueCarGen (P := P) m) := ⟨fun x y => leGlueGen m x.1 y.1⟩

-- [D-0535] GlueCarGen.le_def
theorem GlueCarGen.le_def (m : P) (x y : GlueCarGen (P := P) m) :
    x ≤ y ↔ leGlueGen m x.1 y.1 := Iff.rfl

section GlueAntisymmGen
variable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
include hm hmt hbt

-- [D-0536] glueGen_antisymm
set_option maxHeartbeats 8000000 in
theorem glueGen_antisymm {x y : GlueBaseGen P} (hxc : canonGen m x = x) (hyc : canonGen m y = y)
    (hxy : leGlueGen m x y) (hyx : leGlueGen m y x) : x = y := by
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  obtain ⟨u', hu', v', hv', hvu⟩ := hyx
  rcases x with vx | vx | vx <;> rcases y with vy | vy | vy <;>
    simp only [occsGen, canonGen] at hxc hyc hu hv hu' hv' ⊢ <;>
    split_ifs at hxc hyc hu hv hu' hv' <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      at hu hv hu' hv' <;>
    (first | obtain rfl | rfl := hu | subst hu) <;>
    (first | obtain rfl | rfl := hv | subst hv) <;>
    (first | obtain rfl | rfl := hu' | subst hu') <;>
    (first | obtain rfl | rfl := hv' | subst hv') <;>
    (try simp_all [rawRuleGen]) <;>
    first
      | rfl
      | exact le_antisymm ‹_ ≤ _› ‹_ ≤ _›
      | exact absurd (le_antisymm huv hvu) (by assumption)
      | exact absurd (le_antisymm huv hvu).symm (by assumption)

-- [D-0537] glueGen_trans
set_option maxHeartbeats 8000000 in
theorem glueGen_trans {x y z : GlueBaseGen P} (hxc : canonGen m x = x) (hyc : canonGen m y = y)
    (hzc : canonGen m z = z) (hxy : leGlueGen m x y) (hyz : leGlueGen m y z) :
    leGlueGen m x z := by
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  obtain ⟨v', hv', w, hw, hvw⟩ := hyz
  have hux : canonGen m u = x := occsGen_canon_mem m hm hxc u hu
  have hwz : canonGen m w = z := occsGen_canon_mem m hm hzc w hw
  have hu_mem := hu
  have hw_mem := hw
  rcases x with vx | vx | vx <;> rcases y with vy | vy | vy <;> rcases z with vz | vz | vz <;>
    simp only [occsGen, canonGen] at hxc hyc hzc hu hv hv' hw hux hwz <;>
    (try split_ifs at hxc hyc hzc hu hv hv' hw hux hwz) <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      at hu hv hv' hw <;>
    (first | obtain rfl | rfl := hu | subst hu) <;>
    (first | obtain rfl | rfl := hv | subst hv) <;>
    (first | obtain rfl | rfl := hv' | subst hv') <;>
    (first | obtain rfl | rfl := hw | subst hw) <;>
    first
      | (refine ⟨_, ?_, _, ?_, rawRuleGen_trans m huv hvw⟩ <;> simp_all [occsGen] <;> done)
      | (refine ⟨_, ?_, _, ?_, rawRuleGen_trans m huv (rawRuleGen_trans m ?_ hvw)⟩
         · simp_all [occsGen]; done
         · simp_all [occsGen]; done
         · simp_all [rawRuleGen]; done)
      | (refine ⟨_, ?_, _, ?_, rawRuleGen_trans m (rawRuleGen_trans m huv ?_) hvw⟩
         · simp_all [occsGen]; done
         · simp_all [occsGen]; done
         · simp_all [rawRuleGen]; done)
      | (subst hux; refine ⟨_, ?_, _, ?_, hvw⟩ <;> simp_all [occsGen] <;> done)
      | (subst hwz; refine ⟨_, ?_, _, ?_, huv⟩ <;> simp_all [occsGen] <;> done)
      | (refine ⟨_, hu_mem, _, hw_mem, ?_⟩
         simp_all [rawRuleGen] <;> exact le_trans ‹_ ≤ _› ‹_ ≤ _›)
      | (unfold leGlueGen; simp_all [occsGen, rawRuleGen])
      | (subst_vars; exact leGlueGen_refl _ _)
      | fail "glueGen_trans: a transitivity case fell through. Do not let a fallback absorb it -- fix rawRuleGen/occsGen or add the case."

-- [D-0538] glueCarPartialOrderGen
@[reducible]
def glueCarPartialOrderGen : PartialOrder (GlueCarGen (P := P) m) where
  le x y := leGlueGen m x.1 y.1
  le_refl x := leGlueGen_refl m x.1
  le_trans x y z := glueGen_trans m hm hmt hbt x.2 y.2 z.2
  le_antisymm x y hxy hyx := Subtype.ext (glueGen_antisymm m hm hmt hbt x.2 y.2 hxy hyx)

end GlueAntisymmGen

end PhiConstructionGen

section CoherentLiftGen

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0539] hmL_of
theorem hmL_of (hbt : (⊥ : L) ≠ ⊤) : (OrderHom.id : EndP L) ≠ ⊥ := endPId_ne_bot hbt
-- [D-0540] hmtL_of
theorem hmtL_of (hbt : (⊥ : L) ≠ ⊤) : (OrderHom.id : EndP L) ≠ ⊤ := endPId_ne_top hbt
-- [D-0541] hbtEL_of
theorem hbtEL_of (hbt : (⊥ : L) ≠ ⊤) : (⊥ : EndP L) ≠ (⊤ : EndP L) := endP_bot_ne_top hbt

-- [D-0542] iotaGen
noncomputable def iotaGen (x : L) : GlueCar (P := EndP L) (OrderHom.id) :=
  glueA (OrderHom.id : EndP L) (constHom x)

-- [D-0543] iotaGen_le_iff
theorem iotaGen_le_iff (hbt : (⊥ : L) ≠ ⊤) (x y : L) : iotaGen x ≤ iotaGen y ↔ x ≤ y :=
  (glueA_le_iff (OrderHom.id : EndP L) (hmL_of hbt) (constHom x) (constHom y)).trans
    (constHom_le_iff x y)

-- [D-0544] iotaGen_injective
theorem iotaGen_injective : Function.Injective (@iotaGen L _ _ _ _) := by
  intro x y h
  exact constHom_injective (glueA_injective (OrderHom.id : EndP L) h)

-- [D-0545] iotaGen_monotone
theorem iotaGen_monotone (hbt : (⊥ : L) ≠ ⊤) {x y : L} (hxy : x ≤ y) : iotaGen x ≤ iotaGen y :=
  (iotaGen_le_iff hbt x y).mpr hxy

-- [D-0546] iotaEndPGen
noncomputable def iotaEndPGen (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    EndP (GlueCar (P := EndP L) (OrderHom.id : EndP L)) :=
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  { toFun := fun w => iotaGen (f (pGen (L := L) w))
    monotone' := fun w w' hle =>
      iotaGen_monotone hbt (f.monotone (pGen_monotone (hmL_of hbt) (hbtEL_of hbt) w w' hle)) }

-- [D-0547] iotaEndPGen_apply
theorem iotaEndPGen_apply (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    ∀ w : GlueCar (P := EndP L) (OrderHom.id),
      (iotaEndPGen hbt f : GlueCar (P := EndP L) (OrderHom.id) → GlueCar (P := EndP L) (OrderHom.id)) w
        = iotaGen (f (pGen (L := L) w)) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  intro w
  rfl

end CoherentLiftGen

section CoherentLiftGenJoin

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0548] iotaEndPGen_monotone
theorem iotaEndPGen_monotone (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} (hfg : f ≤ g) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaEndPGen hbt f ≤ iotaEndPGen hbt g := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  rw [OrderHom.le_def]
  intro w
  show iotaGen (f (pGen w)) ≤ iotaGen (g (pGen w))
  exact iotaGen_monotone hbt (OrderHom.le_def.mp hfg (pGen w))

-- [D-0549] ite_dominate_mono
theorem ite_dominate_mono {Q : Type*} [Preorder Q] [OrderBot Q]
    {t f g : EndP L} (hfg : f ≤ g) (v : Q) :
    (if t ≤ f then v else (⊥ : Q)) ≤ (if t ≤ g then v else (⊥ : Q)) := by
  by_cases h : t ≤ f
  · rw [if_pos h, if_pos (h.trans hfg)]
  · rw [if_neg h]
    exact bot_le

-- [D-0550] liftGen
noncomputable def liftGen (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    EndP (GlueCar (P := EndP L) (OrderHom.id : EndP L)) :=
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  iotaEndPGen hbt f
    ⊔ (if (OrderHom.id : EndP L) ≤ f
        then (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id : EndP L)))
        else ⊥)
    ⊔ (if (⊤ : EndP L) ≤ f
        then (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id : EndP L)))
        else ⊥)

-- [D-0551] liftGen_monotone
theorem liftGen_monotone (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} (hfg : f ≤ g) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    liftGen hbt f ≤ liftGen hbt g := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  unfold liftGen
  exact sup_le_sup (sup_le_sup (iotaEndPGen_monotone hbt hfg) (ite_dominate_mono hfg _))
    (ite_dominate_mono hfg _)

end CoherentLiftGenJoin

section CoherentLiftGenBoundary

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0552] constHom_bot_eq
theorem constHom_bot_eq : (constHom (⊥ : L) : EndP L) = ⊥ := by
  ext x; simp [constHom_apply, endPBot_apply]

-- [D-0553] iotaGen_pGen_deflation
theorem iotaGen_pGen_deflation (hbt : (⊥ : L) ≠ ⊤)
    (w : GlueCar (P := EndP L) (OrderHom.id)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaGen (pGen w) ≤ w := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  show leGlue (OrderHom.id : EndP L) (iotaGen (pGen w)).1 w.1
  show leGlue (OrderHom.id : EndP L) (Sum.inl (constHom (pGen w) : EndP L)) w.1
  exact pGen_deflation w

-- [D-0554] iotaGen_bot
theorem iotaGen_bot (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaGen (⊥ : L) = ⊥ := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  show glueA (OrderHom.id : EndP L) (constHom (⊥ : L)) = ⊥
  rw [constHom_bot_eq]
  rfl

-- [D-0555] liftGen_bot
theorem liftGen_bot (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    liftGen hbt (⊥ : EndP L) = ⊥ := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  unfold liftGen
  have h1 : ¬ (OrderHom.id : EndP L) ≤ (⊥ : EndP L) := fun h => (hmL_of hbt) (le_bot_iff.mp h)
  have h2 : ¬ (⊤ : EndP L) ≤ (⊥ : EndP L) := fun h => (hbtEL_of hbt) (le_bot_iff.mp h).symm
  have hA : iotaEndPGen hbt (⊥ : EndP L) = ⊥ := by
    ext w
    show iotaGen ((⊥ : EndP L) (pGen w))
      = (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) w
    rw [endPBot_apply]
    exact iotaGen_bot hbt
  rw [if_neg h1, if_neg h2, hA]
  exact le_antisymm (sup_le (sup_le le_rfl le_rfl) le_rfl) bot_le

-- [D-0556] liftGen_id
theorem liftGen_id (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    liftGen hbt (OrderHom.id : EndP L) = (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  unfold liftGen
  have h1 : (OrderHom.id : EndP L) ≤ (OrderHom.id : EndP L) := le_refl _
  have h2 : ¬ (⊤ : EndP L) ≤ (OrderHom.id : EndP L) := fun h => (hmtL_of hbt) (top_le_iff.mp h)
  have hdefl : iotaEndPGen hbt (OrderHom.id : EndP L)
      ≤ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
    rw [OrderHom.le_def]
    intro w
    show iotaGen ((OrderHom.id : EndP L) (pGen w)) ≤ w
    rw [endPId_apply]
    exact iotaGen_pGen_deflation hbt w
  rw [if_pos h1, if_neg h2]
  exact le_antisymm (sup_le (sup_le hdefl le_rfl) bot_le) (le_trans le_sup_right le_sup_left)

-- [D-0557] liftGen_top
theorem liftGen_top (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    liftGen hbt (⊤ : EndP L) = (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  unfold liftGen
  have h2 : (⊤ : EndP L) ≤ (⊤ : EndP L) := le_refl _
  rw [if_pos h2]
  exact le_antisymm le_top le_sup_right

end CoherentLiftGenBoundary

section GlueAAGen

-- [D-0558] rawRule_leGlue_canon
theorem rawRule_leGlue_canon {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    [Fintype P] (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) (w1 w2 : GlueBase P)
    (h : rawRule m w1 w2) : leGlue m (canon m w1) (canon m w2) :=
  ⟨w1, mem_occs_canon m hm hmt hbt w1, w2, mem_occs_canon m hm hmt hbt w2, h⟩

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0559] glueAAGen
noncomputable def glueAAGen (hbt : (⊥ : L) ≠ ⊤) (x : GlueCar (P := EndP L) (OrderHom.id)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    GlueCar (P := EndP (GlueCar (P := EndP L) (OrderHom.id))) (OrderHom.id) :=
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  match x.1 with
  | Sum.inl f => ⟨Sum.inl (iotaEndPGen hbt f), rfl⟩
  | Sum.inr (Sum.inl f) =>
      incl (OrderHom.id) (hmL_of hbt') (hbtEL_of hbt') (Sum.inr (Sum.inl (liftGen hbt f)))
  | Sum.inr (Sum.inr f) =>
      incl (OrderHom.id) (hmL_of hbt') (hbtEL_of hbt') (Sum.inr (Sum.inr (liftGen hbt f)))

-- [D-0560] glueAAGen_monotone
set_option maxHeartbeats 4000000 in
theorem glueAAGen_monotone (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (OrderHom.id)}
    (hxy : x ≤ y) : glueAAGen hbt x ≤ glueAAGen hbt y := by
  have hm0 : (OrderHom.id : EndP L) ≠ ⊥ := hmL_of hbt
  have hmt0 : (OrderHom.id : EndP L) ≠ ⊤ := hmtL_of hbt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm' : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ ⊥ := hmL_of hbt'
  have hmt' : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ ⊤ := hmtL_of hbt'
  have hbtE' : (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) := hbtEL_of hbt'
  obtain ⟨xv, hxv⟩ := x
  obtain ⟨yv, hyv⟩ := y
  have hxy' : leGlue (OrderHom.id : EndP L) xv yv := hxy
  rw [GlueCar.le_def]
  show leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
    (glueAAGen hbt (⟨xv, hxv⟩ : GlueCar (P := EndP L) (OrderHom.id))).1
    (glueAAGen hbt (⟨yv, hyv⟩ : GlueCar (P := EndP L) (OrderHom.id))).1
  rcases xv with f | f | f <;> rcases yv with f' | f' | f'
  ·
    show leGlue _ (Sum.inl (iotaEndPGen hbt f)) (Sum.inl (iotaEndPGen hbt f'))
    have hff' : f ≤ f' := (tagA_iso (OrderHom.id : EndP L) hm0 f f').mp hxy'
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inl (iotaEndPGen hbt f)) (Sum.inl (iotaEndPGen hbt f')) (iotaEndPGen_monotone hbt hff')
  ·
    show leGlue _ (Sum.inl (iotaEndPGen hbt f)) (canon _ (Sum.inr (Sum.inl (liftGen hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id)))) := by
        simp only [canon]
        rw [if_neg (Ne.symm hbtE')]
      rw [liftGen_top, hcanonB]
      exact leGlue_tagA_tagB_top _ _
    · have hfm : f ≤ (OrderHom.id : EndP L) :=
        (leGlue_tagA_tagB_iff (OrderHom.id : EndP L) f f' hft).mp hxy'
      have hle : iotaEndPGen hbt f ≤ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
        refine le_trans (iotaEndPGen_monotone hbt hfm) ?_
        rw [OrderHom.le_def]
        intro w
        rw [iotaEndPGen_apply]
        exact iotaGen_pGen_deflation hbt w
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inl (iotaEndPGen hbt f)) (Sum.inr (Sum.inl (liftGen hbt f'))) hle
  ·
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inl (iotaEndPGen hbt f)) (Sum.inr (Sum.inr (liftGen hbt f'))) trivial
  ·
    exact absurd hxy' (not_leGlue_tagB_tagA (OrderHom.id : EndP L) f f' hm0 hbt0
      (ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv))
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inl (liftGen hbt f)))) (canon _ (Sum.inr (Sum.inl (liftGen hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      have hle : liftGen hbt f ≤ liftGen hbt (⊤ : EndP L) := by rw [liftGen_top]; exact le_top
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inr (Sum.inl (liftGen hbt (⊤ : EndP L)))) hle
    · have hwb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv
      have hff' : f ≤ f' := (leGlue_tagB_tagB_iff (OrderHom.id : EndP L) f f' hft hwb).mp hxy'
      exact rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inr (Sum.inl (liftGen hbt f'))) (liftGen_monotone hbt hff')
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inl (liftGen hbt f)))) (canon _ (Sum.inr (Sum.inr (liftGen hbt f'))))
    have hmf' : (OrderHom.id : EndP L) ≤ f' := (leGlue_tagB_tagC_iff (OrderHom.id : EndP L) f f').mp hxy'
    have hle : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≤ liftGen hbt f' := by
      unfold liftGen
      rw [if_pos hmf']
      exact le_trans le_sup_right le_sup_left
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inr (Sum.inr (liftGen hbt f'))) hle
  ·
    exact absurd hxy' (not_leGlue_tagC_tagA (OrderHom.id : EndP L) f f'
      (ne_bot_of_canon_tagC (OrderHom.id : EndP L) f hxv))
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inr (liftGen hbt f)))) (canon _ (Sum.inr (Sum.inl (liftGen hbt f'))))
    by_cases hft : f' = (⊤ : EndP L)
    · subst hft
      rw [liftGen_top]
      have hfm : f ≤ (OrderHom.id : EndP L) :=
        (leGlue_tagC_tagB_top_iff (OrderHom.id : EndP L) f).mp hxy'
      have hle : liftGen hbt f ≤ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
        rw [← liftGen_id hbt]
        exact liftGen_monotone hbt hfm
      have e1 : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id)))) := by
        show (if (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) = ⊥
            then Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id)))
            else if (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
                = (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
              then Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))
              else Sum.inr (Sum.inr (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))))
            = Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))
        rw [if_neg hm', if_pos rfl]
      have e2 : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))) =
          Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id)))) := by
        show (if (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) = ⊥
            then Sum.inl (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
            else Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id)))))
            = Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))
        rw [if_neg (Ne.symm hbtE')]
      have hcanon : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))))) =
          canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))))) := by
        rw [e1, e2]
      have hb := rawRule_leGlue_canon _ hm' hmt' hbtE'
        (Sum.inr (Sum.inr (liftGen hbt f)))
        (Sum.inr (Sum.inr (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))))) hle
      rwa [hcanon] at hb
    · exact absurd hxy' (not_leGlue_tagC_tagB (OrderHom.id : EndP L) f f' hft)
  ·
    show leGlue _ (canon _ (Sum.inr (Sum.inr (liftGen hbt f)))) (canon _ (Sum.inr (Sum.inr (liftGen hbt f'))))
    have hff' : f ≤ f' := (leGlue_tagC_tagC_iff (OrderHom.id : EndP L) f f').mp hxy'
    exact rawRule_leGlue_canon _ hm' hmt' hbtE'
      (Sum.inr (Sum.inr (liftGen hbt f))) (Sum.inr (Sum.inr (liftGen hbt f'))) (liftGen_monotone hbt hff')

end GlueAAGen

section GlueAAGenReflect

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0561] iotaEndPGen_le_iff
theorem iotaEndPGen_le_iff (hbt : (⊥ : L) ≠ ⊤) {f g : EndP L} :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (iotaEndPGen hbt f ≤ iotaEndPGen hbt g ↔ f ≤ g) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  constructor
  · intro h
    rw [OrderHom.le_def]
    intro x
    have hw := OrderHom.le_def.mp h (iotaGen x)
    rw [iotaEndPGen_apply, iotaEndPGen_apply] at hw
    have hpx : pGen (iotaGen x) = x := pGen_section x
    rw [hpx] at hw
    exact (iotaGen_le_iff hbt _ _).mp hw
  · exact iotaEndPGen_monotone hbt

-- [D-0562] iotaEndPGen_bot
theorem iotaEndPGen_bot (hbt : (⊥ : L) ≠ ⊤) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaEndPGen hbt (⊥ : EndP L) = ⊥ := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  ext w
  show iotaGen ((⊥ : EndP L) (pGen w)) = (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) w
  rw [endPBot_apply]
  exact iotaGen_bot hbt

-- [D-0563] iotaGen_ne_top
theorem iotaGen_ne_top (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaGen x ≠ (⊤ : GlueCar (P := EndP L) (OrderHom.id)) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  intro h
  have hv := congrArg Subtype.val h
  have h1 : (iotaGen x : GlueCar (P := EndP L) (OrderHom.id)).1 = Sum.inl (constHom x : EndP L) := rfl
  have h2 : (⊤ : GlueCar (P := EndP L) (OrderHom.id)).1 = Sum.inr (Sum.inr (⊤ : EndP L)) := by
    show canon (OrderHom.id : EndP L) (Sum.inr (Sum.inr (⊤ : EndP L))) = Sum.inr (Sum.inr (⊤ : EndP L))
    simp only [canon]
    rw [if_neg (hbtEL_of hbt).symm, if_neg (hmtL_of hbt).symm]
  rw [h1, h2] at hv
  exact absurd hv (by simp)

-- [D-0564] liftGen_apply
theorem liftGen_apply (hbt : (⊥ : L) ≠ ⊤) (f : EndP L)
    (w : GlueCar (P := EndP L) (OrderHom.id)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (liftGen hbt f) w
      = iotaGen (f (pGen w))
          ⊔ (if (OrderHom.id : EndP L) ≤ f then w else ⊥)
          ⊔ (if (⊤ : EndP L) ≤ f then (⊤ : GlueCar (P := EndP L) (OrderHom.id)) else ⊥) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  unfold liftGen
  simp only [OrderHom.coe_sup, Pi.sup_apply, iotaEndPGen_apply]
  congr 2
  · split_ifs with h1
    · exact endPId_apply w
    · exact endPBot_apply w
  · split_ifs with h2
    · exact endPTop_apply w
    · exact endPBot_apply w

-- [D-0565] liftGen_eq_bot_iff
theorem liftGen_eq_bot_iff (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (liftGen hbt f = ⊥ ↔ f = ⊥) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  constructor
  · intro h
    unfold liftGen at h
    have hh := sup_eq_bot_iff.mp h
    have hh2 := sup_eq_bot_iff.mp hh.1
    have h1 : iotaEndPGen hbt f = ⊥ := hh2.1
    have h2 : iotaEndPGen hbt f = iotaEndPGen hbt (⊥ : EndP L) := h1.trans (iotaEndPGen_bot hbt).symm
    have h3 : iotaEndPGen hbt f ≤ iotaEndPGen hbt (⊥ : EndP L) := le_of_eq h2
    have h4 : f ≤ (⊥ : EndP L) := (iotaEndPGen_le_iff hbt).mp h3
    exact le_bot_iff.mp h4
  · intro h; subst h; exact liftGen_bot hbt

-- [D-0566] liftGen_eq_id_iff
theorem liftGen_eq_id_iff (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (liftGen hbt f = (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ↔ f = (OrderHom.id : EndP L)) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  constructor
  · intro h
    have hfnt : f ≠ (⊤ : EndP L) := by
      intro hfe; subst hfe
      rw [liftGen_top] at h
      exact (hmtL_of hbt') h.symm
    have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hfnt (top_le_iff.mp hc)
    have key : ∀ z : L,
        iotaGen (f z) ⊔ (if (OrderHom.id : EndP L) ≤ f then iotaGen z else ⊥)
          ⊔ (if (⊤ : EndP L) ≤ f then (⊤ : GlueCar (P := EndP L) (OrderHom.id)) else ⊥)
          = iotaGen z := by
      intro z
      have e1 := liftGen_apply hbt f (iotaGen z)
      rw [h] at e1
      have hpx : pGen (iotaGen z) = z := pGen_section z
      rw [hpx] at e1
      have hidz : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) (iotaGen z) = iotaGen z := rfl
      rw [hidz] at e1
      exact e1.symm
    have hle : f ≤ (OrderHom.id : EndP L) := by
      rw [OrderHom.le_def]
      intro z
      have hk := key z
      have hzz : iotaGen (f z) ≤ iotaGen z := by
        rw [← hk]; exact le_trans le_sup_left le_sup_left
      exact (iotaGen_le_iff hbt _ _).mp hzz
    by_cases hmf : (OrderHom.id : EndP L) ≤ f
    · exact le_antisymm hle hmf
    · exfalso
      have hcon : ∀ z : L, iotaGen (f z) = iotaGen z := by
        intro z
        have hk := key z
        simp only [if_neg hmf, if_neg hnle, sup_bot_eq] at hk
        exact hk
      have hfeq : f = (OrderHom.id : EndP L) := by
        ext z; exact iotaGen_injective (hcon z)
      exact hmf (hfeq ▸ le_refl _)
  · intro h; subst h; exact liftGen_id hbt

-- [D-0567] liftGen_eq_top_iff
theorem liftGen_eq_top_iff (hbt : (⊥ : L) ≠ ⊤) {f : EndP L} :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (liftGen hbt f = ⊤ ↔ f = ⊤) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  constructor
  · intro h
    by_contra hne
    have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hne (top_le_iff.mp hc)
    have e1 := liftGen_apply hbt f (iotaGen (⊥ : L))
    rw [h] at e1
    have hpx : pGen (iotaGen (⊥ : L)) = (⊥ : L) := pGen_section (⊥ : L)
    rw [hpx, if_neg hnle, endPTop_apply] at e1
    by_cases hmf : (OrderHom.id : EndP L) ≤ f
    · rw [if_pos hmf, sup_bot_eq] at e1
      have hzz : (⊥ : L) ≤ f (⊥ : L) := by
        have := OrderHom.le_def.mp hmf (⊥ : L)
        simpa [endPId_apply] using this
      have hle2 : iotaGen (⊥ : L) ≤ iotaGen (f (⊥ : L)) := iotaGen_monotone hbt hzz
      have habs : iotaGen (f (⊥ : L)) ⊔ iotaGen (⊥ : L) = iotaGen (f (⊥ : L)) := sup_eq_left.mpr hle2
      rw [habs] at e1
      exact iotaGen_ne_top hbt _ e1.symm
    · rw [if_neg hmf, sup_bot_eq, sup_bot_eq] at e1
      exact iotaGen_ne_top hbt _ e1.symm
  · intro h; subst h; exact liftGen_top hbt

-- [D-0568] liftGen_apply_iotaGen_of_not_top
theorem liftGen_apply_iotaGen_of_not_top (hbt : (⊥ : L) ≠ ⊤) {g : EndP L}
    (hg : ¬ (⊤ : EndP L) ≤ g) (z : L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    (liftGen hbt g) (iotaGen z) = iotaGen (g z) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  have e1 := liftGen_apply hbt g (iotaGen z)
  have hpx : pGen (iotaGen z) = z := pGen_section z
  rw [hpx, if_neg hg] at e1
  by_cases hmg : (OrderHom.id : EndP L) ≤ g
  · rw [if_pos hmg, sup_bot_eq] at e1
    have hzz : z ≤ g z := by
      have := OrderHom.le_def.mp hmg z
      simpa [endPId_apply] using this
    have hle : iotaGen z ≤ iotaGen (g z) := iotaGen_monotone hbt hzz
    rw [sup_eq_left.mpr hle] at e1
    exact e1
  · rw [if_neg hmg, sup_bot_eq, sup_bot_eq] at e1
    exact e1

-- [D-0569] glueAAGen_reflect
set_option maxHeartbeats 4000000 in
theorem glueAAGen_reflect (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (OrderHom.id)}
    (hxy : glueAAGen hbt x ≤ glueAAGen hbt y) : x ≤ y := by
  have hm0 : (OrderHom.id : EndP L) ≠ ⊥ := hmL_of hbt
  have hmt0 : (OrderHom.id : EndP L) ≠ ⊤ := hmtL_of hbt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm' : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ ⊥ := hmL_of hbt'
  have hmt' : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ ⊤ := hmtL_of hbt'
  have hbtE' : (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) := hbtEL_of hbt'
  obtain ⟨xv, hxv⟩ := x
  obtain ⟨yv, hyv⟩ := y
  rw [GlueCar.le_def] at hxy
  rw [GlueCar.le_def]
  show leGlue (OrderHom.id : EndP L) xv yv
  rcases xv with f | f | f <;> rcases yv with f' | f' | f'
  ·
    have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inl (iotaEndPGen hbt f)) (Sum.inl (iotaEndPGen hbt f')) := hxy
    have hff' : iotaEndPGen hbt f ≤ iotaEndPGen hbt f' := (tagA_iso _ hm' _ _).mp hxy2
    exact (tagA_iso (OrderHom.id : EndP L) hm0 f f').mpr ((iotaEndPGen_le_iff hbt).mp hff')
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't; exact leGlue_tagA_tagB_top _ _
    · have hΛnb : liftGen hbt f' ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => (ne_bot_of_canon_tagB (OrderHom.id : EndP L) f' hyv) ((liftGen_eq_bot_iff hbt).mp hc)
      have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt f'))) = Sum.inr (Sum.inl (liftGen hbt f')) := by
        simp only [canon]; rw [if_neg hΛnb]
      have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inl (iotaEndPGen hbt f)) (Sum.inr (Sum.inl (liftGen hbt f'))) := by
        rw [← hcanonB]; exact hxy
      have hΛnt : liftGen hbt f' ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf't ((liftGen_eq_top_iff hbt).mp hc)
      have hle : iotaEndPGen hbt f ≤ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        (leGlue_tagA_tagB_iff (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (iotaEndPGen hbt f) (liftGen hbt f') hΛnt).mp hxy2
      have hfm : f ≤ (OrderHom.id : EndP L) := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hle (iotaGen z)
        rw [iotaEndPGen_apply] at hz
        have hpx : pGen (iotaGen z) = z := pGen_section z
        rw [hpx] at hz
        have hidz : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) (iotaGen z) = iotaGen z := rfl
        rw [hidz] at hz
        exact (iotaGen_le_iff hbt _ _).mp hz
      exact (leGlue_tagA_tagB_iff (OrderHom.id : EndP L) f f' hf't).mpr hfm
  ·
    exact tagA_le_tagC (OrderHom.id : EndP L) f f'
  ·
    exfalso
    have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv
    have hΛnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
    have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inl (liftGen hbt f))) = Sum.inr (Sum.inl (liftGen hbt f)) := by
      simp only [canon]; rw [if_neg hΛnb]
    have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inl (iotaEndPGen hbt f')) := by
      rw [← hcanonB]; exact hxy
    exact not_leGlue_tagB_tagA (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
      (liftGen hbt f) (iotaEndPGen hbt f') hm' hbtE' hΛnb hxy2
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      exact ⟨Sum.inr (Sum.inl f), self_mem_occs _ _, Sum.inr (Sum.inl (⊤ : EndP L)), self_mem_occs _ _, le_top⟩
    · have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv
      have hf'b : f' ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f' hyv
      have hΛnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
      have hΛ'nb : liftGen hbt f' ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf'b ((liftGen_eq_bot_iff hbt).mp hc)
      have hΛ'nt : liftGen hbt f' ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf't ((liftGen_eq_top_iff hbt).mp hc)
      have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt f))) = Sum.inr (Sum.inl (liftGen hbt f)) := by
        simp only [canon]; rw [if_neg hΛnb]
      have hcanonB' : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt f'))) = Sum.inr (Sum.inl (liftGen hbt f')) := by
        simp only [canon]; rw [if_neg hΛ'nb]
      have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inr (Sum.inl (liftGen hbt f'))) := by
        rw [← hcanonB, ← hcanonB']; exact hxy
      have hΛle : liftGen hbt f ≤ liftGen hbt f' :=
        (leGlue_tagB_tagB_iff (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (liftGen hbt f) (liftGen hbt f') hΛ'nt hΛnb).mp hxy2
      have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : f ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hΛle (iotaGen z)
        have heq : (liftGen hbt f') (iotaGen z) = iotaGen (f' z) :=
          liftGen_apply_iotaGen_of_not_top hbt hnle z
        rw [heq] at hz
        have hlb : iotaGen (f z) ≤ (liftGen hbt f) (iotaGen z) := by
          have e1 := liftGen_apply hbt f (iotaGen z)
          have hpx : pGen (iotaGen z) = z := pGen_section z
          rw [hpx] at e1
          rw [e1]
          exact le_trans le_sup_left le_sup_left
        exact (iotaGen_le_iff hbt _ _).mp (le_trans hlb hz)
      exact (leGlue_tagB_tagB_iff (OrderHom.id : EndP L) f f' hf't hfb).mpr hfin
  ·
    have hf''b : f' ≠ (⊥ : EndP L) := (canon_inr_inr_ne (OrderHom.id : EndP L) f' hyv).1
    have hf''m : f' ≠ (OrderHom.id : EndP L) := (canon_inr_inr_ne (OrderHom.id : EndP L) f' hyv).2
    have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv
    have hΛfnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
    have hΛf'nb : liftGen hbt f' ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hf''b ((liftGen_eq_bot_iff hbt).mp hc)
    have hΛf'nm : liftGen hbt f' ≠ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hf''m ((liftGen_eq_id_iff hbt).mp hc)
    have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inl (liftGen hbt f))) = Sum.inr (Sum.inl (liftGen hbt f)) := by
      simp only [canon]; rw [if_neg hΛfnb]
    have hcanonC : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inr (liftGen hbt f'))) = Sum.inr (Sum.inr (liftGen hbt f')) := by
      simp only [canon]; rw [if_neg hΛf'nb, if_neg hΛf'nm]
    have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inl (liftGen hbt f))) (Sum.inr (Sum.inr (liftGen hbt f'))) := by
      rw [← hcanonB, ← hcanonC]; exact hxy
    have hmΛ : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≤ liftGen hbt f' :=
      (leGlue_tagB_tagC_iff (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (liftGen hbt f) (liftGen hbt f')).mp hxy2
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't; exact (leGlue_tagB_tagC_iff (OrderHom.id : EndP L) f (⊤ : EndP L)).mpr le_top
    · have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : (OrderHom.id : EndP L) ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hmΛ (iotaGen z)
        have heq : (liftGen hbt f') (iotaGen z) = iotaGen (f' z) :=
          liftGen_apply_iotaGen_of_not_top hbt hnle z
        rw [heq] at hz
        have hidz : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) (iotaGen z) = iotaGen z := rfl
        rw [hidz] at hz
        exact (iotaGen_le_iff hbt _ _).mp hz
      exact (leGlue_tagB_tagC_iff (OrderHom.id : EndP L) f f').mpr hfin
  ·
    exfalso
    have hfb := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).1
    have hfm := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).2
    have hΛfnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
    have hΛfnm : liftGen hbt f ≠ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfm ((liftGen_eq_id_iff hbt).mp hc)
    have hcanonC : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inr (liftGen hbt f))) = Sum.inr (Sum.inr (liftGen hbt f)) := by
      simp only [canon]; rw [if_neg hΛfnb, if_neg hΛfnm]
    have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inr (liftGen hbt f))) (Sum.inl (iotaEndPGen hbt f')) := by
      rw [← hcanonC]; exact hxy
    exact not_leGlue_tagC_tagA (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
      (liftGen hbt f) (iotaEndPGen hbt f') hΛfnb hxy2
  ·
    have hfb := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).1
    have hfm := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).2
    have hΛfnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
    have hΛfnm : liftGen hbt f ≠ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
      fun hc => hfm ((liftGen_eq_id_iff hbt).mp hc)
    have hcanonC : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inr (liftGen hbt f))) = Sum.inr (Sum.inr (liftGen hbt f)) := by
      simp only [canon]; rw [if_neg hΛfnb, if_neg hΛfnm]
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't
      have hΛtop_ne_bot : liftGen hbt (⊤ : EndP L) ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) := by
        rw [liftGen_top]; exact Ne.symm hbtE'
      have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt (⊤ : EndP L)))) = Sum.inr (Sum.inl (liftGen hbt (⊤ : EndP L))) := by
        simp only [canon]
        rw [if_neg hΛtop_ne_bot]
      have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (liftGen hbt f))) (Sum.inr (Sum.inl (liftGen hbt (⊤ : EndP L)))) := by
        rw [← hcanonC, ← hcanonB]; exact hxy
      rw [liftGen_top] at hxy2
      have hle : liftGen hbt f ≤ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        (leGlue_tagC_tagB_top_iff (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (liftGen hbt f)).mp hxy2
      by_cases hft : f = (⊤ : EndP L)
      · exfalso
        subst hft
        rw [liftGen_top] at hle
        exact hmt' (le_antisymm le_top hle)
      · have hnle : ¬ (⊤ : EndP L) ≤ f := fun hc => hft (top_le_iff.mp hc)
        have hfin : f ≤ (OrderHom.id : EndP L) := by
          rw [OrderHom.le_def]
          intro z
          have hz := OrderHom.le_def.mp hle (iotaGen z)
          have heq : (liftGen hbt f) (iotaGen z) = iotaGen (f z) :=
            liftGen_apply_iotaGen_of_not_top hbt hnle z
          rw [heq] at hz
          have hidz : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) (iotaGen z) = iotaGen z := rfl
          rw [hidz] at hz
          exact (iotaGen_le_iff hbt _ _).mp hz
        exact (leGlue_tagC_tagB_top_iff (OrderHom.id : EndP L) f).mpr hfin
    · exfalso
      have hf'b : f' ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f' hyv
      have hΛ'nb : liftGen hbt f' ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf'b ((liftGen_eq_bot_iff hbt).mp hc)
      have hΛ'nt : liftGen hbt f' ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf't ((liftGen_eq_top_iff hbt).mp hc)
      have hcanonB : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inl (liftGen hbt f'))) = Sum.inr (Sum.inl (liftGen hbt f')) := by
        simp only [canon]; rw [if_neg hΛ'nb]
      have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (liftGen hbt f))) (Sum.inr (Sum.inl (liftGen hbt f'))) := by
        rw [← hcanonC, ← hcanonB]; exact hxy
      exact not_leGlue_tagC_tagB (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (liftGen hbt f) (liftGen hbt f') hΛ'nt hxy2
  ·
    by_cases hf't : f' = (⊤ : EndP L)
    · subst hf't; exact (leGlue_tagC_tagC_iff (OrderHom.id : EndP L) f (⊤ : EndP L)).mpr le_top
    · have hfb := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).1
      have hfm := (canon_inr_inr_ne (OrderHom.id : EndP L) f hxv).2
      have hf'b := (canon_inr_inr_ne (OrderHom.id : EndP L) f' hyv).1
      have hf'm := (canon_inr_inr_ne (OrderHom.id : EndP L) f' hyv).2
      have hΛfnb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
      have hΛfnm : liftGen hbt f ≠ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hfm ((liftGen_eq_id_iff hbt).mp hc)
      have hΛ'nb : liftGen hbt f' ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf'b ((liftGen_eq_bot_iff hbt).mp hc)
      have hΛ'nm : liftGen hbt f' ≠ (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
        fun hc => hf'm ((liftGen_eq_id_iff hbt).mp hc)
      have hcanonCf : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (liftGen hbt f))) = Sum.inr (Sum.inr (liftGen hbt f)) := by
        simp only [canon]; rw [if_neg hΛfnb, if_neg hΛfnm]
      have hcanonCf' : canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (liftGen hbt f'))) = Sum.inr (Sum.inr (liftGen hbt f')) := by
        simp only [canon]; rw [if_neg hΛ'nb, if_neg hΛ'nm]
      have hxy2 : leGlue (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
          (Sum.inr (Sum.inr (liftGen hbt f))) (Sum.inr (Sum.inr (liftGen hbt f'))) := by
        rw [← hcanonCf, ← hcanonCf']; exact hxy
      have hΛle : liftGen hbt f ≤ liftGen hbt f' := (leGlue_tagC_tagC_iff _ _ _).mp hxy2
      have hnle : ¬ (⊤ : EndP L) ≤ f' := fun hc => hf't (top_le_iff.mp hc)
      have hfin : f ≤ f' := by
        rw [OrderHom.le_def]
        intro z
        have hz := OrderHom.le_def.mp hΛle (iotaGen z)
        have heq : (liftGen hbt f') (iotaGen z) = iotaGen (f' z) :=
          liftGen_apply_iotaGen_of_not_top hbt hnle z
        rw [heq] at hz
        have hlb : iotaGen (f z) ≤ (liftGen hbt f) (iotaGen z) := by
          have e1 := liftGen_apply hbt f (iotaGen z)
          have hpx : pGen (iotaGen z) = z := pGen_section z
          rw [hpx] at e1
          rw [e1]
          exact le_trans le_sup_left le_sup_left
        exact (iotaGen_le_iff hbt _ _).mp (le_trans hlb hz)
      exact (leGlue_tagC_tagC_iff (OrderHom.id : EndP L) f f').mpr hfin

-- [D-0570] glueAAGen_le_iff
theorem glueAAGen_le_iff (hbt : (⊥ : L) ≠ ⊤) {x y : GlueCar (P := EndP L) (OrderHom.id)} :
    glueAAGen hbt x ≤ glueAAGen hbt y ↔ x ≤ y :=
  ⟨glueAAGen_reflect hbt, glueAAGen_monotone hbt⟩

-- [D-0571] glueAAGen_injective
theorem glueAAGen_injective (hbt : (⊥ : L) ≠ ⊤) : Function.Injective (glueAAGen hbt) := by
  have hm0 : (OrderHom.id : EndP L) ≠ ⊥ := hmL_of hbt
  have hmt0 : (OrderHom.id : EndP L) ≠ ⊤ := hmtL_of hbt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  letI := glueCarPartialOrder (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
    (hmL_of hbt') (hmtL_of hbt') (hbtEL_of hbt')
  intro x y h
  exact le_antisymm ((glueAAGen_le_iff hbt).mp h.le) ((glueAAGen_le_iff hbt).mp h.ge)

end GlueAAGenReflect

section GlueAAGenOverlap

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0572] iotaEndPGen_constHom
theorem iotaEndPGen_constHom (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    iotaEndPGen hbt (constHom x) = constHom (iotaGen x) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  ext w
  rw [iotaEndPGen_apply, constHom_apply, constHom_apply]

-- [D-0573] glueAAGen_iotaGen
theorem glueAAGen_iotaGen (hbt : (⊥ : L) ≠ ⊤) (x : L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    glueAAGen hbt (iotaGen x) = iotaGen (iotaGen x) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  apply Subtype.ext
  show (Sum.inl (iotaEndPGen hbt (constHom x)) : GlueBase (EndP (GlueCar (P := EndP L) (OrderHom.id))))
      = Sum.inl (constHom (iotaGen x))
  rw [iotaEndPGen_constHom hbt x]

end GlueAAGenOverlap

section GlueAAPDDeflation

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0574] glueAAGen_pGen_deflation_tagA
theorem glueAAGen_pGen_deflation_tagA (hbt : (⊥ : L) ≠ ⊤) (f : EndP L) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    pGen (L := GlueCar (P := EndP L) (OrderHom.id))
      (glueAAGen hbt (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (OrderHom.id)))
      ≤ (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (OrderHom.id)) := by
  have hm0 : (OrderHom.id : EndP L) ≠ ⊥ := hmL_of hbt
  have hmt0 : (OrderHom.id : EndP L) ≠ ⊤ := hmtL_of hbt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hval : pGen (L := GlueCar (P := EndP L) (OrderHom.id))
      (glueAAGen hbt (⟨Sum.inl f, rfl⟩ : GlueCar (P := EndP L) (OrderHom.id)))
      = iotaGen (f (⊥ : L)) := by
    have hb : pGen (L := L) (⊥ : GlueCar (P := EndP L) (OrderHom.id)) = (⊥ : L) := by
      rw [← iotaGen_bot hbt]
      exact pGen_section (⊥ : L)
    show (iotaEndPGen hbt f) (⊥ : GlueCar (P := EndP L) (OrderHom.id)) = iotaGen (f (⊥ : L))
    rw [iotaEndPGen_apply, hb]
  rw [hval, GlueCar.le_def]
  show leGlue (OrderHom.id : EndP L) (Sum.inl (constHom (f (⊥ : L)) : EndP L)) (Sum.inl f)
  exact (tagA_iso (OrderHom.id : EndP L) hm0 (constHom (f (⊥ : L))) f).mpr (by
    rw [OrderHom.le_def]; intro z; rw [constHom_apply]; exact f.monotone bot_le)

-- [D-0575] glueAAGen_pGen_deflation_tagB
set_option maxHeartbeats 4000000 in
theorem glueAAGen_pGen_deflation_tagB (hbt : (⊥ : L) ≠ ⊤) {f : EndP L}
    (hxv : canon (OrderHom.id : EndP L) (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl f))
    (hft : f ≠ (⊤ : EndP L)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueLattice (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    letI := glueBoundedOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    pGen (L := GlueCar (P := EndP L) (OrderHom.id))
      (glueAAGen hbt (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (OrderHom.id)))
      ≤ (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (OrderHom.id)) := by
  have hm0 : (OrderHom.id : EndP L) ≠ ⊥ := hmL_of hbt
  have hmt0 : (OrderHom.id : EndP L) ≠ ⊤ := hmtL_of hbt
  have hbt0 : (⊥ : EndP L) ≠ (⊤ : EndP L) := hbtEL_of hbt
  letI := glueCarPartialOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueLattice (OrderHom.id : EndP L) hm0 hmt0 hbt0
  letI := glueBoundedOrder (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hfb : f ≠ (⊥ : EndP L) := ne_bot_of_canon_tagB (OrderHom.id : EndP L) f hxv
  haveI hnt : Nontrivial (GlueCar (P := EndP L) (OrderHom.id)) :=
    glueCar_nontrivial (OrderHom.id : EndP L) hm0 hmt0 hbt0
  have hbt' : (⊥ : GlueCar (P := EndP L) (OrderHom.id)) ≠ ⊤ := bot_ne_top_of_nontrivial
  have hm' : (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) ≠ ⊥ := hmL_of hbt'
  have hlb : liftGen hbt f ≠ (⊥ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
    fun hc => hfb ((liftGen_eq_bot_iff hbt).mp hc)
  have hlt : liftGen hbt f ≠ (⊤ : EndP (GlueCar (P := EndP L) (OrderHom.id))) :=
    fun hc => hft ((liftGen_eq_top_iff hbt).mp hc)
  have hgAA : glueAAGen hbt (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (OrderHom.id))
      = incl (OrderHom.id) hm' (hbtEL_of hbt') (Sum.inr (Sum.inl (liftGen hbt f))) := rfl
  have hc1 : (incl (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id))) hm' (hbtEL_of hbt')
      (Sum.inr (Sum.inl (liftGen hbt f)))).1 = Sum.inr (Sum.inl (liftGen hbt f)) := by
    show canon (OrderHom.id : EndP (GlueCar (P := EndP L) (OrderHom.id)))
        (Sum.inr (Sum.inl (liftGen hbt f))) = Sum.inr (Sum.inl (liftGen hbt f))
    rw [canon, if_neg hlb]
  have hval : pGen (L := GlueCar (P := EndP L) (OrderHom.id))
      (glueAAGen hbt (⟨Sum.inr (Sum.inl f), hxv⟩ : GlueCar (P := EndP L) (OrderHom.id)))
      = (⊥ : GlueCar (P := EndP L) (OrderHom.id)) := by
    rw [hgAA]
    unfold pGen
    simp only [hc1, if_neg hlt]
  rw [hval]
  exact bot_le

end GlueAAPDDeflation

section CrossTagCA

variable {L : Type u} [DecidableEq L] [Lattice L] [BoundedOrder L] [Fintype L]

-- [D-0576] endP_eq_top_of_apply_bot_eq_top
omit [DecidableEq L] [Fintype L] in
theorem endP_eq_top_of_apply_bot_eq_top (f : EndP L) (h : f (⊥ : L) = (⊤ : L)) :
    f = (⊤ : EndP L) := by
  apply OrderHom.ext
  funext x
  have hle : f (⊥ : L) ≤ f x := f.monotone bot_le
  rw [h] at hle
  have hx : f x = (⊤ : L) := top_le_iff.mp hle
  rw [hx]
  rfl

-- [D-0577] crossTag_CA_sufficient
theorem crossTag_CA_sufficient (hbt : (⊥ : L) ≠ ⊤) (f : EndP L)
    (hfb : f ≠ (⊥ : EndP L)) (hfm : f ≠ (OrderHom.id : EndP L))
    (hidf : (OrderHom.id : EndP L) ≤ f)
    (Y : GlueCar (P := EndP L) (OrderHom.id))
    (hY : pGen (L := L) Y = f (⊥ : L)) :
    letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
    Y ≤ (incl (OrderHom.id : EndP L) (hmL_of hbt) (hbtEL_of hbt) (Sum.inr (Sum.inr f))) := by
  letI := glueCarPartialOrder (OrderHom.id : EndP L) (hmL_of hbt) (hmtL_of hbt) (hbtEL_of hbt)
  have hCfix : (incl (OrderHom.id : EndP L) (hmL_of hbt) (hbtEL_of hbt)
      (Sum.inr (Sum.inr f))).1 = Sum.inr (Sum.inr f) := by
    show canon (OrderHom.id : EndP L) (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr f)
    rw [canon, if_neg hfb, if_neg hfm]
  rw [GlueCar.le_def]
  show leGlue (OrderHom.id : EndP L) Y.1
      (incl (OrderHom.id : EndP L) (hmL_of hbt) (hbtEL_of hbt) (Sum.inr (Sum.inr f))).1
  rw [hCfix]
  rcases hY1 : Y.1 with v | v | v
  · show leGlue (OrderHom.id : EndP L) (Sum.inl v) (Sum.inr (Sum.inr f))
    exact leGlue_tagA_tagC (OrderHom.id : EndP L) v f
  · show leGlue (OrderHom.id : EndP L) (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr f))
    exact (leGlue_tagB_tagC_iff (OrderHom.id : EndP L) v f).mpr hidf
  · show leGlue (OrderHom.id : EndP L) (Sum.inr (Sum.inr v)) (Sum.inr (Sum.inr f))
    have hpg : pGen (L := L) Y = (⊤ : L) := by
      show (match Y.1 with
        | Sum.inl f => f (⊥ : L)
        | Sum.inr (Sum.inl f) => if f = (⊤ : EndP L) then (⊤ : L) else (⊥ : L)
        | Sum.inr (Sum.inr _) => (⊤ : L)) = (⊤ : L)
      rw [hY1]
    have hftop : f (⊥ : L) = (⊤ : L) := hY.symm.trans hpg
    have hfeqtop : f = (⊤ : EndP L) := endP_eq_top_of_apply_bot_eq_top f hftop
    have hvf : v ≤ f := by rw [hfeqtop]; exact le_top
    exact (leGlue_tagC_tagC_iff (OrderHom.id : EndP L) v f).mpr hvf

end CrossTagCA

section Phase3aStep4PsiInvMonotone

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-0578] iotaAGen
abbrev iotaAGen (_m : P) (x : P) : GlueBaseGen P := Sum.inl x
-- [D-0579] iotaBGen
abbrev iotaBGen (m : P) (x : P) : GlueBaseGen P := canonGen m (Sum.inr (Sum.inl x))
-- [D-0580] iotaCGen
abbrev iotaCGen (m : P) (x : P) : GlueBaseGen P := canonGen m (Sum.inr (Sum.inr x))

-- [D-0581] self_mem_occsGen
theorem self_mem_occsGen (m : P) (x : GlueBaseGen P) : x ∈ occsGen m x := by
  cases x with
  | inl x => simp only [occsGen]; split_ifs <;> simp
  | inr x => cases x with
    | inl x => simp only [occsGen]; split_ifs <;> simp
    | inr x => simp [occsGen]

-- [D-0582] occs_inl_memGen
theorem occs_inl_memGen (m : P) (x : P) {u : GlueBaseGen P} (hu : u ∈ occsGen m (Sum.inl x)) :
    u = Sum.inl x ∨ (x = m ∧ u = Sum.inr (Sum.inl (⊥ : P))) ∨
      (x = ⊤ ∧ u = Sum.inr (Sum.inr (⊥ : P))) := by
  simp only [occsGen] at hu
  split_ifs at hu with h1 h2 <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inl ⟨h1, hu⟩)
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inr ⟨h2, hu⟩)
  · exact Or.inl hu

-- [D-0583] tagA_isoGen
theorem tagA_isoGen (m : P) (hm : m ≠ ⊥) (x y : P) :
    leGlueGen m (iotaAGen m x) (iotaAGen m y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases occs_inl_memGen m x hu with hu' | ⟨hxm, hu'⟩ | ⟨hxt, hu'⟩ <;> subst hu' <;>
      rcases occs_inl_memGen m y hv with hv' | ⟨hym, hv'⟩ | ⟨hyt, hv'⟩ <;> subst hv'
    · exact huv
    · obtain rfl := hym.symm; exact huv
    · subst hyt; exact le_top
    · exact huv.elim
    · obtain rfl := hxm.symm; obtain rfl := hym.symm; exact le_refl m
    · exact absurd (le_bot_iff.mp huv) hm
    · exact huv.elim
    · exact huv.elim
    · subst hxt; subst hyt; exact le_refl _
  · intro hxy
    exact ⟨iotaAGen m x, self_mem_occsGen m _, iotaAGen m y, self_mem_occsGen m _, hxy⟩

-- [D-0584] iotaB_generic_eqGen
theorem iotaB_generic_eqGen (m x : P) (hxb : x ≠ ⊥) : iotaBGen m x = Sum.inr (Sum.inl x) := by
  show canonGen m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x)
  simp only [canonGen]; rw [if_neg hxb]

-- [D-0585] occs_iotaB_memGen
theorem occs_iotaB_memGen (m : P) (x : P) {u : GlueBaseGen P}
    (hu : u ∈ occsGen m (iotaBGen m x)) :
    (x ≠ ⊥ ∧ x ≠ ⊤ ∧ u = Sum.inr (Sum.inl x)) ∨
    (x = ⊥ ∧ (u = Sum.inl m ∨ u = Sum.inr (Sum.inl (⊥ : P)))) ∨
    (x = ⊤ ∧ (u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m))) := by
  by_cases hxb : x = ⊥
  · subst hxb
    have hiv : iotaBGen m (⊥ : P) = Sum.inl m := by
      show canonGen m (Sum.inr (Sum.inl (⊥ : P))) = Sum.inl m
      simp [canonGen]
    rw [hiv] at hu
    have hoc : occsGen m (Sum.inl m) = [Sum.inl m, Sum.inr (Sum.inl (⊥ : P))] := by
      simp [occsGen]
    rw [hoc] at hu
    exact Or.inr (Or.inl ⟨rfl, by simpa using hu⟩)
  · have hiv : iotaBGen m x = Sum.inr (Sum.inl x) := by
      show canonGen m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x)
      simp only [canonGen]; rw [if_neg hxb]
    rw [hiv] at hu
    by_cases hxt : x = ⊤
    · subst hxt
      have hoc : occsGen m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by
        simp [occsGen]
      rw [hoc] at hu
      exact Or.inr (Or.inr ⟨rfl, by simpa using hu⟩)
    · have hoc : occsGen m (Sum.inr (Sum.inl x)) = [Sum.inr (Sum.inl x)] := by
        simp only [occsGen]; rw [if_neg hxt]
      rw [hoc] at hu
      exact Or.inl ⟨hxb, hxt, by simpa using hu⟩

-- [D-0586] leGlue_tagA_tagB_iffGen
theorem leGlue_tagA_tagB_iffGen (m w y : P) (hyt : y ≠ ⊤) :
    leGlueGen m (Sum.inl w) (Sum.inr (Sum.inl y)) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsy : occsGen m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
      simp only [occsGen]; rw [if_neg hyt]
    rw [hoccsy] at hv
    have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
    subst hv'
    rcases occs_inl_memGen m w hu with hu' | ⟨hwm, hu'⟩ | ⟨hwt, hu'⟩ <;> subst hu'
    · exact huv
    · exact le_of_eq hwm
    · exact huv.elim
  · intro hwle
    exact ⟨Sum.inl w, self_mem_occsGen m _, Sum.inr (Sum.inl y), self_mem_occsGen m _, hwle⟩

-- [D-0587] leGlue_tagB_tagB_iffGen
theorem leGlue_tagB_tagB_iffGen (m w y : P) (hyt : y ≠ ⊤) (hwb : w ≠ ⊥) :
    leGlueGen m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inl y)) ↔ w ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccsy : occsGen m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
      simp only [occsGen]; rw [if_neg hyt]
    rw [hoccsy] at hv
    have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
    subst hv'
    rw [← iotaB_generic_eqGen m w hwb] at hu
    rcases occs_iotaB_memGen m w hu with ⟨_, _, hu'⟩ | ⟨hwb', _⟩ | ⟨hwt, hu' | hu'⟩
    · subst hu'; exact huv
    · exact absurd hwb' hwb
    · subst hwt; subst hu'; exact huv
    · subst hwt; subst hu'; exact huv.elim
  · intro hwle
    exact ⟨Sum.inr (Sum.inl w), self_mem_occsGen m _, Sum.inr (Sum.inl y), self_mem_occsGen m _,
      hwle⟩

-- [D-0588] leGlue_tagA_tagCGen
theorem leGlue_tagA_tagCGen (m w y : P) :
    leGlueGen m (Sum.inl w) (Sum.inr (Sum.inr y)) :=
  ⟨Sum.inl w, self_mem_occsGen m _, Sum.inr (Sum.inr y), self_mem_occsGen m _, trivial⟩

-- [D-0589] leGlue_tagB_tagC_iffGen
theorem leGlue_tagB_tagC_iffGen (m w y : P) :
    leGlueGen m (Sum.inr (Sum.inl w)) (Sum.inr (Sum.inr y)) ↔ m ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hv' : v = Sum.inr (Sum.inr y) := by simpa [occsGen] using hv
    subst hv'
    by_cases hwt : w = ⊤
    · subst hwt
      have hoc : occsGen m (Sum.inr (Sum.inl (⊤ : P))) =
          [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by simp [occsGen]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m) := by simpa using hu
      rcases hu' with hu' | hu' <;> subst hu' <;> exact huv
    · have hoc : occsGen m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
        simp only [occsGen]; rw [if_neg hwt]
      rw [hoc] at hu
      have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
      subst hu'
      exact huv
  · intro hmy
    exact ⟨Sum.inr (Sum.inl w), self_mem_occsGen m _, Sum.inr (Sum.inr y), self_mem_occsGen m _,
      hmy⟩

-- [D-0590] not_leGlue_tagB_tagAGen
theorem not_leGlue_tagB_tagAGen (m w w' : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (hw : w ≠ ⊥) :
    ¬ leGlueGen m (Sum.inr (Sum.inl w)) (Sum.inl w') := by
  rintro ⟨u, hu, v, hv, huv⟩
  by_cases hwt : w = ⊤
  · subst hwt
    have hoccsw : occsGen m (Sum.inr (Sum.inl (⊤ : P))) =
        [Sum.inr (Sum.inl (⊤ : P)), Sum.inr (Sum.inr m)] := by simp [occsGen]
    rw [hoccsw] at hu
    have hu' : u = Sum.inr (Sum.inl (⊤ : P)) ∨ u = Sum.inr (Sum.inr m) := by simpa using hu
    rcases hu' with hu' | hu'
    · subst hu'
      rcases occs_inl_memGen m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
      · subst hv'; exact huv.elim
      · subst hv'; exact hbt (le_antisymm huv bot_le).symm
      · subst hv'; exact hm (le_bot_iff.mp huv)
    · subst hu'
      rcases occs_inl_memGen m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
      · subst hv'; exact huv.elim
      · subst hv'; exact huv.elim
      · subst hv'; exact hm (le_bot_iff.mp huv)
  · have hoccsw : occsGen m (Sum.inr (Sum.inl w)) = [Sum.inr (Sum.inl w)] := by
      simp only [occsGen]; rw [if_neg hwt]
    rw [hoccsw] at hu
    have hu' : u = Sum.inr (Sum.inl w) := by simpa using hu
    subst hu'
    rcases occs_inl_memGen m w' hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩
    · subst hv'; exact huv.elim
    · subst hv'; exact hw (le_bot_iff.mp huv)
    · subst hv'; exact hm (le_bot_iff.mp huv)

-- [D-0591] not_leGlue_tagC_tagAGen
theorem not_leGlue_tagC_tagAGen (m w x : P) (hw : w ≠ ⊥) :
    ¬ leGlueGen m (Sum.inr (Sum.inr w)) (Sum.inl x) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hu' : u = Sum.inr (Sum.inr w) := by simpa [occsGen] using hu
  subst hu'
  rcases occs_inl_memGen m x hv with hv' | ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> subst hv'
  · exact huv.elim
  · exact huv.elim
  · exact hw (le_bot_iff.mp huv)

-- [D-0592] not_leGlue_tagC_tagBGen
theorem not_leGlue_tagC_tagBGen (m w y : P) (hyt : y ≠ ⊤) :
    ¬ leGlueGen m (Sum.inr (Sum.inr w)) (Sum.inr (Sum.inl y)) := by
  rintro ⟨u, hu, v, hv, huv⟩
  have hoccsy : occsGen m (Sum.inr (Sum.inl y)) = [Sum.inr (Sum.inl y)] := by
    simp only [occsGen]; rw [if_neg hyt]
  rw [hoccsy] at hv
  have hv' : v = Sum.inr (Sum.inl y) := by simpa using hv
  subst hv'
  have hu' : u = Sum.inr (Sum.inr w) := by simpa [occsGen] using hu
  subst hu'
  exact huv.elim

-- [D-0593] leGlue_tagC_tagC_iffGen
theorem leGlue_tagC_tagC_iffGen (m x y : P) :
    leGlueGen m (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inr y)) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr x) := by simpa [occsGen] using hu
    have hv' : v = Sum.inr (Sum.inr y) := by simpa [occsGen] using hv
    subst hu'; subst hv'
    exact huv
  · intro hxy
    exact ⟨_, self_mem_occsGen m _, _, self_mem_occsGen m _, hxy⟩

-- [D-0594] leGlue_tagC_tagB_top_iffGen
theorem leGlue_tagC_tagB_top_iffGen (m w' : P) :
    leGlueGen m (Sum.inr (Sum.inr w')) (Sum.inr (Sum.inl (⊤ : P))) ↔ w' ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr w') := by simpa [occsGen] using hu
    subst hu'
    have hv' : v = Sum.inr (Sum.inl (⊤ : P)) ∨ v = Sum.inr (Sum.inr m) := by simpa [occsGen] using hv
    rcases hv' with hv' | hv'
    · subst hv'; exact huv.elim
    · subst hv'; exact huv
  · intro hw'm
    exact ⟨Sum.inr (Sum.inr w'), self_mem_occsGen m _, Sum.inr (Sum.inr m), by simp [occsGen], hw'm⟩

-- [D-0595] phiGen
def phiGen (m : P) : GlueBaseGen P → P
  | Sum.inl _ => ⊥
  | Sum.inr (Sum.inl y) => if y = ⊤ then m else ⊥
  | Sum.inr (Sum.inr y) => y

-- [D-0596] leGlueGen_tagC_iff_le_phiGen
theorem leGlueGen_tagC_iff_le_phiGen (m : P) {v : P} (hv : v ≠ ⊥) (z : GlueBaseGen P) :
    leGlueGen m (Sum.inr (Sum.inr v)) z ↔ v ≤ phiGen m z := by
  cases z with
  | inl a =>
      simp only [phiGen, le_bot_iff]
      exact iff_of_false (not_leGlue_tagC_tagAGen m v a hv) hv
  | inr z => cases z with
    | inl b =>
        by_cases hbt : b = ⊤
        · subst hbt
          simpa [phiGen] using leGlue_tagC_tagB_top_iffGen m v
        · simp only [phiGen, if_neg hbt, le_bot_iff]
          exact iff_of_false (not_leGlue_tagC_tagBGen m v b hbt) hv
    | inr c =>
        simpa [phiGen] using leGlue_tagC_tagC_iffGen m v c

-- [D-0597] ne_bot_of_canon_tagBGen
theorem ne_bot_of_canon_tagBGen (m f : P)
    (hwv : canonGen m (Sum.inr (Sum.inl f)) = Sum.inr (Sum.inl f)) : f ≠ ⊥ := by
  intro hfb
  rw [canonGen, if_pos hfb] at hwv
  exact (Sum.inl_ne_inr) hwv

-- [D-0598] ne_bot_of_canon_tagCGen
theorem ne_bot_of_canon_tagCGen (m f : P)
    (hwv : canonGen m (Sum.inr (Sum.inr f)) = Sum.inr (Sum.inr f)) : f ≠ ⊥ := by
  intro hfb
  rw [canonGen, if_pos hfb] at hwv
  exact (Sum.inl_ne_inr) hwv

-- [D-0599] phiGen_monotone
theorem phiGen_monotone (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueCarGen (P := P) m} (hxy : x ≤ y) :
    phiGen m x.1 ≤ phiGen m y.1 := by
  obtain ⟨xv, hxv⟩ := x
  obtain ⟨yv, hyv⟩ := y
  have hle : leGlueGen m xv yv := hxy
  rcases xv with a | b | c
  · exact bot_le
  · rcases yv with a' | b' | c'
    · exact absurd hle (not_leGlue_tagB_tagAGen m b a' hm hbt (ne_bot_of_canon_tagBGen m b hxv))
    · have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hxv
      simp only [phiGen]
      by_cases hb't : b' = ⊤
      · rw [if_pos hb't]
        split_ifs
        · exact le_refl m
        · exact bot_le
      · have hbb' : b ≤ b' := (leGlue_tagB_tagB_iffGen m b b' hb't hbne).mp hle
        by_cases hbt' : b = ⊤
        · rw [hbt'] at hbb'
          exact absurd (top_le_iff.mp hbb') hb't
        · simp [hbt']
    · have hmc' : m ≤ c' := (leGlue_tagB_tagC_iffGen m b c').mp hle
      simp only [phiGen]
      by_cases hbt' : b = ⊤
      · simpa [hbt'] using hmc'
      · simpa [hbt'] using bot_le
  · rcases yv with a' | b' | c'
    · exact absurd hle (not_leGlue_tagC_tagAGen m c a' (ne_bot_of_canon_tagCGen m c hxv))
    · by_cases hb't : b' = ⊤
      · subst hb't
        have hcm : c ≤ m := (leGlue_tagC_tagB_top_iffGen m c).mp hle
        simpa [phiGen] using hcm
      · exact absurd hle (not_leGlue_tagC_tagBGen m c b' hb't)
    · have hcc' : c ≤ c' := (leGlue_tagC_tagC_iffGen m c c').mp hle
      simpa [phiGen] using hcc'

-- [D-0600] phiGen_mem_upperBounds_image
theorem phiGen_mem_upperBounds_image (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {s : Set (GlueCarGen (P := P) m)} {u : GlueCarGen (P := P) m} (hu : u ∈ upperBounds s) :
    phiGen m u.1 ∈ upperBounds ((fun w : GlueCarGen (P := P) m => phiGen m w.1) '' s) := by
  rintro _ ⟨w, hw, rfl⟩
  exact phiGen_monotone m hm hbt (hu hw)

end Phase3aStep4PsiInvMonotone

-- [D-0601] leGlue_tagA_tagB_topGen
theorem leGlue_tagA_tagB_topGen {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
    (m w : P) : leGlueGen m (Sum.inl w) (Sum.inr (Sum.inl (⊤ : P))) := by
  refine ⟨Sum.inl w, self_mem_occsGen m _, Sum.inr (Sum.inr m), ?_, trivial⟩
  simp [occsGen]

section TagCCompactnessTransfer
variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-0602] tagCGen
noncomputable def tagCGen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (c : P) :
    GlueCarGen (P := P) m :=
  ⟨canonGen m (Sum.inr (Sum.inr c)), canonGen_idem m hm hbt _⟩

-- [D-0603] tagCGen_val_of_generic
theorem tagCGen_val_of_generic (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {c : P}
    (hcb : c ≠ ⊥) (hcm : c ≠ m) :
    (tagCGen m hm hbt c).1 = Sum.inr (Sum.inr c) := by
  show canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c)
  simp only [canonGen]; rw [if_neg hcb, if_neg hcm]

-- [D-0604] skelG3Gen
noncomputable def skelG3Gen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) : GlueCarGen (P := P) m :=
  ⟨canonGen m (Sum.inr (Sum.inl (⊤ : P))), canonGen_idem m hm hbt _⟩

-- [D-0605] skelG3Gen_val
theorem skelG3Gen_val (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    (skelG3Gen m hm hbt).1 = Sum.inr (Sum.inl (⊤ : P)) := by
  show canonGen m (Sum.inr (Sum.inl (⊤ : P))) = Sum.inr (Sum.inl (⊤ : P))
  simp only [canonGen]; rw [if_neg (Ne.symm hbt)]

-- [D-0606] tagAGen
noncomputable def tagAGen (m : P) (a : P) : GlueCarGen (P := P) m :=
  ⟨Sum.inl a, rfl⟩

-- [D-0607] tagAGen_val
theorem tagAGen_val (m : P) (a : P) : (tagAGen m a).1 = Sum.inl a := rfl

-- [D-0608] skelG3Gen_mem_upperBounds_of_pureAB
theorem skelG3Gen_mem_upperBounds_of_pureAB (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {s : Set (GlueCarGen (P := P) m)}
    (hshape : ∀ x ∈ s, (∃ a, x.1 = Sum.inl a) ∨ (∃ b, x.1 = Sum.inr (Sum.inl b))) :
    skelG3Gen m hm hbt ∈ upperBounds s := by
  intro x hx
  show leGlueGen m x.1 (skelG3Gen m hm hbt).1
  rw [skelG3Gen_val]
  rcases hshape x hx with ⟨a, ha⟩ | ⟨b, hb⟩
  · rw [ha]; exact leGlue_tagA_tagB_topGen m a
  · rw [hb]
    exact ⟨Sum.inr (Sum.inl b), self_mem_occsGen m _, Sum.inr (Sum.inl (⊤ : P)),
      self_mem_occsGen m _, le_top⟩

-- [D-0609] tagC_generic_not_isLUB_of_pureAB_hasB
theorem tagC_generic_not_isLUB_of_pureAB_hasB (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {s : Set (GlueCarGen (P := P) m)}
    (hshape : ∀ x ∈ s, (∃ a, x.1 = Sum.inl a) ∨ (∃ b, x.1 = Sum.inr (Sum.inl b)))
    {b0 : P} {x0 : GlueCarGen (P := P) m} (hx0s : x0 ∈ s) (hx0val : x0.1 = Sum.inr (Sum.inl b0))
    {c : P} (hcb : c ≠ ⊥) (hcm : c ≠ m)
    {u : GlueCarGen (P := P) m} (hu : IsLUB s u) (huval : u.1 = Sum.inr (Sum.inr c)) : False := by
  have hle1 : u ≤ skelG3Gen m hm hbt := hu.2 (skelG3Gen_mem_upperBounds_of_pureAB m hm hbt hshape)
  have hcm1 : c ≤ m := by
    have : leGlueGen m u.1 (skelG3Gen m hm hbt).1 := hle1
    rw [huval, skelG3Gen_val] at this
    exact (leGlue_tagC_tagB_top_iffGen m c).mp this
  have hx0le : x0 ≤ u := hu.1 hx0s
  have hmc1 : m ≤ c := by
    have : leGlueGen m x0.1 u.1 := hx0le
    rw [hx0val, huval] at this
    exact (leGlue_tagB_tagC_iffGen m b0 c).mp this
  exact hcm (le_antisymm hcm1 hmc1)

-- [D-0610] tagC_generic_not_isLUB_of_pureA
theorem tagC_generic_not_isLUB_of_pureA (m : P) (hm : m ≠ ⊥)
    (hPdcpo : ∀ T : Set P, T.Nonempty → DirectedOn (· ≤ ·) T → ∃ t, IsLUB T t)
    {s : Set (GlueCarGen (P := P) m)} (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hshapeA : ∀ x ∈ s, ∃ a, x.1 = Sum.inl a)
    {c : P} (hcb : c ≠ ⊥) {u : GlueCarGen (P := P) m} (hu : IsLUB s u)
    (huval : u.1 = Sum.inr (Sum.inr c)) : False := by
  set S_A : Set P := {a | tagAGen m a ∈ s} with hSA_def
  have hSAne : S_A.Nonempty := by
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨a0, ha0⟩ := hshapeA x0 hx0
    have hform : x0 = tagAGen m a0 := Subtype.ext ha0
    refine ⟨a0, ?_⟩
    show tagAGen m a0 ∈ s
    rwa [← hform]
  have hSAdir : DirectedOn (· ≤ ·) S_A := by
    intro a ha a' ha'
    obtain ⟨z, hzs, hz1, hz2⟩ := hdir (tagAGen m a) ha (tagAGen m a') ha'
    obtain ⟨az, hazeq⟩ := hshapeA z hzs
    have hzform : z = tagAGen m az := Subtype.ext hazeq
    have hazSA : az ∈ S_A := by show tagAGen m az ∈ s; rwa [← hzform]
    refine ⟨az, hazSA, ?_, ?_⟩
    · have h1 : leGlueGen m (tagAGen m a).1 z.1 := hz1
      rw [hzform] at h1
      exact (tagA_isoGen m hm a az).mp h1
    · have h2 : leGlueGen m (tagAGen m a').1 z.1 := hz2
      rw [hzform] at h2
      exact (tagA_isoGen m hm a' az).mp h2
  obtain ⟨astar, hastar⟩ := hPdcpo S_A hSAne hSAdir
  have hub : tagAGen m astar ∈ upperBounds s := by
    intro x hx
    obtain ⟨ax, hax⟩ := hshapeA x hx
    have hxform : x = tagAGen m ax := Subtype.ext hax
    have haxSA : ax ∈ S_A := by show tagAGen m ax ∈ s; rwa [← hxform]
    have hle : ax ≤ astar := hastar.1 haxSA
    show leGlueGen m x.1 (tagAGen m astar).1
    rw [hxform, tagAGen_val, tagAGen_val]
    exact (tagA_isoGen m hm ax astar).mpr hle
  have hule : u ≤ tagAGen m astar := hu.2 hub
  have hfin : leGlueGen m u.1 (tagAGen m astar).1 := hule
  rw [huval, tagAGen_val] at hfin
  exact not_leGlue_tagC_tagAGen m c astar hcb hfin

-- [D-0611] exists_tagC_or_skelG3_dominating
theorem exists_tagC_or_skelG3_dominating (m : P)
    {s : Set (GlueCarGen (P := P) m)} (hdir : DirectedOn (· ≤ ·) s)
    {c1 : P} (hc1b : c1 ≠ ⊥) {x1 : GlueCarGen (P := P) m} (hx1s : x1 ∈ s)
    (hx1val : x1.1 = Sum.inr (Sum.inr c1))
    {x : GlueCarGen (P := P) m} (hxs : x ∈ s) :
    ∃ z ∈ s, x ≤ z ∧ ((∃ c2, z.1 = Sum.inr (Sum.inr c2)) ∨ z.1 = Sum.inr (Sum.inl (⊤ : P))) := by
  obtain ⟨z, hzs, hxz, hx1z⟩ := hdir x hxs x1 hx1s
  refine ⟨z, hzs, hxz, ?_⟩
  have hle : leGlueGen m (Sum.inr (Sum.inr c1)) z.1 := by
    have h : leGlueGen m x1.1 z.1 := hx1z
    rwa [hx1val] at h
  rcases z with ⟨zv, hzvc⟩
  rcases zv with a' | b' | c2'
  · exact absurd hle (not_leGlue_tagC_tagAGen m c1 a' hc1b)
  · by_cases hb't : b' = ⊤
    · exact Or.inr (by simp [hb't])
    · exact absurd hle (not_leGlue_tagC_tagBGen m c1 b' hb't)
  · exact Or.inl ⟨c2', rfl⟩

-- [D-0612] tagCGen_t0_mem_upperBounds
theorem tagCGen_t0_mem_upperBounds (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {s : Set (GlueCarGen (P := P) m)} (hdir : DirectedOn (· ≤ ·) s)
    {c1 : P} (hc1b : c1 ≠ ⊥) {x1 : GlueCarGen (P := P) m} (hx1s : x1 ∈ s)
    (hx1val : x1.1 = Sum.inr (Sum.inr c1))
    {t0 : P} (ht0ub : t0 ∈ upperBounds ((fun x : GlueCarGen (P := P) m => phiGen m x.1) '' s)) :
    tagCGen m hm hbt t0 ∈ upperBounds s := by
  intro x hxs
  show leGlueGen m x.1 (tagCGen m hm hbt t0).1
  rcases x with ⟨xv, hxv⟩
  rcases xv with a | b | c'
  ·
    show leGlueGen m (Sum.inl a) (canonGen m (Sum.inr (Sum.inr t0)))
    by_cases ht0b : t0 = ⊥
    · have hval : canonGen m (Sum.inr (Sum.inr (⊥ : P))) = Sum.inl (⊤ : P) := by
        simp [canonGen]
      rw [ht0b, hval]
      exact (tagA_isoGen m hm a ⊤).mpr le_top
    · by_cases ht0m : t0 = m
      · have hval : canonGen m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P)) := by
          simp [canonGen, hm]
        rw [ht0m, hval]
        exact leGlue_tagA_tagB_topGen m a
      · have hval : canonGen m (Sum.inr (Sum.inr t0)) = Sum.inr (Sum.inr t0) := by
          simp only [canonGen]; rw [if_neg ht0b, if_neg ht0m]
        rw [hval]
        exact leGlue_tagA_tagCGen m a t0
  ·
    have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hxv
    obtain ⟨z, hzs, hxz, hzshape⟩ :=
      exists_tagC_or_skelG3_dominating m hdir hc1b hx1s hx1val hxs
    have hmt0 : m ≤ t0 := by
      rcases hzshape with ⟨c2, hzval⟩ | hzval
      · have hc2t0 : c2 ≤ t0 := ht0ub ⟨z, hzs, by show phiGen m z.1 = c2; rw [hzval]; rfl⟩
        have hzc2 : leGlueGen m (Sum.inr (Sum.inl b)) z.1 := hxz
        rw [hzval] at hzc2
        exact le_trans ((leGlue_tagB_tagC_iffGen m b c2).mp hzc2) hc2t0
      · have hzm : phiGen m z.1 = m := by rw [hzval]; simp [phiGen]
        exact hzm ▸ ht0ub ⟨z, hzs, rfl⟩
    show leGlueGen m (Sum.inr (Sum.inl b)) (canonGen m (Sum.inr (Sum.inr t0)))
    have ht0b : t0 ≠ ⊥ := fun h => hm (h ▸ hmt0 |>.antisymm bot_le)
    by_cases ht0m : t0 = m
    · have hval : canonGen m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P)) := by
        simp [canonGen, hm]
      rw [ht0m, hval]
      exact ⟨Sum.inr (Sum.inl b), self_mem_occsGen m _, Sum.inr (Sum.inl (⊤ : P)),
        self_mem_occsGen m _, le_top⟩
    · have hval : canonGen m (Sum.inr (Sum.inr t0)) = Sum.inr (Sum.inr t0) := by
        simp only [canonGen]; rw [if_neg ht0b, if_neg ht0m]
      rw [hval]
      exact (leGlue_tagB_tagC_iffGen m b t0).mpr hmt0
  ·
    have hc't0 : c' ≤ t0 := ht0ub ⟨⟨Sum.inr (Sum.inr c'), hxv⟩, hxs, rfl⟩
    show leGlueGen m (Sum.inr (Sum.inr c')) (canonGen m (Sum.inr (Sum.inr t0)))
    have hc'b : c' ≠ ⊥ := ne_bot_of_canon_tagCGen m c' hxv
    have ht0b : t0 ≠ ⊥ := fun h => hc'b (le_antisymm (h ▸ hc't0) bot_le)
    by_cases ht0m : t0 = m
    · have hval : canonGen m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P)) := by
        simp [canonGen, hm]
      rw [ht0m, hval]
      exact (leGlue_tagC_tagB_top_iffGen m c').mpr (ht0m ▸ hc't0)
    · have hval : canonGen m (Sum.inr (Sum.inr t0)) = Sum.inr (Sum.inr t0) := by
        simp only [canonGen]; rw [if_neg ht0b, if_neg ht0m]
      rw [hval]
      exact (leGlue_tagC_tagC_iffGen m c' t0).mpr hc't0

-- [D-0613] tagCGen_isCompactElement
theorem tagCGen_isCompactElement (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hPdcpo : ∀ T : Set P, T.Nonempty → DirectedOn (· ≤ ·) T → ∃ t, IsLUB T t)
    {v : P} (hvb : v ≠ ⊥) (hvm : ¬ v ≤ m) (hvc : IsCompactElement v) :
    letI := glueCarPartialOrderGen m hm hmt hbt
    IsCompactElement (tagCGen m hm hbt v) := by
  letI := glueCarPartialOrderGen m hm hmt hbt
  intro s u hne hdir hLUB hle
  have hvne_m : v ≠ m := fun h => hvm (h ▸ le_refl v)
  have hule : leGlueGen m (tagCGen m hm hbt v).1 u.1 := hle
  rw [tagCGen_val_of_generic m hm hbt hvb hvne_m] at hule
  rcases h1 : u.1 with a' | b' | c''
  · rw [h1] at hule; exact absurd hule (not_leGlue_tagC_tagAGen m v a' hvb)
  · rw [h1] at hule
    by_cases hb't : b' = ⊤
    · subst hb't
      exact absurd ((leGlue_tagC_tagB_top_iffGen m v).mp hule) hvm
    · exact absurd hule (not_leGlue_tagC_tagBGen m v b' hb't)
  · rw [h1] at hule
    have hvc'' : v ≤ c'' := (leGlue_tagC_tagC_iffGen m v c'').mp hule
    have hc''ne_b : c'' ≠ ⊥ := ne_bot_of_canon_tagCGen m c'' (h1 ▸ u.2)
    have hc''ne_m : c'' ≠ m := fun h => hvm (h ▸ hvc'')
    have hTdir : DirectedOn (· ≤ ·) ((fun x : GlueCarGen (P := P) m => phiGen m x.1) '' s) :=
      directedOn_image_of_monotone (fun _ _ hxy => phiGen_monotone m hm hbt hxy) hdir
    have hTne : ((fun x : GlueCarGen (P := P) m => phiGen m x.1) '' s).Nonempty :=
      hne.image _
    obtain ⟨t0, ht0⟩ := hPdcpo _ hTne hTdir
    by_cases hSC : ∃ c1, ∃ x1 : GlueCarGen (P := P) m, x1 ∈ s ∧ x1.1 = Sum.inr (Sum.inr c1)
    · obtain ⟨c1, x1, hx1s, hx1val⟩ := hSC
      have hc1b : c1 ≠ ⊥ := ne_bot_of_canon_tagCGen m c1 (hx1val ▸ x1.2)
      have hub : tagCGen m hm hbt t0 ∈ upperBounds s :=
        tagCGen_t0_mem_upperBounds m hm hbt hdir hc1b hx1s hx1val ht0.1
      have huz : u ≤ tagCGen m hm hbt t0 := hLUB.2 hub
      have hfin0 : leGlueGen m u.1 (tagCGen m hm hbt t0).1 := huz
      have hfin : leGlueGen m (Sum.inr (Sum.inr c'')) (canonGen m (Sum.inr (Sum.inr t0))) := by
        rw [h1] at hfin0; exact hfin0
      have hc''t0 : c'' ≤ t0 := by
        by_cases ht0b : t0 = ⊥
        · exfalso; apply hc''ne_b
          have hval : canonGen m (Sum.inr (Sum.inr (⊥ : P))) = Sum.inl (⊤ : P) := by
            simp [canonGen]
          rw [ht0b, hval] at hfin
          exact absurd hfin (not_leGlue_tagC_tagAGen m c'' ⊤ hc''ne_b)
        · by_cases ht0m : t0 = m
          · have hval : canonGen m (Sum.inr (Sum.inr m)) = Sum.inr (Sum.inl (⊤ : P)) := by
              simp [canonGen, hm]
            rw [ht0m, hval] at hfin
            have hle2 := (leGlue_tagC_tagB_top_iffGen m c'').mp hfin
            rw [ht0m]; exact hle2
          · have hval : canonGen m (Sum.inr (Sum.inr t0)) = Sum.inr (Sum.inr t0) := by
              simp only [canonGen]; rw [if_neg ht0b, if_neg ht0m]
            rw [hval] at hfin
            exact (leGlue_tagC_tagC_iffGen m c'' t0).mp hfin
      have hvt0 : v ≤ t0 := le_trans hvc'' hc''t0
      obtain ⟨τ, hτT, hvτ⟩ := hvc _ t0 hTne hTdir ht0 hvt0
      obtain ⟨x0, hx0s, hx0val0⟩ := hτT
      have hx0val : phiGen m x0.1 = τ := hx0val0
      rcases h2 : x0.1 with a0 | b0 | c0
      · exfalso; rw [h2] at hx0val; simp [phiGen] at hx0val; rw [← hx0val] at hvτ; exact hvb (le_bot_iff.mp hvτ)
      · exfalso
        rw [h2] at hx0val
        by_cases hb0t : b0 = ⊤
        · subst hb0t; simp [phiGen] at hx0val; rw [← hx0val] at hvτ; exact hvm hvτ
        · simp [phiGen, hb0t] at hx0val; rw [← hx0val] at hvτ; exact hvb (le_bot_iff.mp hvτ)
      · refine ⟨x0, hx0s, ?_⟩
        show leGlueGen m (tagCGen m hm hbt v).1 x0.1
        rw [tagCGen_val_of_generic m hm hbt hvb hvne_m, h2]
        rw [h2] at hx0val
        simp only [phiGen] at hx0val
        exact (leGlue_tagC_tagC_iffGen m v c0).mpr (hx0val ▸ hvτ)
    · push_neg at hSC
      have hshape : ∀ x ∈ s, (∃ a1, x.1 = Sum.inl a1) ∨ (∃ b1, x.1 = Sum.inr (Sum.inl b1)) := by
        rintro ⟨xv, hxvc⟩ hx
        rcases xv with a1 | b1 | c1
        · exact Or.inl ⟨a1, rfl⟩
        · exact Or.inr ⟨b1, rfl⟩
        · exact absurd rfl (hSC c1 ⟨Sum.inr (Sum.inr c1), hxvc⟩ hx)
      by_cases hB : ∃ b0, ∃ x0 : GlueCarGen (P := P) m, x0 ∈ s ∧ x0.1 = Sum.inr (Sum.inl b0)
      · obtain ⟨b0, x0, hx0s, hx0val⟩ := hB
        exact (tagC_generic_not_isLUB_of_pureAB_hasB m hm hbt hshape hx0s hx0val hc''ne_b
          hc''ne_m hLUB h1).elim
      · push_neg at hB
        have hshapeA : ∀ x ∈ s, ∃ a1, x.1 = Sum.inl a1 := by
          intro x hx
          rcases hshape x hx with ⟨a1, ha1⟩ | ⟨b1, hb1⟩
          · exact ⟨a1, ha1⟩
          · exact absurd hb1 (hB b1 x hx)
        exact (tagC_generic_not_isLUB_of_pureA m hm hPdcpo hne hdir hshapeA hc''ne_b hLUB h1).elim

end TagCCompactnessTransfer

section TagACompactnessTransfer
variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-0614] tagAGen_isLUB_image
theorem tagAGen_isLUB_image (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {T : Set P} {t : P} (hLUB : IsLUB T t) :
    letI := glueCarPartialOrderGen m hm hmt hbt
    IsLUB ((fun a => tagAGen m a) '' T) (tagAGen m t) := by
  letI := glueCarPartialOrderGen m hm hmt hbt
  constructor
  · rintro _ ⟨x0, hx0T, rfl⟩
    show leGlueGen m (tagAGen m x0).1 (tagAGen m t).1
    rw [tagAGen_val, tagAGen_val]
    exact (tagA_isoGen m hm x0 t).mpr (hLUB.1 hx0T)
  · rintro u hu
    show leGlueGen m (tagAGen m t).1 u.1
    rcases h1 : u.1 with a' | b' | c'
    · have hall : ∀ x ∈ T, x ≤ a' := by
        intro x hxT
        have hxu : leGlueGen m (tagAGen m x).1 u.1 := hu ⟨x, hxT, rfl⟩
        rw [tagAGen_val, h1] at hxu
        exact (tagA_isoGen m hm x a').mp hxu
      rw [tagAGen_val]
      exact (tagA_isoGen m hm t a').mpr (hLUB.2 hall)
    · by_cases hb't : b' = ⊤
      · subst hb't
        rw [tagAGen_val]
        exact leGlue_tagA_tagB_topGen m t
      · have hall : ∀ x ∈ T, x ≤ m := by
          intro x hxT
          have hxu : leGlueGen m (tagAGen m x).1 u.1 := hu ⟨x, hxT, rfl⟩
          rw [tagAGen_val, h1] at hxu
          exact (leGlue_tagA_tagB_iffGen m x b' hb't).mp hxu
        rw [tagAGen_val]
        exact (leGlue_tagA_tagB_iffGen m t b' hb't).mpr (hLUB.2 hall)
    · rw [tagAGen_val]
      exact leGlue_tagA_tagCGen m t c'

-- [D-0615] isCompactElement_of_tagAGen_isCompactElement
theorem isCompactElement_of_tagAGen_isCompactElement (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : P) ≠ ⊤) {a : P}
    (hac : letI := glueCarPartialOrderGen m hm hmt hbt; IsCompactElement (tagAGen m a)) :
    IsCompactElement a := by
  letI := glueCarPartialOrderGen m hm hmt hbt
  intro T t hTne hTdir hLUB haT
  have hLUB' := tagAGen_isLUB_image m hm hmt hbt hLUB
  have hdir' : DirectedOn (· ≤ ·) ((fun a => tagAGen m a) '' T) :=
    directedOn_image_of_monotone (fun x y hxy => (tagA_isoGen m hm x y).mpr hxy) hTdir
  have hle : tagAGen m a ≤ tagAGen m t := (tagA_isoGen m hm a t).mpr haT
  obtain ⟨y, hys, hay⟩ := hac _ _ (hTne.image _) hdir' hLUB' hle
  obtain ⟨x0, hx0T, rfl⟩ := hys
  have hay' : leGlueGen m (tagAGen m a).1 (tagAGen m x0).1 := hay
  rw [tagAGen_val, tagAGen_val] at hay'
  exact ⟨x0, hx0T, (tagA_isoGen m hm a x0).mp hay'⟩

end TagACompactnessTransfer

section GlueCarGenFunctoriality

variable {P Q : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
  [DecidableEq Q] [PartialOrder Q] [BoundedOrder Q]

-- [D-0616] glueBaseGenEquiv
noncomputable def glueBaseGenEquiv (e : P ≃o Q) : GlueBaseGen P ≃ GlueBaseGen Q :=
  Equiv.sumCongr e.toEquiv (Equiv.sumCongr e.toEquiv e.toEquiv)

-- [D-0617] mapGlueBaseGen
noncomputable def mapGlueBaseGen (e : P ≃o Q) : GlueBaseGen P → GlueBaseGen Q :=
  glueBaseGenEquiv e

-- [D-0618] mapGlueBaseGen_inl
@[simp] theorem mapGlueBaseGen_inl (e : P ≃o Q) (x : P) :
    mapGlueBaseGen e (Sum.inl x) = Sum.inl (e x) := rfl

-- [D-0619] mapGlueBaseGen_inr_inl
@[simp] theorem mapGlueBaseGen_inr_inl (e : P ≃o Q) (x : P) :
    mapGlueBaseGen e (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl (e x)) := rfl

-- [D-0620] mapGlueBaseGen_inr_inr
@[simp] theorem mapGlueBaseGen_inr_inr (e : P ≃o Q) (x : P) :
    mapGlueBaseGen e (Sum.inr (Sum.inr x)) = Sum.inr (Sum.inr (e x)) := rfl

-- [D-0621] mapGlueBaseGen_injective
theorem mapGlueBaseGen_injective (e : P ≃o Q) : Function.Injective (mapGlueBaseGen e) :=
  (glueBaseGenEquiv e).injective

-- [D-0622] canonGen_map
theorem canonGen_map (e : P ≃o Q) (m : P) (x : GlueBaseGen P) :
    canonGen (e m) (mapGlueBaseGen e x) = mapGlueBaseGen e (canonGen m x) := by
  have hbotIff : ∀ x : P, x = ⊥ ↔ e x = ⊥ :=
    fun x => ⟨fun h => by rw [h, e.map_bot], fun h => e.injective (h.trans e.map_bot.symm)⟩
  have htopIff : ∀ x : P, x = ⊤ ↔ e x = ⊤ :=
    fun x => ⟨fun h => by rw [h, e.map_top], fun h => e.injective (h.trans e.map_top.symm)⟩
  have hmIff : ∀ x : P, x = m ↔ e x = e m :=
    fun x => ⟨fun h => by rw [h], fun h => e.injective h⟩
  cases x with
  | inl x => rfl
  | inr x =>
    cases x with
    | inl x =>
      show canonGen (e m) (Sum.inr (Sum.inl (e x)))
        = mapGlueBaseGen e (canonGen m (Sum.inr (Sum.inl x)))
      simp only [canonGen]
      split_ifs with h1 h2 <;>
        simp_all [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl, mapGlueBaseGen_inr_inr, hbotIff]
    | inr x =>
      show canonGen (e m) (Sum.inr (Sum.inr (e x)))
        = mapGlueBaseGen e (canonGen m (Sum.inr (Sum.inr x)))
      simp only [canonGen]
      split_ifs with h1 h2 h3 h4 <;>
        simp_all [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl, mapGlueBaseGen_inr_inr,
          hbotIff, hmIff, e.map_top]

-- [D-0623] rawRuleGen_map
theorem rawRuleGen_map (e : P ≃o Q) (m : P) (u v : GlueBaseGen P) :
    rawRuleGen (e m) (mapGlueBaseGen e u) (mapGlueBaseGen e v) ↔ rawRuleGen m u v := by
  rcases u with x | x | x <;> rcases v with y | y | y <;>
    simp only [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl, mapGlueBaseGen_inr_inr,
      rawRuleGen, e.le_iff_le]

-- [D-0624] occsGen_map
theorem occsGen_map (e : P ≃o Q) (m : P) (x : GlueBaseGen P) :
    occsGen (e m) (mapGlueBaseGen e x) = (occsGen m x).map (mapGlueBaseGen e) := by
  have htopIff : ∀ x : P, x = ⊤ ↔ e x = ⊤ :=
    fun x => ⟨fun h => by rw [h, e.map_top], fun h => e.injective (h.trans e.map_top.symm)⟩
  have hmIff : ∀ x : P, x = m ↔ e x = e m :=
    fun x => ⟨fun h => by rw [h], fun h => e.injective h⟩
  cases x with
  | inl x =>
    show occsGen (e m) (Sum.inl (e x)) = (occsGen m (Sum.inl x)).map (mapGlueBaseGen e)
    simp only [occsGen]
    by_cases hxm : x = m
    · have hexm : e x = e m := by rw [hxm]
      simp_all [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl]
    · have hexm : e x ≠ e m := fun h => hxm (e.injective h)
      by_cases hxt : x = ⊤
      · have hext : e x = ⊤ := by rw [hxt, e.map_top]
        simp_all [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inr]
      · have hext : e x ≠ ⊤ := by
          rw [← e.map_top]; exact fun h => hxt (e.injective h)
        simp_all [mapGlueBaseGen_inl]
  | inr x =>
    cases x with
    | inl x =>
      show occsGen (e m) (Sum.inr (Sum.inl (e x)))
        = (occsGen m (Sum.inr (Sum.inl x))).map (mapGlueBaseGen e)
      simp only [occsGen]
      by_cases hxt : x = ⊤
      · have hext : e x = ⊤ := by rw [hxt, e.map_top]
        simp_all [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl, mapGlueBaseGen_inr_inr]
      · have hext : e x ≠ ⊤ := by
          rw [← e.map_top]; exact fun h => hxt (e.injective h)
        simp_all [mapGlueBaseGen_inr_inl]
    | inr x =>
      show occsGen (e m) (Sum.inr (Sum.inr (e x)))
        = (occsGen m (Sum.inr (Sum.inr x))).map (mapGlueBaseGen e)
      unfold occsGen
      simp [mapGlueBaseGen_inl, mapGlueBaseGen_inr_inl, mapGlueBaseGen_inr_inr]

-- [D-0625] leGlueGen_map_iff
theorem leGlueGen_map_iff (e : P ≃o Q) (m : P) (x y : GlueBaseGen P) :
    leGlueGen (e m) (mapGlueBaseGen e x) (mapGlueBaseGen e y) ↔ leGlueGen m x y := by
  unfold leGlueGen
  rw [occsGen_map, occsGen_map]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    simp only [List.mem_map] at hu hv
    obtain ⟨u0, hu0, rfl⟩ := hu
    obtain ⟨v0, hv0, rfl⟩ := hv
    exact ⟨u0, hu0, v0, hv0, (rawRuleGen_map e m u0 v0).mp huv⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    exact ⟨mapGlueBaseGen e u, List.mem_map_of_mem hu,
      mapGlueBaseGen e v, List.mem_map_of_mem hv, (rawRuleGen_map e m u v).mpr huv⟩

-- [D-0626] glueCarGenEquiv
noncomputable def glueCarGenEquiv (e : P ≃o Q) (m : P) :
    GlueCarGen (P := P) m ≃ GlueCarGen (P := Q) (e m) :=
  (glueBaseGenEquiv e).subtypeEquiv (fun x => by
    constructor
    · intro hx
      show canonGen (e m) (mapGlueBaseGen e x) = mapGlueBaseGen e x
      rw [canonGen_map, hx]
    · intro hx
      have h2 : mapGlueBaseGen e (canonGen m x) = mapGlueBaseGen e x := by
        rw [← canonGen_map]; exact hx
      exact mapGlueBaseGen_injective e h2)

-- [D-0627] glueCarGenOrderIso
noncomputable def glueCarGenOrderIso (e : P ≃o Q) (m : P) :
    GlueCarGen (P := P) m ≃o GlueCarGen (P := Q) (e m) where
  toEquiv := glueCarGenEquiv e m
  map_rel_iff' := by
    intro x y
    show leGlueGen (e m) (mapGlueBaseGen e x.1) (mapGlueBaseGen e y.1) ↔ leGlueGen m x.1 y.1
    exact leGlueGen_map_iff e m x.1 y.1

end GlueCarGenFunctoriality

-- [D-0628] _root_.IsCompactElement.orderIso
theorem _root_.IsCompactElement.orderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α ≃o β) {a : α} (ha : IsCompactElement a) : IsCompactElement (f a) := by
  intro s u hs hdir hlub hle
  have hs' : (f.symm '' s).Nonempty := hs.image _
  have hdir' : DirectedOn (· ≤ ·) (f.symm '' s) :=
    DirectedOn.mono_comp (fun _ _ h => f.symm.monotone h) hdir
  have hlub' : IsLUB (f.symm '' s) (f.symm u) := f.symm.isLUB_image'.mpr hlub
  have hle' : a ≤ f.symm u := by
    rw [← f.le_iff_le, f.apply_symm_apply]
    exact hle
  obtain ⟨x, hx, hax⟩ := ha (f.symm '' s) (f.symm u) hs' hdir' hlub' hle'
  obtain ⟨y, hys, rfl⟩ := hx
  refine ⟨y, hys, ?_⟩
  have h2 := f.le_iff_le.mpr hax
  rwa [f.apply_symm_apply] at h2

section ThetaSkelG3
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0629] leGlue_tagA_skelG3
theorem leGlue_tagA_skelG3 (m w : P) : leGlue m (Sum.inl w) (skelG3 m) :=
  ⟨Sum.inl w, self_mem_occs m _, Sum.inr (Sum.inr m), by simp [occs, skelG3], trivial⟩

-- [D-0630] leGlue_tagB_skelG3
theorem leGlue_tagB_skelG3 (m x : P) : leGlue m (Sum.inr (Sum.inl x)) (skelG3 m) := by
  rcases eq_or_ne x ⊤ with hxt | hxt
  · subst hxt; exact leGlue_refl m (skelG3 m)
  · exact ⟨Sum.inr (Sum.inl x), self_mem_occs m _, skelG3 m, self_mem_occs m _, le_top⟩

-- [D-0631] leGlue_tagC_skelG3_iff
theorem leGlue_tagC_skelG3_iff (m w : P) :
    leGlue m (Sum.inr (Sum.inr w)) (skelG3 m) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = Sum.inr (Sum.inr w) := by simpa [occs] using hu
    subst hu'
    have hoccg3 : occs m (skelG3 m) = [skelG3 m, Sum.inr (Sum.inr m)] := by
      simp [occs, skelG3]
    rw [hoccg3] at hv
    rcases (by simpa using hv : v = skelG3 m ∨ v = Sum.inr (Sum.inr m)) with hv' | hv'
    · subst hv'; exact huv.elim
    · subst hv'; exact huv
  · intro hwm
    exact ⟨Sum.inr (Sum.inr w), self_mem_occs m _, Sum.inr (Sum.inr m), by simp [occs, skelG3], hwm⟩

-- [D-0632] incGlue_skelG3_iff
theorem incGlue_skelG3_iff (m : P) (z : GlueBase P) :
    (¬ leGlue m z (skelG3 m) ∧ ¬ leGlue m (skelG3 m) z) ↔
      ∃ w, z = Sum.inr (Sum.inr w) ∧ ¬ w ≤ m ∧ ¬ m ≤ w := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, _⟩; exact absurd (leGlue_tagA_skelG3 m w) h1
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨h1, _⟩; exact absurd (leGlue_tagB_skelG3 m w) h1
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨w, rfl, ?_, ?_⟩
      · intro hwm; exact h1 ((leGlue_tagC_skelG3_iff m w).mpr hwm)
      · intro hmw; exact h2 ((leGlue_tagB_tagC_iff m ⊤ w).mpr hmw)
    · rintro ⟨w', hweq, hw1, hw2⟩
      have hww' : w = w' := by cases hweq; rfl
      subst hww'
      refine ⟨?_, ?_⟩
      · intro hcon; exact hw1 ((leGlue_tagC_skelG3_iff m w).mp hcon)
      · intro hcon; exact hw2 ((leGlue_tagB_tagC_iff m ⊤ w).mp hcon)

end ThetaSkelG3

section GlueCarSuccJoinIrred

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0633] glueCar_cases
theorem glueCar_cases (m : P) (f : GlueCar (P := P) m) :
    (∃ v : P, f = glueA m v) ∨
    (∃ (x : P) (hx : x ≠ ⊥), f = glueB m x hx) ∨
    (∃ (x : P) (hx : x ≠ ⊥) (hxm : x ≠ m), f = glueC m x hx hxm) := by
  obtain ⟨val, hval⟩ := f
  rcases val with v | w | w
  · exact Or.inl ⟨v, Subtype.ext rfl⟩
  · have hw := canon_inr_inl_ne_bot m w hval
    exact Or.inr (Or.inl ⟨w, hw, Subtype.ext rfl⟩)
  · have hw := canon_inr_inr_ne m w hval
    exact Or.inr (Or.inr ⟨w, hw.1, hw.2, Subtype.ext rfl⟩)

-- [D-0634] not_hasUniqueDownCover_of_two_covers
theorem not_hasUniqueDownCover_of_two_covers {α : Type u} [Preorder α] {a w1 w2 : α}
    (h1 : Covers w1 a) (h2 : Covers w2 a) (hne : w1 ≠ w2) : ¬ HasUniqueDownCover a := by
  rintro ⟨w, -, huniq⟩
  exact hne ((huniq w1 h1).trans (huniq w2 h2).symm)

end GlueCarSuccJoinIrred

section JoinIrredTop
variable {P : Type u} [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0635] joinIrred_top
theorem joinIrred_top (hbt : (⊥ : P) ≠ ⊤) : JoinIrred P (⊤ : P) := by
  refine ⟨hbt.symm, fun b c heq => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hb : b ≠ ⊤ := fun h => hcon.1 h.symm
  have hc : c ≠ ⊤ := fun h => hcon.2 h.symm
  have hble : b ≤ coatomOf P := coatomOf_le hb
  have hcle : c ≤ coatomOf P := coatomOf_le hc
  have hsup : b ⊔ c ≤ coatomOf P := sup_le hble hcle
  rw [← heq] at hsup
  exact coatomOf_ne_top P (top_le_iff.mp hsup)

end JoinIrredTop

section EndPIdNotJoinIrred
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0636] endPId_ne_stepMap
theorem endPId_ne_stepMap (hcard : 3 ≤ Fintype.card P) (x q : P) :
    (OrderHom.id : EndP P) ≠ stepMap x q := by
  intro heq
  have hmem : ∀ y : P, y = x ∨ y = ⊥ := by
    intro y
    have h1 : (OrderHom.id : EndP P) y = (stepMap x q : EndP P) y := by rw [heq]
    rw [endPId_apply] at h1
    by_cases hqy : q ≤ y
    · left; rwa [stepMap_apply_of_ge x q hqy] at h1
    · right; rwa [stepMap_apply_of_not_ge x q hqy] at h1
  have hsub : (Finset.univ : Finset P) ⊆ {x, ⊥} := by
    intro y _
    rcases hmem y with h | h <;> simp [h]
  have hle2 : Fintype.card P ≤ 2 := by
    calc Fintype.card P = (Finset.univ : Finset P).card := (Finset.card_univ).symm
      _ ≤ ({x, ⊥} : Finset P).card := Finset.card_le_card hsub
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

-- [D-0637] endPId_not_joinIrred
theorem endPId_not_joinIrred (hcard : 3 ≤ Fintype.card P) :
    ¬ JoinIrred (EndP P) (OrderHom.id : EndP P) := by
  intro hji
  obtain ⟨x, q, -, heq⟩ := (joinIrred_endP_iff_exists_stepMap _).mp hji
  exact endPId_ne_stepMap hcard x q heq

end EndPIdNotJoinIrred

section GlueBTopNotJoinIrred
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P]

-- [D-0638] coatomOf_ne_bot
theorem coatomOf_ne_bot (hbt : (⊥ : P) ≠ ⊤) (hcard : 3 ≤ Fintype.card P) :
    coatomOf P ≠ (⊥ : P) := by
  intro hc
  have hall : ∀ b : P, b ≠ ⊤ → b = ⊥ := by
    intro b hbne
    have h := coatomOf_le hbne
    rw [hc] at h
    exact le_bot_iff.mp h
  have hsub : (Finset.univ : Finset P) ⊆ {⊥, ⊤} := by
    intro y _
    by_cases hy : y = ⊤
    · simp [hy]
    · simp [hall y hy]
  have hle2 : Fintype.card P ≤ 2 := by
    calc Fintype.card P = (Finset.univ : Finset P).card := (Finset.card_univ).symm
      _ ≤ ({⊥, ⊤} : Finset P).card := Finset.card_le_card hsub
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

variable (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)

-- [D-0639] covers_glueB_coatomOf_glueB_top
theorem covers_glueB_coatomOf_glueB_top (hcard : 3 ≤ Fintype.card P) :
    letI := glueCarPartialOrder m hm hmt hbt
    Covers (glueB m (coatomOf P) (coatomOf_ne_bot hbt hcard))
      (glueB m (⊤ : P) (hbt ∘ Eq.symm)) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hcob : coatomOf P ≠ ⊥ := coatomOf_ne_bot hbt hcard
  have hcot : coatomOf P ≠ ⊤ := coatomOf_ne_top P
  constructor
  · have hle : leGlue m (Sum.inr (Sum.inl (coatomOf P))) (skelG3 m) :=
      leGlue_tagB_skelG3 m (coatomOf P)
    refine lt_of_le_of_ne hle (fun heq => hcot ?_)
    exact glueB_injective m hcob (hbt ∘ Eq.symm) heq
  · intro c hc1 hc2
    obtain ⟨cv, hcvfix⟩ := c
    rcases cv with w' | w' | w'
    · exact absurd hc1.le (not_leGlue_tagB_tagA m (coatomOf P) w' hm hbt hcob)
    · by_cases hw't : w' = ⊤
      · subst hw't
        exact absurd hc2 (lt_irrefl _)
      · have h1 : coatomOf P ≤ w' :=
          (leGlue_tagB_tagB_iff m (coatomOf P) w' hw't hcob).mp hc1.le
        have h2 : w' ≤ coatomOf P := coatomOf_le hw't
        exact hc1.ne (Subtype.ext (congrArg (fun z => Sum.inr (Sum.inl z)) (le_antisymm h1 h2)))
    · have hw'm : w' ≠ m := (canon_inr_inr_ne m w' hcvfix).2
      have h1 : m ≤ w' := (leGlue_tagB_tagC_iff m (coatomOf P) w').mp hc1.le
      have h2 : w' ≤ m := (leGlue_tagC_skelG3_iff m w').mp hc2.le
      exact hw'm (le_antisymm h1 h2).symm

-- [D-0640] not_hasUniqueDownCover_glueB_top
theorem not_hasUniqueDownCover_glueB_top (hcard : 3 ≤ Fintype.card P) :
    letI := glueCarPartialOrder m hm hmt hbt
    ¬ HasUniqueDownCover (glueB m (⊤ : P) (hbt ∘ Eq.symm)) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hcot : coatomOf P ≠ ⊤ := coatomOf_ne_top P
  have hw1cov := covers_glueB_coatomOf_glueB_top m hm hmt hbt hcard
  have hlt : glueA m (⊤ : P) < glueB m (⊤ : P) (hbt ∘ Eq.symm) :=
    glueA_top_lt_glueB_top m hm hmt hbt
  obtain ⟨w2, hw2cov, hw2ge⟩ := exists_covBy_ge hlt
  have hne : glueB m (coatomOf P) (coatomOf_ne_bot hbt hcard) ≠ w2 := by
    intro heq
    rw [← heq] at hw2ge
    have hle2 : leGlue m (Sum.inl (⊤ : P)) (Sum.inr (Sum.inl (coatomOf P))) :=
      (GlueCar.le_def m (glueA m ⊤) (glueB m (coatomOf P) (coatomOf_ne_bot hbt hcard))).mp hw2ge
    have h1 : (⊤ : P) ≤ m := (leGlue_tagA_tagB_iff m (⊤ : P) (coatomOf P) hcot).mp hle2
    exact hmt (top_le_iff.mp h1)
  exact not_hasUniqueDownCover_of_two_covers hw1cov hw2cov hne

end GlueBTopNotJoinIrred

section SplitCard
variable {Q0 : Type u} [Fintype Q0] [DecidableEq Q0] [Lattice Q0] [BoundedOrder Q0]

-- [D-0641] card_joinIrred_eq_succ_of_ne_top
theorem card_joinIrred_eq_succ_of_ne_top (ht : JoinIrred Q0 (⊤ : Q0)) :
    Fintype.card {x : Q0 // JoinIrred Q0 x} =
      Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ (⊤ : Q0)} + 1 := by
  have e : {x : Q0 // JoinIrred Q0 x} ≃
      ({x : Q0 // JoinIrred Q0 x ∧ x ≠ (⊤ : Q0)} ⊕ Unit) := by
    refine ⟨fun z => if h : z.1 = ⊤ then Sum.inr () else Sum.inl ⟨z.1, z.2, h⟩,
      Sum.elim (fun w => ⟨w.1, w.2.1⟩) (fun _ => ⟨⊤, ht⟩), ?_, ?_⟩
    · rintro ⟨v, hv⟩
      by_cases h : v = ⊤
      · subst h; simp
      · simp [h]
    · rintro (⟨w, hw1, hw2⟩ | ⟨⟩)
      · simp [hw2]
      · simp
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit]

-- [D-0642] card_joinIrred_and_ne_eq_of_not_joinIrred
theorem card_joinIrred_and_ne_eq_of_not_joinIrred {m : Q0} (hnm : ¬ JoinIrred Q0 m) :
    Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ m} = Fintype.card {x : Q0 // JoinIrred Q0 x} := by
  have e : {x : Q0 // JoinIrred Q0 x ∧ x ≠ m} ≃ {x : Q0 // JoinIrred Q0 x} :=
    ⟨fun z => ⟨z.1, z.2.1⟩, fun z => ⟨z.1, z.2, fun h => hnm (h ▸ z.2)⟩,
      fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  exact Fintype.card_congr e

end SplitCard

section GlueCarSuccCard
variable {Q0 : Type u} [Fintype Q0] [DecidableEq Q0] [Lattice Q0] [BoundedOrder Q0]
  [UniqueAtomCoatom Q0]

-- [D-0643] jiGlueCarSuccEquiv
noncomputable def jiGlueCarSuccEquiv (m : Q0) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : Q0) ≠ ⊤) (hcard : 3 ≤ Fintype.card Q0) :
    letI := glueLattice m hm hmt hbt
    letI := glueBoundedOrder m hm hmt hbt
    ({x : Q0 // JoinIrred Q0 x} ⊕ {x : Q0 // JoinIrred Q0 x ∧ x ≠ (⊤ : Q0)} ⊕
        {x : Q0 // JoinIrred Q0 x ∧ x ≠ m}) ≃
      {f : GlueCar (P := Q0) m // JoinIrred (GlueCar (P := Q0) m) f} := by
  letI := glueLattice m hm hmt hbt
  letI := glueBoundedOrder m hm hmt hbt
  refine Equiv.ofBijective
    (Sum.elim
      (fun v => (⟨glueA m v.1, (joinIrred_glueA_iff m hm hmt hbt v.1).mpr v.2⟩ :
        {f : GlueCar (P := Q0) m // JoinIrred (GlueCar (P := Q0) m) f}))
      (Sum.elim
        (fun x => ⟨glueB m x.1 x.2.1.1,
          (joinIrred_glueB_iff m hm hmt hbt x.1 x.2.1.1 x.2.2).mpr x.2.1⟩)
        (fun x => ⟨glueC m x.1 x.2.1.1 x.2.2,
          (joinIrred_glueC_iff m hm hmt hbt x.1 x.2.1.1 x.2.2).mpr x.2.1⟩)))
    ⟨?_, ?_⟩
  ·
    rintro (v1 | x1 | x1) (v2 | x2 | x2) heq <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at heq
    · exact congrArg Sum.inl (Subtype.ext (glueA_injective m heq))
    · exact absurd (congrArg Subtype.val heq) (by simp [glueA, glueB])
    · exact absurd (congrArg Subtype.val heq) (by simp [glueA, glueC])
    · exact absurd (congrArg Subtype.val heq) (by simp [glueA, glueB])
    · exact congrArg Sum.inr (congrArg Sum.inl
        (Subtype.ext (glueB_injective m x1.2.1.1 x2.2.1.1 heq)))
    · exact absurd (congrArg Subtype.val heq) (by simp [glueB, glueC])
    · exact absurd (congrArg Subtype.val heq) (by simp [glueA, glueC])
    · exact absurd (congrArg Subtype.val heq) (by simp [glueB, glueC])
    · exact congrArg Sum.inr (congrArg Sum.inr
        (Subtype.ext (glueC_injective m x1.2.1.1 x1.2.2 x2.2.1.1 x2.2.2 heq)))
  ·
    rintro ⟨f, hf⟩
    rcases glueCar_cases m f with ⟨v, hfeq⟩ | ⟨x, hx, hfeq⟩ | ⟨x, hx, hxm, hfeq⟩
    · refine ⟨Sum.inl ⟨v, ?_⟩, ?_⟩
      · exact (joinIrred_glueA_iff m hm hmt hbt v).mp (hfeq ▸ hf)
      · exact Subtype.ext hfeq.symm
    · by_cases hxt : x = ⊤
      · exfalso
        subst hxt
        have hji : JoinIrred (GlueCar (P := Q0) m) (glueB m (⊤ : Q0) hx) := hfeq ▸ hf
        have hud : HasUniqueDownCover (glueB m (⊤ : Q0) hx) :=
          (hasUniqueDownCover_iff_joinIrred _).mpr hji
        exact not_hasUniqueDownCover_glueB_top m hm hmt hbt hcard hud
      · refine ⟨Sum.inr (Sum.inl ⟨x, ?_, hxt⟩), ?_⟩
        · exact (joinIrred_glueB_iff m hm hmt hbt x hx hxt).mp (hfeq ▸ hf)
        · exact Subtype.ext hfeq.symm
    · refine ⟨Sum.inr (Sum.inr ⟨x, ?_, hxm⟩), ?_⟩
      · exact (joinIrred_glueC_iff m hm hmt hbt x hx hxm).mp (hfeq ▸ hf)
      · exact Subtype.ext hfeq.symm

-- [D-0644] card_joinIrred_glueCar_gen
theorem card_joinIrred_glueCar_gen (m : Q0) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : Q0) ≠ ⊤) (hcard : 3 ≤ Fintype.card Q0) (hnm : ¬ JoinIrred Q0 m) :
    letI := glueLattice m hm hmt hbt
    letI := glueBoundedOrder m hm hmt hbt
    Fintype.card {f : GlueCar (P := Q0) m // JoinIrred (GlueCar (P := Q0) m) f} =
      3 * Fintype.card {x : Q0 // JoinIrred Q0 x} - 1 := by
  letI := glueLattice m hm hmt hbt
  letI := glueBoundedOrder m hm hmt hbt
  rw [← Fintype.card_congr (jiGlueCarSuccEquiv m hm hmt hbt hcard)]
  rw [Fintype.card_sum, Fintype.card_sum]
  have hB : Fintype.card {x : Q0 // JoinIrred Q0 x} =
      Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ (⊤ : Q0)} + 1 :=
    card_joinIrred_eq_succ_of_ne_top (joinIrred_top hbt)
  have hC : Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ m} =
      Fintype.card {x : Q0 // JoinIrred Q0 x} :=
    card_joinIrred_and_ne_eq_of_not_joinIrred hnm
  omega

end GlueCarSuccCard

section GlueCarSuccCardHeadline
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
  [UniqueAtomCoatom P]

-- [D-0645] card_joinIrred_glueCar_endP_id
theorem card_joinIrred_glueCar_endP_id (hbt : (⊥ : P) ≠ ⊤) (hcard : 3 ≤ Fintype.card P) :
    letI hm := endPId_ne_bot hbt
    letI hmt := endPId_ne_top hbt
    letI hbtQ := endP_bot_ne_top hbt
    letI := glueLattice (OrderHom.id : EndP P) hm hmt hbtQ
    letI := glueBoundedOrder (OrderHom.id : EndP P) hm hmt hbtQ
    Fintype.card {f : GlueCar (P := EndP P) (OrderHom.id) //
        JoinIrred (GlueCar (P := EndP P) (OrderHom.id)) f} =
      3 * Fintype.card {x : P // JoinIrred P x} * Fintype.card P - 1 := by
  have hm := endPId_ne_bot (P := P) hbt
  have hmt := endPId_ne_top (P := P) hbt
  have hbtQ := endP_bot_ne_top (P := P) hbt
  letI := glueLattice (OrderHom.id : EndP P) hm hmt hbtQ
  letI := glueBoundedOrder (OrderHom.id : EndP P) hm hmt hbtQ
  letI := endPUniqueAtomCoatom (P := P)
  have hcardQ : 3 ≤ Fintype.card (EndP P) :=
    le_trans hcard (Fintype.card_le_of_injective constHom constHom_injective)
  have hnm : ¬ JoinIrred (EndP P) (OrderHom.id : EndP P) := endPId_not_joinIrred hcard
  have hmain := card_joinIrred_glueCar_gen (OrderHom.id : EndP P) hm hmt hbtQ hcardQ hnm
  have hprod : Fintype.card {x : EndP P // JoinIrred (EndP P) x} =
      Fintype.card P * Fintype.card {x : P // JoinIrred P x} := by
    rw [← Fintype.card_congr (jiEquiv (P := P)), Fintype.card_prod]
  rw [hprod] at hmain
  rw [hmain]
  ring_nf

end GlueCarSuccCardHeadline

section ThetaSkelG1
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0646] leGlue_tagA_skelG1_iff
theorem leGlue_tagA_skelG1_iff (m w : P) :
    leGlue m (Sum.inl w) (skelG1 m) ↔ w ≤ m := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccg1 : occs m (skelG1 m) = [skelG1 m, Sum.inr (Sum.inl (⊥ : P))] := by
      simp [occs, skelG1]
    rw [hoccg1] at hv
    have hv' : v = skelG1 m ∨ v = Sum.inr (Sum.inl (⊥ : P)) := by simpa using hv
    rcases occs_inl_mem m w hu with hu' | ⟨hwm, hu'⟩ | ⟨hwt, hu'⟩ <;> subst hu'
    · rcases hv' with hv' | hv' <;> subst hv' <;> first | exact huv | exact huv.elim
    · exact le_of_eq hwm
    · rcases hv' with hv' | hv' <;> subst hv' <;> first | exact huv | exact huv.elim
  · intro hwle
    exact ⟨Sum.inl w, self_mem_occs m _, skelG1 m, self_mem_occs m _, hwle⟩

-- [D-0647] leGlue_skelG1_tagA_iff
theorem leGlue_skelG1_tagA_iff (m w : P) :
    leGlue m (skelG1 m) (Sum.inl w) ↔ m ≤ w := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hoccg1 : occs m (skelG1 m) = [skelG1 m, Sum.inr (Sum.inl (⊥ : P))] := by
      simp [occs, skelG1]
    rw [hoccg1] at hu
    have hu' : u = skelG1 m ∨ u = Sum.inr (Sum.inl (⊥ : P)) := by simpa using hu
    rcases occs_inl_mem m w hv with hv' | ⟨hwm, hv'⟩ | ⟨hwt, hv'⟩ <;> subst hv'
    · rcases hu' with hu' | hu' <;> subst hu' <;> first | exact huv | exact huv.elim
    · exact le_of_eq hwm.symm
    · subst hwt; exact le_top
  · intro hmw
    exact ⟨skelG1 m, self_mem_occs m _, Sum.inl w, self_mem_occs m _, hmw⟩

-- [D-0648] leGlue_skelG1_tagB
theorem leGlue_skelG1_tagB (m x : P) : leGlue m (skelG1 m) (Sum.inr (Sum.inl x)) := by
  rcases eq_or_ne x ⊤ with hxt | hxt
  · subst hxt; exact leGlue_tagA_skelG3 m m
  · exact (leGlue_tagA_tagB_iff m m x hxt).mpr le_rfl

-- [D-0649] leGlue_skelG1_tagC
theorem leGlue_skelG1_tagC (m y : P) : leGlue m (skelG1 m) (Sum.inr (Sum.inr y)) :=
  leGlue_tagA_tagC m m y

-- [D-0650] incGlue_skelG1_iff
theorem incGlue_skelG1_iff (m : P) (z : GlueBase P) :
    (¬ leGlue m z (skelG1 m) ∧ ¬ leGlue m (skelG1 m) z) ↔
      ∃ w, z = Sum.inl w ∧ ¬ w ≤ m ∧ ¬ m ≤ w := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨w, rfl, ?_, ?_⟩
      · intro hwm; exact h1 ((leGlue_tagA_skelG1_iff m w).mpr hwm)
      · intro hmw; exact h2 ((leGlue_skelG1_tagA_iff m w).mpr hmw)
    · rintro ⟨w', hweq, hw1, hw2⟩
      have hww' : w = w' := by cases hweq; rfl
      subst hww'
      refine ⟨?_, ?_⟩
      · intro hcon; exact hw1 ((leGlue_tagA_skelG1_iff m w).mp hcon)
      · intro hcon; exact hw2 ((leGlue_skelG1_tagA_iff m w).mp hcon)
  · constructor
    · rintro ⟨_, h2⟩; exact absurd (leGlue_skelG1_tagB m w) h2
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨_, h2⟩; exact absurd (leGlue_skelG1_tagC m w) h2
    · rintro ⟨w', hcon, _, _⟩; cases hcon

end ThetaSkelG1

section ThetaGenericGated
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0651] incGlue_tagA_of_le
theorem incGlue_tagA_of_le (m : P) (hm : m ≠ ⊥) {v : P} (hvm : v ≤ m) (hvne : v ≠ m)
    (z : GlueBase P) :
    (¬ leGlue m z (Sum.inl v) ∧ ¬ leGlue m (Sum.inl v) z) ↔
      ∃ w, z = Sum.inl w ∧ ¬ w ≤ v ∧ ¬ v ≤ w := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w, rfl, fun hle => h1 ((tagA_iso m hm w v).mpr hle),
        fun hle => h2 ((tagA_iso m hm v w).mpr hle)⟩
    · rintro ⟨w', hweq, hw1, hw2⟩
      have hww' : w = w' := by cases hweq; rfl
      subst hww'
      exact ⟨fun hcon => hw1 ((tagA_iso m hm w v).mp hcon),
        fun hcon => hw2 ((tagA_iso m hm v w).mp hcon)⟩
  · constructor
    · rintro ⟨_, h2⟩
      rcases eq_or_ne w ⊤ with hwt | hwt
      · subst hwt; exact absurd (leGlue_tagA_skelG3 m v) h2
      · exact absurd ((leGlue_tagA_tagB_iff m v w hwt).mpr hvm) h2
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨_, h2⟩; exact absurd (leGlue_tagA_tagC m v w) h2
    · rintro ⟨w', hcon, _, _⟩; cases hcon

-- [D-0652] incGlue_tagC_of_ge
theorem incGlue_tagC_of_ge (m : P) {v : P} (hvm : m ≤ v) (hvne : v ≠ m)
    (z : GlueBase P) :
    (¬ leGlue m z (Sum.inr (Sum.inr v)) ∧ ¬ leGlue m (Sum.inr (Sum.inr v)) z) ↔
      ∃ w, z = Sum.inr (Sum.inr w) ∧ ¬ w ≤ v ∧ ¬ v ≤ w := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, _⟩; exact absurd (leGlue_tagA_tagC m w v) h1
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨h1, _⟩; exact absurd ((leGlue_tagB_tagC_iff m w v).mpr hvm) h1
    · rintro ⟨w', hcon, _, _⟩; cases hcon
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w, rfl, fun hle => h1 ((leGlue_tagC_tagC_iff m w v).mpr hle),
        fun hle => h2 ((leGlue_tagC_tagC_iff m v w).mpr hle)⟩
    · rintro ⟨w', hweq, hw1, hw2⟩
      have hww' : w = w' := by cases hweq; rfl
      subst hww'
      exact ⟨fun hcon => hw1 ((leGlue_tagC_tagC_iff m w v).mp hcon),
        fun hcon => hw2 ((leGlue_tagC_tagC_iff m v w).mp hcon)⟩

end ThetaGenericGated

section ThetaMeetSkelG3
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0653] isGLB_inc_skelG3
theorem isGLB_inc_skelG3 (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hne : {w : P | ¬ w ≤ m ∧ ¬ m ≤ w}.Nonempty)
    {q : P} (hqb : q ≠ ⊥) (hqm : q ≠ m)
    (hq : IsGLB {w : P | ¬ w ≤ m ∧ ¬ m ≤ w} q) :
    letI := glueCarPartialOrder m hm hmt hbt
    IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt (⊤ : P) ∧
      ¬ glueBt m hm hbt (⊤ : P) ≤ z} (glueCt m hm hbt q) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hgBval : (glueBt m hm hbt (⊤ : P)).1 = skelG3 m := by
    show iotaB m (⊤ : P) = skelG3 m
    show canon m (Sum.inr (Sum.inl (⊤ : P))) = Sum.inr (Sum.inl (⊤ : P))
    simp only [canon]; rw [if_neg hbt.symm]
  have hgCval : (glueCt m hm hbt q).1 = Sum.inr (Sum.inr q) := iotaC_generic_eq m q hqb hqm
  have hgCwval : ∀ w : P, ¬ w ≤ m → ¬ m ≤ w → (glueCt m hm hbt w).1 = Sum.inr (Sum.inr w) := by
    intro w hw1 hw2
    have hwb : w ≠ ⊥ := by
      intro heq; rw [heq] at hw1; exact hw1 bot_le
    have hwm : w ≠ m := by
      intro heq; rw [heq] at hw2; exact hw2 (le_refl m)
    exact iotaC_generic_eq m w hwb hwm
  have hmem : ∀ w : P, ¬ w ≤ m → ¬ m ≤ w → glueCt m hm hbt w ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt (⊤ : P) ∧
        ¬ glueBt m hm hbt (⊤ : P) ≤ z} := by
    intro w hw1 hw2
    have hincpair := (incGlue_skelG3_iff m (glueCt m hm hbt w).1).mpr ⟨w, hgCwval w hw1 hw2, hw1, hw2⟩
    constructor
    · rw [GlueCar.le_def, hgBval]; exact hincpair.1
    · rw [GlueCar.le_def, hgBval]; exact hincpair.2
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    have hz1' : ¬ leGlue m z.1 (skelG3 m) := by
      intro hcon; rw [← hgBval] at hcon
      exact hz1 ((GlueCar.le_def m z (glueBt m hm hbt (⊤ : P))).mpr hcon)
    have hz2' : ¬ leGlue m (skelG3 m) z.1 := by
      intro hcon; rw [← hgBval] at hcon
      exact hz2 ((GlueCar.le_def m (glueBt m hm hbt (⊤ : P)) z).mpr hcon)
    obtain ⟨w, hzeq, hw1, hw2⟩ := (incGlue_skelG3_iff m z.1).mp ⟨hz1', hz2'⟩
    have hzw : z.1 = iotaC m w := by
      have hcanon : canon m z.1 = z.1 := z.2
      rw [hzeq] at hcanon ⊢
      exact hcanon.symm
    have hzeq2 : z = glueCt m hm hbt w := Subtype.ext hzw
    rw [hzeq2]
    exact (glueCt_le_iff m hm hmt hbt q w).mpr
      (hq.1 (show w ∈ {w : P | ¬ w ≤ m ∧ ¬ m ≤ w} from ⟨hw1, hw2⟩))
  ·
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      rw [GlueCar.le_def, hgCval]
      exact leGlue_tagA_tagC m w' q
    ·
      exfalso
      obtain ⟨w, hw1, hw2⟩ := hne
      have hzle := hz' (hmem w hw1 hw2)
      rw [GlueCar.le_def, hgCwval w hw1 hw2] at hzle
      exact hw2 ((leGlue_tagB_tagC_iff m w' w).mp hzle)
    ·
      have hbound : ∀ w ∈ {w : P | ¬ w ≤ m ∧ ¬ m ≤ w}, w' ≤ w := by
        intro w hw
        have hzle := hz' (hmem w hw.1 hw.2)
        rw [GlueCar.le_def, hgCwval w hw.1 hw.2] at hzle
        exact (leGlue_tagC_tagC_iff m w' w).mp hzle
      have hw'q : w' ≤ q := hq.2 hbound
      rw [GlueCar.le_def, hgCval]
      exact (leGlue_tagC_tagC_iff m w' q).mpr hw'q

-- [D-0654] isLUB_inc_skelG1
theorem isLUB_inc_skelG1 (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hne : {w : P | ¬ w ≤ m ∧ ¬ m ≤ w}.Nonempty)
    {q : P} (hq : IsLUB {w : P | ¬ w ≤ m ∧ ¬ m ≤ w} q) :
    letI := glueCarPartialOrder m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m | ¬ z ≤ glueA m m ∧ ¬ glueA m m ≤ z} (glueA m q) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hmem : ∀ w : P, ¬ w ≤ m → ¬ m ≤ w → glueA m w ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueA m m ∧ ¬ glueA m m ≤ z} := by
    intro w hw1 hw2
    have hincpair := (incGlue_skelG1_iff m (glueA m w).1).mpr ⟨w, rfl, hw1, hw2⟩
    exact hincpair
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    obtain ⟨w, hzeq, hw1, hw2⟩ := (incGlue_skelG1_iff m z.1).mp ⟨hz1, hz2⟩
    have hzeq2 : z = glueA m w := Subtype.ext hzeq
    rw [hzeq2]
    exact (glueA_le_iff m hm w q).mpr (hq.1 ⟨hw1, hw2⟩)
  ·
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      have hbound : ∀ w ∈ {w : P | ¬ w ≤ m ∧ ¬ m ≤ w}, w ≤ w' := by
        intro w hw
        exact (glueA_le_iff m hm w w').mp (hz' (hmem w hw.1 hw.2))
      exact (glueA_le_iff m hm q w').mpr (hq.2 hbound)
    ·
      rcases eq_or_ne w' ⊤ with hwt | hwt
      · subst hwt
        rw [GlueCar.le_def]
        exact leGlue_tagA_skelG3 m q
      · exfalso
        obtain ⟨w, hw1, hw2⟩ := hne
        have hzle := hz' (hmem w hw1 hw2)
        rw [GlueCar.le_def] at hzle
        exact hw1 ((leGlue_tagA_tagB_iff m w w' hwt).mp hzle)
    ·
      rw [GlueCar.le_def]
      exact leGlue_tagA_tagC m q w'

section BranchingWitnesses

-- [D-0655] branchF1
noncomputable def branchF1 {P : Type*} [PartialOrder P] [BoundedOrder P] (v : P) : EndP P :=
  OrderHom.const P v

-- [D-0656] branchF2
noncomputable def branchF2 {P : Type*} [PartialOrder P] [BoundedOrder P] (v : P) : EndP P where
  toFun := fun x => if x = ⊥ then v else ⊤
  monotone' := by
    intro x y hxy
    by_cases hx : x = (⊥ : P)
    · by_cases hy : y = (⊥ : P)
      · simp [hx, hy]
      · simp only [hx, if_neg hy]
        exact le_top
    · have hy : y ≠ (⊥ : P) := by
        intro hy0
        exact hx (le_antisymm (hy0 ▸ hxy) bot_le)
      simp only [if_neg hx, if_neg hy]
      exact le_refl _

-- [D-0657] branchF1_apply_bot
theorem branchF1_apply_bot {P : Type*} [PartialOrder P] [BoundedOrder P] (v : P) :
    (branchF1 v : P → P) (⊥ : P) = v := rfl

-- [D-0658] branchF2_apply_bot
theorem branchF2_apply_bot {P : Type*} [PartialOrder P] [BoundedOrder P] (v : P) :
    (branchF2 v : P → P) (⊥ : P) = v := by
  show (if (⊥ : P) = ⊥ then v else ⊤) = v
  simp

-- [D-0659] branchF1_ne_branchF2
theorem branchF1_ne_branchF2 {P : Type*} [PartialOrder P] [BoundedOrder P] (v : P)
    (hv : v ≠ (⊤ : P)) (hbt : (⊥ : P) ≠ ⊤) : branchF1 v ≠ branchF2 v := by
  intro h
  have h1 : (branchF1 v : P → P) ⊤ = (branchF2 v : P → P) ⊤ := by rw [h]
  have hb1 : (branchF1 v : P → P) ⊤ = v := rfl
  have hb2 : (branchF2 v : P → P) ⊤ = ⊤ := by
    show (if (⊤ : P) = ⊥ then v else ⊤) = ⊤
    rw [if_neg (Ne.symm hbt)]
  rw [hb1, hb2] at h1
  exact hv h1

end BranchingWitnesses

end ThetaMeetSkelG3

section ThetaGenericNotLe
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0660] isLUB_ne_bot_ne_top_coatomOf
theorem isLUB_ne_bot_ne_top_coatomOf (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : IsLUB {x : P | x ≠ ⊥ ∧ x ≠ ⊤} (coatomOf P) := by
  constructor
  · rintro x ⟨_, hxt⟩; exact coatomOf_le hxt
  · intro c hc
    rcases eq_or_ne (coatomOf P) ⊥ with hcb | hcb
    · rw [hcb]; exact bot_le
    · exact hc ⟨hcb, coatomOf_ne_top P⟩

-- [D-0661] incGlue_tagA_of_not_le
theorem incGlue_tagA_of_not_le (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvm : ¬ v ≤ m) (hvt : v ≠ ⊤) (z : GlueBase P) (hz : canon m z = z) :
    (¬ leGlue m z (Sum.inl v) ∧ ¬ leGlue m (Sum.inl v) z) ↔
      (∃ w, z = Sum.inl w ∧ ¬ w ≤ v ∧ ¬ v ≤ w) ∨
      (∃ x, z = Sum.inr (Sum.inl x) ∧ x ≠ ⊥ ∧ x ≠ ⊤) := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨w, rfl, fun hle => h1 ((tagA_iso m hm w v).mpr hle),
        fun hle => h2 ((tagA_iso m hm v w).mpr hle)⟩
    · rintro (⟨w', hweq, hw1, hw2⟩ | ⟨x, hcon, _, _⟩)
      · have hww' : w = w' := by cases hweq; rfl
        subst hww'
        exact ⟨fun hcon => hw1 ((tagA_iso m hm w v).mp hcon),
          fun hcon => hw2 ((tagA_iso m hm v w).mp hcon)⟩
      · cases hcon
  · have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hz
    constructor
    · rintro ⟨_, h2⟩
      rcases eq_or_ne w ⊤ with hwt | hwt
      · subst hwt; exact absurd (leGlue_tagA_skelG3 m v) h2
      · exact Or.inr ⟨w, rfl, hwb, hwt⟩
    · rintro (⟨w', hcon, _, _⟩ | ⟨x, hxeq, hxb, hxt⟩)
      · cases hcon
      · have hwx : w = x := by cases hxeq; rfl
        subst hwx
        exact ⟨not_leGlue_tagB_tagA m w v hm hbt hxb,
          fun hcon => hvm ((leGlue_tagA_tagB_iff m v w hxt).mp hcon)⟩
  · constructor
    · rintro ⟨_, h2⟩; exact absurd (leGlue_tagA_tagC m v w) h2
    · rintro (⟨w', hcon, _, _⟩ | ⟨x, hcon, _, _⟩) <;> cases hcon

variable [UniqueAtomCoatom P]

-- [D-0662] isLUB_inc_tagA_of_not_le
theorem isLUB_inc_tagA_of_not_le (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvm : ¬ v ≤ m) (hvt : v ≠ ⊤) (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {s : P} (hs : IsLUB {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} s) :
    letI := glueCarPartialOrder m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m | ¬ z ≤ glueA m v ∧ ¬ glueA m v ≤ z}
      (glueJoin m hm hbt (glueA m s) (glueBt m hm hbt (coatomOf P))) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hmemA : ∀ w : P, ¬ w ≤ v → ¬ v ≤ w → glueA m w ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueA m v ∧ ¬ glueA m v ≤ z} :=
    fun w hw1 hw2 => (incGlue_tagA_of_not_le m hm hbt hvm hvt (Sum.inl w) rfl).mpr
      (Or.inl ⟨w, rfl, hw1, hw2⟩)
  have hmemB : ∀ x : P, x ≠ ⊥ → x ≠ ⊤ → glueBt m hm hbt x ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueA m v ∧ ¬ glueA m v ≤ z} := by
    intro x hxb hxt
    have hval : (glueBt m hm hbt x).1 = Sum.inr (Sum.inl x) := iotaB_generic_eq m x hxb
    have hcanon : canon m (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x) := by
      simp only [canon]; rw [if_neg hxb]
    have hincpair := (incGlue_tagA_of_not_le m hm hbt hvm hvt (Sum.inr (Sum.inl x)) hcanon).mpr
      (Or.inr ⟨x, rfl, hxb, hxt⟩)
    constructor
    · rw [GlueCar.le_def, hval]; exact hincpair.1
    · rw [GlueCar.le_def, hval]; exact hincpair.2
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    obtain ⟨w, hzeq, hw1, hw2⟩ | ⟨x, hzeq, hxb, hxt⟩ :=
      (incGlue_tagA_of_not_le m hm hbt hvm hvt z.1 z.2).mp ⟨hz1, hz2⟩
    · have hzeq2 : z = glueA m w := Subtype.ext hzeq
      rw [hzeq2]
      exact le_trans ((glueA_le_iff m hm w s).mpr (hs.1 ⟨hw1, hw2⟩))
        (glueJoin_le_left m hm hmt hbt (glueA m s) (glueBt m hm hbt (coatomOf P)))
    · have hzeq2 : z = glueBt m hm hbt x := by
        apply Subtype.ext
        rw [hzeq]
        exact (iotaB_generic_eq m x hxb).symm
      rw [hzeq2]
      exact le_trans ((glueBt_le_iff m hm hmt hbt x (coatomOf P)).mpr (coatomOf_le hxt))
        (glueJoin_le_right m hm hmt hbt (glueA m s) (glueBt m hm hbt (coatomOf P)))
  ·
    have hvalB : ∀ y : P, y ≠ ⊥ → (glueBt m hm hbt y).1 = Sum.inr (Sum.inl y) :=
      fun y hy => iotaB_generic_eq m y hy
    have hcob : coatomOf P ≠ ⊥ := by
      obtain ⟨x, hxb, hxt⟩ := hne3
      intro heq
      exact hxb (le_bot_iff.mp (heq ▸ coatomOf_le hxt))
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      exfalso
      obtain ⟨x, hxb, hxt⟩ := hne3
      have hzle := hz' (hmemB x hxb hxt)
      rw [GlueCar.le_def, hvalB x hxb] at hzle
      exact not_leGlue_tagB_tagA m x w' hm hbt hxb hzle
    ·
      rcases eq_or_ne w' ⊤ with hw't | hw't
      · subst hw't
        apply le_glueJoin m hm hmt hbt
        · rw [GlueCar.le_def]; exact leGlue_tagA_skelG3 m s
        · rw [GlueCar.le_def, hvalB (coatomOf P) hcob]; exact leGlue_tagB_skelG3 m (coatomOf P)
      · apply le_glueJoin m hm hmt hbt
        · have hbound : ∀ w ∈ {w : P | ¬ w ≤ v ∧ ¬ v ≤ w}, w ≤ m := by
            intro w hw
            have hzle := hz' (hmemA w hw.1 hw.2)
            rw [GlueCar.le_def] at hzle
            exact (leGlue_tagA_tagB_iff m w w' hw't).mp hzle
          rw [GlueCar.le_def]
          exact (leGlue_tagA_tagB_iff m s w' hw't).mpr (hs.2 hbound)
        · have hbound : ∀ x ∈ {x : P | x ≠ ⊥ ∧ x ≠ ⊤}, x ≤ w' := by
            intro x hx
            have hzle := hz' (hmemB x hx.1 hx.2)
            rw [GlueCar.le_def, hvalB x hx.1] at hzle
            exact (leGlue_tagB_tagB_iff m x w' hw't hx.1).mp hzle
          rw [GlueCar.le_def, hvalB (coatomOf P) hcob]
          exact (leGlue_tagB_tagB_iff m (coatomOf P) w' hw't hcob).mpr
            ((isLUB_ne_bot_ne_top_coatomOf P).2 hbound)
    ·
      apply le_glueJoin m hm hmt hbt
      · rw [GlueCar.le_def]; exact leGlue_tagA_tagC m s w'
      · obtain ⟨x, hxb, hxt⟩ := hne3
        have hzle := hz' (hmemB x hxb hxt)
        rw [GlueCar.le_def, hvalB x hxb] at hzle
        have hmw' : m ≤ w' := (leGlue_tagB_tagC_iff m x w').mp hzle
        rw [GlueCar.le_def, hvalB (coatomOf P) hcob]
        exact (leGlue_tagB_tagC_iff m (coatomOf P) w').mpr hmw'

-- [D-0663] glueA_ne_isLUB_inc_tagA_of_not_le
theorem glueA_ne_isLUB_inc_tagA_of_not_le (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvm : ¬ v ≤ m) (hvt : v ≠ ⊤) (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {s : P} (hs : IsLUB {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} s) :
    letI := glueCarPartialOrder m hm hmt hbt
    glueA m v ≠ glueJoin m hm hbt (glueA m s) (glueBt m hm hbt (coatomOf P)) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hcob : coatomOf P ≠ ⊥ := by
    obtain ⟨x, hxb, hxt⟩ := hne3
    intro heq
    exact hxb (le_bot_iff.mp (heq ▸ coatomOf_le hxt))
  intro heq
  have hb : glueBt m hm hbt (coatomOf P) ≤
      glueJoin m hm hbt (glueA m s) (glueBt m hm hbt (coatomOf P)) :=
    glueJoin_le_right m hm hmt hbt (glueA m s) (glueBt m hm hbt (coatomOf P))
  rw [← heq, GlueCar.le_def] at hb
  have hval : (glueBt m hm hbt (coatomOf P)).1 = Sum.inr (Sum.inl (coatomOf P)) :=
    iotaB_generic_eq m (coatomOf P) hcob
  rw [hval] at hb
  exact not_leGlue_tagB_tagA m (coatomOf P) v hm hbt hcob hb

end ThetaGenericNotLe

section ThetaGenericNotGe
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]

-- [D-0664] isGLB_ne_bot_ne_top_atomOf
theorem isGLB_ne_bot_ne_top_atomOf (P : Type u) [Lattice P] [BoundedOrder P]
    [UniqueAtomCoatom P] : IsGLB {x : P | x ≠ ⊥ ∧ x ≠ ⊤} (atomOf P) := by
  constructor
  · rintro x ⟨hxb, _⟩; exact atomOf_le hxb
  · intro c hc
    rcases eq_or_ne (atomOf P) ⊤ with hat | hat
    · rw [hat]; exact le_top
    · exact hc ⟨atomOf_ne_bot P, hat⟩

-- [D-0665] incGlue_tagC_of_not_ge
theorem incGlue_tagC_of_not_ge (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvm : ¬ m ≤ v) (hvb : v ≠ ⊥) (z : GlueBase P) (hz : canon m z = z) :
    (¬ leGlue m z (Sum.inr (Sum.inr v)) ∧ ¬ leGlue m (Sum.inr (Sum.inr v)) z) ↔
      (∃ w, z = Sum.inr (Sum.inr w) ∧ w ≠ m ∧ ¬ w ≤ v ∧ ¬ v ≤ w) ∨
      (∃ x, z = Sum.inr (Sum.inl x) ∧ x ≠ ⊥ ∧ (x = ⊤ → ¬ v ≤ m)) := by
  rcases z with w | w | w
  · constructor
    · rintro ⟨h1, _⟩; exact absurd (leGlue_tagA_tagC m w v) h1
    · rintro (⟨w', hcon, _, _, _⟩ | ⟨x, hcon, _, _⟩) <;> cases hcon
  · have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hz
    constructor
    · rintro ⟨h1, h2⟩
      refine Or.inr ⟨w, rfl, hwb, fun hwt => ?_⟩
      intro hvm'
      rw [hwt] at h2
      exact h2 ((leGlue_tagC_tagB_top_iff m v).mpr hvm')
    · rintro (⟨w', hcon, _, _, _⟩ | ⟨x, hxeq, _, hcond⟩)
      · cases hcon
      · have hwx : w = x := by cases hxeq; rfl
        subst hwx
        rcases eq_or_ne w ⊤ with hwt | hwt
        · subst hwt
          exact ⟨fun hcon => hvm ((leGlue_tagB_tagC_iff m ⊤ v).mp hcon),
            fun hcon => (hcond rfl) ((leGlue_tagC_tagB_top_iff m v).mp hcon)⟩
        · exact ⟨fun hcon => hvm ((leGlue_tagB_tagC_iff m w v).mp hcon),
            not_leGlue_tagC_tagB m v w hwt⟩
  · obtain ⟨hwb, hwm⟩ := canon_inr_inr_ne m w hz
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨w, rfl, hwm, fun hle => h1 ((leGlue_tagC_tagC_iff m w v).mpr hle),
        fun hle => h2 ((leGlue_tagC_tagC_iff m v w).mpr hle)⟩
    · rintro (⟨w', hweq, _, hw1, hw2⟩ | ⟨x, hcon, _, _⟩)
      · have hww' : w = w' := by cases hweq; rfl
        subst hww'
        exact ⟨fun hcon => hw1 ((leGlue_tagC_tagC_iff m w v).mp hcon),
          fun hcon => hw2 ((leGlue_tagC_tagC_iff m v w).mp hcon)⟩
      · cases hcon

variable [UniqueAtomCoatom P]

-- [D-0666] isGLB_inc_tagC_of_not_ge
theorem isGLB_inc_tagC_of_not_ge (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvm : ¬ m ≤ v) (hvb : v ≠ ⊥) (hvne : v ≠ m) (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {i : P} (hib : i ≠ ⊥) (him : i ≠ m)
    (hi : IsGLB {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} i) :
    letI := glueLattice m hm hmt hbt
    IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueC m v hvb hvne ∧ ¬ glueC m v hvb hvne ≤ z}
      (glueC m i hib him ⊓ glueBt m hm hbt (atomOf P)) := by
  letI := glueLattice m hm hmt hbt
  have hat : atomOf P ≠ ⊤ := by
    obtain ⟨x, hxb, hxt⟩ := hne3
    intro heq
    exact hxt (top_le_iff.mp (heq ▸ atomOf_le hxb))
  have hvalB : ∀ y : P, y ≠ ⊥ → (glueBt m hm hbt y).1 = Sum.inr (Sum.inl y) :=
    fun y hy => iotaB_generic_eq m y hy
  have hmemC : ∀ w : P, (hwb : w ≠ ⊥) → (hwm : w ≠ m) → ¬ w ≤ v → ¬ v ≤ w →
      glueC m w hwb hwm ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueC m v hvb hvne ∧ ¬ glueC m v hvb hvne ≤ z} :=
    fun w _ _ hw1 hw2 => ⟨fun hcon => hw1 ((leGlue_tagC_tagC_iff m w v).mp hcon),
      fun hcon => hw2 ((leGlue_tagC_tagC_iff m v w).mp hcon)⟩
  have hmemB : ∀ x : P, x ≠ ⊥ → x ≠ ⊤ → glueBt m hm hbt x ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueC m v hvb hvne ∧ ¬ glueC m v hvb hvne ≤ z} := by
    intro x hxb hxt
    constructor
    · rw [GlueCar.le_def, hvalB x hxb]
      intro hcon; exact hvm ((leGlue_tagB_tagC_iff m x v).mp hcon)
    · rw [GlueCar.le_def, hvalB x hxb]
      exact not_leGlue_tagC_tagB m v x hxt
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    obtain ⟨w, hzeq, hwm, hw1, hw2⟩ | ⟨x, hzeq, hxb, _⟩ :=
      (incGlue_tagC_of_not_ge m hm hbt hvm hvb z.1 z.2).mp ⟨hz1, hz2⟩
    · have hwb : w ≠ ⊥ := fun heq => hw1 (heq ▸ bot_le)
      have hzeq2 : z = glueC m w hwb hwm := Subtype.ext hzeq
      rw [hzeq2]
      refine le_trans inf_le_left ?_
      rw [GlueCar.le_def]
      exact (leGlue_tagC_tagC_iff m i w).mpr (hi.1 ⟨hw1, hw2⟩)
    · have hzeq2 : z = glueBt m hm hbt x := by
        apply Subtype.ext; rw [hzeq]; exact (iotaB_generic_eq m x hxb).symm
      rw [hzeq2]
      exact le_trans inf_le_right ((glueBt_le_iff m hm hmt hbt (atomOf P) x).mpr
        (atomOf_le hxb))
  ·
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      apply le_inf
      · rw [GlueCar.le_def]; exact leGlue_tagA_tagC m w' i
      · obtain ⟨x, hxb, hxt⟩ := hne3
        have hzle := hz' (hmemB x hxb hxt)
        rw [GlueCar.le_def, hvalB x hxb] at hzle
        have hw'm : w' ≤ m := (leGlue_tagA_tagB_iff m w' x hxt).mp hzle
        rw [GlueCar.le_def, hvalB (atomOf P) (atomOf_ne_bot P)]
        exact (leGlue_tagA_tagB_iff m w' (atomOf P) hat).mpr hw'm
    ·
      have hw'b : w' ≠ ⊥ := canon_inr_inl_ne_bot m w' hzc
      have hzeq2 : (⟨Sum.inr (Sum.inl w'), hzc⟩ : GlueCar (P := P) m) = glueBt m hm hbt w' := by
        apply Subtype.ext
        exact (iotaB_generic_eq m w' hw'b).symm
      rw [hzeq2] at hz' ⊢
      apply le_inf
      · have hbound : ∀ w ∈ {w : P | ¬ w ≤ v ∧ ¬ v ≤ w}, m ≤ w := by
          intro w hw
          rcases eq_or_ne w m with hwm | hwm
          · rw [hwm]
          · have hwb : w ≠ ⊥ := fun heq => hw.1 (heq ▸ bot_le)
            have hzle := hz' (hmemC w hwb hwm hw.1 hw.2)
            rw [GlueCar.le_def, hvalB w' hw'b] at hzle
            exact (leGlue_tagB_tagC_iff m w' w).mp hzle
        have hmi : m ≤ i := hi.2 hbound
        rw [GlueCar.le_def, hvalB w' hw'b]
        exact (leGlue_tagB_tagC_iff m w' i).mpr hmi
      · have hbound : ∀ x ∈ {x : P | x ≠ ⊥ ∧ x ≠ ⊤}, w' ≤ x := by
          intro x hx
          have hzle := hz' (hmemB x hx.1 hx.2)
          rw [GlueCar.le_def, hvalB w' hw'b, hvalB x hx.1] at hzle
          exact (leGlue_tagB_tagB_iff m w' x hx.2 hw'b).mp hzle
        exact (glueBt_le_iff m hm hmt hbt w' (atomOf P)).mpr
          ((isGLB_ne_bot_ne_top_atomOf P).2 hbound)
    ·
      exfalso
      obtain ⟨x, hxb, hxt⟩ := hne3
      have hzle := hz' (hmemB x hxb hxt)
      rw [GlueCar.le_def, hvalB x hxb] at hzle
      exact not_leGlue_tagC_tagB m w' x hxt hzle

-- [D-0667] glueC_ne_isGLB_inc_tagC_of_not_ge
theorem glueC_ne_isGLB_inc_tagC_of_not_ge (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvne : v ≠ m) (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {i : P} (hib : i ≠ ⊥) (him : i ≠ m)
    (hi : IsGLB {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} i) :
    letI := glueLattice m hm hmt hbt
    glueC m v hvb hvne ≠ glueC m i hib him ⊓ glueBt m hm hbt (atomOf P) := by
  letI := glueLattice m hm hmt hbt
  have hat : atomOf P ≠ ⊤ := by
    obtain ⟨x, hxb, hxt⟩ := hne3
    intro heq
    exact hxt (top_le_iff.mp (heq ▸ atomOf_le hxb))
  intro heq
  have hle0 : glueC m i hib him ⊓ glueBt m hm hbt (atomOf P) ≤ glueBt m hm hbt (atomOf P) :=
    inf_le_right
  rw [← heq, GlueCar.le_def] at hle0
  have hval : (glueBt m hm hbt (atomOf P)).1 = Sum.inr (Sum.inl (atomOf P)) :=
    iotaB_generic_eq m (atomOf P) (atomOf_ne_bot P)
  rw [hval] at hle0
  exact not_leGlue_tagC_tagB m v (atomOf P) hat hle0

end ThetaGenericNotGe

section ThetaGenericCopyB
variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
variable [UniqueAtomCoatom P]

-- [D-0668] incGlue_tagB_iff
theorem incGlue_tagB_iff (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvt : v ≠ ⊤) (z : GlueBase P) (hz : canon m z = z) :
    (¬ leGlue m z (Sum.inr (Sum.inl v)) ∧ ¬ leGlue m (Sum.inr (Sum.inl v)) z) ↔
      (∃ x, z = Sum.inl x ∧ ¬ x ≤ m) ∨
      (∃ w, z = Sum.inr (Sum.inl w) ∧ w ≠ ⊥ ∧ ¬ w ≤ v ∧ ¬ v ≤ w) ∨
      (∃ y, z = Sum.inr (Sum.inr y) ∧ ¬ m ≤ y) := by
  rcases z with x | w | y
  · constructor
    · rintro ⟨h1, _⟩
      exact Or.inl ⟨x, rfl, fun hxm => h1 ((leGlue_tagA_tagB_iff m x v hvt).mpr hxm)⟩
    · rintro (⟨x', hxeq, hxm⟩ | ⟨w', hcon, _, _, _⟩ | ⟨y', hcon, _⟩)
      · have hxx' : x = x' := by cases hxeq; rfl
        subst hxx'
        exact ⟨fun hcon => hxm ((leGlue_tagA_tagB_iff m x v hvt).mp hcon),
          not_leGlue_tagB_tagA m v x hm hbt hvb⟩
      · cases hcon
      · cases hcon
  · have hwb : w ≠ ⊥ := canon_inr_inl_ne_bot m w hz
    constructor
    · rintro ⟨h1, h2⟩
      have hwt : w ≠ ⊤ := by
        intro hwt'; subst hwt'; exact h2 (leGlue_tagB_skelG3 m v)
      exact Or.inr (Or.inl ⟨w, rfl, hwb,
        fun hle => h1 ((leGlue_tagB_tagB_iff m w v hvt hwb).mpr hle),
        fun hle => h2 ((leGlue_tagB_tagB_iff m v w hwt hvb).mpr hle)⟩)
    · rintro (⟨x, hcon, _⟩ | ⟨w', hweq, hw'b, hw1, hw2⟩ | ⟨y, hcon, _⟩)
      · cases hcon
      · have hww' : w = w' := by cases hweq; rfl
        subst hww'
        refine ⟨fun hcon => hw1 ((leGlue_tagB_tagB_iff m w v hvt hwb).mp hcon), ?_⟩
        rcases eq_or_ne w ⊤ with hwt | hwt
        · subst hwt; exact absurd le_top hw2
        · exact fun hcon => hw2 ((leGlue_tagB_tagB_iff m v w hwt hvb).mp hcon)
      · cases hcon
  · constructor
    · rintro ⟨_, h2⟩
      exact Or.inr (Or.inr ⟨y, rfl, fun hmy => h2 ((leGlue_tagB_tagC_iff m v y).mpr hmy)⟩)
    · rintro (⟨x, hcon, _⟩ | ⟨w', hcon, _, _, _⟩ | ⟨y', hyeq, hmy⟩)
      · cases hcon
      · cases hcon
      · have hyy' : y = y' := by cases hyeq; rfl
        subst hyy'
        exact ⟨not_leGlue_tagC_tagB m y v hvt,
          fun hcon => hmy ((leGlue_tagB_tagC_iff m v y).mp hcon)⟩

-- [D-0669] isLUB_inc_tagB_of_ne_empty
theorem isLUB_inc_tagB_of_ne_empty (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvt : v ≠ ⊤)
    (hne : {w : P | ¬ w ≤ v ∧ ¬ v ≤ w}.Nonempty)
    {κ : P} (hκ : IsLUB {y : P | ¬ m ≤ y} κ) (hjm : κ ⊔ m ≠ m) :
    letI := glueCarPartialOrder m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z}
      (glueC m (κ ⊔ m)
        (fun heq => hm (le_bot_iff.mp (heq ▸ (le_sup_right : m ≤ κ ⊔ m)))) hjm) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hvalB : ∀ y : P, y ≠ ⊥ → (glueBt m hm hbt y).1 = Sum.inr (Sum.inl y) :=
    fun y hy => iotaB_generic_eq m y hy
  have hmemA : ∀ x : P, ¬ x ≤ m → glueA m x ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro x hxm
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inl x) rfl).mpr (Or.inl ⟨x, rfl, hxm⟩)
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.2
  have hmemB : ∀ w : P, w ≠ ⊥ → ¬ w ≤ v → ¬ v ≤ w → glueBt m hm hbt w ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro w hwb hw1 hw2
    have hcanon : canon m (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w) := by
      simp only [canon]; rw [if_neg hwb]
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inr (Sum.inl w)) hcanon).mpr
      (Or.inr (Or.inl ⟨w, rfl, hwb, hw1, hw2⟩))
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB w hwb, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB w hwb, hvalB v hvb]; exact hincpair.2
  have hmemC : ∀ (y : P) (_hmy : ¬ m ≤ y) (hyb : y ≠ ⊥) (hym : y ≠ m), glueC m y hyb hym ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro y hmy hyb hym
    have hcanon : canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y) := by
      simp only [canon]; rw [if_neg hyb, if_neg hym]
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inr (Sum.inr y)) hcanon).mpr
      (Or.inr (Or.inr ⟨y, rfl, hmy⟩))
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.2
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    have hz1' : ¬ leGlue m z.1 (Sum.inr (Sum.inl v)) := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz1 ((GlueCar.le_def m z (glueBt m hm hbt v)).mpr hcon)
    have hz2' : ¬ leGlue m (Sum.inr (Sum.inl v)) z.1 := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz2 ((GlueCar.le_def m (glueBt m hm hbt v) z).mpr hcon)
    obtain ⟨x, hzeq, hxm⟩ | ⟨w, hzeq, hwb, hw1, hw2⟩ | ⟨y, hzeq, hmy⟩ :=
      (incGlue_tagB_iff m hm hbt hvb hvt z.1 z.2).mp ⟨hz1', hz2'⟩
    · have hzeq2 : z = glueA m x := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      exact leGlue_tagA_tagC m x (κ ⊔ m)
    · have hzeq2 : z = glueBt m hm hbt w := by
        apply Subtype.ext; rw [hzeq]; exact (iotaB_generic_eq m w hwb).symm
      rw [hzeq2, GlueCar.le_def, hvalB w hwb]
      exact (leGlue_tagB_tagC_iff m w (κ ⊔ m)).mpr le_sup_right
    · have hzcanon : canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y) := hzeq ▸ z.2
      have hyb : y ≠ ⊥ := (canon_inr_inr_ne m y hzcanon).1
      have hym : y ≠ m := (canon_inr_inr_ne m y hzcanon).2
      have hzeq2 : z = glueC m y hyb hym := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      show leGlue m (Sum.inr (Sum.inr y)) (Sum.inr (Sum.inr (κ ⊔ m)))
      exact (leGlue_tagC_tagC_iff m y (κ ⊔ m)).mpr (le_trans (hκ.1 hmy) le_sup_left)
  ·
    have hex : ∃ y : P, ¬ m ≤ y ∧ ¬ y ≤ m := by
      by_contra hcon
      push_neg at hcon
      exact hjm (le_antisymm (sup_le (hκ.2 hcon) le_rfl) le_sup_right)
    obtain ⟨y0, hy01, hy02⟩ := hex
    have hy0b : y0 ≠ ⊥ := fun heq => hy02 (heq ▸ bot_le)
    have hy0m : y0 ≠ m := fun heq => hy01 (heq ▸ le_refl m)
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      exfalso
      obtain ⟨w, hw1, hw2⟩ := hne
      have hwb : w ≠ ⊥ := fun heq => hw1 (heq ▸ bot_le)
      have hzle := hz' (hmemB w hwb hw1 hw2)
      rw [GlueCar.le_def, hvalB w hwb] at hzle
      exact not_leGlue_tagB_tagA m w w' hm hbt hwb hzle
    ·
      exfalso
      have hzle := hz' (hmemC y0 hy01 hy0b hy0m)
      rw [GlueCar.le_def] at hzle
      rcases eq_or_ne w' ⊤ with hw't | hw't
      · subst hw't; exact hy02 ((leGlue_tagC_tagB_top_iff m y0).mp hzle)
      · exact absurd hzle (not_leGlue_tagC_tagB m y0 w' hw't)
    ·
      have hbound : ∀ y ∈ {y : P | ¬ m ≤ y}, y ≤ w' := by
        intro y hy
        have hym : y ≠ m := fun heq => hy (heq ▸ le_refl m)
        by_cases hyb : y = ⊥
        · subst hyb; exact bot_le
        · have hzle := hz' (hmemC y hy hyb hym)
          rw [GlueCar.le_def] at hzle
          exact (leGlue_tagC_tagC_iff m y w').mp hzle
      have hkw' : κ ≤ w' := hκ.2 hbound
      obtain ⟨w, hw1, hw2⟩ := hne
      have hwb : w ≠ ⊥ := fun heq => hw1 (heq ▸ bot_le)
      have hzle := hz' (hmemB w hwb hw1 hw2)
      rw [GlueCar.le_def, hvalB w hwb] at hzle
      have hmw' : m ≤ w' := (leGlue_tagB_tagC_iff m w w').mp hzle
      rw [GlueCar.le_def]
      exact (leGlue_tagC_tagC_iff m (κ ⊔ m) w').mpr (sup_le hkw' hmw')

-- [D-0670] isGLB_inc_tagB_of_ne_empty
theorem isGLB_inc_tagB_of_ne_empty (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvt : v ≠ ⊤)
    (hne : {w : P | ¬ w ≤ v ∧ ¬ v ≤ w}.Nonempty)
    {μ : P} (hμ : IsGLB {x : P | ¬ x ≤ m} μ) :
    letI := glueCarPartialOrder m hm hmt hbt
    IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z}
      (glueA m (μ ⊓ m)) := by
  letI := glueCarPartialOrder m hm hmt hbt
  have hvalB : ∀ y : P, y ≠ ⊥ → (glueBt m hm hbt y).1 = Sum.inr (Sum.inl y) :=
    fun y hy => iotaB_generic_eq m y hy
  have hmemA : ∀ x : P, ¬ x ≤ m → glueA m x ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro x hxm
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inl x) rfl).mpr (Or.inl ⟨x, rfl, hxm⟩)
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.2
  have hmemB : ∀ w : P, w ≠ ⊥ → ¬ w ≤ v → ¬ v ≤ w → glueBt m hm hbt w ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro w hwb hw1 hw2
    have hcanon : canon m (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w) := by
      simp only [canon]; rw [if_neg hwb]
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inr (Sum.inl w)) hcanon).mpr
      (Or.inr (Or.inl ⟨w, rfl, hwb, hw1, hw2⟩))
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB w hwb, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB w hwb, hvalB v hvb]; exact hincpair.2
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    have hz1' : ¬ leGlue m z.1 (Sum.inr (Sum.inl v)) := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz1 ((GlueCar.le_def m z (glueBt m hm hbt v)).mpr hcon)
    have hz2' : ¬ leGlue m (Sum.inr (Sum.inl v)) z.1 := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz2 ((GlueCar.le_def m (glueBt m hm hbt v) z).mpr hcon)
    obtain ⟨x, hzeq, hxm⟩ | ⟨w, hzeq, hwb, hw1, hw2⟩ | ⟨y, hzeq, hmy⟩ :=
      (incGlue_tagB_iff m hm hbt hvb hvt z.1 z.2).mp ⟨hz1', hz2'⟩
    · have hzeq2 : z = glueA m x := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      exact (tagA_iso m hm (μ ⊓ m) x).mpr (le_trans inf_le_left (hμ.1 hxm))
    · have hzeq2 : z = glueBt m hm hbt w := by
        apply Subtype.ext; rw [hzeq]; exact (iotaB_generic_eq m w hwb).symm
      rw [hzeq2, GlueCar.le_def, hvalB w hwb]
      have hwt : w ≠ ⊤ := fun heq => hw2 (heq ▸ le_top)
      exact (leGlue_tagA_tagB_iff m (μ ⊓ m) w hwt).mpr inf_le_right
    · have hzcanon : canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y) := hzeq ▸ z.2
      have hyb : y ≠ ⊥ := (canon_inr_inr_ne m y hzcanon).1
      have hym : y ≠ m := (canon_inr_inr_ne m y hzcanon).2
      have hzeq2 : z = glueC m y hyb hym := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      exact leGlue_tagA_tagC m (μ ⊓ m) y
  ·
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      have hbound : ∀ x ∈ {x : P | ¬ x ≤ m}, w' ≤ x := by
        intro x hx
        have hzle := hz' (hmemA x hx)
        rw [GlueCar.le_def] at hzle
        exact (tagA_iso m hm w' x).mp hzle
      have hwmu : w' ≤ μ := hμ.2 hbound
      obtain ⟨w, hw1, hw2⟩ := hne
      have hwb : w ≠ ⊥ := fun heq => hw1 (heq ▸ bot_le)
      have hzle := hz' (hmemB w hwb hw1 hw2)
      rw [GlueCar.le_def, hvalB w hwb] at hzle
      have hwt : w ≠ ⊤ := fun heq => hw2 (heq ▸ le_top)
      have hw'm : w' ≤ m := (leGlue_tagA_tagB_iff m w' w hwt).mp hzle
      rw [GlueCar.le_def]
      exact (tagA_iso m hm w' (μ ⊓ m)).mpr (le_inf hwmu hw'm)
    ·
      exfalso
      have hzle := hz' (hmemA ⊤ (fun h => hmt (top_le_iff.mp h)))
      rw [GlueCar.le_def] at hzle
      exact not_leGlue_tagB_tagA m w' ⊤ hm hbt (canon_inr_inl_ne_bot m w' hzc) hzle
    ·
      exfalso
      have hw'b : w' ≠ ⊥ := (canon_inr_inr_ne m w' hzc).1
      have hzle : leGlue m (Sum.inr (Sum.inr w')) (Sum.inl (⊤ : P)) := by
        have hthis := hz' (hmemA ⊤ (fun h => hmt (top_le_iff.mp h)))
        rwa [GlueCar.le_def] at hthis
      obtain ⟨u, hu, v', hv', huv⟩ := hzle
      have hu' : u = Sum.inr (Sum.inr w') := by simpa [occs] using hu
      subst hu'
      have hoccA : occs m (Sum.inl (⊤ : P)) = [Sum.inl (⊤ : P), Sum.inr (Sum.inr (⊥ : P))] := by
        simp [occs, Ne.symm hmt]
      rw [hoccA] at hv'
      have hv'' : v' = Sum.inl (⊤ : P) ∨ v' = Sum.inr (Sum.inr (⊥ : P)) := by simpa using hv'
      rcases hv'' with hv'' | hv''
      · subst hv''; exact huv.elim
      · subst hv''; exact hw'b (le_bot_iff.mp huv)

-- [D-0671] glueBt_ne_isGLB_of_glueC_inc
theorem glueBt_ne_isGLB_of_glueC_inc (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvt : v ≠ ⊤)
    {q : P} (hqb : q ≠ ⊥) (hqm : q ≠ m) (hqge : m ≤ q) :
    letI := glueCarPartialOrder m hm hmt hbt
    ¬ IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueC m q hqb hqm ∧ ¬ glueC m q hqb hqm ≤ z}
      (glueBt m hm hbt v) := by
  letI := glueCarPartialOrder m hm hmt hbt
  intro hgi
  have hlb : glueA m (⊤ : P) ∈ lowerBounds
      {z : GlueCar (P := P) m | ¬ z ≤ glueC m q hqb hqm ∧ ¬ glueC m q hqb hqm ≤ z} := by
    rintro z ⟨hz1, hz2⟩
    obtain ⟨zv, hzc⟩ := z
    rcases zv with w' | w' | w'
    · exact absurd ((GlueCar.le_def m ⟨Sum.inl w', hzc⟩ (glueC m q hqb hqm)).mpr
        (leGlue_tagA_tagC m w' q)) hz1
    · exact absurd ((GlueCar.le_def m ⟨Sum.inr (Sum.inl w'), hzc⟩ (glueC m q hqb hqm)).mpr
        ((leGlue_tagB_tagC_iff m w' q).mpr hqge)) hz1
    · rw [GlueCar.le_def]; exact leGlue_tagA_tagC m ⊤ w'
  have hle := hgi.2 hlb
  rw [GlueCar.le_def] at hle
  have hvalv : (glueBt m hm hbt v).1 = Sum.inr (Sum.inl v) := iotaB_generic_eq m v hvb
  rw [hvalv] at hle
  exact hmt (top_le_iff.mp ((leGlue_tagA_tagB_iff m ⊤ v hvt).mp hle))

-- [D-0672] isLUB_inc_tagB_of_inc_empty
theorem isLUB_inc_tagB_of_inc_empty (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {v : P} (hvb : v ≠ ⊥) (hvt : v ≠ ⊤)
    (hvinc : {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} = ∅)
    {κ : P} (hκ : IsLUB {y : P | ¬ m ≤ y} κ) (hκb : κ ≠ ⊥) (hκm : κ ≠ m) :
    letI := glueLattice m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z}
      (glueC m κ hκb hκm) := by
  letI := glueLattice m hm hmt hbt
  have hvalB : ∀ y : P, y ≠ ⊥ → (glueBt m hm hbt y).1 = Sum.inr (Sum.inl y) :=
    fun y hy => iotaB_generic_eq m y hy
  have hmemA : ∀ x : P, ¬ x ≤ m → glueA m x ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro x hxm
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inl x) rfl).mpr (Or.inl ⟨x, rfl, hxm⟩)
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.2
  have hmemC : ∀ (y : P) (_hmy : ¬ m ≤ y) (hyb : y ≠ ⊥) (hym : y ≠ m), glueC m y hyb hym ∈
      {z : GlueCar (P := P) m | ¬ z ≤ glueBt m hm hbt v ∧ ¬ glueBt m hm hbt v ≤ z} := by
    intro y hmy hyb hym
    have hcanon : canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y) := by
      simp only [canon]; rw [if_neg hyb, if_neg hym]
    have hincpair := (incGlue_tagB_iff m hm hbt hvb hvt (Sum.inr (Sum.inr y)) hcanon).mpr
      (Or.inr (Or.inr ⟨y, rfl, hmy⟩))
    refine ⟨?_, ?_⟩
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.1
    · rw [GlueCar.le_def, hvalB v hvb]; exact hincpair.2
  constructor
  ·
    rintro z ⟨hz1, hz2⟩
    have hz1' : ¬ leGlue m z.1 (Sum.inr (Sum.inl v)) := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz1 ((GlueCar.le_def m z (glueBt m hm hbt v)).mpr hcon)
    have hz2' : ¬ leGlue m (Sum.inr (Sum.inl v)) z.1 := by
      intro hcon; rw [← hvalB v hvb] at hcon
      exact hz2 ((GlueCar.le_def m (glueBt m hm hbt v) z).mpr hcon)
    obtain ⟨x, hzeq, hxm⟩ | ⟨w, hzeq, hwb, hw1, hw2⟩ | ⟨y, hzeq, hmy⟩ :=
      (incGlue_tagB_iff m hm hbt hvb hvt z.1 z.2).mp ⟨hz1', hz2'⟩
    · have hzeq2 : z = glueA m x := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      exact leGlue_tagA_tagC m x κ
    · exfalso
      have hmem : w ∈ {w : P | ¬ w ≤ v ∧ ¬ v ≤ w} := ⟨hw1, hw2⟩
      rw [hvinc] at hmem
      exact hmem
    · have hzcanon : canon m (Sum.inr (Sum.inr y)) = Sum.inr (Sum.inr y) := hzeq ▸ z.2
      have hyb : y ≠ ⊥ := (canon_inr_inr_ne m y hzcanon).1
      have hym : y ≠ m := (canon_inr_inr_ne m y hzcanon).2
      have hzeq2 : z = glueC m y hyb hym := Subtype.ext hzeq
      rw [hzeq2, GlueCar.le_def]
      show leGlue m (Sum.inr (Sum.inr y)) (Sum.inr (Sum.inr κ))
      exact (leGlue_tagC_tagC_iff m y κ).mpr (hκ.1 hmy)
  ·
    intro z' hz'
    obtain ⟨zv, hzc⟩ := z'
    rcases zv with w' | w' | w'
    ·
      exfalso
      have hex : ∃ y0 : P, ¬ m ≤ y0 ∧ y0 ≠ ⊥ := by
        by_contra hcon
        push_neg at hcon
        have hle : κ ≤ ⊥ := hκ.2 (fun y hy => le_of_eq (hcon y hy))
        exact hκb (le_bot_iff.mp hle)
      obtain ⟨y0, hy01, hy0b⟩ := hex
      have hy0m : y0 ≠ m := fun heq => hy01 (heq ▸ le_refl m)
      have hzle := hz' (hmemC y0 hy01 hy0b hy0m)
      rw [GlueCar.le_def] at hzle
      exact not_leGlue_tagC_tagA m y0 w' hy0b hzle
    ·
      rcases eq_or_ne w' ⊤ with hw't | hw't
      · subst hw't
        by_cases hkm : κ ≤ m
        · rw [GlueCar.le_def]
          exact (leGlue_tagC_tagB_top_iff m κ).mpr hkm
        · exfalso
          have hex1 : ∃ y1 : P, ¬ m ≤ y1 ∧ ¬ y1 ≤ m := by
            by_contra hcon
            push_neg at hcon
            exact hkm (hκ.2 (fun y hy => hcon y hy))
          obtain ⟨y1, hy11, hy12⟩ := hex1
          have hy1b : y1 ≠ ⊥ := fun heq => hy12 (heq ▸ bot_le)
          have hy1m : y1 ≠ m := fun heq => hy11 (heq ▸ le_refl m)
          have hzle := hz' (hmemC y1 hy11 hy1b hy1m)
          rw [GlueCar.le_def] at hzle
          exact hy12 ((leGlue_tagC_tagB_top_iff m y1).mp hzle)
      · exfalso
        have hzle := hz' (hmemA ⊤ (fun h => hmt (top_le_iff.mp h)))
        rw [GlueCar.le_def] at hzle
        exact hmt (top_le_iff.mp ((leGlue_tagA_tagB_iff m ⊤ w' hw't).mp hzle))
    ·
      have hbound : ∀ y ∈ {y : P | ¬ m ≤ y}, y ≤ w' := by
        intro y hy
        have hym : y ≠ m := fun heq => hy (heq ▸ le_refl m)
        by_cases hyb : y = ⊥
        · subst hyb; exact bot_le
        · have hzle := hz' (hmemC y hy hyb hym)
          rw [GlueCar.le_def] at hzle
          exact (leGlue_tagC_tagC_iff m y w').mp hzle
      have hkw' : κ ≤ w' := hκ.2 hbound
      rw [GlueCar.le_def]
      exact (leGlue_tagC_tagC_iff m κ w').mpr hkw'

-- [D-0673] glueC_inf_glueBt_atomOf_eq_iff
theorem glueC_inf_glueBt_atomOf_eq_iff (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {i : P} (hib : i ≠ ⊥) (him : i ≠ m) :
    letI := glueLattice m hm hmt hbt
    glueC m i hib him ⊓ glueBt m hm hbt (atomOf P) = glueBt m hm hbt (atomOf P) ↔ m ≤ i := by
  letI := glueLattice m hm hmt hbt
  have hval : (glueBt m hm hbt (atomOf P)).1 = Sum.inr (Sum.inl (atomOf P)) :=
    iotaB_generic_eq m (atomOf P) (atomOf_ne_bot P)
  rw [inf_eq_right, GlueCar.le_def, hval]
  exact leGlue_tagB_tagC_iff m (atomOf P) i

-- [D-0674] isGLB_inc_glueC_kappa_eq_glueBt_atomOf_iff
theorem isGLB_inc_glueC_kappa_eq_glueBt_atomOf_iff
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {κ : P} (hκb : κ ≠ ⊥) (hκm : κ ≠ m) (hκnge : ¬ m ≤ κ)
    {i : P} (hib : i ≠ ⊥) (him : i ≠ m)
    (hi : IsGLB {w : P | ¬ w ≤ κ ∧ ¬ κ ≤ w} i) :
    letI := glueLattice m hm hmt hbt
    IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueC m κ hκb hκm ∧ ¬ glueC m κ hκb hκm ≤ z}
      (glueBt m hm hbt (atomOf P)) ↔ m ≤ i := by
  letI := glueLattice m hm hmt hbt
  have hglb := isGLB_inc_tagC_of_not_ge m hm hmt hbt hκnge hκb hκm hne3 hib him hi
  constructor
  · intro h
    have heq := IsGLB.unique h hglb
    exact (glueC_inf_glueBt_atomOf_eq_iff m hm hmt hbt hib him).mp heq.symm
  · intro hmi
    have heq := (glueC_inf_glueBt_atomOf_eq_iff m hm hmt hbt hib him).mpr hmi
    exact heq ▸ hglb

-- [D-0675] glueB_atomOf_roundtrip_iff_of_not_ge
theorem glueB_atomOf_roundtrip_iff_of_not_ge
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {κ : P} (hκ : IsLUB {y : P | ¬ m ≤ y} κ) (hκb : κ ≠ ⊥) (hκm : κ ≠ m) (hκnge : ¬ m ≤ κ)
    {i : P} (hib : i ≠ ⊥) (him : i ≠ m)
    (hi : IsGLB {w : P | ¬ w ≤ κ ∧ ¬ κ ≤ w} i) :
    letI := glueLattice m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m |
        ¬ z ≤ glueBt m hm hbt (atomOf P) ∧ ¬ glueBt m hm hbt (atomOf P) ≤ z}
      (glueC m κ hκb hκm) ∧
    (IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueC m κ hκb hκm ∧ ¬ glueC m κ hκb hκm ≤ z}
      (glueBt m hm hbt (atomOf P)) ↔ m ≤ i) := by
  letI := glueLattice m hm hmt hbt
  have hat : atomOf P ≠ ⊤ := by
    obtain ⟨x, hxb, hxt⟩ := hne3
    intro heq; exact hxt (top_le_iff.mp (heq ▸ atomOf_le hxb))
  exact ⟨isLUB_inc_tagB_of_inc_empty m hm hmt hbt (atomOf_ne_bot P) hat
      (inc_atomOf_eq_empty P) hκ hκb hκm,
    isGLB_inc_glueC_kappa_eq_glueBt_atomOf_iff m hm hmt hbt hne3 hκb hκm hκnge hib him hi⟩

-- [D-0676] glueB_atomOf_not_roundtrip_of_ge
theorem glueB_atomOf_not_roundtrip_of_ge
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hne3 : ∃ x : P, x ≠ ⊥ ∧ x ≠ ⊤)
    {κ : P} (hκ : IsLUB {y : P | ¬ m ≤ y} κ) (hκb : κ ≠ ⊥) (hκm : κ ≠ m) (hκge : m ≤ κ) :
    letI := glueLattice m hm hmt hbt
    IsLUB {z : GlueCar (P := P) m |
        ¬ z ≤ glueBt m hm hbt (atomOf P) ∧ ¬ glueBt m hm hbt (atomOf P) ≤ z}
      (glueC m κ hκb hκm) ∧
    ¬ IsGLB {z : GlueCar (P := P) m | ¬ z ≤ glueC m κ hκb hκm ∧ ¬ glueC m κ hκb hκm ≤ z}
      (glueBt m hm hbt (atomOf P)) := by
  letI := glueLattice m hm hmt hbt
  have hat : atomOf P ≠ ⊤ := by
    obtain ⟨x, hxb, hxt⟩ := hne3
    intro heq; exact hxt (top_le_iff.mp (heq ▸ atomOf_le hxb))
  exact ⟨isLUB_inc_tagB_of_inc_empty m hm hmt hbt (atomOf_ne_bot P) hat
      (inc_atomOf_eq_empty P) hκ hκb hκm,
    glueBt_ne_isGLB_of_glueC_inc m hm hmt hbt (atomOf_ne_bot P) hat hκb hκm hκge⟩

end ThetaGenericCopyB

section GlueCarSuccCardJoinIrredMarked

variable {Q0 : Type u} [Fintype Q0] [DecidableEq Q0] [Lattice Q0] [BoundedOrder Q0]
  [UniqueAtomCoatom Q0]

-- [D-0677] card_joinIrred_eq_succ_of_joinIrred
theorem card_joinIrred_eq_succ_of_joinIrred {m : Q0} (hm : JoinIrred Q0 m) :
    Fintype.card {x : Q0 // JoinIrred Q0 x} =
      Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ m} + 1 := by
  have e : {x : Q0 // JoinIrred Q0 x} ≃
      ({x : Q0 // JoinIrred Q0 x ∧ x ≠ m} ⊕ Unit) := by
    refine ⟨fun z => if h : z.1 = m then Sum.inr () else Sum.inl ⟨z.1, z.2, h⟩,
      Sum.elim (fun w => ⟨w.1, w.2.1⟩) (fun _ => ⟨m, hm⟩), ?_, ?_⟩
    · rintro ⟨v, hv⟩
      by_cases h : v = m
      · subst h; simp
      · simp [h]
    · rintro (⟨w, hw1, hw2⟩ | ⟨⟩)
      · simp [hw2]
      · simp
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit]

-- [D-0678] card_joinIrred_glueCar_gen_of_joinIrred
theorem card_joinIrred_glueCar_gen_of_joinIrred (m : Q0) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : Q0) ≠ ⊤) (hcard : 3 ≤ Fintype.card Q0) (hjm : JoinIrred Q0 m) :
    letI := glueLattice m hm hmt hbt
    letI := glueBoundedOrder m hm hmt hbt
    Fintype.card {f : GlueCar (P := Q0) m // JoinIrred (GlueCar (P := Q0) m) f} =
      3 * Fintype.card {x : Q0 // JoinIrred Q0 x} - 2 := by
  letI := glueLattice m hm hmt hbt
  letI := glueBoundedOrder m hm hmt hbt
  rw [← Fintype.card_congr (jiGlueCarSuccEquiv m hm hmt hbt hcard)]
  rw [Fintype.card_sum, Fintype.card_sum]
  have hB : Fintype.card {x : Q0 // JoinIrred Q0 x} =
      Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ (⊤ : Q0)} + 1 :=
    card_joinIrred_eq_succ_of_ne_top (joinIrred_top hbt)
  have hC : Fintype.card {x : Q0 // JoinIrred Q0 x} =
      Fintype.card {x : Q0 // JoinIrred Q0 x ∧ x ≠ m} + 1 :=
    card_joinIrred_eq_succ_of_joinIrred hjm
  omega

end GlueCarSuccCardJoinIrredMarked

section ConstHomJoinIrred

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
  [UniqueAtomCoatom P]

-- [D-0679] joinIrred_constHom_iff
theorem joinIrred_constHom_iff (v : P) :
    JoinIrred (EndP P) (constHom v) ↔ JoinIrred P v := by
  letI := endPUniqueAtomCoatom (P := P)
  rw [← hasUniqueDownCover_iff_joinIrred, ← hasUniqueDownCover_iff_joinIrred,
    hasUniqueDownCover_constHom_iff]

-- [D-0680] card_joinIrred_glueCar_endP_constHom
theorem card_joinIrred_glueCar_endP_constHom (mid : P) (hmb : mid ≠ ⊥) (hmt : mid ≠ ⊤)
    (hbt : (⊥ : P) ≠ ⊤) (hcard : 3 ≤ Fintype.card P) (hji : JoinIrred P mid) :
    letI hm : (constHom mid : EndP P) ≠ ⊥ := fun h =>
      hmb (constHom_injective (h.trans (by ext x; rfl)))
    letI hmt' : (constHom mid : EndP P) ≠ ⊤ := fun h =>
      hmt (constHom_injective (h.trans endP_top_eq_constHom_top))
    letI hbtQ := endP_bot_ne_top hbt
    letI := glueLattice (constHom mid : EndP P) hm hmt' hbtQ
    letI := glueBoundedOrder (constHom mid : EndP P) hm hmt' hbtQ
    Fintype.card {f : GlueCar (P := EndP P) (constHom mid) //
        JoinIrred (GlueCar (P := EndP P) (constHom mid)) f} =
      3 * Fintype.card {x : P // JoinIrred P x} * Fintype.card P - 2 := by
  have hm : (constHom mid : EndP P) ≠ ⊥ := fun h =>
    hmb (constHom_injective (h.trans (by ext x; rfl)))
  have hmt' : (constHom mid : EndP P) ≠ ⊤ := fun h =>
    hmt (constHom_injective (h.trans endP_top_eq_constHom_top))
  have hbtQ := endP_bot_ne_top (P := P) hbt
  letI := glueLattice (constHom mid : EndP P) hm hmt' hbtQ
  letI := glueBoundedOrder (constHom mid : EndP P) hm hmt' hbtQ
  letI := endPUniqueAtomCoatom (P := P)
  have hcardQ : 3 ≤ Fintype.card (EndP P) :=
    le_trans hcard (Fintype.card_le_of_injective constHom constHom_injective)
  have hjm : JoinIrred (EndP P) (constHom mid) := (joinIrred_constHom_iff mid).mpr hji
  have hmain := card_joinIrred_glueCar_gen_of_joinIrred (constHom mid : EndP P)
    hm hmt' hbtQ hcardQ hjm
  have hprod : Fintype.card {x : EndP P // JoinIrred (EndP P) x} =
      Fintype.card P * Fintype.card {x : P // JoinIrred P x} := by
    rw [← Fintype.card_congr (jiEquiv (P := P)), Fintype.card_prod]
  rw [hprod] at hmain
  rw [hmain]
  ring_nf

end ConstHomJoinIrred

end GluingTowerLibrary
