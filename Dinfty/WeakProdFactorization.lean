import Dinfty.AtomFactorGeneration

-- [D-1763] §Unique-factorization-for-restricted-products
open scoped Classical

universe u v

namespace WeakProdFactorization

open WeakProductAbsorption AtomFactorGeneration

-- [D-1764] §Atom-factors-correspond-along-an-isomorphism
-- [D-1765] atomFactorIso
def atomFactorIso {L : Type u} {L' : Type v} [PartialOrder L] [OrderBot L]
    [PartialOrder L'] [OrderBot L'] (e : L ≃o L') (α : L) :
    ↥(atomFactor L α) ≃o ↥(atomFactor L' (e α)) where
  toFun w := ⟨e w.1, mem_atomFactor_map e α w.2⟩
  invFun v := ⟨e.symm v.1, by
    have h := mem_atomFactor_map e.symm (e α) v.2
    rwa [e.symm_apply_apply] at h⟩
  left_inv w := Subtype.ext (e.symm_apply_apply w.1)
  right_inv v := Subtype.ext (e.apply_symm_apply v.1)
  map_rel_iff' := e.map_rel_iff

-- [D-1766] §The-axes-of-a-restricted-product
section Axis

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable (lam : ∀ j, D j)
variable (hlam_ne : ∀ j, lam j ≠ ⊥) (hlam_le : ∀ j (z : D j), z ≠ ⊥ → lam j ≤ z)

include hlam_ne hlam_le

-- [D-1767] single_lam_inj
theorem single_lam_inj {i j : ℕ} (h : (single i (lam i) : WeakProd D) = single j (lam j)) :
    i = j := by
  by_contra hij
  have hval := congrFun (congrArg Subtype.val h) i
  rw [single_apply_self, single_apply_ne hij] at hval
  exact hlam_ne i hval

-- [D-1768] eq_single_of_mem_atomFactor
theorem eq_single_of_mem_atomFactor {j : ℕ} {w : WeakProd D}
    (hw : w ∈ atomFactor (WeakProd D) (single j (lam j))) :
    w = single j (w.1 j) := by
  apply Subtype.ext
  funext i
  by_cases hij : i = j
  · subst hij
    rw [single_apply_self]
  · rw [single_apply_ne hij]
    exact atomFactor_single lam hlam_ne hlam_le hw i hij

-- [D-1769] axisIso
noncomputable def axisIso (j : ℕ) :
    ↥(atomFactor (WeakProd D) (single j (lam j))) ≃o D j where
  toFun w := w.1.1 j
  invFun a := ⟨single j a, mem_atomFactor_single lam hlam_ne hlam_le a⟩
  left_inv w := by
    apply Subtype.ext
    exact (eq_single_of_mem_atomFactor lam hlam_ne hlam_le w.2).symm
  right_inv a := single_apply_self j a
  map_rel_iff' := by
    intro w w'
    constructor
    · intro h i
      by_cases hij : i = j
      · subst hij
        exact h
      · rw [atomFactor_single lam hlam_ne hlam_le w.2 i hij]
        exact bot_le
    · intro h
      exact h j

end Axis

-- [D-1770] §The-induced-permutation-of-factors
section Transfer

variable {D : ℕ → Type u} {E : ℕ → Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

-- [D-1771] exists_transfer
theorem exists_transfer (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    ∃ i : ℕ, e (single j (lamD j)) = single i (lamE i) :=
  atom_eq_single lamE hE_ne hE_le
    (orderIso_isAtom e (isAtom_single lamD hD_ne hD_le j))

-- [D-1772] transferIndex
noncomputable def transferIndex (e : WeakProd D ≃o WeakProd E) (j : ℕ) : ℕ :=
  (exists_transfer lamD lamE hD_ne hD_le hE_ne hE_le e j).choose

-- [D-1773] transferIndex_eq
theorem transferIndex_eq (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    e (single j (lamD j)) = single (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)
      (lamE (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)) :=
  (exists_transfer lamD lamE hD_ne hD_le hE_ne hE_le e j).choose_spec

-- [D-1774] transferIndex_spec
theorem transferIndex_spec (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    Nonempty (D j ≃o E (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)) := by
  refine ⟨((axisIso lamD hD_ne hD_le j).symm.trans
    (atomFactorIso e (single j (lamD j)))).trans ?_⟩
  rw [transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j]
  exact axisIso lamE hE_ne hE_le _

-- [D-1775] transferIndex_injective
theorem transferIndex_injective (e : WeakProd D ≃o WeakProd E) :
    Function.Injective (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e) := by
  intro j j' h
  have h1 := transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j
  have h2 := transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j'
  rw [h] at h1
  exact single_lam_inj lamD hD_ne hD_le (e.injective (h1.trans h2.symm))

-- [D-1776] transferIndex_surjective
theorem transferIndex_surjective (e : WeakProd D ≃o WeakProd E) :
    Function.Surjective (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e) := by
  intro i
  obtain ⟨j, hj⟩ := atom_eq_single lamD hD_ne hD_le
    (orderIso_isAtom e.symm (isAtom_single lamE hE_ne hE_le i))
  refine ⟨j, ?_⟩
  have himg : e (single j (lamD j)) = single i (lamE i) := by
    rw [← hj, e.apply_symm_apply]
  have heq := transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j
  exact single_lam_inj lamE hE_ne hE_le (heq.symm.trans himg)

-- [D-1777] weakProd_uniqueFactorization
theorem weakProd_uniqueFactorization (e : WeakProd D ≃o WeakProd E) :
    ∃ σ : ℕ → ℕ, Function.Bijective σ ∧ ∀ j, Nonempty (D j ≃o E (σ j)) :=
  ⟨transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e,
   ⟨transferIndex_injective lamD lamE hD_ne hD_le hE_ne hE_le e,
    transferIndex_surjective lamD lamE hD_ne hD_le hE_ne hE_le e⟩,
   transferIndex_spec lamD lamE hD_ne hD_le hE_ne hE_le e⟩

end Transfer

-- [D-1778] §Factors-of-a-product-with-a-finite-piece
section ProdFactor

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic A]

-- [D-1779] mem_atomFactor_prod_right
theorem mem_atomFactor_prod_right {β : B} {p : A × B} :
    p ∈ atomFactor (A × B) (((⊥ : A), β)) ↔ p.1 = ⊥ ∧ p.2 ∈ atomFactor B β := by
  constructor
  · intro hmem
    have hp1 : p.1 = ⊥ := by
      by_contra hne
      obtain ⟨α, hα, hαle⟩ := (IsAtomic.eq_bot_or_exists_atom_le p.1).resolve_left hne
      have hat : IsAtom ((α, (⊥ : B)) : A × B) := prodIsAtom_iff.mpr (Or.inl ⟨hα, rfl⟩)
      have heq := hmem _ hat ⟨hαle, bot_le⟩
      exact hα.1 (congrArg Prod.fst heq)
    refine ⟨hp1, ?_⟩
    intro β' hβ' hβ'le
    have hat : IsAtom (((⊥ : A), β') : A × B) := prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ'⟩)
    exact congrArg Prod.snd (hmem _ hat ⟨bot_le, hβ'le⟩)
  · rintro ⟨hp1, hp2⟩
    rintro ⟨c, d⟩ hcd hle
    rcases prodIsAtom_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exfalso
      have h2 : c ≤ (⊥ : A) := by
        rw [← hp1]
        exact hle.1
      exact hc.1 (le_bot_iff.mp h2)
    · exact Prod.ext hc (hp2 d hd hle.2)

-- [D-1780] atomFactorProdRightIso
def atomFactorProdRightIso (β : B) :
    ↥(atomFactor (A × B) (((⊥ : A), β))) ≃o ↥(atomFactor B β) where
  toFun p := ⟨p.1.2, (mem_atomFactor_prod_right.mp p.2).2⟩
  invFun b := ⟨((⊥ : A), b.1), mem_atomFactor_prod_right.mpr ⟨rfl, b.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (mem_atomFactor_prod_right.mp p.2).1.symm rfl
  right_inv b := rfl
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [(mem_atomFactor_prod_right.mp p.2).1, (mem_atomFactor_prod_right.mp q.2).1]
    · intro h
      exact h.2

end ProdFactor

-- [D-1781] §The-copy-A-input-a-finite-piece-s-factors-are
section FinitePiece

variable {D : ℕ → Type u} {E : ℕ → Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable [PartialOrder S] [OrderBot S]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

-- [D-1782] factor_of_prod
theorem factor_of_prod (e : WeakProd D ≃o (WeakProd E × S)) (β : S) (hβ : IsAtom β) :
    ∃ j : ℕ, Nonempty (↥(atomFactor S β) ≃o D j) := by
  haveI : IsAtomic (WeakProd E) := isAtomic_weakProd lamE hE_ne hE_le
  have hat : IsAtom (((⊥ : WeakProd E), β)) := prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ⟩)
  obtain ⟨j, hj⟩ := atom_eq_single lamD hD_ne hD_le (orderIso_isAtom e.symm hat)
  have hej : e (single j (lamD j)) = ((⊥ : WeakProd E), β) := by
    rw [← hj, e.apply_symm_apply]
  have i1 : ↥(atomFactor S β) ≃o ↥(atomFactor (WeakProd E × S) (((⊥ : WeakProd E), β))) :=
    (atomFactorProdRightIso (A := WeakProd E) β).symm
  have i2 : ↥(atomFactor (WeakProd E × S) (e (single j (lamD j))))
      ≃o ↥(atomFactor (WeakProd D) (single j (lamD j))) :=
    (atomFactorIso e (single j (lamD j))).symm
  rw [hej] at i2
  exact ⟨j, ⟨(i1.trans i2).trans (axisIso lamD hD_ne hD_le j)⟩⟩

-- [D-1783] factor_index_lt
theorem factor_index_lt [∀ j, Fintype (D j)] [Fintype S] {N : ℕ}
    (hmono : StrictMono (fun j => Fintype.card (D j)))
    (e : WeakProd D ≃o (WeakProd E × S)) (β : S) (hβ : IsAtom β)
    (hcard : Fintype.card ↥(atomFactor S β) < Fintype.card (D N)) :
    ∃ j, j < N ∧ Nonempty (↥(atomFactor S β) ≃o D j) := by
  obtain ⟨j, ⟨iso⟩⟩ := factor_of_prod lamD lamE hD_ne hD_le hE_ne hE_le e β hβ
  refine ⟨j, ?_, ⟨iso⟩⟩
  have hc : Fintype.card (D j) = Fintype.card ↥(atomFactor S β) :=
    (Fintype.card_congr iso.toEquiv).symm
  by_contra hge
  push_neg at hge
  have h2 : Fintype.card (D N) ≤ Fintype.card (D j) := hmono.le_iff_le.mpr hge
  omega

end FinitePiece

-- [D-1784] §The-left-hand-factor-and-the-converse-direction
section ProdFactorLeft

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic B]

-- [D-1785] mem_atomFactor_prod_left
theorem mem_atomFactor_prod_left {α : A} {p : A × B} :
    p ∈ atomFactor (A × B) ((α, (⊥ : B))) ↔ p.2 = ⊥ ∧ p.1 ∈ atomFactor A α := by
  constructor
  · intro hmem
    have hp2 : p.2 = ⊥ := by
      by_contra hne
      obtain ⟨β, hβ, hβle⟩ := (IsAtomic.eq_bot_or_exists_atom_le p.2).resolve_left hne
      have hat : IsAtom (((⊥ : A), β) : A × B) := prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ⟩)
      have heq := hmem _ hat ⟨bot_le, hβle⟩
      exact hβ.1 (congrArg Prod.snd heq)
    refine ⟨hp2, ?_⟩
    intro α' hα' hα'le
    have hat : IsAtom ((α', (⊥ : B)) : A × B) := prodIsAtom_iff.mpr (Or.inl ⟨hα', rfl⟩)
    exact congrArg Prod.fst (hmem _ hat ⟨hα'le, bot_le⟩)
  · rintro ⟨hp2, hp1⟩
    rintro ⟨c, d⟩ hcd hle
    rcases prodIsAtom_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Prod.ext (hp1 c hc hle.1) hd
    · exfalso
      have h2 : d ≤ (⊥ : B) := by
        rw [← hp2]
        exact hle.2
      exact hd.1 (le_bot_iff.mp h2)

-- [D-1786] atomFactorProdLeftIso
def atomFactorProdLeftIso (α : A) :
    ↥(atomFactor (A × B) ((α, (⊥ : B)))) ≃o ↥(atomFactor A α) where
  toFun p := ⟨p.1.1, (mem_atomFactor_prod_left.mp p.2).2⟩
  invFun a := ⟨(a.1, (⊥ : B)), mem_atomFactor_prod_left.mpr ⟨rfl, a.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (mem_atomFactor_prod_left.mp p.2).1.symm
  right_inv a := rfl
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      refine ⟨h, ?_⟩
      rw [(mem_atomFactor_prod_left.mp p.2).1, (mem_atomFactor_prod_left.mp q.2).1]
    · intro h
      exact h.1

end ProdFactorLeft

section Converse

variable {D : ℕ → Type u} {E : ℕ → Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

-- [D-1787] factor_index_of_prod
theorem factor_index_of_prod (e : WeakProd D ≃o (WeakProd E × S)) (j : ℕ) :
    (∃ i, Nonempty (D j ≃o E i))
      ∨ (∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β))) := by
  haveI : IsAtomic (WeakProd E) := isAtomic_weakProd lamE hE_ne hE_le
  have hat : IsAtom (e (single j (lamD j))) :=
    orderIso_isAtom e (isAtom_single lamD hD_ne hD_le j)
  have hbase : ↥(atomFactor (WeakProd D) (single j (lamD j)))
      ≃o ↥(atomFactor (WeakProd E × S) (e (single j (lamD j)))) :=
    atomFactorIso e (single j (lamD j))
  rcases prodIsAtom_iff.mp hat with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨i, hi⟩ := atom_eq_single lamE hE_ne hE_le h1
    have hsplit : e (single j (lamD j)) = ((single i (lamE i) : WeakProd E), (⊥ : S)) :=
      Prod.ext hi h2
    rw [hsplit] at hbase
    exact Or.inl ⟨i, ⟨((axisIso lamD hD_ne hD_le j).symm.trans hbase).trans
      ((atomFactorProdLeftIso (B := S) (single i (lamE i))).trans
        (axisIso lamE hE_ne hE_le i))⟩⟩
  · have hsplit : e (single j (lamD j)) = (((⊥ : WeakProd E)), (e (single j (lamD j))).2) :=
      Prod.ext h1 rfl
    rw [hsplit] at hbase
    exact Or.inr ⟨(e (single j (lamD j))).2, h2,
      ⟨((axisIso lamD hD_ne hD_le j).symm.trans hbase).trans
        (atomFactorProdRightIso (A := WeakProd E) _)⟩⟩

-- [D-1788] factor_in_finite_piece
theorem factor_in_finite_piece [∀ j, Fintype (D j)] [∀ i, Fintype (E i)]
    (e : WeakProd D ≃o (WeakProd E × S)) (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i)) :
    ∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β)) := by
  rcases factor_index_of_prod lamD lamE hD_ne hD_le hE_ne hE_le e j with ⟨i, ⟨iso⟩⟩ | h
  · exact absurd (Fintype.card_congr iso.toEquiv) (Nat.ne_of_lt (hsmall i))
  · exact h

end Converse

-- [D-1789] §The-copy-A-exclusion-assembled
section CopyA

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic A] [IsAtomic B] [Fintype A] [Fintype B]

-- [D-1790] card_atomFactor_le
theorem card_atomFactor_le {X : Type u} [PartialOrder X] [OrderBot X] [Fintype X]
    (x : X) : Fintype.card ↥(atomFactor X x) ≤ Fintype.card X :=
  Fintype.card_le_of_injective (fun w => w.1) (fun _ _ h => Subtype.ext h)

-- [D-1791] card_atomFactor_prod_le
theorem card_atomFactor_prod_le {γ : A × B} (hγ : IsAtom γ) :
    Fintype.card ↥(atomFactor (A × B) γ) ≤ Fintype.card A
      ∨ Fintype.card ↥(atomFactor (A × B) γ) ≤ Fintype.card B := by
  obtain ⟨a, b⟩ := γ
  rcases prodIsAtom_iff.mp hγ with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    have hb' : b = ⊥ := hb
    subst hb'
    have := Fintype.card_congr (atomFactorProdLeftIso (B := B) a).toEquiv
    rw [this]
    exact card_atomFactor_le a
  · right
    have ha' : a = ⊥ := ha
    subst ha'
    have := Fintype.card_congr (atomFactorProdRightIso (A := A) b).toEquiv
    rw [this]
    exact card_atomFactor_le b

variable {D : ℕ → Type u} {E : ℕ → Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

-- [D-1792] no_iso_of_small_pieces
theorem no_iso_of_small_pieces [∀ j, Fintype (D j)] [∀ i, Fintype (E i)] (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i))
    (hA : Fintype.card A < Fintype.card (D j))
    (hB : Fintype.card B < Fintype.card (D j)) :
    IsEmpty (WeakProd D ≃o (WeakProd E × (A × B))) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨β, hβ, ⟨iso⟩⟩ :=
    factor_in_finite_piece lamD lamE hD_ne hD_le hE_ne hE_le e j hsmall
  have hcard : Fintype.card (D j) = Fintype.card ↥(atomFactor (A × B) β) :=
    Fintype.card_congr iso.toEquiv
  rcases card_atomFactor_prod_le hβ with h | h <;> omega

end CopyA

-- [D-1793] §A-finite-piece-on-the-left-as-well
section LeftPiece

variable {D : ℕ → Type u} {E : ℕ → Type u} {T : Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable [PartialOrder T] [OrderBot T] [IsAtomic T]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

-- [D-1794] isAtom_singleL
include hD_ne hD_le in
theorem isAtom_singleL (j : ℕ) :
    IsAtom (((single j (lamD j) : WeakProd D), (⊥ : T))) :=
  prodIsAtom_iff.mpr (Or.inl ⟨isAtom_single lamD hD_ne hD_le j, rfl⟩)

-- [D-1795] axisIsoL
include hD_ne hD_le in
noncomputable def axisIsoL (j : ℕ) :
    ↥(atomFactor (WeakProd D × T) (((single j (lamD j) : WeakProd D), (⊥ : T)))) ≃o D j :=
  (atomFactorProdLeftIso (B := T) (single j (lamD j))).trans (axisIso lamD hD_ne hD_le j)

-- [D-1796] factor_index_of_prodL
include hD_ne hD_le hE_ne hE_le in
theorem factor_index_of_prodL (e : (WeakProd D × T) ≃o (WeakProd E × S)) (j : ℕ) :
    (∃ i, Nonempty (D j ≃o E i))
      ∨ (∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β))) := by
  haveI : IsAtomic (WeakProd E) := isAtomic_weakProd lamE hE_ne hE_le
  have hat : IsAtom (e (((single j (lamD j) : WeakProd D), (⊥ : T)))) :=
    orderIso_isAtom e (isAtom_singleL (T := T) lamD hD_ne hD_le j)
  have hbase : ↥(atomFactor (WeakProd D × T)
        (((single j (lamD j) : WeakProd D), (⊥ : T))))
      ≃o ↥(atomFactor (WeakProd E × S) (e (((single j (lamD j) : WeakProd D), (⊥ : T))))) :=
    atomFactorIso e _
  rcases prodIsAtom_iff.mp hat with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨i, hi⟩ := atom_eq_single lamE hE_ne hE_le h1
    have hsplit : e (((single j (lamD j) : WeakProd D), (⊥ : T)))
        = ((single i (lamE i) : WeakProd E), (⊥ : S)) := Prod.ext hi h2
    rw [hsplit] at hbase
    exact Or.inl ⟨i, ⟨((axisIsoL (T := T) lamD hD_ne hD_le j).symm.trans hbase).trans
      ((atomFactorProdLeftIso (B := S) (single i (lamE i))).trans
        (axisIso lamE hE_ne hE_le i))⟩⟩
  · have hsplit : e (((single j (lamD j) : WeakProd D), (⊥ : T)))
        = (((⊥ : WeakProd E)), (e (((single j (lamD j) : WeakProd D), (⊥ : T)))).2) :=
      Prod.ext h1 rfl
    rw [hsplit] at hbase
    exact Or.inr ⟨(e (((single j (lamD j) : WeakProd D), (⊥ : T)))).2, h2,
      ⟨((axisIsoL (T := T) lamD hD_ne hD_le j).symm.trans hbase).trans
        (atomFactorProdRightIso (A := WeakProd E) _)⟩⟩

-- [D-1797] factor_in_finite_pieceL
include hD_ne hD_le hE_ne hE_le in
theorem factor_in_finite_pieceL [∀ j, Fintype (D j)] [∀ i, Fintype (E i)]
    (e : (WeakProd D × T) ≃o (WeakProd E × S)) (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i)) :
    ∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β)) := by
  rcases factor_index_of_prodL (T := T) lamD lamE hD_ne hD_le hE_ne hE_le e j with
    ⟨i, ⟨iso⟩⟩ | h
  · exact absurd (Fintype.card_congr iso.toEquiv) (Nat.ne_of_lt (hsmall i))
  · exact h

-- [D-1798] no_iso_of_small_piecesL
include hD_ne hD_le hE_ne hE_le in
theorem no_iso_of_small_piecesL {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A]
    [PartialOrder B] [OrderBot B] [IsAtomic A] [IsAtomic B] [Fintype A] [Fintype B]
    [∀ j, Fintype (D j)] [∀ i, Fintype (E i)] (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i))
    (hA : Fintype.card A < Fintype.card (D j))
    (hB : Fintype.card B < Fintype.card (D j)) :
    IsEmpty ((WeakProd D × T) ≃o (WeakProd E × (A × B))) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨β, hβ, ⟨iso⟩⟩ :=
    factor_in_finite_pieceL (T := T) lamD lamE hD_ne hD_le hE_ne hE_le e j hsmall
  have hcard : Fintype.card (D j) = Fintype.card ↥(atomFactor (A × B) β) :=
    Fintype.card_congr iso.toEquiv
  rcases card_atomFactor_prod_le hβ with h | h <;> omega

end LeftPiece

end WeakProdFactorization
