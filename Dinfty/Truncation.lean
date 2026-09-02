import Dinfty.WeakProdFactorization

-- [D-3024] §The-definable-finite-truncation
open scoped Classical

universe u v

namespace Truncation

open WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization

-- [D-3025] §The-truncation-and-its-invariance
section Def

variable {L : Type u} {L' : Type v} [PartialOrder L] [OrderBot L]
variable [PartialOrder L'] [OrderBot L']

-- [D-3026] smallPart
def smallPart (L : Type u) [PartialOrder L] [OrderBot L] (N : ℕ) : Set L :=
  {p | ∀ β : L, IsAtom β → β ≤ p → Nat.card ↥(atomFactor L β) ≤ N}

-- [D-3027] mem_smallPart_map
theorem mem_smallPart_map (e : L ≃o L') (N : ℕ) {p : L} :
    p ∈ smallPart L N ↔ e p ∈ smallPart L' N := by
  constructor
  · intro h γ hγ hγp
    have hpre : IsAtom (e.symm γ) := by
      have := orderIso_isAtom e.symm hγ
      exact this
    have hle : e.symm γ ≤ p := by
      have := (OrderIso.le_iff_le e.symm).mpr hγp
      rwa [e.symm_apply_apply] at this
    have hcard := Nat.card_congr (atomFactorIso e (e.symm γ)).toEquiv
    rw [e.apply_symm_apply] at hcard
    exact hcard ▸ h _ hpre hle
  · intro h β hβ hβp
    have hcard := Nat.card_congr (atomFactorIso e β).toEquiv
    exact hcard ▸ h _ (orderIso_isAtom e hβ) (e.monotone hβp)

-- [D-3028] smallPartIso
def smallPartIso (e : L ≃o L') (N : ℕ) :
    ↥(smallPart L N) ≃o ↥(smallPart L' N) where
  toFun p := ⟨e p.1, (mem_smallPart_map e N).mp p.2⟩
  invFun q := ⟨e.symm q.1, by
    rw [mem_smallPart_map e N, e.apply_symm_apply]
    exact q.2⟩
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := e.map_rel_iff

end Def

-- [D-3029] §The-collapse-a-tail-entirely-above-the-threshold
section Collapse

variable {E : ℕ → Type u} {S : Type u}
variable [∀ i, PartialOrder (E i)] [∀ i, OrderBot (E i)]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamE : ∀ i, E i)
variable (hE_ne : ∀ i, lamE i ≠ ⊥) (hE_le : ∀ i (z : E i), z ≠ ⊥ → lamE i ≤ z)

-- [D-3030] mem_smallPart_prod_right
include hE_ne hE_le in
theorem mem_smallPart_prod_right (N : ℕ) (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    {p : WeakProd E × S} :
    p ∈ smallPart (WeakProd E × S) N ↔ p.1 = ⊥ := by
  haveI : IsAtomic (WeakProd E) := isAtomic_weakProd lamE hE_ne hE_le
  constructor
  · intro h
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, p.1.1 i ≠ ⊥ := by
      by_contra hcon
      push_neg at hcon
      exact hne (WeakProd.eq_bot_iff'.mpr hcon)
    have hat : IsAtom (((single i (lamE i) : WeakProd E), (⊥ : S))) :=
      isAtom_singleL (T := S) lamE hE_ne hE_le i
    have hle : ((single i (lamE i) : WeakProd E), (⊥ : S)) ≤ p :=
      ⟨single_le_iff.mpr (hE_le i _ hi), bot_le⟩
    have hcard : Nat.card ↥(atomFactor (WeakProd E × S)
        (((single i (lamE i) : WeakProd E), (⊥ : S)))) = Nat.card (E i) :=
      Nat.card_congr (axisIsoL (T := S) lamE hE_ne hE_le i).toEquiv
    have := h _ hat hle
    rw [hcard] at this
    exact absurd this (not_le.mpr (hbig i))
  · intro h β hβ hβp
    have hb1 : β.1 = ⊥ := le_bot_iff.mp (h ▸ hβp.1)
    have hb2 : IsAtom β.2 := by
      rcases prodIsAtom_iff.mp hβ with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (hb1 ▸ h1) (by simp [IsAtom])
      · exact h2
    have hsplit : β = ((⊥ : WeakProd E), β.2) := Prod.ext hb1 rfl
    have hcard : Nat.card ↥(atomFactor (WeakProd E × S) β)
        = Nat.card ↥(atomFactor S β.2) := by
      rw [hsplit]
      exact Nat.card_congr (atomFactorProdRightIso (A := WeakProd E) β.2).toEquiv
    rw [hcard]
    exact hS _ hb2

-- [D-3031] smallPartRightIso
include hE_ne hE_le in
def smallPartRightIso (N : ℕ) (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N) :
    ↥(smallPart (WeakProd E × S) N) ≃o S where
  toFun p := p.1.2
  invFun a := ⟨((⊥ : WeakProd E), a), by
    rw [mem_smallPart_prod_right lamE hE_ne hE_le N hbig hS]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_smallPart_prod_right lamE hE_ne hE_le N hbig hS).mp p.2).symm
    · rfl
  right_inv _ := rfl
  map_rel_iff' {p q} := by
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [(mem_smallPart_prod_right lamE hE_ne hE_le N hbig hS).mp p.2,
        (mem_smallPart_prod_right lamE hE_ne hE_le N hbig hS).mp q.2]
    · intro h
      exact h.2

end Collapse

-- [D-3032] §The-necessary-condition
section Necessary

variable {D : ℕ → Type u} {E : ℕ → Type u} {T : Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ i, PartialOrder (E i)] [∀ i, OrderBot (E i)]
variable [PartialOrder T] [OrderBot T]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamE : ∀ i, E i)
variable (hE_ne : ∀ i, lamE i ≠ ⊥) (hE_le : ∀ i (z : E i), z ≠ ⊥ → lamE i ≤ z)

-- [D-3033] seed_iso_smallPart
include hE_ne hE_le in

theorem seed_iso_smallPart (e : (WeakProd D × T) ≃o (WeakProd E × S)) (N : ℕ)
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N) :
    Nonempty (↥(smallPart (WeakProd D × T) N) ≃o S) :=
  ⟨(smallPartIso e N).trans (smallPartRightIso lamE hE_ne hE_le N hbig hS)⟩

end Necessary

-- [D-3034] §Identifying-the-surviving-side
section Left

variable {D : ℕ → Type u} {T : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [PartialOrder T] [OrderBot T] [IsAtomic T]
variable (lamD : ∀ j, D j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)

-- [D-3035] weakBelow
def weakBelow (D : ℕ → Type u) [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
    (N : ℕ) : Set (WeakProd D) :=
  {w | ∀ j, w.1 j ≠ ⊥ → Nat.card (D j) ≤ N}

-- [D-3036] weakBelowOrderBot
instance weakBelowOrderBot (N : ℕ) : OrderBot ↥(weakBelow D N) where
  bot := ⟨⊥, fun j hj => absurd rfl hj⟩
  bot_le x := by
    change (⊥ : WeakProd D) ≤ x.1
    exact bot_le

-- [D-3037] mem_smallPart_prod_left
include hD_ne hD_le in
theorem mem_smallPart_prod_left (N : ℕ)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N)
    {p : WeakProd D × T} :
    p ∈ smallPart (WeakProd D × T) N ↔ p.1 ∈ weakBelow D N := by
  haveI : IsAtomic (WeakProd D) := isAtomic_weakProd lamD hD_ne hD_le
  constructor
  · intro h j hj
    have hat : IsAtom (((single j (lamD j) : WeakProd D), (⊥ : T))) :=
      isAtom_singleL (T := T) lamD hD_ne hD_le j
    have hle : ((single j (lamD j) : WeakProd D), (⊥ : T)) ≤ p :=
      ⟨single_le_iff.mpr (hD_le j _ hj), bot_le⟩
    have hcard : Nat.card ↥(atomFactor (WeakProd D × T)
        (((single j (lamD j) : WeakProd D), (⊥ : T)))) = Nat.card (D j) :=
      Nat.card_congr (axisIsoL (T := T) lamD hD_ne hD_le j).toEquiv
    exact hcard ▸ h _ hat hle
  · intro h β hβ hβp
    rcases prodIsAtom_iff.mp hβ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨j, hj⟩ := atom_eq_single lamD hD_ne hD_le h1
      have hsplit : β = ((single j (lamD j) : WeakProd D), (⊥ : T)) := Prod.ext hj h2
      have hcard : Nat.card ↥(atomFactor (WeakProd D × T) β) = Nat.card (D j) := by
        rw [hsplit]
        exact Nat.card_congr (axisIsoL (T := T) lamD hD_ne hD_le j).toEquiv
      rw [hcard]
      refine h j ?_
      have hle : (single j (lamD j) : WeakProd D) ≤ p.1 := by
        have := hβp.1
        rwa [hsplit] at this
      intro hbot
      exact hD_ne j (le_bot_iff.mp (hbot ▸ single_le_iff.mp hle))
    · have hsplit : β = ((⊥ : WeakProd D), β.2) := Prod.ext h1 rfl
      have hcard : Nat.card ↥(atomFactor (WeakProd D × T) β)
          = Nat.card ↥(atomFactor T β.2) := by
        rw [hsplit]
        exact Nat.card_congr (atomFactorProdRightIso (A := WeakProd D) β.2).toEquiv
      rw [hcard]
      exact hT _ h2

-- [D-3038] smallPartLeftIso
include hD_ne hD_le in
def smallPartLeftIso (N : ℕ)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N) :
    ↥(smallPart (WeakProd D × T) N) ≃o (↥(weakBelow D N) × T) where
  toFun p := (⟨p.1.1, (mem_smallPart_prod_left lamD hD_ne hD_le N hT).mp p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2),
    (mem_smallPart_prod_left lamD hD_ne hD_le N hT).mpr q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Left

-- [D-3039] §The-surviving-side-is-an-explicit-finite-product
section Explicit

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]

-- [D-3040] consF
def consF (I : Finset ℕ) (f : (j : {x // x ∈ I}) → D j.1) : ∀ j, D j :=
  fun j => if h : j ∈ I then f ⟨j, h⟩ else ⊥

-- [D-3041] consF_mem
theorem consF_mem {I : Finset ℕ} (f : (j : {x // x ∈ I}) → D j.1) {j : ℕ} (h : j ∈ I) :
    consF I f j = f ⟨j, h⟩ := by simp [consF, h]

-- [D-3042] consF_not_mem
theorem consF_not_mem {I : Finset ℕ} (f : (j : {x // x ∈ I}) → D j.1) {j : ℕ}
    (h : j ∉ I) : consF I f j = ⊥ := by simp [consF, h]

-- [D-3043] piToWeak
def piToWeak (N : ℕ) (I : Finset ℕ) (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I)
    (f : (j : {x // x ∈ I}) → D j.1) : ↥(weakBelow D N) :=
  ⟨⟨consF I f, ⟨I.sup id + 1, fun j hj =>
      consF_not_mem f (fun hmem => by
        have hle : id j ≤ I.sup id := Finset.le_sup (f := id) hmem
        simp only [id_eq] at hle
        omega)⟩⟩,
   fun j hj => by
     by_cases h : j ∈ I
     · exact (hI j).mpr h
     · exact absurd (consF_not_mem f h) hj⟩

-- [D-3044] piToWeak_apply
theorem piToWeak_apply (N : ℕ) (I : Finset ℕ) (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I)
    (f : (j : {x // x ∈ I}) → D j.1) (j : ℕ) :
    (piToWeak N I hI f).1.1 j = consF I f j := rfl

-- [D-3045] weakBelowPi
def weakBelowPi (N : ℕ) (I : Finset ℕ) (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I) :
    ↥(weakBelow D N) ≃o ((j : {x // x ∈ I}) → D j.1) where
  toFun w := fun j => w.1.1 j.1
  invFun f := piToWeak N I hI f
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    rw [piToWeak_apply]
    by_cases h : j ∈ I
    · exact consF_mem _ h
    · have hbot : w.1.1 j = ⊥ := by
        by_contra hne
        exact h ((hI j).mp (w.2 j hne))
      rw [consF_not_mem _ h, hbot]
  right_inv f := by
    funext j
    change consF I f j.1 = f j
    exact consF_mem f j.2
  map_rel_iff' {w w'} := by
    constructor
    · intro h j
      by_cases hj : j ∈ I
      · exact h ⟨j, hj⟩
      · have hbot : w.1.1 j = ⊥ := by
          by_contra hne
          exact hj ((hI j).mp (w.2 j hne))
        rw [hbot]
        exact bot_le
    · intro h j
      exact h j.1

-- [D-3046] card_weakBelow
theorem card_weakBelow (N : ℕ) (I : Finset ℕ)
    (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I) :
    Nat.card ↥(weakBelow D N) = ∏ j ∈ I, Nat.card (D j) := by
  rw [Nat.card_congr (weakBelowPi N I hI).toEquiv, Nat.card_pi]
  exact Finset.prod_coe_sort I (fun j => Nat.card (D j))

end Explicit

-- [D-3047] §The-finite-equation
section Equation

variable {D : ℕ → Type u} {E : ℕ → Type u} {T : Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ i, PartialOrder (E i)] [∀ i, OrderBot (E i)]
variable [PartialOrder T] [OrderBot T] [IsAtomic T]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamD : ∀ j, D j) (lamE : ∀ i, E i)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ i, lamE i ≠ ⊥) (hE_le : ∀ i (z : E i), z ≠ ⊥ → lamE i ≤ z)

-- [D-3048] seed_iso_prod
include hD_ne hD_le hE_ne hE_le in
theorem seed_iso_prod (e : (WeakProd D × T) ≃o (WeakProd E × S)) (N : ℕ)
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N) :
    Nonempty ((↥(weakBelow D N) × T) ≃o S) :=
  ⟨((smallPartLeftIso lamD hD_ne hD_le N hT).symm.trans
    (smallPartIso e N)).trans (smallPartRightIso lamE hE_ne hE_le N hbig hS)⟩

-- [D-3049] card_eq_prod
include hD_ne hD_le hE_ne hE_le in
theorem card_eq_prod (e : (WeakProd D × T) ≃o (WeakProd E × S)) (N : ℕ)
    (hbig : ∀ i, N < Nat.card (E i))
    (hS : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N)
    (hT : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N)
    (I : Finset ℕ) (hI : ∀ j, Nat.card (D j) ≤ N ↔ j ∈ I) :
    Nat.card S = (∏ j ∈ I, Nat.card (D j)) * Nat.card T := by
  have h := (seed_iso_prod lamD lamE hD_ne hD_le hE_ne hE_le e N hbig hS hT).some
  rw [← Nat.card_congr h.toEquiv, Nat.card_prod, card_weakBelow N I hI]

end Equation

end Truncation
