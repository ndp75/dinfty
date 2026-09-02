import Dinfty.WeakProductAbsorption

-- [D-1487] §Generation-by-atom-factors-the-invariant
open scoped Classical

universe u v

namespace AtomFactorGeneration

open WeakProductAbsorption

-- [D-1488] §The-factor-part-and-generation
variable {L : Type u} [PartialOrder L] [OrderBot L]

-- [D-1489] factorPart
def factorPart (L : Type u) [PartialOrder L] [OrderBot L] : Set L :=
  {w | ∃ α : L, IsAtom α ∧ w ∈ atomFactor L α}

-- [D-1490] GenByFactors
def GenByFactors (L : Type u) [PartialOrder L] [OrderBot L] : Prop :=
  ∀ w : L, IsLUB {u : L | u ∈ factorPart L ∧ u ≤ w} w

-- [D-1491] §It-is-an-order-theoretic-property
-- [D-1492] mem_factorPart_map
theorem mem_factorPart_map {L' : Type v} [PartialOrder L'] [OrderBot L']
    (e : L ≃o L') {w : L} (hw : w ∈ factorPart L) : e w ∈ factorPart L' := by
  obtain ⟨α, hα, hmem⟩ := hw
  exact ⟨e α, orderIso_isAtom e hα, mem_atomFactor_map e α hmem⟩

-- [D-1493] factorPart_image
theorem factorPart_image {L' : Type v} [PartialOrder L'] [OrderBot L']
    (e : L ≃o L') : e '' factorPart L = factorPart L' := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_factorPart_map e hw
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have h := mem_factorPart_map e.symm hy
    exact h

-- [D-1494] genByFactors_orderIso
theorem genByFactors_orderIso {L' : Type v} [PartialOrder L'] [OrderBot L']
    (e : L ≃o L') (h : GenByFactors L) : GenByFactors L' := by
  intro w
  constructor
  · rintro u ⟨hu, hle⟩
    exact hle
  · intro v hv
    have hkey : e.symm w ≤ e.symm v := by
      refine (h (e.symm w)).2 ?_
      rintro u ⟨hu, hle⟩
      have h1 : e u ∈ factorPart L' := mem_factorPart_map e hu
      have h2 : e u ≤ w := by
        have := e.monotone hle
        rwa [e.apply_symm_apply] at this
      have h3 : e u ≤ v := hv ⟨h1, h2⟩
      have := e.symm.monotone h3
      rwa [e.symm_apply_apply] at this
    have := e.monotone hkey
    rwa [e.apply_symm_apply, e.apply_symm_apply] at this

-- [D-1495] no_iso_of_genByFactors_ne
theorem no_iso_of_genByFactors_ne {L' : Type v} [PartialOrder L'] [OrderBot L']
    (h : GenByFactors L) (h' : ¬ GenByFactors L') : IsEmpty (L ≃o L') :=
  ⟨fun e => h' (genByFactors_orderIso e h)⟩

-- [D-1496] §The-ordinal-sum-obstruction-in-the-form
-- [D-1497] not_genByFactors_of_strict_upper
theorem not_genByFactors_of_strict_upper {t w : L}
    (ht : ∀ u ∈ factorPart L, u ≤ t) (hlt : t < w) : ¬ GenByFactors L := by
  intro h
  have hub : t ∈ upperBounds {u : L | u ∈ factorPart L ∧ u ≤ w} := by
    rintro u ⟨hu, -⟩
    exact ht u hu
  exact absurd (le_antisymm ((h w).2 hub) (le_of_lt hlt)) (ne_of_gt hlt)

-- [D-1498] §Multiplicativity
section Prod

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B]

-- [D-1499] prodIsAtom_iff
theorem prodIsAtom_iff {p : A × B} :
    IsAtom p ↔ (IsAtom p.1 ∧ p.2 = ⊥) ∨ (p.1 = ⊥ ∧ IsAtom p.2) := by
  obtain ⟨a, b⟩ := p
  constructor
  · intro hp
    by_cases ha : a = ⊥
    · subst ha
      refine Or.inr ⟨rfl, ⟨?_, ?_⟩⟩
      · intro hb
        exact hp.1 (Prod.ext rfl hb)
      · intro y hy
        have : ((⊥ : A), y) < ((⊥ : A), b) := by
          refine lt_of_le_of_ne ⟨le_rfl, le_of_lt hy⟩ ?_
          intro hcon
          exact absurd (congrArg Prod.snd hcon) (ne_of_lt hy)
        exact congrArg Prod.snd (hp.2 _ this)
    · have hb : b = ⊥ := by
        by_contra hbne
        have hlt : ((a : A), (⊥ : B)) < (a, b) := by
          refine lt_of_le_of_ne ⟨le_rfl, bot_le⟩ ?_
          intro hcon
          exact hbne (congrArg Prod.snd hcon).symm
        exact ha (congrArg Prod.fst (hp.2 _ hlt))
      subst hb
      refine Or.inl ⟨⟨ha, ?_⟩, rfl⟩
      intro x hx
      have : ((x : A), (⊥ : B)) < (a, ⊥) := by
        refine lt_of_le_of_ne ⟨le_of_lt hx, le_rfl⟩ ?_
        intro hcon
        exact absurd (congrArg Prod.fst hcon) (ne_of_lt hx)
      exact congrArg Prod.fst (hp.2 _ this)
  · rintro (⟨ha, rfl⟩ | ⟨rfl, hb⟩)
    · refine ⟨?_, ?_⟩
      · intro hcon
        exact ha.1 (congrArg Prod.fst hcon)
      · rintro ⟨x, y⟩ hlt
        have hle := le_of_lt hlt
        have hy : y = ⊥ := le_bot_iff.mp hle.2
        subst hy
        have hxa : x ≠ a := by
          intro hcon
          subst hcon
          exact absurd rfl (ne_of_lt hlt)
        rw [ha.2 x (lt_of_le_of_ne hle.1 hxa)]
        rfl
    · refine ⟨?_, ?_⟩
      · intro hcon
        exact hb.1 (congrArg Prod.snd hcon)
      · rintro ⟨x, y⟩ hlt
        have hle := le_of_lt hlt
        have hx : x = ⊥ := le_bot_iff.mp hle.1
        subst hx
        have hyb : y ≠ b := by
          intro hcon
          subst hcon
          exact absurd rfl (ne_of_lt hlt)
        rw [hb.2 y (lt_of_le_of_ne hle.2 hyb)]
        rfl

variable [IsAtomic A] [IsAtomic B]

-- [D-1500] mem_factorPart_prod
theorem mem_factorPart_prod {p : A × B} :
    p ∈ factorPart (A × B) ↔
      (p.2 = ⊥ ∧ p.1 ∈ factorPart A) ∨ (p.1 = ⊥ ∧ p.2 ∈ factorPart B) := by
  constructor
  · rintro ⟨γ, hγ, hmem⟩
    rcases prodIsAtom_iff.mp hγ with ⟨hγ1, hγ2⟩ | ⟨hγ1, hγ2⟩
    · refine Or.inl ⟨?_, ⟨γ.1, hγ1, ?_⟩⟩
      · by_contra hbne
        obtain ⟨β, hβ, hβle⟩ := (IsAtomic.eq_bot_or_exists_atom_le p.2).resolve_left hbne
        have hat : IsAtom (((⊥ : A), β) : A × B) := prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ⟩)
        have heq := hmem _ hat ⟨bot_le, hβle⟩
        have h2 : β = γ.2 := congrArg Prod.snd heq
        rw [hγ2] at h2
        exact hβ.1 h2
      · intro α hα hαle
        have hat : IsAtom ((α, (⊥ : B)) : A × B) := prodIsAtom_iff.mpr (Or.inl ⟨hα, rfl⟩)
        exact congrArg Prod.fst (hmem _ hat ⟨hαle, bot_le⟩)
    · refine Or.inr ⟨?_, ⟨γ.2, hγ2, ?_⟩⟩
      · by_contra hane
        obtain ⟨α, hα, hαle⟩ := (IsAtomic.eq_bot_or_exists_atom_le p.1).resolve_left hane
        have hat : IsAtom ((α, (⊥ : B)) : A × B) := prodIsAtom_iff.mpr (Or.inl ⟨hα, rfl⟩)
        have heq := hmem _ hat ⟨hαle, bot_le⟩
        have h2 : α = γ.1 := congrArg Prod.fst heq
        rw [hγ1] at h2
        exact hα.1 h2
      · intro β hβ hβle
        have hat : IsAtom (((⊥ : A), β) : A × B) := prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ⟩)
        exact congrArg Prod.snd (hmem _ hat ⟨bot_le, hβle⟩)
  · rintro (⟨hb, α, hα, hmem⟩ | ⟨ha, β, hβ, hmem⟩)
    · refine ⟨(α, ⊥), prodIsAtom_iff.mpr (Or.inl ⟨hα, rfl⟩), ?_⟩
      rintro ⟨c, d⟩ hcd hle
      rcases prodIsAtom_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
      · exact Prod.ext (hmem c hc hle.1) hd
      · exfalso
        have h2 : d ≤ (⊥ : B) := by rw [← hb]; exact hle.2
        exact hd.1 (le_bot_iff.mp h2)
    · refine ⟨(⊥, β), prodIsAtom_iff.mpr (Or.inr ⟨rfl, hβ⟩), ?_⟩
      rintro ⟨c, d⟩ hcd hle
      rcases prodIsAtom_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
      · exfalso
        have h2 : c ≤ (⊥ : A) := by rw [← ha]; exact hle.1
        exact hc.1 (le_bot_iff.mp h2)
      · exact Prod.ext hc (hmem d hd hle.2)

-- [D-1501] genByFactors_prod_iff
theorem genByFactors_prod_iff :
    GenByFactors (A × B) ↔ GenByFactors A ∧ GenByFactors B := by
  constructor
  · intro h
    constructor
    · intro a
      refine ⟨fun u hu => hu.2, ?_⟩
      intro v hv
      have hub : ((v, (⊥ : B)) : A × B)
          ∈ upperBounds {u : A × B | u ∈ factorPart (A × B) ∧ u ≤ (a, (⊥ : B))} := by
        rintro ⟨c, d⟩ ⟨hcd, hle⟩
        have hd : d = ⊥ := le_bot_iff.mp hle.2
        subst hd
        rcases mem_factorPart_prod.mp hcd with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact ⟨hv ⟨hc, hle.1⟩, le_rfl⟩
        · refine ⟨?_, le_rfl⟩
          rw [hc]
          exact bot_le
      exact ((h (a, (⊥ : B))).2 hub).1
    · intro b
      refine ⟨fun u hu => hu.2, ?_⟩
      intro v hv
      have hub : (((⊥ : A), v) : A × B)
          ∈ upperBounds {u : A × B | u ∈ factorPart (A × B) ∧ u ≤ ((⊥ : A), b)} := by
        rintro ⟨c, d⟩ ⟨hcd, hle⟩
        have hc : c = ⊥ := le_bot_iff.mp hle.1
        subst hc
        rcases mem_factorPart_prod.mp hcd with ⟨hd, -⟩ | ⟨-, hd⟩
        · refine ⟨le_rfl, ?_⟩
          rw [hd]
          exact bot_le
        · exact ⟨le_rfl, hv ⟨hd, hle.2⟩⟩
      exact ((h ((⊥ : A), b)).2 hub).2
  · rintro ⟨hA, hB⟩ ⟨a, b⟩
    refine ⟨fun u hu => hu.2, ?_⟩
    rintro ⟨x, y⟩ hxy
    refine ⟨?_, ?_⟩
    · refine (hA a).2 ?_
      rintro u ⟨hu, hle⟩
      exact (hxy (show ((u, (⊥ : B)) : A × B) ∈ _ from
        ⟨mem_factorPart_prod.mpr (Or.inl ⟨rfl, hu⟩), ⟨hle, bot_le⟩⟩)).1
    · refine (hB b).2 ?_
      rintro u ⟨hu, hle⟩
      exact (hxy (show (((⊥ : A), u) : A × B) ∈ _ from
        ⟨mem_factorPart_prod.mpr (Or.inr ⟨rfl, hu⟩), ⟨bot_le, hle⟩⟩)).2

end Prod

-- [D-1502] §The-restricted-product-is-generated-by-its-atom
section WeakProdGen

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable (lam : ∀ j, D j)
variable (hlam_ne : ∀ j, lam j ≠ ⊥) (hlam_le : ∀ j (z : D j), z ≠ ⊥ → lam j ≤ z)

include hlam_ne hlam_le

-- [D-1503] single_mem_factorPart
theorem single_mem_factorPart (j : ℕ) (a : D j) :
    (single j a : WeakProd D) ∈ factorPart (WeakProd D) :=
  ⟨single j (lam j), isAtom_single lam hlam_ne hlam_le j,
   mem_atomFactor_single lam hlam_ne hlam_le a⟩

-- [D-1504] genByFactors_weakProd
theorem genByFactors_weakProd : GenByFactors (WeakProd D) := by
  intro w
  constructor
  · rintro u ⟨-, hle⟩
    exact hle
  · intro v hv j
    have hmem : (single j (w.1 j) : WeakProd D)
        ∈ {u : WeakProd D | u ∈ factorPart (WeakProd D) ∧ u ≤ w} :=
      ⟨single_mem_factorPart lam hlam_ne hlam_le j (w.1 j), single_le_iff.mpr le_rfl⟩
    exact single_le_iff.mp (hv hmem)

-- [D-1505] weakProd_prod_ne
theorem weakProd_prod_ne {S : Type u} [PartialOrder S] [OrderBot S] [IsAtomic S]
    (hS : ¬ GenByFactors S) :
    IsEmpty (WeakProd D ≃o (WeakProd D × S)) := by
  haveI := isAtomic_weakProd lam hlam_ne hlam_le
  refine no_iso_of_genByFactors_ne (genByFactors_weakProd lam hlam_ne hlam_le) ?_
  intro hcon
  exact hS (genByFactors_prod_iff.mp hcon).2

end WeakProdGen

end AtomFactorGeneration
