import Dinfty.ProdAut

-- [D-1459] §No-infinite-absorption-X-X-2-for-the-tower-s
open scoped Classical

universe u v

namespace WeakProductAbsorption

-- [D-1460] §The-atom-factor
-- [D-1461] orderIso_isAtom
theorem orderIso_isAtom {L : Type u} {L' : Type v} [PartialOrder L] [OrderBot L]
    [PartialOrder L'] [OrderBot L'] (e : L ≃o L') {a : L} (ha : IsAtom a) :
    IsAtom (e a) := by
  constructor
  · intro hcon
    refine ha.1 ?_
    have h := congrArg e.symm hcon
    rwa [e.symm_apply_apply, e.symm.map_bot] at h
  · intro b hb
    have hb' : e.symm b < a := by
      have h := e.symm.strictMono hb
      rwa [e.symm_apply_apply] at h
    have h2 := ha.2 _ hb'
    have h3 := congrArg e h2
    rwa [e.apply_symm_apply, e.map_bot] at h3

-- [D-1462] atomFactor
def atomFactor (L : Type u) [PartialOrder L] [OrderBot L] (α : L) : Set L :=
  {w | ∀ β : L, IsAtom β → β ≤ w → β = α}

-- [D-1463] bot_mem_atomFactor
theorem bot_mem_atomFactor {L : Type u} [PartialOrder L] [OrderBot L] (α : L) :
    (⊥ : L) ∈ atomFactor L α := by
  intro β hβ hle
  exact absurd (le_bot_iff.mp hle) hβ.1

-- [D-1464] mem_atomFactor_map
theorem mem_atomFactor_map {L : Type u} {L' : Type v} [PartialOrder L] [OrderBot L]
    [PartialOrder L'] [OrderBot L'] (e : L ≃o L') (α : L) {w : L}
    (hw : w ∈ atomFactor L α) : e w ∈ atomFactor L' (e α) := by
  intro β hβ hle
  have hβ' : IsAtom (e.symm β) := orderIso_isAtom e.symm hβ
  have hle' : e.symm β ≤ w := by
    have h := e.symm.monotone hle
    rwa [e.symm_apply_apply] at h
  have h2 := hw _ hβ' hle'
  rw [← h2, e.apply_symm_apply]

-- [D-1465] §Two-elements-is-two-elements-the-C-obstruction
section ProdTwo

variable {L : Type u} [PartialOrder L] [OrderBot L]

-- [D-1466] isAtom_prodTop
theorem isAtom_prodTop : IsAtom (((⊥ : L), (1 : Fin 2))) := by
  constructor
  · intro hcon
    have h2 : (1 : Fin 2) = 0 := congrArg Prod.snd hcon
    exact absurd h2 (by decide)
  · rintro ⟨a, i⟩ hlt
    have hle : ((a, i) : L × Fin 2) ≤ (⊥, 1) := le_of_lt hlt
    have ha : a = ⊥ := le_bot_iff.mp hle.1
    subst ha
    have hi : i ≠ 1 := by
      intro hcon
      subst hcon
      exact absurd rfl (ne_of_lt hlt)
    have h0 : ∀ j : Fin 2, j ≠ 1 → j = 0 := by decide
    rw [h0 i hi]
    rfl

-- [D-1467] atomFactor_prodTwo_top
theorem atomFactor_prodTwo_top [IsAtomic L] {w : L × Fin 2}
    (hw : w ∈ atomFactor (L × Fin 2) ((⊥ : L), (1 : Fin 2))) :
    w = ⊥ ∨ w = ((⊥ : L), (1 : Fin 2)) := by
  obtain ⟨a, i⟩ := w
  have ha : a = ⊥ := by
    by_contra hcon
    obtain ⟨α, hα, hαle⟩ := (IsAtomic.eq_bot_or_exists_atom_le a).resolve_left hcon
    have hatom : IsAtom ((α, (0 : Fin 2)) : L × Fin 2) := by
      constructor
      · intro hbot
        exact hα.1 (congrArg Prod.fst hbot)
      · rintro ⟨b, j⟩ hlt
        have hle : ((b, j) : L × Fin 2) ≤ (α, 0) := le_of_lt hlt
        have hj : j = 0 := le_antisymm hle.2 (Fin.zero_le j)
        subst hj
        have hbne : b ≠ α := by
          intro hcon2
          subst hcon2
          exact absurd rfl (ne_of_lt hlt)
        have hbot : b = ⊥ := hα.2 b (lt_of_le_of_ne hle.1 hbne)
        subst hbot
        rfl
    have hprodle : ((α, (0 : Fin 2)) : L × Fin 2) ≤ (a, i) := ⟨hαle, Fin.zero_le i⟩
    have heq := hw _ hatom hprodle
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.snd heq
    exact absurd h2 (by decide)
  subst ha
  have h0 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases h0 i with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

-- [D-1468] no_iso_prod_two
theorem no_iso_prod_two [IsAtomic L]
    (h : ∀ α : L, IsAtom α → ∃ w, w ∈ atomFactor L α ∧ w ≠ ⊥ ∧ w ≠ α) :
    IsEmpty (L ≃o (L × Fin 2)) := by
  refine ⟨fun e => ?_⟩
  set α : L := e.symm ((⊥ : L), (1 : Fin 2)) with hα
  have hαatom : IsAtom α := orderIso_isAtom e.symm isAtom_prodTop
  obtain ⟨w, hw, hwb, hwα⟩ := h α hαatom
  have himg : e w ∈ atomFactor (L × Fin 2) (e α) := mem_atomFactor_map e α hw
  rw [hα, e.apply_symm_apply] at himg
  rcases atomFactor_prodTwo_top himg with hcase | hcase
  · refine hwb ?_
    have h3 := congrArg e.symm hcase
    rwa [e.symm_apply_apply, e.symm.map_bot] at h3
  · refine hwα ?_
    have h3 := congrArg e.symm hcase
    rwa [e.symm_apply_apply] at h3

end ProdTwo

-- [D-1469] §The-restricted-product
section WeakProdDef

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]

-- [D-1470] WeakProd
def WeakProd (D : ℕ → Type u) [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)] : Type u :=
  {x : ∀ j, D j // ∃ N, ∀ j, N ≤ j → x j = ⊥}

-- [D-1471] inst-PartialOrder
instance : PartialOrder (WeakProd D) := Subtype.partialOrder _

-- [D-1472] WeakProd.le_def
theorem WeakProd.le_def {x y : WeakProd D} : x ≤ y ↔ ∀ j, x.1 j ≤ y.1 j := Iff.rfl

-- [D-1473] inst-OrderBot
instance : OrderBot (WeakProd D) where
  bot := ⟨fun _ => ⊥, ⟨0, fun _ _ => rfl⟩⟩
  bot_le _ := fun _ => bot_le

-- [D-1474] WeakProd.bot_apply
@[simp] theorem WeakProd.bot_apply (j : ℕ) : (⊥ : WeakProd D).1 j = ⊥ := rfl

-- [D-1475] WeakProd.eq_bot_iff'
theorem WeakProd.eq_bot_iff' {x : WeakProd D} : x = ⊥ ↔ ∀ j, x.1 j = ⊥ := by
  constructor
  · rintro rfl j
    rfl
  · intro h
    exact Subtype.ext (funext h)

-- [D-1476] single
def single (j : ℕ) (a : D j) : WeakProd D :=
  ⟨Function.update (fun i => (⊥ : D i)) j a, ⟨j + 1, by
    intro i hi
    rw [Function.update_of_ne (by omega)]⟩⟩

-- [D-1477] single_apply_self
@[simp] theorem single_apply_self (j : ℕ) (a : D j) : (single j a).1 j = a := by
  show Function.update (fun i => (⊥ : D i)) j a j = a
  simp

-- [D-1478] single_apply_ne
@[simp] theorem single_apply_ne {j i : ℕ} (h : i ≠ j) (a : D j) :
    (single j a).1 i = ⊥ := by
  show Function.update (fun i => (⊥ : D i)) j a i = ⊥
  rw [Function.update_of_ne h]

-- [D-1479] single_le_iff
theorem single_le_iff {j : ℕ} {a : D j} {x : WeakProd D} :
    single j a ≤ x ↔ a ≤ x.1 j := by
  constructor
  · intro h
    have h2 := h j
    rwa [single_apply_self] at h2
  · intro h i
    by_cases hij : i = j
    · subst hij
      rwa [single_apply_self]
    · rw [single_apply_ne hij]
      exact bot_le

end WeakProdDef

-- [D-1480] §Atoms-and-atom-factors-of-the-restricted-product
section WeakProdAtoms

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable (lam : ∀ j, D j)
variable (hlam_ne : ∀ j, lam j ≠ ⊥) (hlam_le : ∀ j (z : D j), z ≠ ⊥ → lam j ≤ z)

include hlam_ne hlam_le

-- [D-1481] isAtom_single
theorem isAtom_single (j : ℕ) : IsAtom (single j (lam j) : WeakProd D) := by
  constructor
  · intro hcon
    refine hlam_ne j ?_
    have h := congrFun (congrArg Subtype.val hcon) j
    rwa [single_apply_self] at h
  · intro w hlt
    rw [WeakProd.eq_bot_iff']
    intro i
    by_cases hij : i = j
    · subst hij
      by_contra hne
      have h1 : lam i ≤ w.1 i := hlam_le i _ hne
      have h2 : single i (lam i) ≤ w := single_le_iff.mpr h1
      exact absurd (le_antisymm (le_of_lt hlt) h2) (ne_of_lt hlt)
    · have h3 := (le_of_lt hlt) i
      rw [single_apply_ne hij] at h3
      exact le_bot_iff.mp h3

-- [D-1482] atom_eq_single
theorem atom_eq_single {β : WeakProd D} (hβ : IsAtom β) :
    ∃ j, β = single j (lam j) := by
  have hne : ∃ j, β.1 j ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    exact hβ.1 (WeakProd.eq_bot_iff'.mpr hcon)
  obtain ⟨j, hj⟩ := hne
  refine ⟨j, ?_⟩
  have hle : single j (lam j) ≤ β := single_le_iff.mpr (hlam_le j _ hj)
  rcases (hβ.le_iff.mp hle) with h | h
  · exact absurd h (isAtom_single lam hlam_ne hlam_le j).1
  · exact h.symm

-- [D-1483] atomFactor_single
theorem atomFactor_single {j : ℕ} {w : WeakProd D}
    (hw : w ∈ atomFactor (WeakProd D) (single j (lam j))) (i : ℕ) (hij : i ≠ j) :
    w.1 i = ⊥ := by
  by_contra hcon
  have hle : single i (lam i) ≤ w := single_le_iff.mpr (hlam_le i _ hcon)
  have h1 := hw _ (isAtom_single lam hlam_ne hlam_le i) hle
  have h2 := congrFun (congrArg Subtype.val h1) i
  rw [single_apply_self, single_apply_ne hij] at h2
  exact hlam_ne i h2

-- [D-1484] mem_atomFactor_single
theorem mem_atomFactor_single {j : ℕ} (a : D j) :
    (single j a : WeakProd D) ∈ atomFactor (WeakProd D) (single j (lam j)) := by
  intro β hβ hle
  obtain ⟨i, rfl⟩ := atom_eq_single lam hlam_ne hlam_le hβ
  by_cases hij : i = j
  · subst hij
    rfl
  · exfalso
    have h1 := single_le_iff.mp hle
    rw [single_apply_ne hij] at h1
    exact hlam_ne i (le_bot_iff.mp h1)

-- [D-1485] isAtomic_weakProd
theorem isAtomic_weakProd : IsAtomic (WeakProd D) := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = ⊥
  · exact Or.inl hx
  · rw [WeakProd.eq_bot_iff'] at hx
    push_neg at hx
    obtain ⟨j, hj⟩ := hx
    exact Or.inr ⟨single j (lam j), isAtom_single lam hlam_ne hlam_le j,
      single_le_iff.mpr (hlam_le j _ hj)⟩

-- [D-1486] weakProd_no_absorb_two
theorem weakProd_no_absorb_two (c : ∀ j, D j)
    (hc_ne : ∀ j, c j ≠ ⊥) (hc_lam : ∀ j, c j ≠ lam j) :
    IsEmpty (WeakProd D ≃o (WeakProd D × Fin 2)) := by
  haveI := isAtomic_weakProd lam hlam_ne hlam_le
  refine no_iso_prod_two (fun α hα => ?_)
  obtain ⟨j, rfl⟩ := atom_eq_single lam hlam_ne hlam_le hα
  refine ⟨single j (c j), mem_atomFactor_single lam hlam_ne hlam_le (c j), ?_, ?_⟩
  · intro hcon
    refine hc_ne j ?_
    have h := congrFun (congrArg Subtype.val hcon) j
    rwa [single_apply_self] at h
  · intro hcon
    refine hc_lam j ?_
    have h := congrFun (congrArg Subtype.val hcon) j
    rwa [single_apply_self, single_apply_self] at h

end WeakProdAtoms

end WeakProductAbsorption
