import Mathlib.Tactic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Set

-- [D-2990] §The-cut-obstruction
open scoped Classical

namespace CutObstruction

variable {L : Type*}

-- [D-2991] IsCut
def IsCut [Preorder L] (A : Set L) : Prop := ∀ a ∈ A, ∀ b ∉ A, a ≤ b

-- [D-2992] IsCut.isLowerSet
theorem IsCut.isLowerSet [PartialOrder L] {A : Set L} (h : IsCut A) :
    IsLowerSet A := by
  intro a c hca ha
  by_contra hc
  exact hc (le_antisymm hca (h a ha c hc) ▸ ha)

-- [D-2993] isCut_image
theorem isCut_image {L' : Type*} [Preorder L] [Preorder L'] (e : L ≃o L')
    {A : Set L} (h : IsCut A) : IsCut (e '' A) := by
  rintro a ⟨a0, ha0, rfl⟩ b hb
  rw [← e.apply_symm_apply b]
  refine e.map_rel_iff.mpr (h a0 ha0 (e.symm b) ?_)
  intro hmem
  exact hb ⟨_, hmem, e.apply_symm_apply b⟩

-- [D-2994] cut_prod
theorem cut_prod {P Q : Type*} [PartialOrder P] [BoundedOrder P]
    [PartialOrder Q] [BoundedOrder Q] (hP : (⊥ : P) ≠ ⊤) (hQ : (⊥ : Q) ≠ ⊤)
    {A : Set (P × Q)} (hA : IsCut A) :
    (∀ a ∈ A, a = (⊥ : P × Q)) ∨ (∀ b ∈ Aᶜ, b = (⊤ : P × Q)) := by
  by_cases hu : ((⊤ : P), (⊥ : Q)) ∈ A
  · by_cases hv : ((⊥ : P), (⊤ : Q)) ∈ A
    · refine Or.inr (fun b hb => ?_)
      have h1 := hA _ hu b hb
      have h2 := hA _ hv b hb
      exact Prod.ext (top_le_iff.mp h1.1) (top_le_iff.mp h2.2)
    · exact absurd (le_antisymm bot_le (hA _ hu _ hv).1) hP
  · by_cases hv : ((⊥ : P), (⊤ : Q)) ∈ A
    · exact absurd (le_antisymm bot_le (hA _ hv _ hu).2) hQ
    · refine Or.inl (fun a ha => ?_)
      have h1 := hA a ha _ hu
      have h2 := hA a ha _ hv
      exact Prod.ext (le_bot_iff.mp h2.1) (le_bot_iff.mp h1.2)

-- [D-2995] cut_of_orderIso
theorem cut_of_orderIso {P Q : Type*} [PartialOrder L] [PartialOrder P]
    [BoundedOrder P] [PartialOrder Q] [BoundedOrder Q]
    (hP : (⊥ : P) ≠ ⊤) (hQ : (⊥ : Q) ≠ ⊤) {A : Set L} (hA : IsCut A)
    (e : L ≃o (P × Q)) :
    (∀ a ∈ A, ∀ a' ∈ A, a = a') ∨ (∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, b = b') := by
  rcases cut_prod hP hQ (isCut_image e hA) with h | h
  · refine Or.inl (fun a ha a' ha' => e.injective ?_)
    rw [h _ ⟨a, ha, rfl⟩, h _ ⟨a', ha', rfl⟩]
  · refine Or.inr (fun b hb b' hb' => e.injective ?_)
    have hcompl : ∀ c, c ∉ A → e c ∈ (e '' A)ᶜ := by
      intro c hc hmem
      obtain ⟨c0, hc0, hce⟩ := hmem
      exact hc (e.injective hce ▸ hc0)
    rw [h _ (hcompl b hb), h _ (hcompl b' hb')]

-- [D-2996] §The-obstruction
-- [D-2997] two_le_card_of_bot_ne_top
theorem two_le_card_of_bot_ne_top {P : Type*} [PartialOrder P] [BoundedOrder P]
    [Fintype P] (hP : (⊥ : P) ≠ ⊤) : 2 ≤ Fintype.card P := by
  by_contra h
  have hs : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hP (Subsingleton.elim _ _)

-- [D-2998] no_iso_of_cut
theorem no_iso_of_cut {P Q : Type*} [PartialOrder L] [Fintype L]
    [PartialOrder P] [BoundedOrder P] [Fintype P]
    [PartialOrder Q] [BoundedOrder Q] [Fintype Q]
    (hP : (⊥ : P) ≠ ⊤) (hQ : (⊥ : Q) ≠ ⊤)
    {A : Set L} (hA : IsCut A) (hAne : A.Nonempty) (hcne : (Aᶜ : Set L).Nonempty)
    (hdvd : Fintype.card P ∣ Fintype.card ↥(Aᶜ))
    (e : L ≃o (P × Q)) : False := by
  classical
  have hPcard : 2 ≤ Fintype.card P := two_le_card_of_bot_ne_top hP
  have hcpos : 0 < Fintype.card ↥(Aᶜ) :=
    Fintype.card_pos_iff.mpr ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
  have hc2 : 2 ≤ Fintype.card ↥(Aᶜ) :=
    le_trans hPcard (Nat.le_of_dvd hcpos hdvd)
  have hsub : ∀ a ∈ A, ∀ a' ∈ A, a = a' := by
    rcases cut_of_orderIso hP hQ hA e with h | h
    · exact h
    · exfalso
      have : Subsingleton ↥(Aᶜ) := ⟨fun b b' => Subtype.ext (h b.1 b.2 b'.1 b'.2)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr this
      omega
  have hA1 : Fintype.card ↥A = 1 := by
    have hpos : 0 < Fintype.card ↥A :=
      Fintype.card_pos_iff.mpr ⟨⟨hAne.choose, hAne.choose_spec⟩⟩
    have hle : Fintype.card ↥A ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr
        ⟨fun a a' => Subtype.ext (hsub a.1 a.2 a'.1 a'.2)⟩
    omega
  have hsplit : Fintype.card ↥A + Fintype.card ↥(Aᶜ) = Fintype.card L := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl A)
  have hLcard : Fintype.card L = Fintype.card P * Fintype.card Q := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_prod]
  have hd1 : Fintype.card P ∣ Fintype.card L := ⟨Fintype.card Q, hLcard⟩
  have hd2 : Fintype.card P ∣ Fintype.card L - Fintype.card ↥(Aᶜ) :=
    Nat.dvd_sub hd1 hdvd
  rw [show Fintype.card L - Fintype.card ↥(Aᶜ) = 1 by omega] at hd2
  have := Nat.dvd_one.mp hd2
  omega

-- [D-2999] §The-same-with-the-bounds-supplied-as-data
-- [D-3000] cut_prod_bounds
theorem cut_prod_bounds {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    {pb pt : P} {qb qt : Q}
    (hpb : ∀ p, pb ≤ p) (hpt : ∀ p, p ≤ pt)
    (hqb : ∀ q, qb ≤ q) (hqt : ∀ q, q ≤ qt)
    (hP : pb ≠ pt) (hQ : qb ≠ qt) {A : Set (P × Q)} (hA : IsCut A) :
    (∀ a ∈ A, a = (pb, qb)) ∨ (∀ b ∈ Aᶜ, b = (pt, qt)) := by
  by_cases hu : ((pt : P), (qb : Q)) ∈ A
  · by_cases hv : ((pb : P), (qt : Q)) ∈ A
    · refine Or.inr (fun b hb => ?_)
      have h1 := hA _ hu b hb
      have h2 := hA _ hv b hb
      exact Prod.ext (le_antisymm (hpt b.1) h1.1) (le_antisymm (hqt b.2) h2.2)
    · exact absurd (le_antisymm (hpb pt) (hA _ hu _ hv).1) hP
  · by_cases hv : ((pb : P), (qt : Q)) ∈ A
    · exact absurd (le_antisymm (hqb qt) (hA _ hv _ hu).2) hQ
    · refine Or.inl (fun a ha => ?_)
      have h1 := hA a ha _ hu
      have h2 := hA a ha _ hv
      exact Prod.ext (le_antisymm h2.1 (hpb a.1)) (le_antisymm h1.2 (hqb a.2))

-- [D-3001] cut_of_orderIso_bounds
theorem cut_of_orderIso_bounds {P Q : Type*} [PartialOrder L] [PartialOrder P]
    [PartialOrder Q] {pb pt : P} {qb qt : Q}
    (hpb : ∀ p, pb ≤ p) (hpt : ∀ p, p ≤ pt)
    (hqb : ∀ q, qb ≤ q) (hqt : ∀ q, q ≤ qt)
    (hP : pb ≠ pt) (hQ : qb ≠ qt) {A : Set L} (hA : IsCut A)
    (e : L ≃o (P × Q)) :
    (∀ a ∈ A, ∀ a' ∈ A, a = a') ∨ (∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, b = b') := by
  rcases cut_prod_bounds hpb hpt hqb hqt hP hQ (isCut_image e hA) with h | h
  · refine Or.inl (fun a ha a' ha' => e.injective ?_)
    rw [h _ ⟨a, ha, rfl⟩, h _ ⟨a', ha', rfl⟩]
  · refine Or.inr (fun b hb b' hb' => e.injective ?_)
    have hcompl : ∀ c, c ∉ A → e c ∈ (e '' A)ᶜ := by
      intro c hc hmem
      obtain ⟨c0, hc0, hce⟩ := hmem
      exact hc (e.injective hce ▸ hc0)
    rw [h _ (hcompl b hb), h _ (hcompl b' hb')]

-- [D-3002] no_iso_of_cut_bounds
theorem no_iso_of_cut_bounds {P Q : Type*} [PartialOrder L] [Fintype L]
    [PartialOrder P] [Fintype P] [PartialOrder Q] [Fintype Q]
    {pb pt : P} {qb qt : Q}
    (hpb : ∀ p, pb ≤ p) (hpt : ∀ p, p ≤ pt)
    (hqb : ∀ q, qb ≤ q) (hqt : ∀ q, q ≤ qt)
    (hP : pb ≠ pt) (hQ : qb ≠ qt)
    {A : Set L} (hA : IsCut A) (hAne : A.Nonempty) (hcne : (Aᶜ : Set L).Nonempty)
    (hdvd : Fintype.card P ∣ Fintype.card ↥(Aᶜ))
    (e : L ≃o (P × Q)) : False := by
  classical
  have hPcard : 2 ≤ Fintype.card P := by
    by_contra hcon
    have hs : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact hP (Subsingleton.elim _ _)
  have hcpos : 0 < Fintype.card ↑(Aᶜ) :=
    Fintype.card_pos_iff.mpr ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
  have hc2 : 2 ≤ Fintype.card ↥(Aᶜ) := le_trans hPcard (Nat.le_of_dvd hcpos hdvd)
  have hsub : ∀ a ∈ A, ∀ a' ∈ A, a = a' := by
    rcases cut_of_orderIso_bounds hpb hpt hqb hqt hP hQ hA e with h | h
    · exact h
    · exfalso
      have hss : Subsingleton ↥(Aᶜ) := ⟨fun b b' => Subtype.ext (h b.1 b.2 b'.1 b'.2)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hss
      omega
  have hA1 : Fintype.card ↥A = 1 := by
    have hpos : 0 < Fintype.card ↥A :=
      Fintype.card_pos_iff.mpr ⟨⟨hAne.choose, hAne.choose_spec⟩⟩
    have hle : Fintype.card ↥A ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr
        ⟨fun a a' => Subtype.ext (hsub a.1 a.2 a'.1 a'.2)⟩
    omega
  have hsplit : Fintype.card ↥A + Fintype.card ↥(Aᶜ) = Fintype.card L := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl A)
  have hLcard : Fintype.card L = Fintype.card P * Fintype.card Q := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_prod]
  have hd1 : Fintype.card P ∣ Fintype.card L := ⟨Fintype.card Q, hLcard⟩
  have hd2 : Fintype.card P ∣ Fintype.card L - Fintype.card ↥(Aᶜ) :=
    Nat.dvd_sub hd1 hdvd
  rw [show Fintype.card L - Fintype.card ↥(Aᶜ) = 1 by omega] at hd2
  have := Nat.dvd_one.mp hd2
  omega

end CutObstruction
