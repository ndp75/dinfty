import Mathlib.Tactic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Set

/-!
# The cut obstruction

A **cut** of a poset `L` is a set `A` with everything in `A` below everything
outside it — an ordinal-sum decomposition `L = A ⊕ Aᶜ`.

The point of this file is one fact:

> **A product has only trivial cuts.**  If `P` and `Q` are bounded and each has
> `⊥ ≠ ⊤`, then any cut of `P × Q` is a subsingleton or has subsingleton
> complement.

The proof is three lines of order theory.  `(⊤, ⊥)` and `(⊥, ⊤)` are
incomparable, so a cut cannot separate them; whichever side they land on
collapses the other side to `⊥` or to `⊤`.

Combined with a divisibility count on the *upper* part this is a genuine
obstruction to `L ≃o P × Q`, and it needs nothing about `L` except the cut:

```
no_iso_of_cut :  IsCut A → A.Nonempty → Aᶜ.Nonempty →
                 card P ∣ card ↥(Aᶜ) → (L ≃o P × Q) → False
```

Read it as: the cut forces `A` to be a single point, so `card L = 1 + card Aᶜ`;
but `card P` divides both `card L` and `card Aᶜ`, hence divides `1`.

This file is pure order theory — it mentions nothing about the tower.
-/

open scoped Classical

namespace CutObstruction

variable {L : Type*}

/-- `A` is a **cut** of `L`: everything in `A` lies below everything outside it.

Antisymmetry makes `A` automatically a down-set: if `c ≤ a ∈ A` and `c ∉ A` then
`a ≤ c` too, so `a = c ∈ A`. -/
def IsCut [Preorder L] (A : Set L) : Prop := ∀ a ∈ A, ∀ b ∉ A, a ≤ b

theorem IsCut.isLowerSet [PartialOrder L] {A : Set L} (h : IsCut A) :
    IsLowerSet A := by
  intro a c hca ha
  by_contra hc
  exact hc (le_antisymm hca (h a ha c hc) ▸ ha)

/-- Cuts transport along order isomorphisms. -/
theorem isCut_image {L' : Type*} [Preorder L] [Preorder L'] (e : L ≃o L')
    {A : Set L} (h : IsCut A) : IsCut (e '' A) := by
  rintro a ⟨a0, ha0, rfl⟩ b hb
  rw [← e.apply_symm_apply b]
  refine e.map_rel_iff.mpr (h a0 ha0 (e.symm b) ?_)
  intro hmem
  exact hb ⟨_, hmem, e.apply_symm_apply b⟩

/-- **A product has only trivial cuts.**

`(⊤, ⊥)` and `(⊥, ⊤)` are incomparable, so a cut cannot put one in `A` and the
other outside.  If both are in `A`, everything outside is above both, hence `⊤`.
If both are outside, everything inside is below both, hence `⊥`. -/
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

/-- The same, transported: a cut of anything isomorphic to a product is a
subsingleton or has subsingleton complement. -/
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

/-! ## The obstruction -/

theorem two_le_card_of_bot_ne_top {P : Type*} [PartialOrder P] [BoundedOrder P]
    [Fintype P] (hP : (⊥ : P) ≠ ⊤) : 2 ≤ Fintype.card P := by
  by_contra h
  have hs : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hP (Subsingleton.elim _ _)

/-- **The cut obstruction.**

If `L` carries a cut whose *upper* part `Aᶜ` has size divisible by `card P`,
then `L` is not isomorphic to `P × Q` — for any bounded nondegenerate `P`, `Q`.

The cut collapses `A` to one point (the upper part is too big to be the side
that collapses), so `card L = 1 + card ↥(Aᶜ)`; then `card P` divides `card L`
and `card ↥(Aᶜ)`, hence `1`. -/
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
  -- the upper part is too big to be the collapsing side
  have hsub : ∀ a ∈ A, ∀ a' ∈ A, a = a' := by
    rcases cut_of_orderIso hP hQ hA e with h | h
    · exact h
    · exfalso
      have : Subsingleton ↥(Aᶜ) := ⟨fun b b' => Subtype.ext (h b.1 b.2 b'.1 b'.2)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr this
      omega
  -- so `A` is a single point
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
  -- `card P` divides `card L` and `card ↥(Aᶜ)`, hence `1`
  have hd1 : Fintype.card P ∣ Fintype.card L := ⟨Fintype.card Q, hLcard⟩
  have hd2 : Fintype.card P ∣ Fintype.card L - Fintype.card ↥(Aᶜ) :=
    Nat.dvd_sub hd1 hdvd
  rw [show Fintype.card L - Fintype.card ↥(Aᶜ) = 1 by omega] at hd2
  have := Nat.dvd_one.mp hd2
  omega

/-! ## The same, with the bounds supplied as data

`BoundedOrder` instances are often not registered on the posets we actually meet
(a dualised seed has a bottom and a top, but neither is an instance).  So here is
the same statement with the four bounds passed in explicitly.  This is the form
the tower uses. -/

/-- **A product has only trivial cuts** — bounds as data. -/
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

/-- **The cut obstruction**, bounds as data.

`L` carries a cut whose upper part `Aᶜ` has size divisible by `card P`.  Then
`L ≃o P × Q` is impossible.  The cut collapses `A` to one point — the upper part
is too big to be the side that collapses — so `card L = 1 + card ↥(Aᶜ)`, and
`card P` divides both `card L` and `card ↥(Aᶜ)`, hence `1`. -/
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
