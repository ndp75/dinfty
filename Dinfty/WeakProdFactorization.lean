import Dinfty.AtomFactorGeneration

/-!
# Unique factorization for restricted products

`Indecomposable` stopped at exactly this worry:

> The factors `(D j)ᵒᵖ` are pairwise non-isomorphic … but "no shift" is not a
> proof, and **unique factorization can fail for infinite products**.

For restricted products of posets each having a **least non-`⊥` element**, it
does not fail.  This module proves it, and the proof is short because the
atom-factor already does the work: the axes are order-theoretically visible from
the atoms, so an isomorphism has no choice but to permute them.

## The statement

```lean
transferIndex   : ℕ → ℕ                     -- induced by e : WeakProd D ≃o WeakProd E
transferIndex_spec       : D j ≃o E (transferIndex e j)
transferIndex_injective  /  transferIndex_surjective
```

So an isomorphism of restricted products **is** a permutation of the factors,
factorwise.  `WeakProductAbsorption.tower_no_absorb_two` is the special case
`E = C₂ :: D` seen through cardinality; this is the general fact, and it needs
no cardinality at all.

## Why this is the copy-`A` step

`AtomFactorGeneration` disposes of copy-`B` and copy-`C` competitors — their
seeds are ordinal sums and fail `GenByFactors`.  Copy-`A` competitors *are*
generated, so generation says nothing about them; what excludes them is that
their seed `(↑p) × S_q` would have to reproduce the marked point's factor list
`{D 0, …, D (N-1)}`, and `↑p` is a proper up-set unless `p = ⊥`.

`transferIndex` is that comparison made precise: the factors correspond one for
one, so a competitor cannot quietly absorb or split one.

**Still needed for the copy-`A` step** (and not proved here): the finite
competitor's factors must be matched against the *tail* `{D j : j ≥ N}` as well,
which is where the tower's cardinality growth enters — `↑p ⊆ D (N-1)` and
`S_q ⊆ J(D (N-1))` are both smaller than `D N`, so neither can be mistaken for a
tail factor.  Those are two `Fintype.card` inequalities about the tower, not
statements about restricted products, and they are stated but not proved in
`Dinfty/SeedShape.lean`'s docstring.
-/

open scoped Classical

universe u v

namespace WeakProdFactorization

open WeakProductAbsorption AtomFactorGeneration

/-! ## Atom-factors correspond along an isomorphism -/

/-- **Corresponding atom-factors are order-isomorphic.**  This is the formal
replacement for "the multiset of atom-factors is an invariant". -/
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

/-! ## The axes of a restricted product -/

section Axis

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable (lam : ∀ j, D j)
variable (hlam_ne : ∀ j, lam j ≠ ⊥) (hlam_le : ∀ j (z : D j), z ≠ ⊥ → lam j ≤ z)

include hlam_ne hlam_le

/-- Distinct indices give distinct atoms. -/
theorem single_lam_inj {i j : ℕ} (h : (single i (lam i) : WeakProd D) = single j (lam j)) :
    i = j := by
  by_contra hij
  have hval := congrFun (congrArg Subtype.val h) i
  rw [single_apply_self, single_apply_ne hij] at hval
  exact hlam_ne i hval

/-- An element of the `j`-th atom-factor is `single j` of its `j`-th coordinate. -/
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

/-- **The `j`-th atom-factor is the `j`-th factor.** -/
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

/-! ## The induced permutation of factors -/

section Transfer

variable {D : ℕ → Type u} {E : ℕ → Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

/-- The image of the `j`-th atom is an atom, hence some `single i (lamE i)`. -/
theorem exists_transfer (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    ∃ i : ℕ, e (single j (lamD j)) = single i (lamE i) :=
  atom_eq_single lamE hE_ne hE_le
    (orderIso_isAtom e (isAtom_single lamD hD_ne hD_le j))

/-- **The index map an isomorphism induces on factors.** -/
noncomputable def transferIndex (e : WeakProd D ≃o WeakProd E) (j : ℕ) : ℕ :=
  (exists_transfer lamD lamE hD_ne hD_le hE_ne hE_le e j).choose

theorem transferIndex_eq (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    e (single j (lamD j)) = single (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)
      (lamE (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)) :=
  (exists_transfer lamD lamE hD_ne hD_le hE_ne hE_le e j).choose_spec

/-- **Corresponding factors are isomorphic** — the factors are permuted, not
reshaped. -/
theorem transferIndex_spec (e : WeakProd D ≃o WeakProd E) (j : ℕ) :
    Nonempty (D j ≃o E (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e j)) := by
  refine ⟨((axisIso lamD hD_ne hD_le j).symm.trans
    (atomFactorIso e (single j (lamD j)))).trans ?_⟩
  rw [transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j]
  exact axisIso lamE hE_ne hE_le _

theorem transferIndex_injective (e : WeakProd D ≃o WeakProd E) :
    Function.Injective (transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e) := by
  intro j j' h
  have h1 := transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j
  have h2 := transferIndex_eq lamD lamE hD_ne hD_le hE_ne hE_le e j'
  rw [h] at h1
  exact single_lam_inj lamD hD_ne hD_le (e.injective (h1.trans h2.symm))

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

/-- **Unique factorization.**  An isomorphism of restricted products is a
permutation of the factors, factorwise — so unique factorization does *not* fail
here, which is what `Indecomposable` left in doubt. -/
theorem weakProd_uniqueFactorization (e : WeakProd D ≃o WeakProd E) :
    ∃ σ : ℕ → ℕ, Function.Bijective σ ∧ ∀ j, Nonempty (D j ≃o E (σ j)) :=
  ⟨transferIndex lamD lamE hD_ne hD_le hE_ne hE_le e,
   ⟨transferIndex_injective lamD lamE hD_ne hD_le hE_ne hE_le e,
    transferIndex_surjective lamD lamE hD_ne hD_le hE_ne hE_le e⟩,
   transferIndex_spec lamD lamE hD_ne hD_le hE_ne hE_le e⟩

end Transfer

/-! ## Factors of a product with a finite piece -/

section ProdFactor

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic A]

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

/-- **A right-hand atom's factor is computed in the right-hand poset.** -/
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

/-! ## The copy-`A` input: a finite piece's factors are factors of the product -/

section FinitePiece

variable {D : ℕ → Type u} {E : ℕ → Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable [PartialOrder S] [OrderBot S]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le hE_ne hE_le

/-- **Every atom-factor of the finite piece is one of the `D j`.**

If a restricted product is isomorphic to another restricted product times a
piece `S`, then each of `S`'s own atom-factors is a factor of the first product.
This is the copy-`A` input: a competitor's finite seed cannot contain a factor
that is not already on the marked point's list. -/
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

/-- **The index is bounded by cardinality.**  If the factor is smaller than
`D N` and the family grows, the matching index is below `N`.  This is the step
that confines a competitor's finite seed to the *initial* factors. -/
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

/-! ## The left-hand factor, and the converse direction -/

section ProdFactorLeft

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic B]

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

/-- **A left-hand atom's factor is computed in the left-hand poset.** -/
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

/-- **Every factor of the first product reappears**, either as a factor of the
second product or as an atom-factor of the finite piece. -/
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

/-- **Cardinality forces the finite piece to carry it.**  If `D j` is strictly
smaller than every `E i`, it cannot be one of them, so it must appear among the
atom-factors of `S`.

This is the step that pins `p = ⊥` in the copy-`A` case: with `E` the tail of
the tower and `D j = D (N-1)`, the marked point's `(N-1)`-st factor has to be
reproduced inside the competitor's finite seed, and a proper up-set is too
small (`TowerCardGrowth.card_upSet_lt`). -/
theorem factor_in_finite_piece [∀ j, Fintype (D j)] [∀ i, Fintype (E i)]
    (e : WeakProd D ≃o (WeakProd E × S)) (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i)) :
    ∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β)) := by
  rcases factor_index_of_prod lamD lamE hD_ne hD_le hE_ne hE_le e j with ⟨i, ⟨iso⟩⟩ | h
  · exact absurd (Fintype.card_congr iso.toEquiv) (Nat.ne_of_lt (hsmall i))
  · exact h

end Converse

/-! ## The copy-`A` exclusion, assembled -/

section CopyA

variable {A : Type u} {B : Type u} [PartialOrder A] [OrderBot A] [PartialOrder B]
  [OrderBot B] [IsAtomic A] [IsAtomic B] [Fintype A] [Fintype B]

theorem card_atomFactor_le {X : Type u} [PartialOrder X] [OrderBot X] [Fintype X]
    (x : X) : Fintype.card ↥(atomFactor X x) ≤ Fintype.card X :=
  Fintype.card_le_of_injective (fun w => w.1) (fun _ _ h => Subtype.ext h)

/-- **An atom-factor of a product lives in one of the two sides**, so it is no
bigger than that side. -/
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

/-- **The copy-`A` exclusion.**

If a competitor's finite seed is a product `A × B` of two pieces *both* strictly
smaller than `D j`, and `D j` is strictly smaller than every tail factor, then no
isomorphism exists: `D j` has to reappear as an atom-factor of the finite seed
(`factor_in_finite_piece`), but every atom-factor of `A × B` fits inside `A` or
inside `B`.

For the tower this is `A = ↑p`, `B = S_q`, `j = N-1`: a **proper** up-set of
`D (N-1)` is strictly smaller (`TowerCardGrowth.card_upSet_lt`) and so is the
seed of a join-irreducible (`TowerCardGrowth.card_joinIrred_lt`) — so `p ≠ ⊥` is
impossible, which is exactly the step the induction needs. -/
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

/-! ## A finite piece on the left as well

`topJ`'s seed is `WeakProd (Fam 0) × C₂`, not a bare `WeakProd`, so the
comparison it needs has a finite piece on **both** sides.  The proofs are the
ones above with `single j (lamD j)` replaced by `(single j (lamD j), ⊥)`, whose
atom-factor is still `D j` because a left-hand atom's factor is computed on the
left (`atomFactorProdLeftIso`). -/

section LeftPiece

variable {D : ℕ → Type u} {E : ℕ → Type u} {T : Type u} {S : Type u}
variable [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]
variable [PartialOrder T] [OrderBot T] [IsAtomic T]
variable [PartialOrder S] [OrderBot S] [IsAtomic S]
variable (lamD : ∀ j, D j) (lamE : ∀ j, E j)
variable (hD_ne : ∀ j, lamD j ≠ ⊥) (hD_le : ∀ j (z : D j), z ≠ ⊥ → lamD j ≤ z)
variable (hE_ne : ∀ j, lamE j ≠ ⊥) (hE_le : ∀ j (z : E j), z ≠ ⊥ → lamE j ≤ z)

include hD_ne hD_le in
theorem isAtom_singleL (j : ℕ) :
    IsAtom (((single j (lamD j) : WeakProd D), (⊥ : T))) :=
  prodIsAtom_iff.mpr (Or.inl ⟨isAtom_single lamD hD_ne hD_le j, rfl⟩)

include hD_ne hD_le in
/-- The `j`-th axis is still the `j`-th factor, with a piece on the left. -/
noncomputable def axisIsoL (j : ℕ) :
    ↥(atomFactor (WeakProd D × T) (((single j (lamD j) : WeakProd D), (⊥ : T)))) ≃o D j :=
  (atomFactorProdLeftIso (B := T) (single j (lamD j))).trans (axisIso lamD hD_ne hD_le j)

include hD_ne hD_le hE_ne hE_le in
/-- **Every factor of the left product reappears** — as a factor of the right
product, or as an atom-factor of the right-hand finite piece. -/
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

include hD_ne hD_le hE_ne hE_le in
theorem factor_in_finite_pieceL [∀ j, Fintype (D j)] [∀ i, Fintype (E i)]
    (e : (WeakProd D × T) ≃o (WeakProd E × S)) (j : ℕ)
    (hsmall : ∀ i, Fintype.card (D j) < Fintype.card (E i)) :
    ∃ β : S, IsAtom β ∧ Nonempty (D j ≃o ↥(atomFactor S β)) := by
  rcases factor_index_of_prodL (T := T) lamD lamE hD_ne hD_le hE_ne hE_le e j with
    ⟨i, ⟨iso⟩⟩ | h
  · exact absurd (Fintype.card_congr iso.toEquiv) (Nat.ne_of_lt (hsmall i))
  · exact h

include hD_ne hD_le hE_ne hE_le in
/-- **The copy-`A` exclusion, with a finite piece on the left.** -/
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
