import Dinfty.ProdAut

/-!
# No infinite absorption: `X ≇ X × 2` for the tower's restricted product

`Indecomposable` reduced §17's two-seed question to a statement in poset
algebra and then stopped there, with the remaining question named exactly:

> **Does not settle:** whether such an infinite absorption exists here.  The
> factors `(D j)ᵒᵖ` are pairwise non-isomorphic … but "no shift" is not a proof,
> and unique factorization can fail for infinite products.

**It does not exist**, and the proof needs neither unique factorization nor
pairwise-distinctness of the factors — only the property `Indecomposable`
already isolated, that **each factor has a least non-`⊥` element**.

## The invariant: the atom-factor

For an atom `α` of a poset with `⊥`, put

```lean
atomFactor L α = {w | ∀ β, IsAtom β → β ≤ w → β = α}
```

— everything whose atoms are all `α`.  It is order-theoretic, so an isomorphism
carries `atomFactor L α` onto `atomFactor L' (e α)` (`atomFactorIso`).

Now look at `L × C₂`.  Its extra atom is `z = (⊥, 1)`, and — as soon as `L` is
atomic — `atomFactor (L × C₂) z` is **exactly `{⊥, z}`**, two elements
(`atomFactor_prodTwo_top`).  So:

```lean
no_iso_prod_two :
  (∀ α, IsAtom α → ∃ w ∈ atomFactor L α, w ≠ ⊥ ∧ w ≠ α) → IsEmpty (L ≃o L × C₂)
```

An isomorphism would produce an atom of `L` whose own atom-factor has only two
elements.  **A two-element factor cannot be hidden**: it is visible from the
atom alone.

## Instantiated at the restricted product

`WeakProd D` is `{x : ∀ j, D j // x j = ⊥ for large j}`, ordered pointwise —
the object `Indecomposable` calls `⨁_j (D j)ᵒᵖ`, up to the dualisation that
`§17`'s recursion introduces.  If every `D j` has a least non-`⊥` element
`lam j`, then

* every atom of `WeakProd D` is a `single j (lam j)` (`atom_eq_single`),
* and `atomFactor (WeakProd D) (single j (lam j))` is the `j`-th axis
  (`atomFactor_single`) — i.e. `D j` itself.

So the hypothesis of `no_iso_prod_two` says exactly *no `D j` has only two
elements*, and

```lean
weakProd_no_absorb_two : IsEmpty (WeakProd D ≃o WeakProd D × C₂)
```

Every `D k` of the tower has a least non-`⊥` element
(`UniqueAtomCoatom.unique_atom`, carried at every level) and has more than two
(already `|D 0| = 3`), so the tower's family satisfies both hypotheses.

## Scope — read this before citing it

This closes the poset-algebra question `Indecomposable` left open, and with it
the only route by which the two seeds of §17 could have been identified.  It
does **not** close `TwoPointFixed`.

Two things stand between them, and both are unformalised:

1. that `JBelow midInf` and `JBelow (toD 0 ⊤)` really are `WeakProd`-shaped
   with seeds `1` and `C₂` — the down-set/join-irreducible recursion at the
   *colimit*, which exists in the notes and not in Lean;
2. and, even granted that, seed separation quantifies over **all** of stage
   `N`, not just the two points.  Non-isomorphism of these two seeds is
   necessary, not sufficient.

So: the seeds do not collide.  Whether some *third* element shares `midInf`'s
seed is untouched.
-/

open scoped Classical

universe u v

namespace WeakProductAbsorption

/-! ## The atom-factor -/

/-- Atoms transport along an order-isomorphism. -/
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

/-- Everything whose atoms are all `α`.  `⊥` is in it vacuously. -/
def atomFactor (L : Type u) [PartialOrder L] [OrderBot L] (α : L) : Set L :=
  {w | ∀ β : L, IsAtom β → β ≤ w → β = α}

theorem bot_mem_atomFactor {L : Type u} [PartialOrder L] [OrderBot L] (α : L) :
    (⊥ : L) ∈ atomFactor L α := by
  intro β hβ hle
  exact absurd (le_bot_iff.mp hle) hβ.1

/-- **The atom-factor is an isomorphism invariant.** -/
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

/-! ## Two elements is two elements: the `× C₂` obstruction -/

section ProdTwo

variable {L : Type u} [PartialOrder L] [OrderBot L]

/-- `(⊥, 1)` is an atom of `L × Fin 2`. -/
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

/-- **The extra factor is visible.**  When `L` is atomic, the atom-factor of
`(⊥, 1)` in `L × Fin 2` is exactly `{⊥, (⊥,1)}`. -/
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

/-- **No poset absorbs a two-element factor**, provided every one of its own
atom-factors has a third element. -/
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

/-! ## The restricted product -/

section WeakProdDef

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]

/-- `{x : ∀ j, D j // x j = ⊥ for all large j}`, ordered pointwise. -/
def WeakProd (D : ℕ → Type u) [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)] : Type u :=
  {x : ∀ j, D j // ∃ N, ∀ j, N ≤ j → x j = ⊥}

instance : PartialOrder (WeakProd D) := Subtype.partialOrder _

theorem WeakProd.le_def {x y : WeakProd D} : x ≤ y ↔ ∀ j, x.1 j ≤ y.1 j := Iff.rfl

instance : OrderBot (WeakProd D) where
  bot := ⟨fun _ => ⊥, ⟨0, fun _ _ => rfl⟩⟩
  bot_le _ := fun _ => bot_le

@[simp] theorem WeakProd.bot_apply (j : ℕ) : (⊥ : WeakProd D).1 j = ⊥ := rfl

theorem WeakProd.eq_bot_iff' {x : WeakProd D} : x = ⊥ ↔ ∀ j, x.1 j = ⊥ := by
  constructor
  · rintro rfl j
    rfl
  · intro h
    exact Subtype.ext (funext h)

/-- The element supported at `j` with value `a`. -/
def single (j : ℕ) (a : D j) : WeakProd D :=
  ⟨Function.update (fun i => (⊥ : D i)) j a, ⟨j + 1, by
    intro i hi
    rw [Function.update_of_ne (by omega)]⟩⟩

@[simp] theorem single_apply_self (j : ℕ) (a : D j) : (single j a).1 j = a := by
  show Function.update (fun i => (⊥ : D i)) j a j = a
  simp

@[simp] theorem single_apply_ne {j i : ℕ} (h : i ≠ j) (a : D j) :
    (single j a).1 i = ⊥ := by
  show Function.update (fun i => (⊥ : D i)) j a i = ⊥
  rw [Function.update_of_ne h]

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

/-! ## Atoms and atom-factors of the restricted product -/

section WeakProdAtoms

variable {D : ℕ → Type u} [∀ j, PartialOrder (D j)] [∀ j, OrderBot (D j)]
variable (lam : ∀ j, D j)
variable (hlam_ne : ∀ j, lam j ≠ ⊥) (hlam_le : ∀ j (z : D j), z ≠ ⊥ → lam j ≤ z)

include hlam_ne hlam_le

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

/-- **Every atom of the restricted product is a `single`** — this is where the
least non-`⊥` element is spent. -/
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

/-- **The atom-factor of the `j`-th atom is the `j`-th axis.** -/
theorem atomFactor_single {j : ℕ} {w : WeakProd D}
    (hw : w ∈ atomFactor (WeakProd D) (single j (lam j))) (i : ℕ) (hij : i ≠ j) :
    w.1 i = ⊥ := by
  by_contra hcon
  have hle : single i (lam i) ≤ w := single_le_iff.mpr (hlam_le i _ hcon)
  have h1 := hw _ (isAtom_single lam hlam_ne hlam_le i) hle
  have h2 := congrFun (congrArg Subtype.val h1) i
  rw [single_apply_self, single_apply_ne hij] at h2
  exact hlam_ne i h2

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

theorem isAtomic_weakProd : IsAtomic (WeakProd D) := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = ⊥
  · exact Or.inl hx
  · rw [WeakProd.eq_bot_iff'] at hx
    push_neg at hx
    obtain ⟨j, hj⟩ := hx
    exact Or.inr ⟨single j (lam j), isAtom_single lam hlam_ne hlam_le j,
      single_le_iff.mpr (hlam_le j _ hj)⟩

/-- **The restricted product absorbs no two-element factor.**

The only hypothesis beyond "each factor has a least non-`⊥` element" is that
each factor has a *third* element — for the tower, `|D 0| = 3` and the levels
only grow. -/
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
