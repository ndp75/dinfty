import Dinfty.SeedChain
import Dinfty.WeakProdFactorization

open GluingTowerLibrary SierpinskiApplication

/-!
# The shape, proved

This is the input `SeedShape` named and left open: for a join-irreducible
`z = toD N y`,

```lean
seedShape : (JBelow z)ᵒᵈ ≃o (WeakProd (fun j => D (N + j)) × (LevelSeed N y)ᵒᵈ)
```

Both sides are increasing unions (`ChainUnion`), the level-wise pieces match
(`SeedLevelStep.levelStepIso`), and the two chain maps agree under that match
(`SeedLevelStep.levelStepIso_symm_bot`: the tower's embedding is exactly
insertion of `⊥` in the new coordinate).  `ChainUnion.chainUnionIso` does the
rest.

## Where the dualisation goes

`levelStepIso` produces `(D k)ᵒᵈ × LevelSeed k v`, and the chain map inserts
`toDual ⊥` — the **top** of `(D k)ᵒᵈ`.  `WeakProd` inserts `⊥`.  So the whole
identification is stated for the *dual* of the seed, where the new factor is
`D k` itself and the inserted value is `⊥`.  That is why every statement about
seeds in this development carries a `ᵒᵈ`.
-/

open scoped Classical

namespace SeedShapeProof

open SeedChain SeedLevelStep ChainUnion WeakProductAbsorption JSeedRecursion
open SeedSeparation JoinIrredLevelStable JoinIrredDInfty

private theorem prodEq {A B : Type*} {p q : A × B} (h1 : p.1 = q.1) (h2 : p.2 = q.2) :
    p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only at h1 h2
  subst h1
  subst h2
  rfl

variable (N : ℕ) (y : D N) (hy : JoinIrred (D N) y)

/-- The family of factors: the tower from level `N` on. -/
abbrev Fam (j : ℕ) : Type := D (N + j)

/-- The finite piece: the dual of the seed at the bottom level. -/
abbrev Base : Type := (SeedAt N y 0)ᵒᵈ

/-- The dualised seed at level `N + k`. -/
abbrev DSeed (k : ℕ) : Type := (SeedAt N y k)ᵒᵈ

/-! ## The level step, dualised -/

/-- `levelStepIso`, dualised: the new factor is `D (N+k)` and the inserted value
will be its `⊥`. -/
noncomputable def dLevelStep (k : ℕ) :
    DSeed N y (k + 1) ≃o (Fam N k × DSeed N y k) :=
  ((levelStepIso (N + k) (yAt N y k) (joinIrred_yAt N y hy k)).dual).trans
    ((prodDualIso ((D (N + k))ᵒᵈ) (SeedAt N y k)).trans
      (prodCongrIso (dualDualIso (D (N + k))) (OrderIso.refl _)))

theorem dLevelStep_step (k : ℕ) (u : DSeed N y k) :
    dLevelStep N y hy k (seedStep N y k u) = ((⊥ : Fam N k), u) := by
  have hsymm : (levelStepIso (N + k) (yAt N y k) (joinIrred_yAt N y hy k)).symm
      (OrderDual.toDual (⊥ : D (N + k)), u) = seedStep N y k u := by
    apply Subtype.ext
    exact levelStepIso_symm_bot (N + k) (yAt N y k) (joinIrred_yAt N y hy k) u
  have hfwd : levelStepIso (N + k) (yAt N y k) (joinIrred_yAt N y hy k)
      (seedStep N y k u) = (OrderDual.toDual (⊥ : D (N + k)), u) := by
    rw [← hsymm, OrderIso.apply_symm_apply]
    rfl
  show (prodCongrIso (dualDualIso (D (N + k))) (OrderIso.refl _))
      ((prodDualIso ((D (N + k))ᵒᵈ) (SeedAt N y k))
        ((levelStepIso (N + k) (yAt N y k) (joinIrred_yAt N y hy k)) (seedStep N y k u)))
    = ((⊥ : Fam N k), u)
  rw [hfwd]
  rfl

/-! ## The restricted-product side, as an increasing union -/

/-- Elements of `WeakProd Fam × Base` supported below `k`. -/
abbrev Supp (k : ℕ) : Type :=
  {x : WeakProd (Fam N) × Base N y // ∀ j, k ≤ j → x.1.1 j = ⊥}

noncomputable def suppStep (k : ℕ) (x : Supp N y k) : Supp N y (k + 1) :=
  ⟨x.1, fun j hj => x.2 j (Nat.le_of_succ_le hj)⟩

/-- **The restricted product is the increasing union of its finite-support
pieces.** -/
noncomputable def suppPres : Pres (WeakProd (Fam N) × Base N y) (Supp N y) where
  step := suppStep N y
  incl := fun _ x => x.1
  incl_le_iff := fun _ _ _ => Iff.rfl
  incl_step := fun _ _ => rfl
  incl_surj := by
    intro x
    obtain ⟨M, hM⟩ := x.1.2
    exact ⟨M, ⟨x, hM⟩, rfl⟩

/-! ## Peeling one coordinate off the finite-support pieces -/

section Peel

variable (k : ℕ)

private theorem upd_supp (x : WeakProd (Fam N)) (p : Fam N k) :
    ∃ M, ∀ j, M ≤ j → Function.update x.1 k p j = ⊥ := by
  obtain ⟨M, hM⟩ := x.2
  refine ⟨max M (k + 1), fun j hj => ?_⟩
  rw [Function.update_of_ne (by omega)]
  exact hM j (le_trans (le_max_left M (k + 1)) hj)

/-- Replace the `k`-th coordinate. -/
noncomputable def updAt (x : WeakProd (Fam N)) (p : Fam N k) : WeakProd (Fam N) :=
  ⟨Function.update x.1 k p, upd_supp N k x p⟩

@[simp] theorem updAt_apply_self (x : WeakProd (Fam N)) (p : Fam N k) :
    (updAt N k x p).1 k = p := Function.update_self _ _ _

@[simp] theorem updAt_apply_ne (x : WeakProd (Fam N)) (p : Fam N k) {j : ℕ} (h : j ≠ k) :
    (updAt N k x p).1 j = x.1 j := Function.update_of_ne h _ _

/-- Peel the `k`-th coordinate off. -/
noncomputable def peelFun (x : Supp N y (k + 1)) : Fam N k × Supp N y k :=
  (x.1.1.1 k, ⟨(updAt N k x.1.1 ⊥, x.1.2), by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact updAt_apply_self N k x.1.1 ⊥
    · rw [updAt_apply_ne N k x.1.1 ⊥ (by omega)]
      exact x.2 j (by omega)⟩)

/-- …and put it back. -/
noncomputable def peelInv (w : Fam N k × Supp N y k) : Supp N y (k + 1) :=
  ⟨(updAt N k w.2.1.1 w.1, w.2.1.2), by
    intro j hj
    rw [updAt_apply_ne N k w.2.1.1 w.1 (by omega)]
    exact w.2.2 j (by omega)⟩

theorem peelInv_peelFun (x : Supp N y (k + 1)) : peelInv N y k (peelFun N y k x) = x := by
  refine Subtype.ext (prodEq ?_ rfl)
  refine Subtype.ext ?_
  funext j
  show (updAt N k (updAt N k x.1.1 ⊥) (x.1.1.1 k)).1 j = x.1.1.1 j
  by_cases h : j = k
  · rw [h, updAt_apply_self]
  · rw [updAt_apply_ne N k _ _ h, updAt_apply_ne N k _ _ h]

theorem peelFun_peelInv (w : Fam N k × Supp N y k) : peelFun N y k (peelInv N y k w) = w := by
  refine prodEq (updAt_apply_self N k w.2.1.1 w.1) ?_
  refine Subtype.ext (prodEq ?_ rfl)
  refine Subtype.ext ?_
  funext j
  show (updAt N k (updAt N k w.2.1.1 w.1) ⊥).1 j = w.2.1.1.1 j
  by_cases h : j = k
  · rw [h, updAt_apply_self]
    exact (w.2.2 k (le_refl k)).symm
  · rw [updAt_apply_ne N k _ _ h, updAt_apply_ne N k _ _ h]

theorem peelFun_le_iff (a b : Supp N y (k + 1)) :
    peelFun N y k a ≤ peelFun N y k b ↔ a ≤ b := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, h2.2⟩
    by_cases h : j = k
    · rw [h]
      exact h1
    · have hj : (updAt N k a.1.1 ⊥).1 j ≤ (updAt N k b.1.1 ⊥).1 j := h2.1 j
      rwa [updAt_apply_ne N k _ _ h, updAt_apply_ne N k _ _ h] at hj
  · intro h
    refine ⟨h.1 k, ⟨fun j => ?_, h.2⟩⟩
    show (updAt N k a.1.1 ⊥).1 j ≤ (updAt N k b.1.1 ⊥).1 j
    by_cases hj : j = k
    · rw [hj, updAt_apply_self, updAt_apply_self]
    · rw [updAt_apply_ne N k _ _ hj, updAt_apply_ne N k _ _ hj]
      exact h.1 j

/-- **The `(k+1)`-supported piece is the `k`-th factor times the `k`-supported
piece.** -/
noncomputable def peelIso : Supp N y (k + 1) ≃o (Fam N k × Supp N y k) where
  toFun := peelFun N y k
  invFun := peelInv N y k
  left_inv := peelInv_peelFun N y k
  right_inv := peelFun_peelInv N y k
  map_rel_iff' := fun {a b} => peelFun_le_iff N y k a b

theorem peelIso_step (x : Supp N y k) :
    peelIso N y k (suppStep N y k x) = ((⊥ : Fam N k), x) := by
  show peelFun N y k (suppStep N y k x) = ((⊥ : Fam N k), x)
  refine prodEq (x.2 k (le_refl k)) ?_
  refine Subtype.ext (prodEq ?_ rfl)
  refine Subtype.ext ?_
  funext j
  show (updAt N k x.1.1 ⊥).1 j = x.1.1.1 j
  by_cases h : j = k
  · rw [h, updAt_apply_self]
    exact (x.2 k (le_refl k)).symm
  · exact updAt_apply_ne N k _ _ h

end Peel

/-! ## The level-wise isomorphism, and the shape -/

/-- `Supp 0` is just the finite piece. -/
noncomputable def suppZeroIso : Base N y ≃o Supp N y 0 where
  toFun s := ⟨(⊥, s), fun _ _ => rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv x := by
    refine Subtype.ext (prodEq ?_ rfl)
    refine Subtype.ext ?_
    funext j
    exact (x.2 j (Nat.zero_le j)).symm
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨fun _ => le_rfl, h⟩

/-- The level-wise match. -/
noncomputable def levelIso : ∀ k, DSeed N y k ≃o Supp N y k
  | 0 => suppZeroIso N y
  | k + 1 =>
      (dLevelStep N y hy k).trans
        ((prodCongrIso (OrderIso.refl _) (levelIso k)).trans (peelIso N y k).symm)

theorem levelIso_step (k : ℕ) (u : DSeed N y k) :
    levelIso N y hy (k + 1) (seedStep N y k u) = suppStep N y k (levelIso N y hy k u) := by
  show (peelIso N y k).symm ((prodCongrIso (OrderIso.refl _) (levelIso N y hy k))
      (dLevelStep N y hy k (seedStep N y k u)))
    = suppStep N y k (levelIso N y hy k u)
  rw [dLevelStep_step N y hy k u]
  apply (peelIso N y k).injective
  rw [OrderIso.apply_symm_apply, peelIso_step N y k]
  rfl

/-- **The shape.**  The dual of the seed of a stage-`N` join-irreducible is the
restricted product of the tail, times the finite seed at level `N`. -/
noncomputable def seedShape :
    (JBelow (toD N y))ᵒᵈ ≃o (WeakProd (Fam N) × Base N y) :=
  chainUnionIso (jBelowPres N y).dual (suppPres N y) (levelIso N y hy)
    (levelIso_step N y hy)

end SeedShapeProof
