import Dinfty.SeedsDiffer
import Dinfty.TowerCardGrowth

open GluingTowerLibrary SierpinskiApplication

/-!
# The copy-`A` classification: only the marked point survives

`SeedShapeProof.seedShape` turned seed separation into a **finite** question
about the level-`N` seed.  This module answers it for copy `A`.

A join-irreducible of `D (k+1)` in copy `A` is `glueA (markedPt k) F` with `F`
join-irreducible in `EndP (D k)`, i.e. `F = jiOrderIso (toDual p, q)` for a
threshold `p : D k` and a join-irreducible value `q`.  Its seed is a **product**:

```lean
copyASeedIso : (LevelSeed (k+1) (glueA (markedPt k) F))ᵒᵈ
                 ≃o (UpSet k p × (LevelSeed k q)ᵒᵈ)
```

— `UpSet k p = {a : D k // p ≤ a}`, and the tower's own embedding is the case
`p = ⊥`, where `UpSet k ⊥` is all of `D k`.

Then `WeakProdFactorization.no_iso_of_small_pieces` closes it:

> **`copyA_forces_bot`** — if `p ≠ ⊥`, the seed cannot be `midInf`'s.

because a **proper** up-set of `D k` is strictly smaller than `D k`
(`TowerCardGrowth.card_upSet_lt`), the seed `(LevelSeed k q)ᵒᵈ` sits inside
`J(D k)` and so is also strictly smaller (`card_joinIrred_lt`), and `D k` is
smaller than every tail factor (`card_D_strictMono`) — so `D k` would have to
reappear as an atom-factor of a product both of whose sides are too small.

## Scope

Copy `A` only.  Copies `B` and `C` — whose seeds are ordinal sums rather than
products — are not treated here.
-/

open scoped Classical

namespace CopyAClassification

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth TowerNoAbsorption SeedShapeProof ChainUnion
open SeedSeparation MidAnchor SeedChain

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## The copy-`A` seed, for an arbitrary join-irreducible -/

section CopyAGen

variable (k : ℕ) (F : EndP (D k))

/-- `copyAFun` for an arbitrary `F`, not just a `constHom`. -/
noncomputable def copyAFunGen
    (f : {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ F}) :
    LevelSeed (k + 1) (glueA (markedPt k) F) :=
  ⟨glueA (markedPt k) f.1,
   (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) f.1).mpr f.2.1,
   (glueA_le_iff (markedPt k) (hmk k) f.1 F).mpr f.2.2⟩

theorem copyAFunGen_injective : Function.Injective (copyAFunGen k F) := by
  intro a b h
  exact Subtype.ext (glueA_injective (markedPt k) (congrArg Subtype.val h))

theorem copyAFunGen_surjective : Function.Surjective (copyAFunGen k F) := by
  intro w
  obtain ⟨f, hf⟩ := le_glueA_imp_glueA_shaped (markedPt k) (hmk k) (hbtk k) w.1 F w.2.2
  have hw : w.1 = glueA (markedPt k) f := Subtype.ext hf
  refine ⟨⟨f, ?_, ?_⟩, Subtype.ext hw.symm⟩
  · exact (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) f).mp (hw ▸ w.2.1)
  · exact (glueA_le_iff (markedPt k) (hmk k) f F).mp (hw ▸ w.2.2)

/-- **Copy `A` is downward closed, for any `F`.** -/
noncomputable def copyAIsoGen :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ F}
      ≃o LevelSeed (k + 1) (glueA (markedPt k) F) where
  toEquiv := Equiv.ofBijective (copyAFunGen k F)
    ⟨copyAFunGen_injective k F, copyAFunGen_surjective k F⟩
  map_rel_iff' := by
    intro a b
    show (copyAFunGen k F a) ≤ (copyAFunGen k F b) ↔ a ≤ b
    exact glueA_le_iff (markedPt k) (hmk k) a.1 b.1

end CopyAGen

/-! ## …and it is a product -/

section Product

variable (k : ℕ)

/-- The up-set of `p` in `D k`. -/
abbrev UpSet (p : D k) : Type := {a : D k // p ≤ a}

/-- `{a' : (D k)ᵒᵈ // a' ≤ toDual p}` **is** the up-set of `p`, dualised twice. -/
def upSetDualIso (p : D k) :
    ({a' : (D k)ᵒᵈ // a' ≤ OrderDual.toDual p})ᵒᵈ ≃o UpSet k p where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **The copy-`A` seed of a join-irreducible is a product**: an up-set of the
level below, times the seed of the value. -/
noncomputable def copyASeedIso (a : (D k)ᵒᵈ) (q : {x : D k // JoinIrred (D k) x}) :
    LevelSeed (k + 1) (glueA (markedPt k) (jiOrderIso (a, q)).1)
      ≃o (({a' : (D k)ᵒᵈ // a' ≤ a}) × LevelSeed k q.1) := by
  letI := realUniqueAtomCoatom k
  exact (copyAIsoGen k (jiOrderIso (a, q)).1).symm.trans
    ((subtypeShuffle (fun f : EndP (D k) => JoinIrred (EndP (D k)) f)
        (jiOrderIso (a, q))).trans
      ((jSeedIso (P := D k) a q).trans
        (prodCongrIso (OrderIso.refl _)
          (subtypeShuffle (fun x : D k => JoinIrred (D k) x) q).symm)))

/-- The dualised form: `S_y ≅ UpSet k p × S_q`. -/
noncomputable def copyASeedDualIso (p : D k) (q : {x : D k // JoinIrred (D k) x}) :
    (LevelSeed (k + 1) (glueA (markedPt k)
        (jiOrderIso (OrderDual.toDual p, q)).1))ᵒᵈ
      ≃o (UpSet k p × (LevelSeed k q.1)ᵒᵈ) :=
  ((copyASeedIso k (OrderDual.toDual p) q).dual).trans
    ((prodDualIso ({a' : (D k)ᵒᵈ // a' ≤ OrderDual.toDual p}) (LevelSeed k q.1)).trans
      (prodCongrIso (upSetDualIso k p) (OrderIso.refl _)))

end Product

/-! ## The two cardinality bounds -/

theorem card_upSet_lt_D (k : ℕ) {p : D k} (hp : p ≠ ⊥) :
    Fintype.card (UpSet k p) < Fintype.card (D k) := card_upSet_lt hp

theorem card_levelSeed_lt (k : ℕ) (v : D k) :
    Fintype.card ((LevelSeed k v)ᵒᵈ) < Fintype.card (D k) := by
  have h1 : Fintype.card ((LevelSeed k v)ᵒᵈ)
      ≤ Fintype.card {x : D k // JoinIrred (D k) x} :=
    Fintype.card_le_of_injective
      (fun u => (⟨u.1, u.2.1⟩ : {x : D k // JoinIrred (D k) x}))
      (by
        intro a b h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h)
  letI := (towerLevel k).nontriv
  exact lt_of_le_of_lt h1 (TowerCardGrowth.card_joinIrred_lt (P := D k))

/-! ## The exclusion -/

/-- **Only the marked point's threshold survives.**  A copy-`A` competitor with
threshold `p ≠ ⊥` cannot have `midInf`'s seed. -/
theorem copyA_forces_bot (k : ℕ) {p : D k} (hp : p ≠ ⊥)
    (q : {x : D k // JoinIrred (D k) x})
    (e : WeakProd (Fam 0) ≃o (WeakProd (Fam (k + 1)) ×
      ((LevelSeed (k + 1) (glueA (markedPt k)
        (jiOrderIso (OrderDual.toDual p, q)).1))ᵒᵈ))) : False := by
  haveI hob : OrderBot (UpSet k p) :=
    { bot := ⟨p, le_refl p⟩
      bot_le := fun a => a.2 }
  haveI : IsAtomic (UpSet k p) := GluingTowerLibrary.isAtomic_of_finite
  haveI hob2 : OrderBot ((LevelSeed k q.1)ᵒᵈ) :=
    { bot := (⟨q.1, q.2, le_refl _⟩ : LevelSeed k q.1)
      bot_le := fun a => a.2.2 }
  haveI : IsAtomic ((LevelSeed k q.1)ᵒᵈ) := GluingTowerLibrary.isAtomic_of_finite
  have e' : WeakProd (Fam 0)
      ≃o (WeakProd (Fam (k + 1)) × (UpSet k p × (LevelSeed k q.1)ᵒᵈ)) :=
    e.trans (prodCongrIso (OrderIso.refl _) (copyASeedDualIso k p q))
  have hsmall : ∀ i, Fintype.card (Fam 0 k) < Fintype.card (Fam (k + 1) i) := by
    intro i
    show Fintype.card (D (0 + k)) < Fintype.card (D (k + 1 + i))
    exact card_D_strictMono (by omega)
  have hA : Fintype.card (UpSet k p) < Fintype.card (Fam 0 k) := by
    show Fintype.card (UpSet k p) < Fintype.card (D (0 + k))
    simpa using card_upSet_lt_D k hp
  have hB : Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (Fam 0 k) := by
    show Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (D (0 + k))
    simpa using card_levelSeed_lt k q.1
  have hempty := no_iso_of_small_pieces (D := Fam 0) (E := Fam (k + 1))
    (A := UpSet k p) (B := (LevelSeed k q.1)ᵒᵈ)
    (fun j => lamD (0 + j)) (fun j => lamD (k + 1 + j))
    (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j))
    (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
    k hsmall hA hB
  exact hempty.elim e'

/-! ## The induction step for copy `A` -/

/-- `midInf`'s seed, with its one-point finite piece dropped. -/
noncomputable def midInfShape : (JBelow midInf)ᵒᵈ ≃o WeakProd (Fam 0) :=
  (seedShape 0 (dMid 0) SeedsDiffer.joinIrred_D0_mid).trans
    (SeedsDiffer.prodUniqueIso (A := WeakProd (Fam 0)) (B := Base 0 (dMid 0)))

/-- From a seed isomorphism with `midInf`, the shape comparison
`copyA_forces_bot` consumes. -/
noncomputable def shapeComparison (N : ℕ) (y : D N) (hy : JoinIrred (D N) y)
    (e : JBelow (toD N y) ≃o JBelow midInf) :
    WeakProd (Fam 0) ≃o (WeakProd (Fam N) × (LevelSeed N y)ᵒᵈ) :=
  (midInfShape.symm.trans (e.dual.symm.trans (seedShape N y hy)))

/-- **The copy-`A` induction step.**  A copy-`A` join-irreducible whose seed is
`midInf`'s must be the tower's own embedding of a level-`k` join-irreducible,
and that one again has `midInf`'s seed. -/
theorem copyA_step (k : ℕ) (F : EndP (D k)) (hF : JoinIrred (EndP (D k)) F)
    (e : JBelow (toD (k + 1) (glueA (markedPt k) F)) ≃o JBelow midInf) :
    ∃ q : D k, JoinIrred (D k) q ∧ glueA (markedPt k) F = iotaD k q
      ∧ Nonempty (JBelow (toD k q) ≃o JBelow midInf) := by
  letI := realUniqueAtomCoatom k
  set aq := jiOrderIso.symm (⟨F, hF⟩ : {f : EndP (D k) // JoinIrred (EndP (D k)) f}) with haq
  have hFval : F = (jiOrderIso aq).1 := by
    rw [haq, OrderIso.apply_symm_apply]
  have hyji : JoinIrred (D (k + 1)) (glueA (markedPt k) F) :=
    (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mpr hF
  have ecmp := shapeComparison (k + 1) (glueA (markedPt k) F) hyji e
  rw [hFval] at ecmp
  have hp : OrderDual.ofDual aq.1 = (⊥ : D k) := by
    by_contra hne
    exact copyA_forces_bot k hne aq.2 ecmp
  have haq1 : aq.1 = OrderDual.toDual (⊥ : D k) := hp
  have hFc : F = constHom aq.2.1 := by
    rw [hFval]
    have hswap : (jiOrderIso aq).1
        = (jiOrderIso (OrderDual.toDual (⊥ : D k), aq.2)).1 := by
      rw [← haq1]
    rw [hswap, jiOrderIso_bot_val (P := D k) aq.2]
  have hiota : glueA (markedPt k) F = iotaD k aq.2.1 := by
    rw [hFc]
    rfl
  have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k aq.2.1 := by
    rw [hiota]
    have h := toD_iotaLe (Nat.le_succ k) aq.2.1
    rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) aq.2.1,
         iotaLe_self (le_refl k) aq.2.1] at h
  exact ⟨aq.2.1, aq.2.2, hiota, ⟨hstep ▸ e⟩⟩

/-! ## The induction, with the copy-`B`/`C` case named

Copy `A` is settled above.  What is left is a single `Prop`. -/

/-- **The remaining input.**  A join-irreducible of `D (k+1)` that is *not* in
copy `A` never has `midInf`'s seed.

Copies `B` and `C` differ from copy `A` in exactly the way
`AtomFactorGeneration` was built for: their seeds are **ordinal sums** — all of
`J(↓ marked point)` sits above the part that carries the atom-factors — rather
than products, so `not_genByFactors_of_strict_upper` is the tool, not
`no_iso_of_small_pieces`.  It is stated and not proved. -/
def CopyBCExcluded : Prop :=
  ∀ (k : ℕ) (y : D (k + 1)), (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow midInf)

theorem D0_joinIrred_cases {y : D 0} (hy : JoinIrred (D 0) y) :
    y = dMid 0 ∨ y = (⊤ : D 0) := by
  have h1 : (y : Fin 3).val ≠ 0 := SeedsDiffer.ne_bot_val hy.1
  have h2 : (y : Fin 3).val < 3 := (y : Fin 3).isLt
  rcases (by omega : (y : Fin 3).val = 1 ∨ (y : Fin 3).val = 2) with h | h
  · refine Or.inl (Fin.ext ?_)
    rw [SeedsDiffer.val_mid]
    exact h
  · refine Or.inr (Fin.ext ?_)
    rw [SeedsDiffer.val_top]
    exact h

/-- **Seed separation for `midInf`, at join-irreducibles, given the copy-`B`/`C`
exclusion.** -/
theorem seedSeparates_midInf_ji (h : CopyBCExcluded) :
    ∀ (N : ℕ) (y : D N), JoinIrred (D N) y →
      Nonempty (JBelow (toD N y) ≃o JBelow midInf) → toD N y = midInf := by
  intro N
  induction N with
  | zero =>
      intro y hy he
      rcases D0_joinIrred_cases hy with rfl | rfl
      · rfl
      · exact SeedsDiffer.jBelow_midInf_not_iso_topJ.elim he.some.symm
  | succ k ih =>
      intro y hy he
      by_cases hA : ∃ F : EndP (D k), y = glueA (markedPt k) F
      · obtain ⟨F, rfl⟩ := hA
        have hF : JoinIrred (EndP (D k)) F :=
          (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mp hy
        obtain ⟨q, hq, hiota, hqe⟩ := copyA_step k F hF he.some
        have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k q := by
          rw [hiota]
          have h2 := toD_iotaLe (Nat.le_succ k) q
          rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) q, iotaLe_self (le_refl k) q] at h2
        rw [hstep]
        exact ih q hq hqe
      · exact absurd he (h k y hA)

/-! ## …and the consequence for `TwoPointFixed`'s `midInf` half -/

/-- The join-irreducible-restricted form of `fixed_of_seedSeparates`: enough,
because an automorphism carries a join-irreducible to a join-irreducible. -/
theorem fixed_of_seedSeparates_ji {z : DInfty} (hz : JoinIrred DInfty z)
    (hsep : ∀ (N : ℕ) (y : D N), JoinIrred (D N) y →
      Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z)
    (θ : DInfty ≃o DInfty) : θ z = z := by
  obtain ⟨N, y, hy⟩ := exists_stage (θ z)
  have hji : JoinIrred DInfty (θ z) := GluingTowerLibrary.joinIrred_orderIso θ hz
  have hjiy : JoinIrred (D N) y := (JoinIrredDInfty.joinIrred_toD_iff N y).mp (hy ▸ hji)
  have hiso : Nonempty (JBelow (toD N y) ≃o JBelow z) := by
    refine ⟨?_⟩
    rw [← hy]
    exact (JBelow.map θ z).symm
  rw [hy]
  exact hsep N y hjiy hiso

/-- **Every automorphism fixes `midInf`, given the copy-`B`/`C` exclusion.** -/
theorem midInf_fixed (h : CopyBCExcluded) (θ : DInfty ≃o DInfty) : θ midInf = midInf :=
  fixed_of_seedSeparates_ji TwoPointHypothesis.joinIrred_midInf
    (seedSeparates_midInf_ji h) θ

end CopyAClassification
