import Dinfty.FirstSliceCut
import Dinfty.Assembly

open GluingTowerLibrary SierpinskiApplication

/-!
# Copy `C` above the marked point

`FirstSliceCut` closed copy `B` and copy-`C`-low at every level and left
`FirstSliceCHigh` — the case `markedPt n ≤ c` — as pillar B's only open Prop.
This file does two things to it.

## 1. Copy-`C`-high is far smaller than it looks

A join-irreducible of `EndP (D k)` is a step map `stepMap q p`
(`jiOrderIso`).  Asking the marked point to lie below it is a *very* strong
condition:

> **`eq_constHom_of_marked_le`** — if `markedPt k ≤ c` and `c` is
> join-irreducible, then `c = constHom q` for a join-irreducible `q ≥ dMid k`.

Evaluate at `⊥`: `stepMap q p ⊥` is `q` when `p = ⊥` and `⊥` otherwise, and the
marked point's value there is `dMid k ≠ ⊥`.  So the threshold must be `⊥`, and
copy-`C`-high consists of the points `glueC m (constHom q)` for
`q ∈ J (D k)` with `dMid k ≤ q` — one per such `q`, not one per join-irreducible
of `EndP (D k)`.  At `k = 1` that is **11** points out of 431 copy-`C` ones.

## 2. …and then it is a counting question

`firstSliceCHigh_of_card` reduces `FirstSliceCHigh n` to

```
¬ (card (D n) ∣ card (LevelSeed (n+1) (glueC (markedPt n) c)))
```

because an isomorphism with `D n × T` makes `card (D n)` divide the seed.

That divisibility genuinely fails, and the reason is visible once (1) is in hand.
The seed splits by tag as

| part | content | size |
|---|---|---|
| copy `A` | *all* of `J (EndP (D n))` (`leGlue_tagA_tagC`) | `card (D n) · |J (D n)|` |
| copy `B` | *all* copy-`B` join-irreducibles (`m ≤ c`), minus the seam `tag_B ⊤` | `card (D n) · |J (D n)| − 1` |
| copy `C` | `{stepMap q' p ≤ constHom q}` = `D n × (J (D n) ∩ ↓q)`, minus the marked point | `card (D n) · N(q) − 1` |

— the copy-`C` condition is **threshold-free** exactly as in `FirstSliceCut`,
because `c` is constant by (1).  So

```
card S ≡ −2   (mod card (D n))
```

and `card (D n) ≥ 3`, so the divisibility fails.  Measured at `k = 1`: every one
of the 11 copy-`C`-high seeds has `|S| ≡ 25 (mod 27)`
(`_archive/check_copyC_high_invariants.py`).

**What is proved here is (1) and (2); the three tag-counts are not yet formalised,
so `FirstSliceCHigh` is reduced, not closed.**

## A correction to the record

`_archive/check_product_invariants.py` — the source of the "13,616 pairs → 0"
figure quoted since §63 as "`FirstSlice 1` holds" — contains

```python
if tg==C and s.JQ1_le[mi][fidx]: continue
```

which **skips copy-`C`-high**.  Its 851 competitors are copy `B` and
copy-`C`-low only.  So that sweep established exactly what the cut obstruction
proves in general, and **`FirstSlice 1` was never checked for copy-`C`-high**.
Re-running with the class put back (`_archive/check_copyC_high_invariants.py`)
gives 176 further pairs, all killed by cardinality alone — so `FirstSlice 1` does
hold, but on evidence gathered today rather than in §63.
-/

open scoped Classical

namespace CopyCHigh

open FirstSliceCut FinishLine SeedLevelStep JSeedRecursion
open WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open TowerCardGrowth CopyAClassification CopyBCStructure CopyBAtoms CopyBExclusion
open TowerNoAbsorption SeedParametrisation SeedCardBound

variable {k : ℕ}

private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1

/-! ## 1. The characterisation -/

/-- **Copy-`C`-high forces threshold `⊥`.**

A join-irreducible of `EndP (D k)` above the marked point is a *constant* map.
The whole content is the value at `⊥`: a step map with a nonzero threshold sends
`⊥` to `⊥`, and the marked point's value there is `dMid k ≠ ⊥`. -/
theorem eq_constHom_of_marked_le {c : EndP (D k)}
    (hc : JoinIrred (EndP (D k)) c) (hmc : markedPt k ≤ c) :
    ∃ q : D k, JoinIrred (D k) q ∧ dMid k ≤ q ∧ c = constHom q := by
  obtain ⟨pq, hpq⟩ := jiOrderIso.surjective (⟨c, hc⟩ :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f})
  have hcv : c = stepMap pq.2.1 (OrderDual.ofDual pq.1) := (congrArg Subtype.val hpq).symm
  set p : D k := OrderDual.ofDual pq.1 with hp
  set q : D k := pq.2.1 with hq
  have hval : dMid k ≤ (stepMap q p : EndP (D k)) (⊥ : D k) := by
    have := hmc (⊥ : D k)
    rwa [hcv] at this
  have hpb : p = (⊥ : D k) := by
    by_contra hpne
    have hnot : ¬ (p ≤ (⊥ : D k)) := fun h => hpne (le_bot_iff.mp h)
    rw [stepMap_apply_of_not_ge q p hnot] at hval
    exact dMid_ne_bot k (le_bot_iff.mp hval)
  refine ⟨q, pq.2.2, ?_, ?_⟩
  · rw [hpb, stepMap_apply_of_ge q (⊥ : D k) (le_refl _)] at hval
    exact hval
  · rw [hcv, hpb]
    exact stepMap_bot q

/-- The copy-`C`-high points, listed: one for each join-irreducible above the
marked value. -/
theorem copyCHigh_shape {c : EndP (D k)} (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c)
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) c hc hcm)) :
    ∃ q : D k, JoinIrred (D k) q ∧ dMid k ≤ q ∧ q ≠ dMid k ∧ c = constHom q := by
  have hcji : JoinIrred (EndP (D k)) c :=
    (joinIrred_glueC_iff (markedPt k) (hmk' k) (D_marked_point_nondegenerate k).2.1
      (D_marked_point_nondegenerate k).2.2 c hc hcm).mp hy
  obtain ⟨q, hq, hmq, hcq⟩ := eq_constHom_of_marked_le hcji hmc
  refine ⟨q, hq, hmq, ?_, hcq⟩
  intro hqm
  exact hcm (by rw [hcq, hqm]; rfl)

/-! ## 2. The reduction to divisibility -/

/-- **`FirstSliceCHigh` is a counting question.**  An isomorphism with
`D n × T` makes `card (D n)` divide the seed, so it is enough that it does not. -/
theorem firstSliceCHigh_of_card (n : ℕ)
    (hdvd : ∀ (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n),
      markedPt n ≤ c → JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm) →
      ¬ (Fintype.card (D n)
          ∣ Fintype.card (LevelSeed (n + 1) (glueC (markedPt n) c hc hcm)))) :
    FirstSliceCHigh n := by
  intro x hx c hc hcm hmc hy
  refine ⟨fun e => ?_⟩
  refine hdvd c hc hcm hmc hy ?_
  refine ⟨Fintype.card (LevelSeed n x), ?_⟩
  have h := Fintype.card_congr e.toEquiv
  rw [Fintype.card_prod] at h
  exact h

/-! ## 3. The three tag-parts, and their sizes -/

section Counting

private def subInter {α : Type*} (p q : α → Prop) :
    {x : {a : α // p a} // q x.1} ≃ {a : α // p a ∧ q a} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def sndSub {α β : Type*} (p : β → Prop) :
    {s : α × β // p s.2} ≃ α × {b : β // p b} where
  toFun s := (s.1.1, ⟨s.1.2, s.2⟩)
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership below a **constant** map is threshold-free — the same fact that
made the copy-`A` part of a copy-`B` seed a product, now at `constHom z`. -/
theorem jiOrderIso_le_constHom (z : D k)
    (w : (D k)ᵒᵈ × {q : D k // JoinIrred (D k) q}) :
    (jiOrderIso w).1 ≤ (constHom z : EndP (D k)) ↔ w.2.1 ≤ z := by
  have hz : (jiOrderIso w).1 = stepMap w.2.1 (OrderDual.ofDual w.1) := rfl
  rw [hz, stepMap_le_iff_apply w.2.2.1]
  exact Iff.rfl

/-- **So the join-irreducibles below a constant map form a product.** -/
noncomputable def constSeedEquiv (z : D k) :
    {f : EndP (D k) // JoinIrred (EndP (D k)) f ∧ f ≤ (constHom z : EndP (D k))}
      ≃ ((D k)ᵒᵈ × {q : D k // JoinIrred (D k) q ∧ q ≤ z}) :=
  (subInter (fun f : EndP (D k) => JoinIrred (EndP (D k)) f)
      (fun f => f ≤ (constHom z : EndP (D k)))).symm.trans
    (((Equiv.subtypeEquiv (jiOrderIso (P := D k)).toEquiv (fun _ => Iff.rfl)).symm.trans
      ((Equiv.subtypeEquivRight (jiOrderIso_le_constHom z)).trans
        ((sndSub _).trans
          (Equiv.prodCongr (Equiv.refl _)
            (subInter (fun q : D k => JoinIrred (D k) q) (fun q => q ≤ z)))))))

theorem card_constSeed (z : D k) :
    Fintype.card {f : EndP (D k) // JoinIrred (EndP (D k)) f
        ∧ f ≤ (constHom z : EndP (D k))}
      = Fintype.card (D k)
          * Fintype.card {q : D k // JoinIrred (D k) q ∧ q ≤ z} := by
  rw [Fintype.card_congr (constSeedEquiv z), Fintype.card_prod]
  congr 1

end Counting

/-! ## 4. The tag partition of a copy-`C`-high seed -/

section Partition

private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-- Copy `C` is monotone in its argument, ascribed at `D (k+1)`. -/
theorem glueC_le_glueC {x y : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k)
    (hy : y ≠ ⊥) (hym : y ≠ markedPt k) (h : x ≤ y) :
    (glueC (markedPt k) x hx hxm : D (k + 1)) ≤ glueC (markedPt k) y hy hym :=
  (leGlue_tagC_tagC_iff (markedPt k) x y).mpr h

/-- The copy-`A` part: **all** join-irreducibles of `EndP (D k)`. -/
abbrev PartA (k : ℕ) : Type := {v : EndP (D k) // JoinIrred (EndP (D k)) v}

/-- The copy-`B` part: all of them except the seam `⊤`. -/
abbrev PartB (k : ℕ) : Type :=
  {b : EndP (D k) // JoinIrred (EndP (D k)) b ∧ b ≠ ⊤}

/-- The copy-`C` part: those below `c`, except the marked point. -/
abbrev PartC (k : ℕ) (c : EndP (D k)) : Type :=
  {c' : EndP (D k) // JoinIrred (EndP (D k)) c' ∧ c' ≠ markedPt k ∧ c' ≤ c}

variable {c : EndP (D k)}

noncomputable def fromSum (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) :
    PartA k ⊕ PartB k ⊕ PartC k c →
      LevelSeed (k + 1) (glueC (markedPt k) c hc hcm) :=
  Sum.elim
    (fun v => ⟨glueA (markedPt k) v.1,
       (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) v.1).mpr v.2,
       CopyCLow.copyA_le_copyC v.1 hc hcm⟩)
    (Sum.elim
      (fun b => ⟨glueB (markedPt k) b.1 b.2.1.1,
         (joinIrred_glueB_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) b.1
            b.2.1.1 b.2.2).mpr b.2.1,
         glueB_le_glueC_of_marked_le k b.2.1.1 hc hcm hmc⟩)
      (fun c' => ⟨glueC (markedPt k) c'.1 c'.2.1.1 c'.2.2.1,
         (joinIrred_glueC_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) c'.1
            c'.2.1.1 c'.2.2.1).mpr c'.2.1,
         glueC_le_glueC c'.2.1.1 c'.2.2.1 hc hcm c'.2.2.2⟩))

@[simp] theorem fromSum_A (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) (v : PartA k) :
    ((fromSum hc hcm hmc (Sum.inl v)).1 : D (k + 1)).1 = Sum.inl v.1 := rfl

@[simp] theorem fromSum_B (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) (b : PartB k) :
    ((fromSum hc hcm hmc (Sum.inr (Sum.inl b))).1 : D (k + 1)).1
      = Sum.inr (Sum.inl b.1) := rfl

@[simp] theorem fromSum_C (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) (c' : PartC k c) :
    ((fromSum hc hcm hmc (Sum.inr (Sum.inr c'))).1 : D (k + 1)).1
      = Sum.inr (Sum.inr c'.1) := rfl

theorem fromSum_injective (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) : Function.Injective (fromSum hc hcm hmc) := by
  intro x y h
  have hv : ((fromSum hc hcm hmc x).1 : D (k + 1)).1
      = ((fromSum hc hcm hmc y).1 : D (k + 1)).1 :=
    congrArg Subtype.val (congrArg Subtype.val h)
  rcases x with u | u | u <;> rcases y with v | v | v <;>
    simp only [fromSum_A, fromSum_B, fromSum_C] at hv
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hv))
  · simp at hv
  · simp at hv
  · simp at hv
  · exact congrArg (fun w => Sum.inr (Sum.inl w))
      (Subtype.ext (Sum.inl.inj (Sum.inr.inj hv)))
  · exact absurd (Sum.inr.inj hv) (by simp)
  · simp at hv
  · exact absurd (Sum.inr.inj hv) (by simp)
  · exact congrArg (fun w => Sum.inr (Sum.inr w))
      (Subtype.ext (Sum.inr.inj (Sum.inr.inj hv)))

theorem fromSum_surjective (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) : Function.Surjective (fromSum hc hcm hmc) := by
  intro u
  obtain ⟨uv, huj, hule⟩ := u
  rcases dSuccCases k uv with ⟨v, hv⟩ | ⟨b, hb, hv⟩ | ⟨c', hc', hcm', hv⟩
  · subst hv
    refine ⟨Sum.inl ⟨v, ?_⟩, ?_⟩
    · exact (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) v).mp huj
    · exact Subtype.ext rfl
  · subst hv
    have hbt : b ≠ ⊤ := by
      intro hcon
      subst hcon
      exact seam_not_joinIrred k huj
    refine ⟨Sum.inr (Sum.inl ⟨b, ?_, hbt⟩), ?_⟩
    · exact (joinIrred_glueB_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) b hb
        hbt).mp huj
    · exact Subtype.ext rfl
  · subst hv
    refine ⟨Sum.inr (Sum.inr ⟨c', ?_, hcm', ?_⟩), ?_⟩
    · exact (joinIrred_glueC_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) c' hc'
        hcm').mp huj
    · exact (leGlue_tagC_tagC_iff (markedPt k) c' c).mp hule
    · exact Subtype.ext rfl

/-- **The seed of a copy-`C`-high point splits by tag.** -/
noncomputable def seedSplit (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) :
    (PartA k ⊕ PartB k ⊕ PartC k c)
      ≃ LevelSeed (k + 1) (glueC (markedPt k) c hc hcm) :=
  Equiv.ofBijective _ ⟨fromSum_injective hc hcm hmc, fromSum_surjective hc hcm hmc⟩

theorem card_seed_split (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c) :
    Fintype.card (LevelSeed (k + 1) (glueC (markedPt k) c hc hcm))
      = Fintype.card (PartA k) + Fintype.card (PartB k)
        + Fintype.card (PartC k c) := by
  rw [← Fintype.card_congr (seedSplit hc hcm hmc), Fintype.card_sum,
    Fintype.card_sum, Nat.add_assoc]

end Partition

/-! ## 5. The three sizes, and the contradiction -/

section Sizes

/-- Copy `A` is the whole of `J (EndP (D k))`, and that is a product. -/
theorem card_partA (k : ℕ) :
    Fintype.card (PartA k)
      = Fintype.card (D k) * Fintype.card (FirstSliceCut.JAll k) := by
  letI := realUniqueAtomCoatom k
  rw [← FirstSliceCut.card_topSeed k]
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight (fun _ => ⟨fun h => ⟨h, le_top⟩, fun h => h.1⟩))

/-- Copy `B` is copy `A` minus the seam. -/
theorem card_partB (k : ℕ) : Fintype.card (PartB k) + 1 = Fintype.card (PartA k) := by
  classical
  have hsplit : Fintype.card {v : PartA k // v.1 = ⊤}
      + Fintype.card {v : PartA k // ¬ v.1 = ⊤} = Fintype.card (PartA k) := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun v : PartA k => v.1 = ⊤))
  have hone : Fintype.card {v : PartA k // v.1 = ⊤} = 1 := by
    have hne : Nonempty {v : PartA k // v.1 = ⊤} :=
      ⟨⟨⟨(⊤ : EndP (D k)), CopyCLow.joinIrred_endP_top k⟩, rfl⟩⟩
    have hss : Subsingleton {v : PartA k // v.1 = ⊤} :=
      ⟨fun a b => Subtype.ext (Subtype.ext (a.2.trans b.2.symm))⟩
    have h1 := Fintype.card_le_one_iff_subsingleton.mpr hss
    have h2 : 0 < Fintype.card {v : PartA k // v.1 = ⊤} :=
      Fintype.card_pos_iff.mpr hne
    omega
  have hB : Fintype.card {v : PartA k // ¬ v.1 = ⊤} = Fintype.card (PartB k) :=
    Fintype.card_congr (subInter (fun f : EndP (D k) => JoinIrred (EndP (D k)) f)
      (fun f => ¬ f = ⊤))
  omega

/-- Copy `C` is the constant-map product minus the marked point. -/
theorem card_partC (k : ℕ) {q : D k} (hq : JoinIrred (D k) q) (hmq : dMid k ≤ q) :
    Fintype.card (PartC k (constHom q)) + 1
      = Fintype.card (D k)
        * Fintype.card {q' : D k // JoinIrred (D k) q' ∧ q' ≤ q} := by
  classical
  letI := realUniqueAtomCoatom k
  set W : Type := {f : EndP (D k) // JoinIrred (EndP (D k)) f
      ∧ f ≤ (constHom q : EndP (D k))} with hW
  have hmji : JoinIrred (EndP (D k)) (markedPt k) :=
    (joinIrred_constHom_iff (dMid k)).mpr (D_mid_joinIrred k)
  have hmle : (markedPt k : EndP (D k)) ≤ (constHom q : EndP (D k)) := by
    intro y
    exact hmq
  have hsplit : Fintype.card {v : W // v.1 = markedPt k}
      + Fintype.card {v : W // ¬ v.1 = markedPt k} = Fintype.card W := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun v : W => v.1 = markedPt k))
  have hone : Fintype.card {v : W // v.1 = markedPt k} = 1 := by
    have hne : Nonempty {v : W // v.1 = markedPt k} :=
      ⟨⟨⟨markedPt k, hmji, hmle⟩, rfl⟩⟩
    have hss : Subsingleton {v : W // v.1 = markedPt k} :=
      ⟨fun a b => Subtype.ext (Subtype.ext (a.2.trans b.2.symm))⟩
    have h1 := Fintype.card_le_one_iff_subsingleton.mpr hss
    have h2 : 0 < Fintype.card {v : W // v.1 = markedPt k} :=
      Fintype.card_pos_iff.mpr hne
    omega
  have hC : Fintype.card {v : W // ¬ v.1 = markedPt k}
      = Fintype.card (PartC k (constHom q)) := by
    refine Fintype.card_congr
      ((subInter (fun f : EndP (D k) => JoinIrred (EndP (D k)) f
          ∧ f ≤ (constHom q : EndP (D k))) (fun f => ¬ f = markedPt k)).trans
        (Equiv.subtypeEquivRight ?_))
    intro f
    exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  have hWc : Fintype.card W = Fintype.card (D k)
      * Fintype.card {q' : D k // JoinIrred (D k) q' ∧ q' ≤ q} := card_constSeed q
  omega

/-- `D k` has at least three elements: `⊥ < dMid k < ⊤`. -/
theorem three_le_card_D (k : ℕ) : 3 ≤ Fintype.card (D k) := by
  classical
  have h : ({⊥, dMid k, ⊤} : Finset (D k)).card ≤ Fintype.card (D k) :=
    Finset.card_le_univ _
  have hbm : (⊥ : D k) ≠ dMid k := fun h => dMid_ne_bot k h.symm
  have hbt : (⊥ : D k) ≠ ⊤ := fun h => top_ne_bot_D k h.symm
  have hmt : dMid k ≠ (⊤ : D k) := dMid_ne_top k
  have hcard : ({⊥, dMid k, ⊤} : Finset (D k)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hbm, hbt]),
      Finset.card_insert_of_notMem (by simp [hmt]), Finset.card_singleton]
  omega

/-- **The divisibility fails.**  `card S ≡ -2 (mod card (D k))`. -/
theorem not_card_dvd (k : ℕ) {c : EndP (D k)} (hc : c ≠ ⊥) (hcm : c ≠ markedPt k)
    (hmc : markedPt k ≤ c)
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) c hc hcm)) :
    ¬ (Fintype.card (D k)
        ∣ Fintype.card (LevelSeed (k + 1) (glueC (markedPt k) c hc hcm))) := by
  obtain ⟨q, hq, hmq, -, hcq⟩ := copyCHigh_shape hc hcm hmc hy
  subst hcq
  intro hdvd
  have hsum := card_seed_split hc hcm hmc
  have hA := card_partA k
  have hB := card_partB k
  have hC := card_partC k hq hmq
  have h3 : 3 ≤ Fintype.card (D k) := three_le_card_D k
  -- `N` divides the copy-`A` count and the constant-map product
  have hdA : Fintype.card (D k) ∣ Fintype.card (PartA k) := ⟨_, hA⟩
  have hdC : Fintype.card (D k) ∣ Fintype.card (D k)
      * Fintype.card {q' : D k // JoinIrred (D k) q' ∧ q' ≤ q} := ⟨_, rfl⟩
  -- so `N` divides `card S + 2`
  have hkey : Fintype.card (D k) ∣ Fintype.card (LevelSeed (k + 1)
      (glueC (markedPt k) (constHom q) hc hcm)) + 2 := by
    have : Fintype.card (LevelSeed (k + 1)
        (glueC (markedPt k) (constHom q) hc hcm)) + 2
        = Fintype.card (PartA k) + Fintype.card (PartA k)
          + (Fintype.card (D k)
            * Fintype.card {q' : D k // JoinIrred (D k) q' ∧ q' ≤ q}) := by
      omega
    rw [this]
    exact Dvd.dvd.add (Dvd.dvd.add hdA hdA) hdC
  have h2 : Fintype.card (D k) ∣ 2 := by
    have hsub := Nat.dvd_sub hkey hdvd
    rwa [Nat.add_sub_cancel_left] at hsub
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- **`FirstSliceCHigh` holds at every level.** -/
theorem firstSliceCHigh (n : ℕ) : FirstSliceCHigh n :=
  firstSliceCHigh_of_card n (fun c hc hcm hmc hy => not_card_dvd n hc hcm hmc hy)

/-- **The first slice, at every level, with no hypothesis left.** -/
theorem firstSlice (n : ℕ) : FirstSlice n :=
  FirstSliceCut.firstSlice n (firstSliceCHigh n)

/-- **PILLAR B.**  `colimit_compat`, with no hypothesis. -/
theorem colimit_compat : Subsingleton (DInfty ≃o DInfty) :=
  FirstSliceCut.colimit_compat_of_firstSliceCHigh firstSliceCHigh

/-- **Theorem B's conclusion at the bilimit**, via the already-proven bridge. -/
theorem DBilimit_rigid : Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_DInfty_rigid colimit_compat

end Sizes

end CopyCHigh
