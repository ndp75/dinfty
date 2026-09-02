import Mathlib.Tactic.IntervalCases
import Dinfty.GenContinuityTransport
import Dinfty.CanonFixed

open GluingTowerLibrary SierpinskiApplication

/-!
# Tags of a glued point, uniformly

`GlueCarGen m` is cut out of `P ⊕ P ⊕ P`, so every point carries a tag.  The
surjectivity argument needs to say "the tag of `d.1 k` is eventually constant,
and on that tail the payload is a chain" — once, not three times.  This module
makes the tag a number and the three copy-inclusions one family.

* `tagIdx` — `0`/`1`/`2`.  It **drops** under `canonGen` (`tagIdx_canonGen_le`)
  and is **preserved** by `baseMapGen` (`tagIdx_baseMapGen`).  That is all the
  monotonicity the tower argument needs, and it is about the normalisation map,
  not about the glue order — where the tag is *not* monotone (`tagCGen c ≤
  skelG3Gen` whenever `c ≤ m`).
* `tagInj t` / `tagPt t` — the raw and bundled tag-`t` inclusions.
* `unTag` — a left inverse of `canonGen ∘ tagInj t`, which makes each
  copy-inclusion injective in one line instead of nine cases.
* `tagPt_isLUB` — one statement dispatching to `tagAGen_isLUB`,
  `tagBGen_isLUB`, `tagCGen_isLUB`, with the side conditions supplied by
  `CanonFixed.Fixed` rather than assumed.
-/

universe u

namespace GlueTag

open GenContinuity

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

/-! ## The tag as a number -/

def tagIdx : GlueBaseGen P → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

theorem tagIdx_le_two (v : GlueBaseGen P) : tagIdx v ≤ 2 := by
  cases v with
  | inl _ => exact Nat.zero_le _
  | inr w => cases w with
    | inl _ => exact Nat.le_of_sub_eq_zero rfl
    | inr _ => exact le_refl _

theorem tagIdx_baseMapGen (g : P →o P') (v : GlueBaseGen P) :
    tagIdx (baseMapGen g v) = tagIdx v := by
  cases v with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

/-- **Normalisation can only lower the tag.**  This is the monotonicity the
tower argument uses; it is a fact about `canonGen`, not about the glue order. -/
theorem tagIdx_canonGen_le (m : P) (v : GlueBaseGen P) :
    tagIdx (canonGen m v) ≤ tagIdx v := by
  cases v with
  | inl _ => exact le_refl _
  | inr w => cases w with
    | inl b =>
        show tagIdx (if b = ⊥ then (Sum.inl m : GlueBaseGen P) else Sum.inr (Sum.inl b)) ≤ 1
        by_cases hb : b = ⊥
        · rw [if_pos hb]; exact Nat.zero_le _
        · rw [if_neg hb]; exact le_refl _
    | inr c =>
        show tagIdx (if c = ⊥ then (Sum.inl ⊤ : GlueBaseGen P)
            else if c = m then Sum.inr (Sum.inl ⊤) else Sum.inr (Sum.inr c)) ≤ 2
        by_cases hc : c = ⊥
        · rw [if_pos hc]; exact Nat.zero_le _
        · rw [if_neg hc]
          by_cases hcm : c = m
          · rw [if_pos hcm]; exact Nat.le_of_sub_eq_zero rfl
          · rw [if_neg hcm]; exact le_refl _

/-! ## The tag-`t` inclusion -/

def tagInj (t : ℕ) (p : P) : GlueBaseGen P :=
  if t = 0 then Sum.inl p else if t = 1 then Sum.inr (Sum.inl p) else Sum.inr (Sum.inr p)

@[simp] theorem tagInj_zero (p : P) : tagInj 0 p = Sum.inl p := rfl
@[simp] theorem tagInj_one (p : P) : tagInj 1 p = Sum.inr (Sum.inl p) := rfl
@[simp] theorem tagInj_two (p : P) : tagInj 2 p = Sum.inr (Sum.inr p) := rfl

theorem tagIdx_tagInj {t : ℕ} (ht : t ≤ 2) (p : P) : tagIdx (tagInj t p) = t := by
  interval_cases t <;> rfl

/-- Every point is a tag-`t` point for its own `t`. -/
theorem exists_payload (v : GlueBaseGen P) : ∃ p, v = tagInj (tagIdx v) p := by
  cases v with
  | inl a => exact ⟨a, rfl⟩
  | inr w => cases w with
    | inl b => exact ⟨b, rfl⟩
    | inr c => exact ⟨c, rfl⟩

theorem baseMapGen_tagInj (g : P →o P') (t : ℕ) (p : P) :
    baseMapGen g (tagInj t p) = tagInj t (g p) := by
  unfold tagInj
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

/-! ## A left inverse, so each copy-inclusion is injective in one line -/

/-- Undoes `canonGen ∘ tagInj t`.  The three redirected values (`Sum.inl m`,
`Sum.inl ⊤`, `Sum.inr (Sum.inl ⊤)`) are sent back to the payload they came
from, which is possible precisely because `t` is fixed. -/
def unTag (t : ℕ) (m : P) : GlueBaseGen P → P
  | Sum.inl a => if t = 0 then a else ⊥
  | Sum.inr (Sum.inl b) => if t = 1 then b else m
  | Sum.inr (Sum.inr c) => c

theorem unTag_canonGen (t : ℕ) (m p : P) : unTag t m (canonGen m (tagInj t p)) = p := by
  by_cases h0 : t = 0
  · subst h0
    show unTag 0 m (canonGen m (Sum.inl p)) = p
    rfl
  · by_cases h1 : t = 1
    · subst h1
      show unTag 1 m (canonGen m (Sum.inr (Sum.inl p))) = p
      simp only [canonGen]
      by_cases hp : p = ⊥
      · rw [if_pos hp]
        show (if (1 : ℕ) = 0 then m else ⊥) = p
        rw [if_neg (by norm_num), hp]
      · rw [if_neg hp]
        show (if (1 : ℕ) = 1 then p else m) = p
        rw [if_pos rfl]
    · have ht : tagInj t p = (Sum.inr (Sum.inr p) : GlueBaseGen P) := by
        unfold tagInj; rw [if_neg h0, if_neg h1]
      rw [ht]
      simp only [canonGen]
      by_cases hp : p = ⊥
      · rw [if_pos hp]
        show (if t = 0 then (⊤ : P) else ⊥) = p
        rw [if_neg h0, hp]
      · rw [if_neg hp]
        by_cases hpm : p = m
        · rw [if_pos hpm]
          show (if t = 1 then (⊤ : P) else m) = p
          rw [if_neg h1, hpm]
        · rw [if_neg hpm]
          rfl

theorem canonGen_tagInj_inj (m : P) (t : ℕ) {u v : P}
    (h : canonGen m (tagInj t u) = canonGen m (tagInj t v)) : u = v := by
  rw [← unTag_canonGen t m u, ← unTag_canonGen t m v, h]

/-! ## The bundled tag-`t` point, and its supremum law -/

noncomputable def tagPt (t : ℕ) (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (p : P) :
    GlueCarGen (P := P) m :=
  ⟨canonGen m (tagInj t p), canonGen_idem m hm hbt _⟩

@[simp] theorem tagPt_val (t : ℕ) (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (p : P) :
    (tagPt t m hm hbt p).1 = canonGen m (tagInj t p) := rfl

theorem tagPt_injective (t : ℕ) (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    Function.Injective (tagPt t m hm hbt) :=
  fun _ _ h => canonGen_tagInj_inj m t (congrArg Subtype.val h)

/-- **One supremum law for all three copies.**  The side conditions are not
assumed: they are read off `CanonFixed.Fixed`, i.e. off the fact that the
family already sits in the canon-fixed region. -/
theorem tagPt_isLUB {t : ℕ} (ht : t ≤ 2) (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (hbt : (⊥ : P) ≠ ⊤) {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty)
    (hfix : ∀ s ∈ S, canonGen m (tagInj t s) = tagInj t s) :
    letI := glueCarPartialOrderGen m hm hmt hbt
    IsLUB (tagPt t m hm hbt '' S) (tagPt t m hm hbt c) := by
  letI := glueCarPartialOrderGen m hm hmt hbt
  interval_cases t
  · have hfun : tagPt 0 m hm hbt = tagAGen m := by
      funext p; exact Subtype.ext rfl
    rw [hfun]
    exact tagAGen_isLUB m hm hmt hbt hS
  · have hSb : ∀ s ∈ S, s ≠ ⊥ := fun s hs => (CanonFixed.fixed_iff m _).mp (hfix s hs)
    have hfun : tagPt 1 m hm hbt = tagBGen m hm hbt := by
      funext p; exact Subtype.ext rfl
    rw [hfun]
    exact tagBGen_isLUB m hm hmt hbt hS hne hSb
  · have hfx : ∀ s ∈ S, s ≠ ⊥ ∧ s ≠ m := fun s hs => (CanonFixed.fixed_iff m _).mp (hfix s hs)
    have hfun : tagPt 2 m hm hbt = tagCGen m hm hbt := by
      funext p; exact Subtype.ext rfl
    rw [hfun]
    exact tagCGen_isLUB m hm hmt hbt hS hne (fun s hs => (hfx s hs).1) (fun s hs => (hfx s hs).2)

end GlueTag
