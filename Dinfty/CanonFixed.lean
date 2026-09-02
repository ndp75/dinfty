import Dinfty.GluingTowerLibrary

open GluingTowerLibrary

/-!
# The canon-fixed condition as a property, not a decidable equation

`GlueCarGen m` is cut out of `GlueBaseGen P` by `canonGen m v = v`, and
`canonGen` branches on `DecidableEq P`.  So the *carrier type* mentions a
`DecidableEq` instance, and two instances — the tower's `endPDecidableEq`,
Mathlib's `OrderHom.instDecidableEqOfForall`, `Classical.propDecidable` — give
syntactically different types that the elaborator's `synthesized = inferred`
check refuses to reconcile, even though they are definitionally equal.  §85
recorded that fight and lost it.

**The condition itself has no decidability in it.**  Unfolding the three
branches of `canonGen`:

| tag | `canonGen m v = v` holds iff |
|---|---|
| `A` | always |
| `B` | `b ≠ ⊥` |
| `C` | `c ≠ ⊥ ∧ c ≠ m` |

`Fixed` below says exactly that, in `Prop`, with no instance argument — and
`fixed_iff` needs no hypotheses at all, not even `m ≠ ⊥`.  The two redirects are
*constructor* clashes (`Sum.inl m` against `Sum.inr _`), so they are refuted
without knowing anything about `P`.

`GlueCarFix m` is therefore the same carrier with the instance removed from the
type, and `equivGlueCarGen` connects it to `GlueCarGen` for **any** choice of
instance.  Composing two of those, at two different instances, is the bridge
§85 could not write.
-/

universe u

namespace CanonFixed

variable {P : Type u} [PartialOrder P] [BoundedOrder P]

/-- **The canon-fixed condition, as a property.**  No `DecidableEq`. -/
def Fixed (m : P) : GlueBaseGen P → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl b) => b ≠ ⊥
  | Sum.inr (Sum.inr c) => c ≠ ⊥ ∧ c ≠ m

@[simp] theorem fixed_inl (m a : P) : Fixed m (Sum.inl a) := trivial

@[simp] theorem fixed_inrl (m b : P) : Fixed m (Sum.inr (Sum.inl b)) ↔ b ≠ ⊥ := Iff.rfl

@[simp] theorem fixed_inrr (m c : P) :
    Fixed m (Sum.inr (Sum.inr c)) ↔ c ≠ ⊥ ∧ c ≠ m := Iff.rfl

/-- **The equation and the property agree**, with no hypotheses on `m` — the two
redirects are refuted by constructor clashes alone. -/
theorem fixed_iff [DecidableEq P] (m : P) (v : GlueBaseGen P) :
    canonGen m v = v ↔ Fixed m v := by
  cases v with
  | inl a => simp [canonGen, Fixed]
  | inr w =>
    cases w with
    | inl b =>
        by_cases hb : b = (⊥ : P)
        · subst hb; simp [canonGen, Fixed]
        · simp [canonGen, Fixed, hb]
    | inr c =>
        by_cases hc : c = (⊥ : P)
        · subst hc; simp [canonGen, Fixed]
        · by_cases hcm : c = m
          · subst hcm; simp [canonGen, Fixed, hc]
          · simp [canonGen, Fixed, hc, hcm]

/-- The glued carrier with the instance removed from its *type*. -/
def GlueCarFix (m : P) := {v : GlueBaseGen P // Fixed m v}

/-- **…and it is the glued carrier, for any `DecidableEq` whatsoever.** -/
def equivGlueCarGen [DecidableEq P] (m : P) : GlueCarFix m ≃ GlueCarGen (P := P) m where
  toFun v := ⟨v.1, (fixed_iff m v.1).mpr v.2⟩
  invFun v := ⟨v.1, (fixed_iff m v.1).mp v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivGlueCarGen_val [DecidableEq P] (m : P) (v : GlueCarFix m) :
    (equivGlueCarGen m v).1 = v.1 := rfl

@[simp] theorem equivGlueCarGen_symm_val [DecidableEq P] (m : P)
    (v : GlueCarGen (P := P) m) : ((equivGlueCarGen m).symm v).1 = v.1 := rfl

/-- **The bridge §85 needed.**  Given two `DecidableEq` instances in scope under
any names, the two glued carriers are equivalent — and the equivalence is the
identity on underlying values, so it transports the order too. -/
def instBridge [DecidableEq P] (m : P) (Q : Type u) (e : Q ≃ GlueCarFix m) :
    Q ≃ GlueCarGen (P := P) m := e.trans (equivGlueCarGen m)

/-- The order does not move either: both carriers order by `leGlueGen` on the
underlying `GlueBaseGen P` values, and the equivalence fixes those. -/
theorem equivGlueCarGen_leGlueGen [DecidableEq P] (m : P) (u v : GlueCarFix m) :
    leGlueGen m (equivGlueCarGen m u).1 (equivGlueCarGen m v).1 ↔ leGlueGen m u.1 v.1 :=
  Iff.rfl

end CanonFixed
