import Dinfty.GluingTowerLibrary

open GluingTowerLibrary

-- [D-0681] §The-canon-fixed-condition-as-a-property-not
universe u

namespace CanonFixed

variable {P : Type u} [PartialOrder P] [BoundedOrder P]

-- [D-0682] Fixed
def Fixed (m : P) : GlueBaseGen P → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl b) => b ≠ ⊥
  | Sum.inr (Sum.inr c) => c ≠ ⊥ ∧ c ≠ m

-- [D-0683] fixed_inl
@[simp] theorem fixed_inl (m a : P) : Fixed m (Sum.inl a) := trivial

-- [D-0684] fixed_inrl
@[simp] theorem fixed_inrl (m b : P) : Fixed m (Sum.inr (Sum.inl b)) ↔ b ≠ ⊥ := Iff.rfl

-- [D-0685] fixed_inrr
@[simp] theorem fixed_inrr (m c : P) :
    Fixed m (Sum.inr (Sum.inr c)) ↔ c ≠ ⊥ ∧ c ≠ m := Iff.rfl

-- [D-0686] fixed_iff
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

-- [D-0687] GlueCarFix
def GlueCarFix (m : P) := {v : GlueBaseGen P // Fixed m v}

-- [D-0688] equivGlueCarGen
def equivGlueCarGen [DecidableEq P] (m : P) : GlueCarFix m ≃ GlueCarGen (P := P) m where
  toFun v := ⟨v.1, (fixed_iff m v.1).mpr v.2⟩
  invFun v := ⟨v.1, (fixed_iff m v.1).mp v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [D-0689] equivGlueCarGen_val
@[simp] theorem equivGlueCarGen_val [DecidableEq P] (m : P) (v : GlueCarFix m) :
    (equivGlueCarGen m v).1 = v.1 := rfl

-- [D-0690] equivGlueCarGen_symm_val
@[simp] theorem equivGlueCarGen_symm_val [DecidableEq P] (m : P)
    (v : GlueCarGen (P := P) m) : ((equivGlueCarGen m).symm v).1 = v.1 := rfl

-- [D-0691] instBridge
def instBridge [DecidableEq P] (m : P) (Q : Type u) (e : Q ≃ GlueCarFix m) :
    Q ≃ GlueCarGen (P := P) m := e.trans (equivGlueCarGen m)

-- [D-0692] equivGlueCarGen_leGlueGen
theorem equivGlueCarGen_leGlueGen [DecidableEq P] (m : P) (u v : GlueCarFix m) :
    leGlueGen m (equivGlueCarGen m u).1 (equivGlueCarGen m v).1 ↔ leGlueGen m u.1 v.1 :=
  Iff.rfl

end CanonFixed
