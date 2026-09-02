import Dinfty.GenContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-2019] §Ingredient-2-tri-v2-is-a-functor
open scoped Classical

universe u

namespace PhiTriFunctor

open GenContinuity

-- [D-2020] §Tripointed-morphisms
section Hom

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {P'' : Type u} [DecidableEq P''] [PartialOrder P''] [BoundedOrder P'']

-- [D-2021] TriHom
structure TriHom (m : P) (m' : P') where
  toFun : P →o P'
  map_bot : toFun ⊥ = ⊥
  map_mark : toFun m = m'
  map_top : toFun ⊤ = ⊤

namespace TriHom

-- [D-2022] id
def id (m : P) : TriHom m m where
  toFun := OrderHom.id
  map_bot := rfl
  map_mark := rfl
  map_top := rfl

-- [D-2023] comp
def comp {m : P} {m' : P'} {m'' : P''} (f' : TriHom m' m'') (f : TriHom m m') :
    TriHom m m'' where
  toFun := f'.toFun.comp f.toFun
  map_bot := by simp only [OrderHom.comp_coe, Function.comp_apply, f.map_bot, f'.map_bot]
  map_mark := by
    simp only [OrderHom.comp_coe, Function.comp_apply, f.map_mark, f'.map_mark]
  map_top := by simp only [OrderHom.comp_coe, Function.comp_apply, f.map_top, f'.map_top]

end TriHom

-- [D-2024] §baseMapGen-is-tagwise-functorial
-- [D-2025] baseMapGen_id
theorem baseMapGen_id (x : GlueBaseGen P) :
    baseMapGen (OrderHom.id : P →o P) x = x := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl a => rfl
    | inr a => rfl

-- [D-2026] baseMapGen_comp
theorem baseMapGen_comp (g : P →o P') (g' : P' →o P'') (x : GlueBaseGen P) :
    baseMapGen (g'.comp g) x = baseMapGen g' (baseMapGen g x) := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl a => rfl
    | inr a => rfl

end Hom

-- [D-2027] §The-glued-order-is-carried-across
section Order

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

-- [D-2028] rawRuleGen_map
theorem rawRuleGen_map (f : TriHom m m') {u v : GlueBaseGen P}
    (h : rawRuleGen m u v) :
    rawRuleGen m' (baseMapGen f.toFun u) (baseMapGen f.toFun v) := by
  cases u with
  | inl a => cases v with
    | inl b => exact f.toFun.monotone h
    | inr y => cases y with
      | inl b =>
          show f.toFun a ≤ m'
          exact le_of_le_of_eq (f.toFun.monotone h) f.map_mark
      | inr b => trivial
  | inr x => cases x with
    | inl a => cases v with
      | inl b => exact absurd h not_false
      | inr y => cases y with
        | inl b => exact f.toFun.monotone h
        | inr b =>
            show m' ≤ f.toFun b
            exact le_of_eq_of_le f.map_mark.symm (f.toFun.monotone h)
    | inr a => cases v with
      | inl b => exact absurd h not_false
      | inr y => cases y with
        | inl b => exact absurd h not_false
        | inr b => exact f.toFun.monotone h

-- [D-2029] occsGen_map
theorem occsGen_map (f : TriHom m m') (hmt' : m' ≠ ⊤) {x u : GlueBaseGen P}
    (hu : u ∈ occsGen m x) :
    baseMapGen f.toFun u ∈ occsGen m' (baseMapGen f.toFun x) := by
  cases x with
  | inl a =>
      simp only [occsGen] at hu
      split_ifs at hu with h1 h2
      · subst h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact self_mem_occsGen _ _
        · show (Sum.inr (Sum.inl (f.toFun ⊥)) : GlueBaseGen P')
            ∈ occsGen m' (Sum.inl (f.toFun a))
          rw [f.map_bot, f.map_mark]
          simp [occsGen]
      · subst h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact self_mem_occsGen _ _
        · show (Sum.inr (Sum.inr (f.toFun ⊥)) : GlueBaseGen P')
            ∈ occsGen m' (Sum.inl (f.toFun ⊤))
          rw [f.map_bot, f.map_top]
          simp [occsGen, Ne.symm hmt']
      · simp only [List.mem_singleton] at hu
        subst hu
        exact self_mem_occsGen _ _
  | inr y => cases y with
    | inl a =>
        simp only [occsGen] at hu
        split_ifs at hu with h1
        · subst h1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact self_mem_occsGen _ _
          · show (Sum.inr (Sum.inr (f.toFun m)) : GlueBaseGen P')
              ∈ occsGen m' (Sum.inr (Sum.inl (f.toFun ⊤)))
            rw [f.map_mark, f.map_top]
            simp [occsGen]
        · simp only [List.mem_singleton] at hu
          subst hu
          exact self_mem_occsGen _ _
    | inr a =>
        simp only [occsGen, List.mem_singleton] at hu
        subst hu
        exact self_mem_occsGen _ _

-- [D-2030] leGlueGen_map
theorem leGlueGen_map (f : TriHom m m') (hmt' : m' ≠ ⊤) {x y : GlueBaseGen P}
    (h : leGlueGen m x y) :
    leGlueGen m' (baseMapGen f.toFun x) (baseMapGen f.toFun y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨baseMapGen f.toFun u, occsGen_map f hmt' hu,
         baseMapGen f.toFun v, occsGen_map f hmt' hv, rawRuleGen_map f huv⟩

-- [D-2031] occsGen_mem_canon
theorem occsGen_mem_canon (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x u : GlueBaseGen P} (hu : u ∈ occsGen m x) : u ∈ occsGen m (canonGen m x) := by
  cases x with
  | inl a => exact hu
  | inr y => cases y with
    | inl a =>
        by_cases ha : a = ⊥
        · subst ha
          simp only [occsGen, if_neg hbt, List.mem_singleton] at hu
          subst hu
          simp [canonGen, occsGen]
        · simpa [canonGen, ha] using hu
    | inr a =>
        simp only [occsGen, List.mem_singleton] at hu
        subst hu
        by_cases ha : a = ⊥
        · subst ha
          simp [canonGen, occsGen, Ne.symm hmt]
        · by_cases ham : a = m
          · subst ham
            simp [canonGen, occsGen, ha]
          · simp [canonGen, occsGen, ha, ham]

-- [D-2032] leGlueGen_canon
theorem leGlueGen_canon (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (h : leGlueGen m x y) :
    leGlueGen m (canonGen m x) (canonGen m y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨u, occsGen_mem_canon m hm hmt hbt hu, v, occsGen_mem_canon m hm hmt hbt hv, huv⟩

end Order

-- [D-2033] §The-descent
section Descent

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

-- [D-2034] canonGen_baseMapGen_canon
theorem canonGen_baseMapGen_canon (f : TriHom m m') (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (hbt' : (⊥ : P') ≠ ⊤) (x : GlueBaseGen P) :
    canonGen m' (baseMapGen f.toFun (canonGen m x))
      = canonGen m' (baseMapGen f.toFun x) := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl a =>
        by_cases ha : a = ⊥
        · subst ha
          simp [canonGen, baseMapGen, f.map_bot, f.map_mark]
        · simp [canonGen, ha]
    | inr a =>
        by_cases ha : a = ⊥
        · subst ha
          simp [canonGen, baseMapGen, f.map_bot, f.map_top]
        · by_cases ham : a = m
          · rw [ham]
            simp [canonGen, baseMapGen, f.map_mark, f.map_top, hm, hm',
              Ne.symm hbt']
          · simp [canonGen, ha, ham]

end Descent

-- [D-2035] §on-objects-the-three-distinguished-points
section Points

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-2036] triBot
def triBot (m : P) : GlueCarGen (P := P) m := ⟨Sum.inl ⊥, rfl⟩

-- [D-2037] triMark
def triMark (m : P) : GlueCarGen (P := P) m := ⟨Sum.inl m, rfl⟩

-- [D-2038] triTop
def triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) : GlueCarGen (P := P) m :=
  ⟨Sum.inr (Sum.inr ⊤), by simp [canonGen, Ne.symm hbt, Ne.symm hmt]⟩

-- [D-2039] triBot_le
theorem triBot_le (m : P) (x : GlueCarGen (P := P) m) : triBot m ≤ x := by
  refine ⟨Sum.inl ⊥, self_mem_occsGen _ _, x.1, self_mem_occsGen _ _, ?_⟩
  cases hx : x.1 with
  | inl a => exact bot_le
  | inr y => cases y with
    | inl a => exact bot_le
    | inr a => trivial

-- [D-2040] le_triTop
theorem le_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : GlueCarGen (P := P) m) : x ≤ triTop m hmt hbt := by
  refine ⟨x.1, self_mem_occsGen _ _, Sum.inr (Sum.inr ⊤), self_mem_occsGen _ _, ?_⟩
  cases hx : x.1 with
  | inl a => trivial
  | inr y => cases y with
    | inl a => exact le_top
    | inr a => exact le_top

-- [D-2041] triMark_ne_triBot
theorem triMark_ne_triBot (m : P) (hm : m ≠ ⊥) : triMark m ≠ triBot m := by
  intro h
  exact hm (Sum.inl.inj (congrArg Subtype.val h))

-- [D-2042] triMark_ne_triTop
theorem triMark_ne_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    triMark m ≠ triTop m hmt hbt := by
  intro h
  have hv := congrArg Subtype.val h
  simp [triMark, triTop] at hv

-- [D-2043] triBot_ne_triTop
theorem triBot_ne_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    triBot m ≠ triTop m hmt hbt := by
  intro h
  have hv := congrArg Subtype.val h
  simp [triBot, triTop] at hv

end Points

-- [D-2044] §on-morphisms-and-the-functor-laws
section Functor

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {P'' : Type u} [DecidableEq P''] [PartialOrder P''] [BoundedOrder P'']
variable {m : P} {m' : P'} {m'' : P''}

-- [D-2045] phiFun
def phiFun (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    GlueCarGen (P := P) m → GlueCarGen (P := P') m' :=
  fun x => ⟨canonGen m' (baseMapGen f.toFun x.1),
            canonGen_idem m' hm' hbt' _⟩

-- [D-2046] phiFun_val
@[simp] theorem phiFun_val (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (x : GlueCarGen (P := P) m) :
    (phiFun f hm' hbt' x).1 = canonGen m' (baseMapGen f.toFun x.1) := rfl

-- [D-2047] phiFun_id
theorem phiFun_id (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    phiFun (TriHom.id m) hm hbt = _root_.id := by
  funext x
  refine Subtype.ext ?_
  show canonGen m (baseMapGen (OrderHom.id : P →o P) x.1) = x.1
  rw [baseMapGen_id]
  exact x.2

-- [D-2048] phiFun_comp
theorem phiFun_comp (f : TriHom m m') (f' : TriHom m' m'')
    (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (hm'' : m'' ≠ ⊥) (hbt'' : (⊥ : P'') ≠ ⊤) :
    phiFun (f'.comp f) hm'' hbt'' = phiFun f' hm'' hbt'' ∘ phiFun f hm' hbt' := by
  funext x
  refine Subtype.ext ?_
  show canonGen m'' (baseMapGen (f'.toFun.comp f.toFun) x.1)
    = canonGen m'' (baseMapGen f'.toFun (canonGen m' (baseMapGen f.toFun x.1)))
  rw [canonGen_baseMapGen_canon f' hm' hm'' hbt'', baseMapGen_comp]

-- [D-2049] phiFun_monotone
theorem phiFun_monotone (f : TriHom m m') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) {x y : GlueCarGen (P := P) m} (h : x ≤ y) :
    phiFun f hm' hbt' x ≤ phiFun f hm' hbt' y :=
  leGlueGen_canon m' hm' hmt' hbt' (leGlueGen_map f hmt' h)

-- [D-2050] §g-is-again-tripointed
-- [D-2051] phiFun_triBot
theorem phiFun_triBot (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triBot m) = triBot m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun ⊥)) = Sum.inl ⊥
  rw [f.map_bot]
  rfl

-- [D-2052] phiFun_triMark
theorem phiFun_triMark (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triMark m) = triMark m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun m)) = Sum.inl m'
  rw [f.map_mark]
  rfl

-- [D-2053] phiFun_triTop
theorem phiFun_triTop (f : TriHom m m') (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triTop m hmt hbt) = triTop m' hmt' hbt' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inr (Sum.inr (f.toFun ⊤))) = Sum.inr (Sum.inr ⊤)
  rw [f.map_top]
  simp [canonGen, Ne.symm hbt', Ne.symm hmt']

-- [D-2054] §Ingredient-2-in-one-statement
-- [D-2055] phi_functor_laws
theorem phi_functor_laws
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤)
    (m'' : P'') (hm'' : m'' ≠ ⊥) (hbt'' : (⊥ : P'') ≠ ⊤)
    (f : TriHom m m') (f' : TriHom m' m'') :
    (triMark m ≠ triBot m ∧ triMark m ≠ triTop m hmt hbt
      ∧ triBot m ≠ triTop m hmt hbt)
    ∧ phiFun (TriHom.id m) hm hbt = _root_.id
    ∧ phiFun (f'.comp f) hm'' hbt'' = phiFun f' hm'' hbt'' ∘ phiFun f hm' hbt'
    ∧ (∀ x y : GlueCarGen (P := P) m, x ≤ y →
        phiFun f hm' hbt' x ≤ phiFun f hm' hbt' y)
    ∧ phiFun f hm' hbt' (triBot m) = triBot m'
    ∧ phiFun f hm' hbt' (triMark m) = triMark m'
    ∧ phiFun f hm' hbt' (triTop m hmt hbt) = triTop m' hmt' hbt' :=
  ⟨⟨triMark_ne_triBot m hm, triMark_ne_triTop m hmt hbt, triBot_ne_triTop m hmt hbt⟩,
   phiFun_id m hm hbt,
   phiFun_comp f f' hm' hbt' hm'' hbt'',
   fun _ _ h => phiFun_monotone f hm' hmt' hbt' h,
   phiFun_triBot f hm' hbt',
   phiFun_triMark f hm' hbt',
   phiFun_triTop f hmt hbt hm' hmt' hbt'⟩

end Functor

end PhiTriFunctor
