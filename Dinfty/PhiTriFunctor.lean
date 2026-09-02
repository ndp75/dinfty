import Dinfty.GenContinuity

open GluingTowerLibrary SierpinskiApplication

/-!
# Ingredient 2: `Φ_tri_v2` is a functor

Pillar A's ingredient 2 has always been carried informally: *`Φ_tri_v2` is a
functor on tripointed posets*.  This file states and proves it.

## The category

Obstruction (T) (`Dinfty/TripointedObstruction.lean`) settled what the morphisms
have to be.  `GlueCarGen` glues at `⊥`, at the marked point `m`, and at `⊤`, so
a tagwise action can only descend if it respects all three.  So:

* **objects** — a bounded partial order `P` with a marked point `m` satisfying
  `m ≠ ⊥`, `m ≠ ⊤`, `⊥ ≠ ⊤`;
* **morphisms** `(P, m) → (P', m')` — a monotone `g` with `g ⊥ = ⊥`,
  `g m = m'`, `g ⊤ = ⊤`  (`TriHom` below).

## `Φ` on objects and on morphisms

On objects `Φ (P, m) = (GlueCarGen m, triMark m)`, with the three distinguished
points

```lean
triBot  m = tag_A ⊥        -- proved least    (triBot_le)
triMark m = tag_A m        -- the new marked point
triTop  m = tag_C ⊤        -- proved greatest (le_triTop)
```

so `Φ` really lands in the same category (`triMark_ne_triBot`,
`triMark_ne_triTop`, `triBot_ne_triTop`).

On morphisms `Φ g` is `GenContinuity.baseMapGen g` **followed by `canonGen`** —
i.e. the tagwise map descended through the glue quotient.  Taking the quotient
seriously is what makes this work, and it is worth saying why.

> **Why the descent, and not `baseMapGen` on the nose.**  `baseMapGen g` does
> *not* preserve canonical forms: `Sum.inr (Sum.inl x)` with `x ≠ ⊥` is
> canonical, but its image `Sum.inr (Sum.inl (g x))` is canonical only if
> `g x ≠ ⊥`.  So a "functor" defined by restriction would need `g` to *reflect*
> `⊥` and `m`, which is a strictly stronger — and unnatural — condition.
> Composing with `canonGen` needs none of that: `canonGen_baseMapGen_canon`
> shows the three glue identifications
> `tag_B ⊥ ~ tag_A m`, `tag_C ⊥ ~ tag_A ⊤`, `tag_C m ~ tag_B ⊤`
> are respected using exactly `g ⊥ = ⊥`, `g m = m'`, `g ⊤ = ⊤` and nothing else.
> The three tripointed conditions are used once each, one per seam.

## The laws

```lean
phiFun_id       : phiFun (TriHom.id m) = id
phiFun_comp     : phiFun (f'.comp f) = phiFun f' ∘ phiFun f
phiFun_monotone : Monotone (phiFun f)
phiFun_triBot / phiFun_triMark / phiFun_triTop
```

Functoriality is cheap; the content is in monotonicity and in the descent, which
is where the seams are consulted.  `occsGen_map` and `rawRuleGen_map` carry the
glued order across, and `occsGen_mem_canon` says that passing to the canonical
form only ever *adds* occurrences — so the glued order can only improve.
-/

open scoped Classical

universe u

namespace PhiTriFunctor

open GenContinuity

/-! ## Tripointed morphisms -/

section Hom

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {P'' : Type u} [DecidableEq P''] [PartialOrder P''] [BoundedOrder P'']

/-- A **tripointed morphism**: monotone, and preserving all three points the
gluing identifies along.  Obstruction (T) says nothing weaker can work. -/
structure TriHom (m : P) (m' : P') where
  toFun : P →o P'
  map_bot : toFun ⊥ = ⊥
  map_mark : toFun m = m'
  map_top : toFun ⊤ = ⊤

namespace TriHom

/-- The identity is tripointed. -/
def id (m : P) : TriHom m m where
  toFun := OrderHom.id
  map_bot := rfl
  map_mark := rfl
  map_top := rfl

/-- Tripointed morphisms compose. -/
def comp {m : P} {m' : P'} {m'' : P''} (f' : TriHom m' m'') (f : TriHom m m') :
    TriHom m m'' where
  toFun := f'.toFun.comp f.toFun
  map_bot := by simp only [OrderHom.comp_coe, Function.comp_apply, f.map_bot, f'.map_bot]
  map_mark := by
    simp only [OrderHom.comp_coe, Function.comp_apply, f.map_mark, f'.map_mark]
  map_top := by simp only [OrderHom.comp_coe, Function.comp_apply, f.map_top, f'.map_top]

end TriHom

/-! ## `baseMapGen` is tagwise-functorial -/

theorem baseMapGen_id (x : GlueBaseGen P) :
    baseMapGen (OrderHom.id : P →o P) x = x := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl a => rfl
    | inr a => rfl

theorem baseMapGen_comp (g : P →o P') (g' : P' →o P'') (x : GlueBaseGen P) :
    baseMapGen (g'.comp g) x = baseMapGen g' (baseMapGen g x) := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl a => rfl
    | inr a => rfl

end Hom

/-! ## The glued order is carried across -/

section Order

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

/-- The raw rule is tagwise, so a monotone map preserving the marked point
carries it across. -/
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

/-- Occurrences are carried across.  The three two-element occurrence lists are
exactly the three glue seams, and each is handled by one of the three tripointed
equations. -/
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

/-- **The glued order is carried across.** -/
theorem leGlueGen_map (f : TriHom m m') (hmt' : m' ≠ ⊤) {x y : GlueBaseGen P}
    (h : leGlueGen m x y) :
    leGlueGen m' (baseMapGen f.toFun x) (baseMapGen f.toFun y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨baseMapGen f.toFun u, occsGen_map f hmt' hu,
         baseMapGen f.toFun v, occsGen_map f hmt' hv, rawRuleGen_map f huv⟩

/-- **Passing to the canonical form only adds occurrences.**  Each of the three
seams sends a one-element occurrence list to a two-element one containing it. -/
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

/-- …so the glued order survives canonicalisation. -/
theorem leGlueGen_canon (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (h : leGlueGen m x y) :
    leGlueGen m (canonGen m x) (canonGen m y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨u, occsGen_mem_canon m hm hmt hbt hu, v, occsGen_mem_canon m hm hmt hbt hv, huv⟩

end Order

/-! ## The descent -/

section Descent

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

/-- **The tagwise map respects the three glue identifications.**

This is the one place the tripointed hypotheses do real work, and each is used
exactly once — `map_mark` for the `tag_B ⊥ ~ tag_A m` seam, `map_top` for
`tag_C ⊥ ~ tag_A ⊤`, and `map_mark` again for `tag_C m ~ tag_B ⊤`. -/
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

/-! ## `Φ` on objects: the three distinguished points -/

section Points

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- The bottom of `Φ (P, m)`: copy `A` at `⊥`. -/
def triBot (m : P) : GlueCarGen (P := P) m := ⟨Sum.inl ⊥, rfl⟩

/-- The marked point of `Φ (P, m)`: copy `A` at `m`.  This is the tower's
`dMid (k+1) = glueA (markedPt k) (markedPt k)`. -/
def triMark (m : P) : GlueCarGen (P := P) m := ⟨Sum.inl m, rfl⟩

/-- The top of `Φ (P, m)`: copy `C` at `⊤`. -/
def triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) : GlueCarGen (P := P) m :=
  ⟨Sum.inr (Sum.inr ⊤), by simp [canonGen, Ne.symm hbt, Ne.symm hmt]⟩

theorem triBot_le (m : P) (x : GlueCarGen (P := P) m) : triBot m ≤ x := by
  refine ⟨Sum.inl ⊥, self_mem_occsGen _ _, x.1, self_mem_occsGen _ _, ?_⟩
  cases hx : x.1 with
  | inl a => exact bot_le
  | inr y => cases y with
    | inl a => exact bot_le
    | inr a => trivial

theorem le_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : GlueCarGen (P := P) m) : x ≤ triTop m hmt hbt := by
  refine ⟨x.1, self_mem_occsGen _ _, Sum.inr (Sum.inr ⊤), self_mem_occsGen _ _, ?_⟩
  cases hx : x.1 with
  | inl a => trivial
  | inr y => cases y with
    | inl a => exact le_top
    | inr a => exact le_top

theorem triMark_ne_triBot (m : P) (hm : m ≠ ⊥) : triMark m ≠ triBot m := by
  intro h
  exact hm (Sum.inl.inj (congrArg Subtype.val h))

theorem triMark_ne_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    triMark m ≠ triTop m hmt hbt := by
  intro h
  have hv := congrArg Subtype.val h
  simp [triMark, triTop] at hv

theorem triBot_ne_triTop (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    triBot m ≠ triTop m hmt hbt := by
  intro h
  have hv := congrArg Subtype.val h
  simp [triBot, triTop] at hv

end Points

/-! ## `Φ` on morphisms, and the functor laws -/

section Functor

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {P'' : Type u} [DecidableEq P''] [PartialOrder P''] [BoundedOrder P'']
variable {m : P} {m' : P'} {m'' : P''}

/-- **`Φ` on morphisms**: the tagwise map, descended through the glue quotient. -/
def phiFun (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    GlueCarGen (P := P) m → GlueCarGen (P := P') m' :=
  fun x => ⟨canonGen m' (baseMapGen f.toFun x.1),
            canonGen_idem m' hm' hbt' _⟩

@[simp] theorem phiFun_val (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (x : GlueCarGen (P := P) m) :
    (phiFun f hm' hbt' x).1 = canonGen m' (baseMapGen f.toFun x.1) := rfl

/-- **Functor law 1: identity.** -/
theorem phiFun_id (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    phiFun (TriHom.id m) hm hbt = _root_.id := by
  funext x
  refine Subtype.ext ?_
  show canonGen m (baseMapGen (OrderHom.id : P →o P) x.1) = x.1
  rw [baseMapGen_id]
  exact x.2

/-- **Functor law 2: composition.** -/
theorem phiFun_comp (f : TriHom m m') (f' : TriHom m' m'')
    (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (hm'' : m'' ≠ ⊥) (hbt'' : (⊥ : P'') ≠ ⊤) :
    phiFun (f'.comp f) hm'' hbt'' = phiFun f' hm'' hbt'' ∘ phiFun f hm' hbt' := by
  funext x
  refine Subtype.ext ?_
  show canonGen m'' (baseMapGen (f'.toFun.comp f.toFun) x.1)
    = canonGen m'' (baseMapGen f'.toFun (canonGen m' (baseMapGen f.toFun x.1)))
  rw [canonGen_baseMapGen_canon f' hm' hm'' hbt'', baseMapGen_comp]

/-- **Functor law 3: `Φ g` is monotone.** -/
theorem phiFun_monotone (f : TriHom m m') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) {x y : GlueCarGen (P := P) m} (h : x ≤ y) :
    phiFun f hm' hbt' x ≤ phiFun f hm' hbt' y :=
  leGlueGen_canon m' hm' hmt' hbt' (leGlueGen_map f hmt' h)

/-! ### `Φ g` is again tripointed -/

theorem phiFun_triBot (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triBot m) = triBot m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun ⊥)) = Sum.inl ⊥
  rw [f.map_bot]
  rfl

theorem phiFun_triMark (f : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triMark m) = triMark m' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inl (f.toFun m)) = Sum.inl m'
  rw [f.map_mark]
  rfl

theorem phiFun_triTop (f : TriHom m m') (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤) :
    phiFun f hm' hbt' (triTop m hmt hbt) = triTop m' hmt' hbt' := by
  refine Subtype.ext ?_
  show canonGen m' (Sum.inr (Sum.inr (f.toFun ⊤))) = Sum.inr (Sum.inr ⊤)
  rw [f.map_top]
  simp [canonGen, Ne.symm hbt', Ne.symm hmt']

/-! ## Ingredient 2, in one statement

Everything above, bundled, so that "ingredient 2 is proved" has a single name to
point at.  Read the seven conjuncts as: `Φ` lands in the category again; it
respects identities; it respects composition; and `Φ g` is a monotone tripointed
map. -/

/-- **Ingredient 2: `Φ_tri_v2` is an endofunctor on tripointed posets.** -/
theorem phi_functor_laws
    (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤) (hbt' : (⊥ : P') ≠ ⊤)
    (m'' : P'') (hm'' : m'' ≠ ⊥) (hbt'' : (⊥ : P'') ≠ ⊤)
    (f : TriHom m m') (f' : TriHom m' m'') :
    -- (i) the image object is again tripointed
    (triMark m ≠ triBot m ∧ triMark m ≠ triTop m hmt hbt
      ∧ triBot m ≠ triTop m hmt hbt)
    -- (ii) identities
    ∧ phiFun (TriHom.id m) hm hbt = _root_.id
    -- (iii) composition
    ∧ phiFun (f'.comp f) hm'' hbt'' = phiFun f' hm'' hbt'' ∘ phiFun f hm' hbt'
    -- (iv) monotone
    ∧ (∀ x y : GlueCarGen (P := P) m, x ≤ y →
        phiFun f hm' hbt' x ≤ phiFun f hm' hbt' y)
    -- (v)-(vii) tripointed
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
