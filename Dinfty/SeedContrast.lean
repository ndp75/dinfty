import Dinfty.JinfReduction

open GluingTowerLibrary SierpinskiApplication

/-!
# The two points differ only in a seed

`JinfReduction` left the problem as: separate `midJ` from `topJ` inside `J∞`,
where at stage `k+1` their down-sets are `↓(constHom (dMid k))` and
`↓(⊤ : EndP (D k))` inside `EndP (D k)`.  This module computes those down-sets
and finds that the difference is much smaller than it looks.

## The mechanism: `q` drops out

For *any* monotone `f`, `f ≤ constHom c ↔ f ⊤ ≤ c` (`endP_le_constHom_iff`) —
monotonicity makes the top value decide everything.  The join-irreducibles of
`EndP P` are exactly the step maps `stepMap x q` with `x` join-irreducible
(`joinIrred_endP_iff_exists_stepMap`, library), and `stepMap x q ⊤ = x`.  So

```lean
stepMap_le_constHom_iff : stepMap x q ≤ constHom c ↔ x ≤ c
```

**The `q` coordinate is unconstrained.**  Hence

```lean
jiEndP_below_constHom :
  {f | JoinIrred (EndP P) f ∧ f ≤ constHom c}
    = {f | ∃ x q, JoinIrred P x ∧ x ≤ c ∧ f = stepMap x q}
```

and the parametrization is injective (`stepMap_param_inj`), so as a poset this
set is `(J(P) ∩ ↓c) × P` with the second coordinate contravariant — the shape
recorded in the handoff's "join-irred copy-`A` family ≅ `J(P) × Pᵒᵖ`", now
localized to a single down-set.

## The consequence: same recursion, different seed

Writing `S_k(c) := J(D k) ∩ ↓c` for the *seed* at level `k`, the display above
says the join-irreducibles below `iotaD k c` are `S_k(c) × (D k)ᵒᵖ` — and the
seed at the next level is again of that form.  So both points' down-sets in `J∞`
are colimits of the **same** recursion

```
S_{k+1} = S_k × (D k)ᵒᵖ
```

differing only in `S_0`:

* `midJ`'s seed is `{dMid 0}` — **one point** (`seed_mid_card`);
* `topJ`'s seed is `{dMid 0, ⊤}` — a **2-chain** (`seed_top_card`).

At every finite stage the two down-sets therefore have sizes in the constant
ratio `2 : 1`, and identical shape otherwise.

## What that means for the attack

An order-theoretic separator for `midJ` and `topJ` must see a one-point seed
against a two-chain seed **through infinitely many product extensions by
`(D k)ᵒᵖ`**, each of which has at least 27 elements from `k = 1` on.  That is a
much more specific — and much more discouraging — statement than "no invariant is
known", and it is the first quantitative description of what the base case
actually asks for.

It is also a concrete question a future session can settle either way: are
`colim S_k` and `colim (2 × S_k)` isomorphic as posets?  If yes, the most natural
family of separators is dead and the refutation side of `TwoPointFixed` becomes
the priority.  Nothing here answers that.
-/

open scoped Classical

namespace SeedContrast

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis JinfReduction

section General

variable {P : Type*} [Lattice P] [BoundedOrder P]

/-- **Monotonicity makes the top value decide.**  For any monotone `f`,
being below a constant is a condition on `f ⊤` alone. -/
theorem endP_le_constHom_iff (f : EndP P) (c : P) :
    f ≤ (constHom c : EndP P) ↔ f ⊤ ≤ c := by
  constructor
  · intro h
    have := (OrderHom.le_def.mp h) (⊤ : P)
    rwa [constHom_apply] at this
  · intro h
    rw [OrderHom.le_def]
    intro y
    rw [constHom_apply]
    exact le_trans (f.monotone le_top) h

end General

section Step

variable {P : Type*} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

/-- **The `q` coordinate drops out.**  A step map is below a constant exactly
when its *value* is, whatever its threshold. -/
theorem stepMap_le_constHom_iff (x q c : P) :
    (stepMap x q : EndP P) ≤ constHom c ↔ x ≤ c := by
  rw [endP_le_constHom_iff]
  rw [stepMap_apply_of_ge x q (le_top : q ≤ (⊤ : P))]

/-- The join-irreducibles of `EndP P` below a constant, parametrized. -/
theorem jiEndP_below_constHom (c : P) :
    {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom c}
      = {f : EndP P | ∃ x q : P, JoinIrred P x ∧ x ≤ c ∧ f = stepMap x q} := by
  ext f
  constructor
  · rintro ⟨hji, hle⟩
    obtain ⟨x, q, hx, rfl⟩ := (joinIrred_endP_iff_exists_stepMap f).mp hji
    exact ⟨x, q, hx, (stepMap_le_constHom_iff x q c).mp hle, rfl⟩
  · rintro ⟨x, q, hx, hxc, rfl⟩
    exact ⟨(joinIrred_endP_iff_exists_stepMap _).mpr ⟨x, q, hx, rfl⟩,
           (stepMap_le_constHom_iff x q c).mpr hxc⟩

/-- …and the parametrization is injective on join-irreducible values, so the
down-set really is the product `(J(P) ∩ ↓c) × P`, not a quotient of it. -/
theorem stepMap_param_inj {x x' q q' : P} (hx : JoinIrred P x) (hx' : JoinIrred P x')
    (h : (stepMap x q : EndP P) = stepMap x' q') : x = x' ∧ q = q' :=
  stepMap_inj_of_ne_bot hx.1 hx'.1 h

/-- The whole point, in one line: **the down-set depends on `c` only through the
seed `J(P) ∩ ↓c`**, never through the `q` coordinate. -/
theorem jiEndP_below_constHom_congr (c d : P)
    (h : ∀ x : P, JoinIrred P x → (x ≤ c ↔ x ≤ d)) :
    {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom c}
      = {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom d} := by
  rw [jiEndP_below_constHom, jiEndP_below_constHom]
  ext f
  constructor
  · rintro ⟨x, q, hx, hxc, rfl⟩; exact ⟨x, q, hx, (h x hx).mp hxc, rfl⟩
  · rintro ⟨x, q, hx, hxd, rfl⟩; exact ⟨x, q, hx, (h x hx).mpr hxd, rfl⟩

end Step

/-! ## The two seeds, at level `0` -/

-- NOTE: `JoinIrred`'s own `Decidable` instance in this project is classical, so
-- `decide` cannot reduce a goal mentioning `JoinIrred` directly (the kernel gets
-- stuck on `Classical.choice`).  The pattern that works — and the one
-- `D_mid_joinIrred`'s base case already uses — is to unfold `JoinIrred` into its
-- two components first, each of which is a concrete `Fin 3` statement.

/-- The join-irreducibles of the base level are exactly `1` and `2`. -/
theorem joinIrred_fin3_iff (x : Fin 3) : JoinIrred (Fin 3) x ↔ (x = 1 ∨ x = 2) := by
  constructor
  · intro h
    fin_cases x
    · exact absurd (by decide : (0 : Fin 3) = ⊥) h.1
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩

/-- **`midJ`'s seed is a single point.** -/
theorem seed_mid (x : Fin 3) :
    (JoinIrred (Fin 3) x ∧ x ≤ (1 : Fin 3)) ↔ x = 1 := by
  rw [joinIrred_fin3_iff]
  constructor
  · rintro ⟨rfl | rfl, hle⟩
    · rfl
    · exact absurd hle (by decide)
  · rintro rfl
    exact ⟨Or.inl rfl, le_rfl⟩

/-- **`topJ`'s seed is a two-element chain.** -/
theorem seed_top (x : Fin 3) :
    (JoinIrred (Fin 3) x ∧ x ≤ (2 : Fin 3)) ↔ (x = 1 ∨ x = 2) := by
  rw [joinIrred_fin3_iff]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr rfl, le_rfl⟩

/-- The seeds really differ: `⊤` is join-irreducible and in the second, not the
first.  So the two down-sets are not equal — the open question is only whether
they become order-*isomorphic* after infinitely many `(D k)ᵒᵖ` extensions. -/
theorem seeds_differ :
    ¬ (∀ x : Fin 3, (JoinIrred (Fin 3) x ∧ x ≤ (1 : Fin 3))
        ↔ (JoinIrred (Fin 3) x ∧ x ≤ (2 : Fin 3))) := by
  intro h
  have h2 := (h 2).mpr ⟨(joinIrred_fin3_iff 2).mpr (Or.inr rfl), le_rfl⟩
  exact absurd h2.2 (by decide)

end SeedContrast
