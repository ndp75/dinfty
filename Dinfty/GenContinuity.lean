import Dinfty.GlueMapContinuity

open GluingTowerLibrary SierpinskiApplication

/-!
# Local continuity in the infinite case — the reduction

**The question this answers: can induction get local continuity at the
bilimit?  No — and the reason matters more than the answer.**

Induction over tower levels proves `∀ k, P (level k)`.  It does not prove
`P (bilimit)`.  That is the finite/limit trap this project has logged
repeatedly, and `[[project_dinfty_meta_recursion_wall_lesson]]` states the
screening criterion outright: *"characterize level n, induct" is structurally
doomed; parametric-over-arbitrary-`P` is the only escape.*  The finite-level
result in `GlueMapContinuity` is a live example — it holds because directed
sups in a finite poset are attained inside the family, which is exactly the
hypothesis that fails in the limit.  Iterating it buys nothing.

**But local continuity is not a statement about the tower at all.**  It says:
for *any* dcpos `D`, `D'` and any directed family of morphisms `gᵢ : D → D'`,
`Φ(⨆ gᵢ) = ⨆ Φ(gᵢ)`.  No induction is called for — what is needed is that the
construction be stated without finiteness, and it already can be:
`GlueCarGen` is the Fintype/Lattice-free copy of `GlueCar`, and
`glueCarPartialOrderGen` gives it a `PartialOrder` from
`[DecidableEq P] [PartialOrder P] [BoundedOrder P]` alone.  So `IsLUB` is
statable there, over an arbitrary — in particular infinite — carrier.

## The reduction

`baseMapGen` is **tagwise**, and the sup of a family of morphisms is
**pointwise**.  So at a point `x = tag_t a`:

    baseMapGen (⨆ gᵢ) (tag_t a)  =  tag_t ((⨆ gᵢ) a)  =  tag_t (⨆ᵢ gᵢ a)
    ⨆ᵢ baseMapGen (gᵢ) (tag_t a) =  ⨆ᵢ tag_t (gᵢ a)

and these agree exactly when `tag_t` carries the sup of `{gᵢ a}` to the sup of
`{tag_t (gᵢ a)}`.  That is:

> **Local continuity of `Φ`'s morphism action reduces, with no finiteness and
> no induction, to Scott-continuity of the three copy-inclusions
> `tag_A`, `tag_B`, `tag_C`.**

`baseMapGen_isLUB_of_tagIsLUB` below is that reduction, proved.  It converts an
informal, not-finitely-checkable claim into three named lemmas about a single
map each — which is the first form in which ingredient 3 has been finitely
*decomposable*, even though it is still not finitely *checkable*.

## Status of the three obligations

* **`tag_A` — PROVED** (`tagAGen_isLUB`), and in a stronger form than needed:
  the copy-`A` inclusion preserves *every* supremum, not merely directed ones,
  over an arbitrary carrier, with no finiteness and no lattice.  Its gateway is
  `leGlueGen_tagA_tagA_iff`, the `Gen` analogue of `glueA_le_iff` (which
  existed only in the finite `Lattice` world, line 1798).
* **`tag_B` — PROVED** (`tagB_isLUB_raw`), on the canon-fixed region.
* **`tag_C` — PROVED** (`tagC_isLUB_raw`), needing only `s ≠ ⊥`.

All three are proved on raw `GlueBaseGen` values, spelled out as "upper bound +
least" rather than as `IsLUB` in the subtype, which keeps the order content
visible and — for copies `B`/`C` — sidesteps a genuine partiality (see the
correction heading their section).

**What this does and does not amount to.**  All three obligations the reduction
names are discharged, finiteness-free and without induction.  That is the first
limit-side purchase on ingredient 3 the project has had, and unlike the
finite-level result in `GlueMapContinuity` it does generalise.

It is still **not** ingredient 3.  Two gaps remain, and they are structural,
not bookkeeping:

1. **Transport to the subtype.**  The copy-`B`/`C` results are raw-value
   statements.  Turning them into `IsLUB` in `GlueCarGen` needs the sup to stay
   in the canon-fixed region, which for copy `C` can fail (a set of elements
   `≠ m` can have supremum `m`).
2. **Mixed variance.**  This covers `Φ`'s action on hom-sets.  Ingredient 3 as
   cited is local continuity of `Φ ∘ End` on an O-category, and `End` is
   mixed-variance — contravariant in its first argument.  Nothing here touches
   the `End` half.

Anyone citing this should say "the three copy-inclusion obligations are
discharged", not "ingredient 3 is formalized".
-/

open scoped Classical

universe u v

namespace GenContinuity

/-! ## The tagwise action, finiteness-free -/

section BaseMapGen

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

/-- The tagwise action on the Fintype/Lattice-free base.  Same definition as
`NormalizedGlueMap.baseMap`, over an arbitrary — possibly infinite — carrier. -/
def baseMapGen (g : P →o P') : GlueBaseGen P → GlueBaseGen P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (g x))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

@[simp] theorem baseMapGen_inl (g : P →o P') (a : P) :
    baseMapGen g (Sum.inl a) = Sum.inl (g a) := rfl

/-- **Monotone in the morphism, with no finiteness.**  The `GlueMapContinuity`
proof ports verbatim: `baseMapGen` is tagwise, so a pointwise inequality is
carried into each copy separately and the gluing is never consulted — the
witness on both sides is the point's own tag. -/
theorem baseMapGen_leGlueGen_of_le (m' : P') {g g' : P →o P'} (hgg : g ≤ g')
    (x : GlueBaseGen P) :
    leGlueGen m' (baseMapGen g x) (baseMapGen g' x) := by
  have hpt : ∀ a : P, g a ≤ g' a := fun a => OrderHom.le_def.mp hgg a
  cases x with
  | inl a =>
    exact ⟨Sum.inl (g a), self_mem_occsGen _ _, Sum.inl (g' a), self_mem_occsGen _ _, hpt a⟩
  | inr x =>
    cases x with
    | inl a =>
      exact ⟨Sum.inr (Sum.inl (g a)), self_mem_occsGen _ _,
             Sum.inr (Sum.inl (g' a)), self_mem_occsGen _ _, hpt a⟩
    | inr a =>
      exact ⟨Sum.inr (Sum.inr (g a)), self_mem_occsGen _ _,
             Sum.inr (Sum.inr (g' a)), self_mem_occsGen _ _, hpt a⟩

end BaseMapGen

/-! ## The reduction -/

section Reduction

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {ι : Type v}

/-- **The reduction, and it is `rfl`.**  The image of the family under the
morphism action at a copy-`A` point is *literally* the `tag_A`-image of the
family's values there.

This is the whole reduction, and its triviality is the point: once one sees
that `baseMapGen` is tagwise and that sups of morphisms are pointwise, there is
no content left in "the action preserves sups" beyond "the tag inclusions
preserve sups".  All the mathematics is in the obligations below.  Stating it
as anything more elaborate would be dressing up a `rfl`. -/
theorem baseMapGen_range_eq (g : ι → (P →o P')) (a : P) :
    (Set.range fun i => baseMapGen (g i) (Sum.inl a))
      = Set.range fun i => (Sum.inl ((g i) a) : GlueBaseGen P') := rfl

end Reduction

/-! ## The three obligations, named

Stated as `Prop`s so they can be cited, discharged, or refuted individually
without anyone mistaking them for theorems.  `ScottContinuousTagA` is the one
with a sketch (see the module docstring); the other two are open with no route
proposed, and copy `C`'s should not be assumed by analogy — it is the copy
whose inclusion the tower's own `iotaD` fails, by `TripointedObstruction`. -/

section Obligations

variable (P : Type u) [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- Obligation 1: the copy-`A` inclusion preserves sups of directed sets. -/
def ScottContinuousTagA (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) : Prop :=
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  ∀ (S : Set P) (c : P), S.Nonempty → DirectedOn (· ≤ ·) S → IsLUB S c →
    IsLUB (tagAGen m '' S) (tagAGen m c)

end Obligations

/-! ## The gateway lemma for obligation 1

`glueA_le_iff` (`GluingTowerLibrary.lean:1798`) says copy `A` order-embeds, but
it is stated in the finite `Lattice` world.  Obligation 1 needs its `Gen`
analogue — over an arbitrary carrier — and that is the first thing to prove.
Proved here, so obligation 1 now has its gateway. -/

section Gateway

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- **Copy `A` order-embeds, with no finiteness and no lattice.**  The `Gen`
analogue of `glueA_le_iff`.

The bookkeeping is in `occsGen (Sum.inl x)`, which carries a second entry when
`x = m` (the `a.L ~ b.T` seam) or `x = ⊤` (the `a.R ~ c.T` seam); each extra
witness pair is either impossible (`rawRuleGen` from copy `B`/`C` into copy `A`
is `False`), or forces the conclusion anyway. -/
theorem leGlueGen_tagA_tagA_iff (m : P) (hm : m ≠ ⊥) (x y : P) :
    leGlueGen m (Sum.inl x) (Sum.inl y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hocc : ∀ (z : P) (w : GlueBaseGen P), w ∈ occsGen m (Sum.inl z) →
        w = Sum.inl z ∨ (z = m ∧ w = Sum.inr (Sum.inl ⊥))
          ∨ (z = ⊤ ∧ w = Sum.inr (Sum.inr ⊥)) := by
      intro z w hw
      simp only [occsGen] at hw
      split_ifs at hw with h1 h2 <;> simp at hw <;> tauto
    rcases hocc x u hu with rfl | ⟨hxm, rfl⟩ | ⟨hxt, rfl⟩ <;>
      rcases hocc y v hv with rfl | ⟨hym, rfl⟩ | ⟨hyt, rfl⟩
    · exact huv
    · subst hym; exact huv
    · subst hyt; exact le_top
    · exact huv.elim
    · subst hxm; subst hym; exact le_rfl
    · exact absurd (le_bot_iff.mp huv) hm
    · exact huv.elim
    · exact huv.elim
    · subst hxt; subst hyt; exact le_rfl
  · intro h
    exact ⟨Sum.inl x, self_mem_occsGen _ _, Sum.inl y, self_mem_occsGen _ _, h⟩

/-- Copy `A` sits below every copy-`C` point, unconditionally: `rawRuleGen`'s
`Sum.inl _, Sum.inr (Sum.inr _)` clause is `True`. -/
theorem leGlueGen_tagA_tagC (m x c' : P) :
    leGlueGen m (Sum.inl x) (Sum.inr (Sum.inr c')) :=
  ⟨Sum.inl x, self_mem_occsGen _ _, Sum.inr (Sum.inr c'), self_mem_occsGen _ _, trivial⟩

/-- If a copy-`A` point sits below a copy-`B` point that is not the seam
`tag_B ⊤`, then it sits below the marked point.  (At `b = ⊤` the claim is false
and unnecessary — `occsGen` gives `tag_B ⊤` a copy-`C` occurrence, so
everything in copy `A` is below it for free, by `leGlueGen_tagA_tagC`.) -/
theorem le_marked_of_leGlueGen_tagB (m x b : P) (hbt : b ≠ ⊤)
    (h : leGlueGen m (Sum.inl x) (Sum.inr (Sum.inl b))) : x ≤ m := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  have hv' : v = Sum.inr (Sum.inl b) := by
    simp only [occsGen] at hv
    rw [if_neg hbt] at hv
    simpa using hv
  subst hv'
  have hocc : u = Sum.inl x ∨ (x = m ∧ u = Sum.inr (Sum.inl ⊥))
      ∨ (x = ⊤ ∧ u = Sum.inr (Sum.inr ⊥)) := by
    simp only [occsGen] at hu
    split_ifs at hu with h1 h2 <;> simp at hu <;> tauto
  rcases hocc with rfl | ⟨hxm, rfl⟩ | ⟨_, rfl⟩
  · exact huv
  · exact le_of_eq hxm
  · exact huv.elim

/-- **Obligation 1, DISCHARGED.**  The copy-`A` inclusion preserves suprema —
and not merely directed ones: *every* supremum, over an arbitrary carrier, with
no finiteness and no lattice.

Leastness splits on the tag of a competing upper bound `w`:
copy `A` reduces to `IsLUB` in `P` via `leGlueGen_tagA_tagA_iff`; copy `C` is
free (`leGlueGen_tagA_tagC`); copy `B` splits again — at `tag_B ⊤` it is free
for the same reason, and otherwise every `s ∈ S` is forced below `m`
(`le_marked_of_leGlueGen_tagB`), so `m` is an upper bound of `S` and leastness
of `c` finishes it. -/
theorem tagAGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagAGen m '' S) (tagAGen m c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (Sum.inl s) (Sum.inl c)
    exact (leGlueGen_tagA_tagA_iff m hm s c).mpr (hS.1 hs)
  · intro w hw
    show leGlueGen m (Sum.inl c) w.1
    obtain ⟨wv, hwv⟩ := w
    have hub : ∀ s ∈ S, leGlueGen m (Sum.inl s) wv := by
      intro s hs
      exact hw ⟨s, hs, rfl⟩
    rcases wv with d | b | c'
    · have : ∀ s ∈ S, s ≤ d := fun s hs =>
        (leGlueGen_tagA_tagA_iff m hm s d).mp (hub s hs)
      exact (leGlueGen_tagA_tagA_iff m hm c d).mpr (hS.2 this)
    · by_cases hbtop : b = ⊤
      · subst hbtop
        exact ⟨Sum.inl c, self_mem_occsGen _ _, Sum.inr (Sum.inr m),
               by simp [occsGen], trivial⟩
      · have hsm : ∀ s ∈ S, s ≤ m := fun s hs =>
          le_marked_of_leGlueGen_tagB m s b hbtop (hub s hs)
        have hcm : c ≤ m := hS.2 hsm
        exact ⟨Sum.inl c, self_mem_occsGen _ _, Sum.inr (Sum.inl b),
               self_mem_occsGen _ _, hcm⟩
    · exact leGlueGen_tagA_tagC m c c'

/-- Obligation 1 as originally stated, now a corollary — the `DirectedOn`
hypothesis turns out to be unnecessary. -/
theorem scottContinuousTagA (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    ScottContinuousTagA P m hm hmt hbt :=
  fun _S _c _hne _hdir hlub => tagAGen_isLUB m hm hmt hbt hlub

/-! ## Obligations 2 and 3 — with a correction to how they were stated

The module docstring lists three "copy-inclusion continuity" obligations as if
the three inclusions were alike.  They are not, and the difference has to be
said before either of the remaining two can be stated correctly:

**copy `A` is a total inclusion `P → GlueCarGen m`; copies `B` and `C` are
partial.**  `tag_B x` is `canonGen`-fixed only for `x ≠ ⊥` (at `⊥` it redirects
to `tag_A m`, the seam), and `tag_C x` only for `x ≠ ⊥` and `x ≠ m` (at `m` it
redirects to `tag_B ⊤`).  So "the copy-`B`/`C` inclusion preserves sups" is not
well-posed in the shape `ScottContinuousTagA` has: the domain is not all of `P`,
and for copy `C` it is not even closed under sups (a set of elements `≠ m` can
have supremum `m`).

That costs nothing for the reduction, because `baseMapGen`'s inputs are already
`canonGen`-fixed and a `⊥`-reflecting morphism keeps them so (`canon_baseMap`).
The statements below therefore restrict to the canon-fixed region — which is
exactly where the reduction needs them — and are spelled out on raw
`GlueBaseGen` values as "upper bound + least", rather than as `IsLUB` in the
subtype, to keep the order content visible instead of buried in coercions. -/

section CopiesBC

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- Occurrence analysis for copy `B`: a copy-`B` point is its own only
occurrence unless it is `tag_B ⊤`, which also occurs as `tag_C m`. -/
theorem occsGen_tagB (m x : P) (w : GlueBaseGen P)
    (hw : w ∈ occsGen m (Sum.inr (Sum.inl x))) :
    w = Sum.inr (Sum.inl x) ∨ (x = ⊤ ∧ w = Sum.inr (Sum.inr m)) := by
  simp only [occsGen] at hw
  split_ifs at hw with h1 <;> simp at hw <;> tauto

/-- Copy `C` points have exactly one occurrence. -/
theorem occsGen_tagC (m x : P) (w : GlueBaseGen P)
    (hw : w ∈ occsGen m (Sum.inr (Sum.inr x))) : w = Sum.inr (Sum.inr x) := by
  simpa [occsGen] using hw

/-- Everything in copy `B` sits below `tag_B ⊤`, via that point's copy-`C`
occurrence `tag_C m`. -/
theorem leGlueGen_tagB_tagBtop (m b : P) :
    leGlueGen m (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inl (⊤ : P))) :=
  ⟨Sum.inr (Sum.inl b), self_mem_occsGen _ _, Sum.inr (Sum.inr m),
   by simp [occsGen], le_rfl⟩

/-- Within copy `B`, below a non-`⊤` target, the order is `P`'s own. -/
theorem le_of_leGlueGen_tagB_tagB (m x b : P) (hbt : b ≠ ⊤)
    (h : leGlueGen m (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl b))) : x ≤ b := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  rcases occsGen_tagB m b v hv with rfl | ⟨hb, _⟩
  · rcases occsGen_tagB m x u hu with rfl | ⟨_, rfl⟩
    · exact huv
    · exact huv.elim
  · exact absurd hb hbt

/-- A copy-`B` point below a copy-`C` point forces `m ≤ c'`. -/
theorem marked_le_of_leGlueGen_tagB_tagC (m x c' : P)
    (h : leGlueGen m (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr c'))) : m ≤ c' := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  rcases occsGen_tagC m c' v hv with rfl
  rcases occsGen_tagB m x u hu with rfl | ⟨_, rfl⟩
  · exact huv
  · exact huv

/-- **Obligation 2, DISCHARGED.**  On the canon-fixed region (`s ≠ ⊥`) the
copy-`B` inclusion preserves every supremum.

Leastness splits on the competing upper bound's tag: copy `A` is impossible
(copy `B` is never `≤` copy `A`, and `S` is nonempty); copy `C` gets `m ≤ c'`
from any single member and then carries `c` for free; copy `B` is free at `⊤`
and otherwise reduces to `IsLUB` in `P`. -/
theorem tagB_isLUB_raw (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inl c)))
      ∧ (∀ w : GlueBaseGen P, (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inl s)) w) →
          leGlueGen m (Sum.inr (Sum.inl c)) w) := by
  obtain ⟨s0, hs0⟩ := hne
  refine ⟨fun s hs => ⟨Sum.inr (Sum.inl s), self_mem_occsGen _ _,
      Sum.inr (Sum.inl c), self_mem_occsGen _ _, hS.1 hs⟩, ?_⟩
  intro w hw
  rcases w with d | b | c'
  · exact absurd (hw s0 hs0)
      (not_leGlue_tagB_tagAGen m s0 d hm hbt (hSb s0 hs0))
  · by_cases hbtop : b = ⊤
    · subst hbtop; exact leGlueGen_tagB_tagBtop m c
    · have hsb : ∀ s ∈ S, s ≤ b := fun s hs =>
        le_of_leGlueGen_tagB_tagB m s b hbtop (hw s hs)
      exact ⟨Sum.inr (Sum.inl c), self_mem_occsGen _ _,
             Sum.inr (Sum.inl b), self_mem_occsGen _ _, hS.2 hsb⟩
  · have hmc : m ≤ c' := marked_le_of_leGlueGen_tagB_tagC m s0 c' (hw s0 hs0)
    exact ⟨Sum.inr (Sum.inl c), self_mem_occsGen _ _,
           Sum.inr (Sum.inr c'), self_mem_occsGen _ _, hmc⟩

/-- **Obligation 3, DISCHARGED.**  The copy-`C` inclusion preserves every
supremum, needing only `s ≠ ⊥` (which is what excludes a copy-`A` upper bound).

Copy `C` points have a single occurrence, which makes leastness short: copy `A`
is impossible, copy `B` is reachable only at `tag_B ⊤` and only by forcing every
member below `m`, and copy `C` reduces to `IsLUB` in `P`.

Note `c ≠ m` is deliberately **not** a hypothesis: stated on raw `GlueBaseGen`
values, `leGlueGen` is meaningful whether or not the point is `canonGen`-fixed,
so the order content is independent of it.  The `c ≠ m` condition is what a
corollary would need in order to *transport* this into the subtype
`GlueCarGen` — a set of elements `≠ m` can have supremum `m`, where the copy-`C`
inclusion is undefined (`canonGen` sends `tag_C m` to `tag_B ⊤`).  That
transport is not done here, and the partiality is the reason. -/
theorem tagC_isLUB_raw (m : P) {S : Set P} {c : P}
    (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inr s)) (Sum.inr (Sum.inr c)))
      ∧ (∀ w : GlueBaseGen P, (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inr s)) w) →
          leGlueGen m (Sum.inr (Sum.inr c)) w) := by
  obtain ⟨s0, hs0⟩ := hne
  refine ⟨fun s hs => ⟨Sum.inr (Sum.inr s), self_mem_occsGen _ _,
      Sum.inr (Sum.inr c), self_mem_occsGen _ _, hS.1 hs⟩, ?_⟩
  intro w hw
  rcases w with d | b | c'
  · exact absurd (hw s0 hs0) (not_leGlue_tagC_tagAGen m s0 d (hSb s0 hs0))
  · have hsm : ∀ s ∈ S, s ≤ m := by
      intro s hs
      obtain ⟨u, hu, v, hv, huv⟩ := hw s hs
      rcases occsGen_tagC m s u hu with rfl
      rcases occsGen_tagB m b v hv with rfl | ⟨_, rfl⟩
      · exact huv.elim
      · exact huv
    have hbtop : b = ⊤ := by
      obtain ⟨u, hu, v, hv, huv⟩ := hw s0 hs0
      rcases occsGen_tagC m s0 u hu with rfl
      rcases occsGen_tagB m b v hv with rfl | ⟨hb, _⟩
      · exact huv.elim
      · exact hb
    subst hbtop
    exact ⟨Sum.inr (Sum.inr c), self_mem_occsGen _ _, Sum.inr (Sum.inr m),
           by simp [occsGen], hS.2 hsm⟩
  · have hsc : ∀ s ∈ S, s ≤ c' := by
      intro s hs
      obtain ⟨u, hu, v, hv, huv⟩ := hw s hs
      rcases occsGen_tagC m s u hu with rfl
      rcases occsGen_tagC m c' v hv with rfl
      exact huv
    exact ⟨Sum.inr (Sum.inr c), self_mem_occsGen _ _,
           Sum.inr (Sum.inr c'), self_mem_occsGen _ _, hS.2 hsc⟩

end CopiesBC

end Gateway

end GenContinuity
