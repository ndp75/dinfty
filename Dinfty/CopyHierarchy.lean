import Dinfty.PhiTri

open GluingTowerLibrary SierpinskiApplication

/-!
# The copy-hierarchy: the glued order's edge structure, named

`Results/03 Phi Gluing Functor.md` describes the **key device** of the vault's
local-continuity proof for `Φ_tri_v2`:

> a **copy-hierarchy lemma** — generic nodes obey a strict one-way bridging
> order `a→{a,b,c}`, `b→{b,c}`, `c→{c}` (sink), bounding any ascending chain to
> ≤2 copy-switches.

It has never been a Lean lemma.  **It does not need proving from scratch: it is
the shape of `rawRuleGen`.**  Reading that definition off:

| from → to | `rawRuleGen` clause |
|---|---|
| `a → a` | `x ≤ y` |
| `a → b` | `x ≤ m` |
| `a → c` | `True` |
| `b → b` | `x ≤ y` |
| `b → c` | `m ≤ y` |
| `b → a` | `False` |
| `c → c` | `x ≤ y` |
| `c → a`, `c → b` | `False` |

So the reachable-copy sets are exactly `a→{a,b,c}`, `b→{b,c}`, `c→{c}` — the
vault's hierarchy, verbatim, and the "sink" is copy `c`'s row having only itself.

`copyIdx_mono` below states it: along `≤`, the copy index never decreases.

## Where the "generic" caveat comes from, and why it is not a blemish

The hierarchy is stated for *generic* nodes, and the exception is exactly the
seam.  `tag_B ⊤` and `tag_C m` are the **same glued point**
(`occsGen (tag_B ⊤) ∋ tag_C m`), so a copy-`C` point can sit below a copy-`B`
one — but only there, and only because the two tags name one point.  The copy
index is therefore well-defined only away from that identification, which is what
"generic" means.  `copyIdx_mono` takes exactly that hypothesis and nothing more.

## Why this is the structure two separate results turn on

* The vault's local-continuity proof uses it to bound ascending chains to ≤2
  copy-switches, giving its dichotomy (eventually constant at a skeleton point,
  or eventually confined to one copy).
* `CopyBFreedom.glueTwist` (2026-08-28) turns on the same fact from the other
  side: copy `A` reaches copy `B` *only* through `a ≤ m`, and copy `B` reaches
  copy `C` *only* through `m ≤ c'` — both conditions on `m` alone, mentioning no
  copy-`B` value.  That is why the copy-`B` component is unconstrained.

One digraph, two consequences: it bounds chains (continuity) and it decouples
copy `B`'s interior (non-rigidity).
-/

open scoped Classical

universe u

namespace CopyHierarchy

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- Which copy a tagged point lives in: `a = 0`, `b = 1`, `c = 2`. -/
def copyIdx : GlueBaseGen P → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

@[simp] theorem copyIdx_inl (x : P) : copyIdx (Sum.inl x) = 0 := rfl
@[simp] theorem copyIdx_inr_inl (x : P) : copyIdx (Sum.inr (Sum.inl x)) = 1 := rfl
@[simp] theorem copyIdx_inr_inr (x : P) : copyIdx (Sum.inr (Sum.inr x)) = 2 := rfl

/-- **The copy-hierarchy lemma.**  Along the glued order the copy index never
decreases: `a → {a,b,c}`, `b → {b,c}`, `c → {c}`.

`hgen` is the "generic node" hypothesis, and it is exactly the seam exclusion:
the target must not be `tag_B ⊤`, which is the *same glued point* as `tag_C m`
and is therefore the one place a copy-`C` point legitimately sits below a
copy-`B` tag. -/
theorem copyIdx_mono (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (hx : canonGen m x = x)
    (hgen : ∀ b : P, y = Sum.inr (Sum.inl b) → b ≠ ⊤)
    (h : leGlueGen m x y) : copyIdx x ≤ copyIdx y := by
  cases x with
  | inl a =>
    -- copy `a` reaches everything: `0 ≤ _`.
    cases y with
    | inl _ => exact le_rfl
    | inr y => cases y with
      | inl _ => exact by simp only [copyIdx]; decide
      | inr _ => exact by simp only [copyIdx]; decide
  | inr x =>
    cases x with
    | inl b =>
      have hbne : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagB_tagAGen m b a' hm hbt hbne)
      | inr y => cases y with
        | inl _ => exact le_rfl
        | inr _ => exact by simp only [copyIdx]; decide
    | inr c =>
      have hcne : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hx
      cases y with
      | inl a' => exact absurd h (not_leGlue_tagC_tagAGen m c a' hcne)
      | inr y => cases y with
        | inl b' => exact absurd h (not_leGlue_tagC_tagBGen m c b' (hgen b' rfl))
        | inr _ => exact le_rfl

/-- **Copy `c` is a sink.**  Nothing generic sits above a copy-`C` point except
copy-`C` points — the bottom row of the table. -/
theorem tagC_sink (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {c : P} {y : GlueBaseGen P}
    (hx : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c))
    (hgen : ∀ b : P, y = Sum.inr (Sum.inl b) → b ≠ ⊤)
    (h : leGlueGen m (Sum.inr (Sum.inr c)) y) : ∃ c' : P, y = Sum.inr (Sum.inr c') := by
  have hmono := copyIdx_mono m hm hbt hx hgen h
  cases y with
  | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
  | inr y => cases y with
    | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
    | inr c' => exact ⟨c', rfl⟩

/-- **Copy `a` is a source.**  Nothing sits below a copy-`A` point except
copy-`A` points — the dual reading, and the reason `tag_A` is the total
inclusion. -/
theorem tagA_source (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {a : P} {x : GlueBaseGen P}
    (hx : canonGen m x = x)
    (h : leGlueGen m x (Sum.inl a)) : ∃ a' : P, x = Sum.inl a' := by
  have hmono := copyIdx_mono m hm hbt hx (by rintro b ⟨⟩) h
  cases x with
  | inl a' => exact ⟨a', rfl⟩
  | inr x => cases x with
    | inl _ => exact absurd hmono (by simp only [copyIdx]; decide)
    | inr _ => exact absurd hmono (by simp only [copyIdx]; decide)

end CopyHierarchy
