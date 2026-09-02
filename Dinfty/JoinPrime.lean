import Dinfty.CopyBCStructure
import Dinfty.CopyBExclusion

open GluingTowerLibrary SierpinskiApplication

/-!
# The §79 scoping note, made a theorem: both `liftGenM` thresholds are join-prime

§79 asked whether `glueAA k` has an embedding/projection partner, reduced it —
*informally* — to whether `liftGenM`'s two correction terms preserve binary
joins, and reduced that in turn to **join-primality** of their thresholds.  It
flagged `⊤` as free (unique coatom) and the marked point as open, warning that
the normalized `D 1` is not distributive, so join-*irreducible* does not give
join-*prime*.

**Both thresholds are join-prime.**  Nothing in that paragraph is informal any
more, and the marked-point half is an induction whose step needs no computation.

## The two ingredients

* `top_joinPrime` — in any lattice with a **unique coatom**, `⊤` is join-prime:
  two elements below the coatom cannot join above it.  Free at every `D k`, via
  `realUniqueAtomCoatom`.
* `dMid_joinPrime` — the marked point, by induction on `k`, in two halves:
  * `constHom_joinPrime` : `c` join-prime in `P` ⟹ `constHom c` join-prime in
    `EndP P`.  Evaluate at `⊥` and use monotonicity — a map dominating `c` at
    `⊥` dominates it everywhere, so the disjunction at one point globalises.
  * `dMid_succ_joinPrime` : `markedPt k` join-prime ⟹ `dMid (k+1)` join-prime.
    The seam is **below every copy-`B` and copy-`C` point** — that is
    `CopyBCStructure.dMid_le_glueB` / `dMid_le_glueC`, already on file — so the
    only live case is copy `A` against copy `A`, and there `glueA m (u ⊔ v)` is
    an upper bound of both, which reduces it to the hypothesis.  **No join
    formula for the glued lattice is needed**, only that copy `A` is an order
    embedding.

The base is `D 0 = Fin 3`, a chain, where every element is join-prime.

## What this settles, and what it does not

`ite_threshold_sup` converts join-primality of a threshold directly into
join-preservation of the step term it guards.  That is the whole of §79's
reduction, and it now says the thresholds raise **no** obstruction.

**It does not yet give `glueAA k` an ep-partner.**  `glueAA` is `liftGenM` only
on copies `B`/`C` and `iotaEndP` on copy `A`, and joins in `D (k+1)` move
between tags, so `glueAA (x ⊔ y) = glueAA x ⊔ glueAA y` still needs the
cross-tag analysis of `glueJoinRaw`.  Do not cite this module as settling that.
-/

open scoped Classical

universe u v

namespace JoinPrimality

open CopyBCStructure CopyBExclusion

/-! ## The notion -/

/-- **Join-prime**: below a join only by being below one of the parts.  Strictly
stronger than join-irreducible once distributivity fails — which is the
situation here, the normalized `D 1` not being distributive. -/
def JoinPrime {P : Type u} [SemilatticeSup P] (x : P) : Prop :=
  ∀ a b : P, x ≤ a ⊔ b → x ≤ a ∨ x ≤ b

theorem joinPrime_of_total {P : Type u} [SemilatticeSup P]
    (htot : ∀ a b : P, a ≤ b ∨ b ≤ a) (x : P) : JoinPrime x := by
  intro a b h
  rcases htot a b with hab | hab
  · exact Or.inr (by rwa [sup_eq_right.mpr hab] at h)
  · exact Or.inl (by rwa [sup_eq_left.mpr hab] at h)

/-! ## `⊤` is join-prime whenever the coatom is unique -/

theorem top_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P] :
    JoinPrime (⊤ : P) := by
  intro a b h
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have ha : a ≠ (⊤ : P) := fun hh => h1 (le_of_eq hh.symm)
  have hb : b ≠ (⊤ : P) := fun hh => h2 (le_of_eq hh.symm)
  have hsup : a ⊔ b ≤ coatomOf P := sup_le (coatomOf_le ha) (coatomOf_le hb)
  exact coatomOf_ne_top P (top_le_iff.mp (h.trans hsup))

/-! ## Constants -/

theorem constHom_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P]
    [DecidableEq P] {c : P} (hc : JoinPrime c) : JoinPrime (constHom c : EndP P) := by
  intro f g h
  have h0 : c ≤ f (⊥ : P) ⊔ g (⊥ : P) := by
    have h1 := OrderHom.le_def.mp h (⊥ : P)
    simpa only [constHom_apply, OrderHom.coe_sup, Pi.sup_apply] using h1
  rcases hc _ _ h0 with h1 | h1
  · refine Or.inl ?_
    rw [OrderHom.le_def]
    intro x
    exact le_trans h1 (f.monotone bot_le)
  · refine Or.inr ?_
    rw [OrderHom.le_def]
    intro x
    exact le_trans h1 (g.monotone bot_le)

theorem top_endP_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P]
    [DecidableEq P] (hP : JoinPrime (⊤ : P)) : JoinPrime (⊤ : EndP P) := by
  rw [endP_top_eq_constHom_top]
  exact constHom_joinPrime hP

/-! ## The inductive step at the tower -/

set_option maxHeartbeats 1000000 in
/-- **The step.**  Outside copy `A` the seam is below everything, so the only
case with content is copy `A` against copy `A`. -/
theorem dMid_succ_joinPrime (k : ℕ) (h : JoinPrime (markedPt k)) :
    JoinPrime (dMid (k + 1)) := by
  have hmk : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
  intro a b hab
  rcases dSuccCases k a with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, hxm, rfl⟩
  · rcases dSuccCases k b with ⟨v, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, hym, rfl⟩
    · have hub : (glueA (markedPt k) u ⊔ glueA (markedPt k) v : D (k + 1))
          ≤ glueA (markedPt k) (u ⊔ v) :=
        sup_le ((glueA_le_iff (markedPt k) hmk u (u ⊔ v)).mpr le_sup_left)
          ((glueA_le_iff (markedPt k) hmk v (u ⊔ v)).mpr le_sup_right)
      rw [dMid_eq_glueA k] at hab
      have hm : markedPt k ≤ u ⊔ v :=
        (glueA_le_iff (markedPt k) hmk (markedPt k) (u ⊔ v)).mp (hab.trans hub)
      rcases h u v hm with h1 | h1
      · exact Or.inl (by
          rw [dMid_eq_glueA k]
          exact (glueA_le_iff (markedPt k) hmk (markedPt k) u).mpr h1)
      · exact Or.inr (by
          rw [dMid_eq_glueA k]
          exact (glueA_le_iff (markedPt k) hmk (markedPt k) v).mpr h1)
    · exact Or.inr (dMid_le_glueB k hy)
    · exact Or.inr (dMid_le_glueC k hy hym)
  · exact Or.inl (dMid_le_glueB k hx)
  · exact Or.inl (dMid_le_glueC k hx hxm)

/-- The base: `D 0` is the three-chain `Fin 3`. -/
theorem dMid_zero_joinPrime : JoinPrime (dMid 0) := by
  refine joinPrime_of_total ?_ _
  intro a b
  have htot : ∀ x y : Fin 3, x ≤ y ∨ y ≤ x := fun x y => le_total x y
  exact htot a b

/-- **The marked point is join-prime at every level.** -/
theorem dMid_joinPrime : ∀ k : ℕ, JoinPrime (dMid k)
  | 0 => dMid_zero_joinPrime
  | k + 1 => dMid_succ_joinPrime k (constHom_joinPrime (dMid_joinPrime k))

/-- **`markedPt k` is join-prime** — `liftGenM`'s first threshold. -/
theorem markedPt_joinPrime (k : ℕ) : JoinPrime (markedPt k) :=
  constHom_joinPrime (dMid_joinPrime k)

/-- **`⊤` is join-prime in `D k`.** -/
theorem top_D_joinPrime (k : ℕ) : JoinPrime (⊤ : D k) := by
  letI := realUniqueAtomCoatom k
  exact top_joinPrime

/-- **`⊤` is join-prime in `EndP (D k)`** — `liftGenM`'s second threshold. -/
theorem top_endP_D_joinPrime (k : ℕ) : JoinPrime (⊤ : EndP (D k)) :=
  top_endP_joinPrime (top_D_joinPrime k)

/-! ## What join-primality buys -/

/-- **A step term preserves binary joins exactly where its threshold is
join-prime.**  This is the whole content of §79's reduction, and both of
`liftGenM`'s thresholds satisfy the hypothesis. -/
theorem ite_threshold_sup {P : Type u} {Q : Type v} [SemilatticeSup P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] [SemilatticeSup Q] [OrderBot Q]
    {t : P} (ht : JoinPrime t) (K : Q) (f g : P) :
    (if t ≤ f ⊔ g then K else ⊥) = (if t ≤ f then K else ⊥) ⊔ (if t ≤ g then K else ⊥) := by
  by_cases hf : t ≤ f
  · rw [if_pos hf, if_pos (le_trans hf le_sup_left)]
    by_cases hg : t ≤ g
    · rw [if_pos hg, sup_idem]
    · rw [if_neg hg, sup_bot_eq]
  · rw [if_neg hf]
    by_cases hg : t ≤ g
    · rw [if_pos hg, if_pos (le_trans hg le_sup_right), bot_sup_eq]
    · rw [if_neg hg, sup_bot_eq]
      refine if_neg (fun hcon => ?_)
      rcases ht f g hcon with h1 | h1
      · exact hf h1
      · exact hg h1

/-- **The tower instance of the first threshold.** -/
theorem markedPt_ite_sup {Q : Type v} [SemilatticeSup Q] [OrderBot Q]
    (k : ℕ) (K : Q) (f g : EndP (D k)) :
    (if markedPt k ≤ f ⊔ g then K else ⊥)
      = (if markedPt k ≤ f then K else ⊥) ⊔ (if markedPt k ≤ g then K else ⊥) :=
  ite_threshold_sup (markedPt_joinPrime k) K f g

/-- **The tower instance of the second threshold.** -/
theorem top_ite_sup {Q : Type v} [SemilatticeSup Q] [OrderBot Q]
    (k : ℕ) (K : Q) (f g : EndP (D k)) :
    (if (⊤ : EndP (D k)) ≤ f ⊔ g then K else ⊥)
      = (if (⊤ : EndP (D k)) ≤ f then K else ⊥) ⊔ (if (⊤ : EndP (D k)) ≤ g then K else ⊥) :=
  ite_threshold_sup (top_endP_D_joinPrime k) K f g

/-! ## Both ingredients of `glueAA` preserve binary joins

`glueAA k` is `iotaEndP k` on copy `A` and `liftGenM` on copies `B`/`C`.  Each
preserves binary joins: the first because copy `A` is a sublattice
(`glueA_sup`), the second because that plus the two threshold lemmas above is
all `liftGenM` is made of. -/

/-- Copy `A` is join-preserving, transported along `constHom`. -/
theorem iotaD_sup (k : ℕ) (a b : D k) : iotaD k (a ⊔ b) = iotaD k a ⊔ iotaD k b := by
  have hmk : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
  have hmtk : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
  have hbtk : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2
  show glueA (markedPt k) (constHom (a ⊔ b)) = _
  rw [← constHom_sup]
  exact (glueA_sup (markedPt k) hmk hmtk hbtk (constHom a) (constHom b)).symm

/-- **`iotaEndP` preserves binary joins** — pointwise, from `iotaD_sup`. -/
theorem iotaEndP_sup (k : ℕ) (f g : EndP (D k)) :
    iotaEndP k (f ⊔ g) = iotaEndP k f ⊔ iotaEndP k g := by
  ext w
  show iotaD k ((f ⊔ g) (pD k w)) = (iotaEndP k f ⊔ iotaEndP k g) w
  simp only [OrderHom.coe_sup, Pi.sup_apply]
  exact iotaD_sup k (f (pD k w)) (g (pD k w))

/-- `liftGenM`'s value, **declared** at `D (k+1)`.

This wrapper is not cosmetic.  `liftGenM`'s codomain is the raw
`EndP (GlueCar (constHom (dMid k)))`, whose lattice lives only inside
`liftGenM`'s own `letI` block, so an application `(liftGenM … f) w` has inferred
type `GlueCar (constHom (dMid k))` and `⊔` cannot be synthesised on it — and a
type ascription does not help, since ascription does not change `inferType`.
Declaring a `def` whose result type *is* `D (k+1)` does. -/
noncomputable def liftVal (k : ℕ) (f : EndP (D k)) (w : D (k + 1)) : D (k + 1) :=
  (liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f) w

set_option maxHeartbeats 2000000 in
/-- **`liftGenM` preserves binary joins**, stated pointwise.

Pointwise is not a weakening: `EndP`'s order and sup are pointwise, so this *is*
`liftGenM (f ⊔ g) = liftGenM f ⊔ liftGenM g`.

The three summands are handled separately: the `iotaEndP` term by `iotaD_sup`,
and the two step terms by `ite_threshold_sup` at thresholds that
`markedPt_joinPrime` and `top_endP_D_joinPrime` certify.  That last pair is
exactly §79's reduction, discharged. -/
theorem liftVal_sup (k : ℕ) (f g : EndP (D k)) (w : D (k + 1)) :
    liftVal k (f ⊔ g) w = liftVal k f w ⊔ liftVal k g w := by
  -- Every operand is spelled with a constant whose DECLARED type is `D (k+1)`
  -- (`iotaD`, `dMid (k+1)`) rather than the definitionally equal `iotaGenM` /
  -- `midM`, because `binop%` computes the type of a `⊔` from the operands'
  -- inferred types and a type ascription does not change `inferType`.
  have hval : ∀ h : EndP (D k), liftVal k h w
      = iotaD k (h (pD k w))
        ⊔ (if (constHom (dMid k) : EndP (D k)) ≤ h then dMid (k + 1) else (⊥ : D (k + 1)))
        ⊔ (if (⊤ : EndP (D k)) ≤ h then (⊤ : D (k + 1)) else (⊥ : D (k + 1))) := fun h =>
    liftGenM_apply (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial h w
  have hI : iotaD k ((f ⊔ g) (pD k w))
      = iotaD k (f (pD k w)) ⊔ iotaD k (g (pD k w)) := by
    simp only [OrderHom.coe_sup, Pi.sup_apply]
    exact iotaD_sup k (f (pD k w)) (g (pD k w))
  have hC : (if (constHom (dMid k) : EndP (D k)) ≤ f ⊔ g then dMid (k + 1)
        else (⊥ : D (k + 1)))
      = (if (constHom (dMid k) : EndP (D k)) ≤ f then dMid (k + 1) else (⊥ : D (k + 1)))
        ⊔ (if (constHom (dMid k) : EndP (D k)) ≤ g then dMid (k + 1)
            else (⊥ : D (k + 1))) :=
    ite_threshold_sup (markedPt_joinPrime k) _ f g
  have hT : (if (⊤ : EndP (D k)) ≤ f ⊔ g then (⊤ : D (k + 1)) else (⊥ : D (k + 1)))
      = (if (⊤ : EndP (D k)) ≤ f then (⊤ : D (k + 1)) else (⊥ : D (k + 1)))
        ⊔ (if (⊤ : EndP (D k)) ≤ g then (⊤ : D (k + 1)) else (⊥ : D (k + 1))) :=
    ite_threshold_sup (top_endP_D_joinPrime k) _ f g
  rw [hval (f ⊔ g), hval f, hval g, hI, hC, hT]
  ac_rfl

/-- **Both ingredients of `glueAA` preserve binary joins.**  What remains for an
ep-partner is *only* the cross-tag bookkeeping: `glueAA` is these two maps read
through the three tags, and joins in `D (k+1)` move between tags. -/
theorem glueAA_ingredients_sup (k : ℕ) (f g : EndP (D k)) :
    iotaEndP k (f ⊔ g) = iotaEndP k f ⊔ iotaEndP k g
      ∧ ∀ w : D (k + 1), liftVal k (f ⊔ g) w = liftVal k f w ⊔ liftVal k g w :=
  ⟨iotaEndP_sup k f g, liftVal_sup k f g⟩

end JoinPrimality
