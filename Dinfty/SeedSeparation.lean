import Dinfty.Definability

open GluingTowerLibrary SierpinskiApplication

/-!
# The search, written into Lean

`_archive/check_midInf_pinning_search.py` found that inside the real `D_1` the
seam `midInf` is the **unique** element whose seed — the poset of
join-irreducibles below it — has its isomorphism type, and likewise for
`toD 0 ⊤`; of the 222 chains `⊥ < a < b` in `D_1`, exactly one passes.

That is a finite computation, and it cannot be replayed in the kernel: no `D`
level enumerates (`DecidabilityBoundary`).  What *can* be written down is the
general statement the computation instantiates, and the theorem that turns it
into pillar B's base case.  This module does that, so the search result has a
home with an exact scope rather than living in a script and a note.

## The transportable object

`JBelow z` is the poset of join-irreducibles of `DInfty` below `z` — the seed's
colimit form.  Any automorphism carries it isomorphically (`JBelow.map`), since
join-irreducibility is order-theoretic (`joinIrred_orderIso`, library) and `θ`
reflects `≤`.

## The hypothesis, and what it buys

```lean
def SeedSeparatesAt (z : DInfty) (N : ℕ) : Prop :=
  ∀ y : D N, Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z
```

— "inside stage `N`, nothing but `z` has `z`'s seed".  Then

```lean
fixed_of_seedSeparates : (∀ N, SeedSeparatesAt z N) → ∀ θ, θ z = z
```

because `θ z` lies in *some* stage (`exists_stage`), and its seed is isomorphic
to `z`'s.  Applied to the two points, that is `TwoPointFixed`
(`twoPointFixed_of_seedSeparates`), hence pillar B.

**So the search verified exactly `SeedSeparatesAt midInf 1` and
`SeedSeparatesAt topJ 1`.**  What is missing is every `N ≥ 2`, and `D 2` is not
enumerable (`|EndP(D 1)| ≈ 1.2 × 10¹⁶`).  The scope of the computation is now
stated rather than described.

## What is proved outright here

The `⊥` case of the level-`0` check needs no computation: `JBelow ⊥` is empty
while `JBelow z` is inhabited for join-irreducible `z`, so no isomorphism exists
and `⊥` is excluded as an image (`bot_ne_of_seed_iso`).  That is the one part of
the search that Lean can replay directly; the mid-versus-top separation is the
part that carries the content, and it is not free.
-/

open scoped Classical

namespace SeedSeparation

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

/-! ## The seed, in colimit form -/

/-- The join-irreducibles of `DInfty` below `z`, as a poset. -/
def JBelow (z : DInfty) : Type := {w : DInfty // JoinIrred DInfty w ∧ w ≤ z}

noncomputable instance (z : DInfty) : PartialOrder (JBelow z) := Subtype.partialOrder _

/-- Every automorphism carries seeds isomorphically. -/
noncomputable def JBelow.map (θ : DInfty ≃o DInfty) (z : DInfty) :
    JBelow z ≃o JBelow (θ z) where
  toFun w := ⟨θ w.1, GluingTowerLibrary.joinIrred_orderIso θ w.2.1, θ.monotone w.2.2⟩
  invFun w := ⟨θ.symm w.1, GluingTowerLibrary.joinIrred_orderIso θ.symm w.2.1, by
    have h := θ.symm.monotone w.2.2
    rwa [θ.symm_apply_apply] at h⟩
  left_inv w := Subtype.ext (θ.symm_apply_apply w.1)
  right_inv w := Subtype.ext (θ.apply_symm_apply w.1)
  map_rel_iff' := θ.map_rel_iff

/-! ## Every element lies in a stage -/

theorem exists_stage (w : DInfty) : ∃ (N : ℕ) (y : D N), w = toD N y := by
  induction w using Quotient.inductionOn with
  | _ p => obtain ⟨N, y⟩ := p; exact ⟨N, y, rfl⟩

/-! ## The hypothesis the search instantiates -/

/-- **"Inside stage `N`, nothing but `z` has `z`'s seed."**  The Python search
verified this at `N = 1` for both `midInf` and `toD 0 ⊤`. -/
def SeedSeparatesAt (z : DInfty) (N : ℕ) : Prop :=
  ∀ y : D N, Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z

/-- **The theorem the search feeds.**  Seed-separation at *every* stage pins the
point. -/
theorem fixed_of_seedSeparates {z : DInfty} (h : ∀ N, SeedSeparatesAt z N)
    (θ : DInfty ≃o DInfty) : θ z = z := by
  obtain ⟨N, y, hy⟩ := exists_stage (θ z)
  have h0 : Nonempty (JBelow z ≃o JBelow (θ z)) := ⟨JBelow.map θ z⟩
  rw [hy] at h0
  rw [hy]
  exact h N y ⟨h0.some.symm⟩

/-- …and applied to the two points, that is `TwoPointFixed`, hence pillar B. -/
theorem twoPointFixed_of_seedSeparates
    (hm : ∀ N, SeedSeparatesAt midInf N)
    (ht : ∀ N, SeedSeparatesAt (toD 0 (⊤ : D 0)) N) : TwoPointFixed :=
  fun θ => ⟨fixed_of_seedSeparates hm θ, fixed_of_seedSeparates ht θ⟩

/-! ## The part of the search Lean can replay: the `⊥` exclusion -/

theorem jBelow_bot_isEmpty : IsEmpty (JBelow (⊥ : DInfty)) := by
  refine ⟨?_⟩
  rintro ⟨w, hji, hle⟩
  exact hji.1 (le_bot_iff.mp hle)

theorem jBelow_nonempty_of_joinIrred {z : DInfty} (hz : JoinIrred DInfty z) :
    Nonempty (JBelow z) := ⟨⟨z, hz, le_rfl⟩⟩

/-- **`⊥` is excluded as an image, with no computation.**  Its seed is empty and
a join-irreducible point's is not. -/
theorem bot_ne_of_seed_iso {z : DInfty} (hz : JoinIrred DInfty z)
    (_e : JBelow (⊥ : DInfty) ≃o JBelow z) : False :=
  (jBelow_bot_isEmpty).elim (_e.symm (jBelow_nonempty_of_joinIrred hz).some)

/-- Instance for the seam. -/
theorem bot_ne_midInf_seed (e : JBelow (⊥ : DInfty) ≃o JBelow midInf) : False :=
  bot_ne_of_seed_iso joinIrred_midInf e

/-- Instance for the stage-`0` top. -/
theorem bot_ne_topJ_seed (e : JBelow (⊥ : DInfty) ≃o JBelow (toD 0 (⊤ : D 0))) : False :=
  bot_ne_of_seed_iso joinIrred_toD_zero_top e

end SeedSeparation
