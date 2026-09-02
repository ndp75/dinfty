import Dinfty.GenContinuity

open GluingTowerLibrary SierpinskiApplication

/-!
# Gap 1 of `GenContinuity`: transport of the copy-`B`/`C` obligations into
`GlueCarGen`

`GenContinuity` discharges the three copy-inclusion obligations, but states the
copy-`B` and copy-`C` ones on **raw** `GlueBaseGen` values ("upper bound +
least") rather than as `IsLUB` in the subtype `GlueCarGen m`, and records the
reason as a structural gap:

> The copy-`B`/`C` results are raw-value statements.  Turning them into `IsLUB`
> in `GlueCarGen` needs the sup to stay in the canon-fixed region, which for
> copy `C` can fail (a set of elements `≠ m` can have supremum `m`).

**The premise is right and the conclusion is wrong.**  The sup genuinely can
leave the canon-fixed region — `S ⊆ {x | x ≠ ⊥ ∧ x ≠ m}` really can have
`⨆ S = m` — but that does not obstruct the transport, because the copy-`C`
inclusion into the subtype is not the partial map `x ↦ ⟨tag_C x, _⟩`; it is the
**total** map `tagCGen`, which composes with `canonGen`.  At `c = m` the value
is `tag_B ⊤` (`tagCGen_marked_eq_skelG3Gen`), and `tag_B ⊤` *is* the least upper
bound of the image in `GlueCarGen`.  The sup does not fail to exist; it
migrates to the seam.

## What makes the transport go through

`canonGen` only ever **adds** occurrences (`occsGen_subset_canonGen`): the two
redirects `tag_B ⊥ ↦ tag_A m` and `tag_C m ↦ tag_B ⊤` land on points whose
`occsGen` list contains the redirected point itself.  So `leGlueGen` is
preserved when both sides are canonicalised (`leGlueGen_canonGen`), and the raw
statements push forward verbatim.

Note the direction.  `leGlueGen m (canonGen m x) y → leGlueGen m x y` is
**false** in general: `tag_A m ≤ tag_A ⊤` holds while `leGlueGen m (tag_B ⊥)
(tag_A ⊤)` fails, since `occsGen (tag_A ⊤) = [tag_A ⊤, tag_C ⊥]` and copy `B`
has no rule into copy `A`.  Only the forward direction is available, and it is
the one the transport needs.  (`leGlueGen` is a partial order on canon-fixed
points only; on raw points it is not, and this is that fact showing up.)

## Result

All three copy-inclusion obligations now hold as `IsLUB` statements in
`GlueCarGen`, for the total bundled inclusions:

* `tagAGen_isLUB`   (in `GenContinuity`, already in subtype form),
* `tagBGen_isLUB`   (here),
* `tagCGen_isLUB`   (here).

The hypotheses are exactly the canon-fixed domain of each inclusion — `s ≠ ⊥`
for copy `B`; `s ≠ ⊥` and `s ≠ m` for copy `C` — with **no condition on the
supremum `c`**, which is the content.

**This closes gap 1 only.**  Gap 2 (mixed variance, the `End` half of
`Φ ∘ End`) is untouched here, and ingredient 3 of Claim 3(b) remains open.
Cite this as "the copy-inclusion obligations transport to `GlueCarGen`", never
as "ingredient 3 is formalized".
-/

open scoped Classical

universe u v

namespace GenContinuity

section Transport

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

/-- **Canonicalisation only adds occurrences.**  Both `canonGen` redirects send
a point to one that lists the original among its occurrences: `tag_B ⊥ ↦ tag_A m`
and `occsGen (tag_A m) ∋ tag_B ⊥`; `tag_C m ↦ tag_B ⊤` and
`occsGen (tag_B ⊤) ∋ tag_C m`.  The third redirect `tag_C ⊥ ↦ tag_A ⊤` works
the same way, needing `m ≠ ⊤` so that `occsGen (tag_A ⊤)` takes its `⊤`-branch
rather than its `m`-branch. -/
theorem occsGen_subset_canonGen (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    (x : GlueBaseGen P) {w : GlueBaseGen P} (hw : w ∈ occsGen m x) :
    w ∈ occsGen m (canonGen m x) := by
  cases x with
  | inl a => simpa [canonGen] using hw
  | inr x =>
    cases x with
    | inl b =>
      by_cases hb : b = ⊥
      · subst hb
        have hwv : w = Sum.inr (Sum.inl (⊥ : P)) := by
          simp only [occsGen] at hw
          rw [if_neg hbt] at hw
          simpa using hw
        subst hwv
        show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inl (⊥ : P))))
        simp only [canonGen, if_pos rfl, occsGen]
        simp
      · show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inl b)))
        simp only [canonGen]
        rw [if_neg hb]
        exact hw
    | inr c =>
      have hwv : w = Sum.inr (Sum.inr c) := by simpa [occsGen] using hw
      subst hwv
      show _ ∈ occsGen m (canonGen m (Sum.inr (Sum.inr c)))
      simp only [canonGen]
      by_cases hc : c = ⊥
      · subst hc
        rw [if_pos rfl]
        simp [occsGen, Ne.symm hmt]
      · rw [if_neg hc]
        by_cases hcm : c = m
        · subst hcm
          rw [if_pos rfl]
          simp only [occsGen, if_pos rfl]
          simp
        · rw [if_neg hcm]
          simp [occsGen]

/-- **`leGlueGen` pushes forward along `canonGen`.**  Immediate from
`occsGen_subset_canonGen`: the witnessing occurrence pair survives untouched.
The converse is false (see the module docstring). -/
theorem leGlueGen_canonGen (m : P) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {x y : GlueBaseGen P} (h : leGlueGen m x y) :
    leGlueGen m (canonGen m x) (canonGen m y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  exact ⟨u, occsGen_subset_canonGen m hmt hbt x hu,
         v, occsGen_subset_canonGen m hmt hbt y hv, huv⟩

/-- Bundled copy-`B` point, via `canonGen` — total, like `tagCGen`. -/
noncomputable def tagBGen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) (b : P) :
    GlueCarGen (P := P) m :=
  ⟨canonGen m (Sum.inr (Sum.inl b)), canonGen_idem m hm hbt _⟩

theorem tagBGen_val_of_ne_bot (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) {b : P}
    (hb : b ≠ ⊥) : (tagBGen m hm hbt b).1 = Sum.inr (Sum.inl b) := by
  show canonGen m (Sum.inr (Sum.inl b)) = Sum.inr (Sum.inl b)
  simp only [canonGen]; rw [if_neg hb]

/-- **The seam, named.**  The copy-`C` inclusion at the marked point is the
copy-`B` top.  This is the value the copy-`C` supremum takes when it leaves the
canon-fixed region, and the reason gap 1 is not an obstruction. -/
theorem tagCGen_marked_eq_skelG3Gen (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤) :
    tagCGen m hm hbt m = skelG3Gen m hm hbt := by
  apply Subtype.ext
  show canonGen m (Sum.inr (Sum.inr m)) = canonGen m (Sum.inr (Sum.inl (⊤ : P)))
  simp only [canonGen]
  rw [if_neg hm]
  simp [Ne.symm hbt]

/-- **Obligation 2, in the subtype.**  On its canon-fixed domain (`s ≠ ⊥`) the
bundled copy-`B` inclusion preserves *every* supremum, as an `IsLUB` statement
in `GlueCarGen m`.

No hypothesis on `c` is needed: `c ≠ ⊥` is forced, since `S` is nonempty and
sits above `⊥`. -/
theorem tagBGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagBGen m hm hbt '' S) (tagBGen m hm hbt c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hraw_ub, hraw_least⟩ := tagB_isLUB_raw m hm hbt hS ⟨s0, hs0⟩ hSb
  have hcb : c ≠ ⊥ := fun h => hSb s0 hs0 (le_bot_iff.mp (h ▸ hS.1 hs0))
  have hcval : (tagBGen m hm hbt c).1 = Sum.inr (Sum.inl c) :=
    tagBGen_val_of_ne_bot m hm hbt hcb
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (tagBGen m hm hbt s).1 (tagBGen m hm hbt c).1
    rw [tagBGen_val_of_ne_bot m hm hbt (hSb s hs), hcval]
    exact hraw_ub s hs
  · intro w hw
    show leGlueGen m (tagBGen m hm hbt c).1 w.1
    rw [hcval]
    refine hraw_least w.1 (fun s hs => ?_)
    have hle : leGlueGen m (tagBGen m hm hbt s).1 w.1 := hw ⟨s, hs, rfl⟩
    rwa [show ((tagBGen m hm hbt s).1) = Sum.inr (Sum.inl s) from
      tagBGen_val_of_ne_bot m hm hbt (hSb s hs)] at hle

/-- **Obligation 3, in the subtype — gap 1 closed.**  On its canon-fixed domain
(`s ≠ ⊥`, `s ≠ m`) the bundled copy-`C` inclusion preserves *every* supremum,
as an `IsLUB` statement in `GlueCarGen m`.

**There is no hypothesis on `c`.**  The case the gap was stated about — `S` in
the canon-fixed region with `⨆ S = m`, where `tag_C c` is not a `GlueCarGen`
point — is covered: there `tagCGen m hm hbt c` is `tag_B ⊤`
(`tagCGen_marked_eq_skelG3Gen`), and the theorem says that is the least upper
bound of the image.  The partiality is real; it just is not an obstruction,
because `canonGen` absorbs it.

Both directions go through `leGlueGen_canonGen`: the upper-bound half
canonicalises the raw inequality on the right, where `c` may move; the
leastness half canonicalises on the left, the right-hand side being fixed
already because `w` lives in the subtype. -/
theorem tagCGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty)
    (hSb : ∀ s ∈ S, s ≠ ⊥) (hSm : ∀ s ∈ S, s ≠ m) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagCGen m hm hbt '' S) (tagCGen m hm hbt c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hraw_ub, hraw_least⟩ := tagC_isLUB_raw m hS ⟨s0, hs0⟩ hSb
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (tagCGen m hm hbt s).1 (tagCGen m hm hbt c).1
    exact leGlueGen_canonGen m hmt hbt (hraw_ub s hs)
  · intro w hw
    show leGlueGen m (tagCGen m hm hbt c).1 w.1
    have hraw : leGlueGen m (Sum.inr (Sum.inr c)) w.1 := by
      refine hraw_least w.1 (fun s hs => ?_)
      have hle : leGlueGen m (tagCGen m hm hbt s).1 w.1 := hw ⟨s, hs, rfl⟩
      rwa [show ((tagCGen m hm hbt s).1) = Sum.inr (Sum.inr s) from
        tagCGen_val_of_generic m hm hbt (hSb s hs) (hSm s hs)] at hle
    have hcan := leGlueGen_canonGen m hmt hbt hraw
    rwa [w.2] at hcan

end Transport

end GenContinuity
