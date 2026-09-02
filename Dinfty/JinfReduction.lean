import Dinfty.TwoPointHypothesis

open GluingTowerLibrary SierpinskiApplication

/-!
# Attacking `TwoPointFixed`: reduce to the join-irreducible poset `J∞`

The two-point hypothesis is about two elements of `DInfty`, but both are
join-irreducible (`joinIrred_midInf`, `joinIrred_toD_zero_top`) and every
automorphism preserves join-irreducibility (`joinIrred_orderIso`).  So the
hypothesis lives entirely inside

    Jinf := {z : DInfty // JoinIrred DInfty z}

which is a *much* smaller object than `DInfty`, and — by `joinIrred_toD_iff` —
is exactly the increasing union of the finite posets `J(D k)`:

    Jinf = ⋃ₖ toD k '' J(D k)          (`jinf_exists_stage`, `mem_jinf_of_stage`)

This is the object the handoff's §7 calls the best current lead, because
`J(D (k+1))` has product structure that `D (k+1)` does not: the copy-`A` family
is `J(D k) × (D k)ᵒᵖ`, and `card_joinIrred_D_succ` counts the whole thing as
`3·|J(D k)|·|D k| − 2`.  Nothing of that structure is visible from `DInfty`; all
of it is visible from `J∞`.

**What this module does:** transports the problem there, exactly.

    twoPointFixed_iff_jinf :
      TwoPointFixed ↔ ∀ θ, Jmap θ midJ = midJ ∧ Jmap θ topJ = topJ

**What it does not do:** prove or refute it.  The two points are now `midJ` and
`topJ` in a countable increasing union of finite posets with known product
structure, and the question is whether `Aut(J∞)` moves either.  That is the
same question, posed over an object where the tower's own recursion is present
rather than erased.

## Why this is the right place to stand, concretely

Copy `A` is downward closed in `GlueCar` — `tagA_of_hdown_at_mid`
(`GlueAAGenReflectM`, general `P`, `[propext, Quot.sound]`) says exactly that
anything `≤` a `tag_A` point is itself `tag_A`.  Since `iotaD k x =
glueA (markedPt k) (constHom x)` is copy `A`, down-sets of stage points never
leave copy `A`, and one level up they are `Mon(D k, ↓x)`:

* `↓ topJ` restricted to stage `k+1` is `↓(⊤ : EndP (D k))` — **all** of
  `EndP (D k)`, since `⊤ : EndP L` is `constHom ⊤`;
* `↓ midJ` restricted to stage `k+1` is `↓(constHom (dMid k))` — the monotone
  maps `D k → [⊥, dMid k]`.

So the two points differ, at every finite stage, by *which interval of `D k` the
endomorphisms are allowed to land in*: all of it versus `[⊥, dMid k]`.  At stage
1 that is `EndP (Fin 3)` (10 elements) versus `Mon(Fin 3, {⊥, dMid 0})` — a
**4-chain**.  A separating order-theoretic property, if one exists, should be
visible in that contrast.
-/

open scoped Classical

namespace JinfReduction

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis

/-! ## The join-irreducible poset -/

/-- `J∞` — the join-irreducibles of the colimit, with the induced order. -/
def Jinf : Type := {z : DInfty // JoinIrred DInfty z}

noncomputable instance : PartialOrder Jinf := Subtype.partialOrder _

@[simp] theorem Jinf_le_iff (a b : Jinf) : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-- Every automorphism of `DInfty` restricts to one of `J∞`. -/
noncomputable def Jmap (θ : DInfty ≃o DInfty) : Jinf ≃o Jinf where
  toFun z := ⟨θ z.1, GluingTowerLibrary.joinIrred_orderIso θ z.2⟩
  invFun z := ⟨θ.symm z.1, GluingTowerLibrary.joinIrred_orderIso θ.symm z.2⟩
  left_inv z := Subtype.ext (θ.symm_apply_apply z.1)
  right_inv z := Subtype.ext (θ.apply_symm_apply z.1)
  map_rel_iff' := θ.map_rel_iff

@[simp] theorem Jmap_val (θ : DInfty ≃o DInfty) (z : Jinf) : (Jmap θ z).1 = θ z.1 := rfl

/-! ## `J∞` is the increasing union of the finite `J(D k)` -/

/-- Every join-irreducible of the colimit is a join-irreducible of some stage —
`joinIrred_toD_iff` in the direction that matters. -/
theorem jinf_exists_stage : ∀ z : DInfty, JoinIrred DInfty z →
    ∃ (k : ℕ) (x : D k), JoinIrred (D k) x ∧ z = toD k x := by
  intro z
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    intro hz
    exact ⟨k, x, (joinIrred_toD_iff k x).mp hz, rfl⟩

/-- …and conversely each stage's join-irreducibles land in `J∞`. -/
theorem mem_jinf_of_stage (k : ℕ) (x : D k) (hx : JoinIrred (D k) x) :
    JoinIrred DInfty (toD k x) :=
  (joinIrred_toD_iff k x).mpr hx

/-- Each stage contributes only finitely much. -/
theorem stage_jinf_finite (k : ℕ) :
    (Set.range (fun x : {x : D k // JoinIrred (D k) x} => toD k x.1)).Finite :=
  Set.finite_range _

/-! ## The two points, and the transported hypothesis -/

noncomputable def midJ : Jinf := ⟨midInf, joinIrred_midInf⟩

noncomputable def topJ : Jinf := ⟨toD 0 (⊤ : D 0), joinIrred_toD_zero_top⟩

theorem midJ_lt_topJ : midJ < topJ := midInf_lt_top_zero

/-- **The two-point hypothesis, transported to `J∞`.**  Nothing is lost: the
statement over `DInfty` and the statement over its join-irreducibles are the
same statement. -/
theorem twoPointFixed_iff_jinf :
    TwoPointFixed ↔ ∀ θ : DInfty ≃o DInfty, Jmap θ midJ = midJ ∧ Jmap θ topJ = topJ := by
  constructor
  · intro h θ
    exact ⟨Subtype.ext (h θ).1, Subtype.ext (h θ).2⟩
  · intro h θ
    exact ⟨congrArg Subtype.val (h θ).1, congrArg Subtype.val (h θ).2⟩

/-- And therefore, chaining §11–§15: refuting rigidity of `J∞` at these two
points refutes pillar B. -/
theorem not_stageFixed_of_jinf_moves
    (h : ¬ ∀ θ : DInfty ≃o DInfty, Jmap θ midJ = midJ ∧ Jmap θ topJ = topJ) :
    ¬ StageFixed :=
  not_stageFixed_of_not_twoPointFixed (fun hc => h (twoPointFixed_iff_jinf.mp hc))

end JinfReduction
