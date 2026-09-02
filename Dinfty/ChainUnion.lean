import Mathlib.Order.Hom.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Increasing unions of posets, and isomorphisms between them

The remaining input to `TwoPointFixed` is that the seed of a stage-`N`
join-irreducible has a product shape.  Both sides of that identification are
**increasing unions of finite pieces**:

* `JBelow z` is the union of the level-wise seeds, along `iotaD`;
* `WeakProd P × S` is the union of the finite prefixes `∏_{j<k} P j × S`, along
  padding with `⊥`.

So the identification follows from levelwise isomorphisms, provided they commute
with the two chains.  That is this module: a `ChainUnion` presentation, and

```lean
chainUnionIso : (∀ k, Ak k ≃o Bk k) → (commuting) → A ≃o B
```

Nothing here mentions `DInfty` — it is a general fact about directed unions
along order-embeddings, which is what makes it worth isolating.

## The presentation

```lean
structure ChainUnion (A) (Ak : ℕ → Type) where
  step  : ∀ k, Ak k → Ak (k+1)
  incl  : ∀ k, Ak k → A
  incl_le_iff : ∀ k a b, incl k a ≤ incl k b ↔ a ≤ b     -- each level embeds
  incl_step   : ∀ k a, incl (k+1) (step k a) = incl k a  -- the chain is coherent
  incl_surj   : ∀ a, ∃ k b, incl k b = a                 -- and exhausts A
```

`incl_le_iff` gives injectivity of each `incl k` for free, and that is what makes
"two representatives of the same element agree once pushed to a common level"
(`eq_of_incl_eq`) — the only real lemma here.
-/

open scoped Classical

universe u v w

namespace ChainUnion

/-- An increasing-union presentation of `A` by the chain `Ak`. -/
structure Pres (A : Type u) [PartialOrder A] (Ak : ℕ → Type v)
    [∀ k, PartialOrder (Ak k)] where
  step : ∀ k, Ak k → Ak (k + 1)
  incl : ∀ k, Ak k → A
  incl_le_iff : ∀ (k : ℕ) (a b : Ak k), incl k a ≤ incl k b ↔ a ≤ b
  incl_step : ∀ (k : ℕ) (a : Ak k), incl (k + 1) (step k a) = incl k a
  incl_surj : ∀ a : A, ∃ (k : ℕ) (b : Ak k), incl k b = a

namespace Pres

variable {A : Type u} [PartialOrder A] {Ak : ℕ → Type v} [∀ k, PartialOrder (Ak k)]
variable (S : Pres A Ak)

theorem incl_injective (k : ℕ) : Function.Injective (S.incl k) := fun a b h =>
  le_antisymm ((S.incl_le_iff k a b).mp (le_of_eq h))
    ((S.incl_le_iff k b a).mp (le_of_eq h.symm))

/-- Push a level-`k` element up `d` steps. -/
def stepPow (k : ℕ) : ∀ (d : ℕ), Ak k → Ak (k + d)
  | 0, a => a
  | d + 1, a => S.step (k + d) (stepPow k d a)

theorem incl_stepPow (k d : ℕ) (a : Ak k) : S.incl (k + d) (S.stepPow k d a) = S.incl k a := by
  induction d with
  | zero => rfl
  | succ d ih =>
      show S.incl (k + d + 1) (S.step (k + d) (S.stepPow k d a)) = S.incl k a
      rw [S.incl_step (k + d) (S.stepPow k d a)]
      exact ih

/-- **Two representatives of the same element agree at a common level.** -/
theorem stepPow_eq_of_incl_eq {k d : ℕ} {a : Ak k} {b : Ak (k + d)}
    (h : S.incl k a = S.incl (k + d) b) : S.stepPow k d a = b :=
  S.incl_injective (k + d) ((S.incl_stepPow k d a).trans h)

end Pres


/-- **A presentation dualises.**  `OrderDual` is the same type, and
`incl_le_iff` just reads with its two sides swapped. -/
def Pres.dual {A : Type u} [PartialOrder A] {Ak : ℕ → Type v} [∀ k, PartialOrder (Ak k)]
    (S : Pres A Ak) : Pres Aᵒᵈ (fun k => (Ak k)ᵒᵈ) where
  step k := S.step k
  incl k := S.incl k
  incl_le_iff k a b := S.incl_le_iff k b a
  incl_step := S.incl_step
  incl_surj := S.incl_surj

/-- `(A × B)ᵒᵈ` and `Aᵒᵈ × Bᵒᵈ` are the same ordered set. -/
def prodDualIso (A : Type u) (B : Type u) [PartialOrder A] [PartialOrder B] :
    (A × B)ᵒᵈ ≃o (Aᵒᵈ × Bᵒᵈ) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- `Aᵒᵈᵒᵈ` is `A`. -/
def dualDualIso (A : Type u) [PartialOrder A] : Aᵒᵈᵒᵈ ≃o A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-! ## Transporting an isomorphism along two presentations -/

section Transport

variable {A : Type u} [PartialOrder A] {Ak : ℕ → Type w} [∀ k, PartialOrder (Ak k)]
variable {B : Type v} [PartialOrder B] {Bk : ℕ → Type w} [∀ k, PartialOrder (Bk k)]
variable (SA : Pres A Ak) (SB : Pres B Bk)
variable (e : ∀ k, Ak k ≃o Bk k)

/-- Any two elements are represented at a **common** level. -/
theorem exists_common (a a' : A) :
    ∃ (n : ℕ) (b b' : Ak n), SA.incl n b = a ∧ SA.incl n b' = a' := by
  obtain ⟨k, b, hb⟩ := SA.incl_surj a
  obtain ⟨k', b', hb'⟩ := SA.incl_surj a'
  rcases le_total k k' with hk | hk
  · obtain ⟨d, rfl⟩ := Nat.le.dest hk
    exact ⟨k + d, SA.stepPow k d b, b', (SA.incl_stepPow k d b).trans hb, hb'⟩
  · obtain ⟨d, rfl⟩ := Nat.le.dest hk
    exact ⟨k' + d, b, SA.stepPow k' d b', hb, (SA.incl_stepPow k' d b').trans hb'⟩

theorem e_stepPow (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a))
    (k d : ℕ) (a : Ak k) :
    e (k + d) (SA.stepPow k d a) = SB.stepPow k d (e k a) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      show e (k + d + 1) (SA.step (k + d) (SA.stepPow k d a))
        = SB.step (k + d) (SB.stepPow k d (e k a))
      rw [hcomm (k + d) (SA.stepPow k d a), ih]

/-- **The level-wise images agree whenever the level-wise sources do.** -/
theorem incl_e_eq
    (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a))
    (i : ℕ) (u : Ak i) (j : ℕ) (v : Ak j) (huv : SA.incl i u = SA.incl j v) :
    SB.incl i (e i u) = SB.incl j (e j v) := by
  rcases le_total i j with hij | hij
  · obtain ⟨d, rfl⟩ := Nat.le.dest hij
    have hs : SA.stepPow i d u = v := SA.stepPow_eq_of_incl_eq huv
    calc SB.incl i (e i u) = SB.incl (i + d) (SB.stepPow i d (e i u)) :=
          (SB.incl_stepPow i d (e i u)).symm
      _ = SB.incl (i + d) (e (i + d) (SA.stepPow i d u)) := by
          rw [e_stepPow SA SB e hcomm i d u]
      _ = SB.incl (i + d) (e (i + d) v) := by rw [hs]
  · obtain ⟨d, rfl⟩ := Nat.le.dest hij
    have hs : SA.stepPow j d v = u := SA.stepPow_eq_of_incl_eq huv.symm
    calc SB.incl (j + d) (e (j + d) u) = SB.incl (j + d) (e (j + d) (SA.stepPow j d v)) := by
          rw [hs]
      _ = SB.incl (j + d) (SB.stepPow j d (e j v)) := by
          rw [e_stepPow SA SB e hcomm j d v]
      _ = SB.incl j (e j v) := SB.incl_stepPow j d (e j v)

/-- The transported map, defined on a chosen representative. -/
noncomputable def transfer (a : A) : B :=
  SB.incl (SA.incl_surj a).choose (e _ (SA.incl_surj a).choose_spec.choose)

/-- **…and it does not depend on the representative.** -/
theorem transfer_eq
    (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a))
    (k : ℕ) (b : Ak k) : transfer SA SB e (SA.incl k b) = SB.incl k (e k b) :=
  incl_e_eq SA SB e hcomm _ ((SA.incl_surj (SA.incl k b)).choose_spec.choose) k b
    (SA.incl_surj (SA.incl k b)).choose_spec.choose_spec

/-- The commuting square, transported to the inverses. -/
theorem hcomm_symm
    (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a))
    (k : ℕ) (b : Bk k) :
    (e (k + 1)).symm (SB.step k b) = SA.step k ((e k).symm b) := by
  apply (e (k + 1)).injective
  rw [OrderIso.apply_symm_apply, hcomm k ((e k).symm b), OrderIso.apply_symm_apply]

/-- The underlying bijection. -/
noncomputable def chainUnionEquiv
    (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a)) :
    A ≃ B where
  toFun := transfer SA SB e
  invFun := transfer SB SA (fun k => (e k).symm)
  left_inv := by
    intro a
    obtain ⟨k, b, rfl⟩ := SA.incl_surj a
    rw [transfer_eq SA SB e hcomm k b,
        transfer_eq SB SA (fun k => (e k).symm) (hcomm_symm SA SB e hcomm) k (e k b),
        OrderIso.symm_apply_apply]
  right_inv := by
    intro b
    obtain ⟨k, c, rfl⟩ := SB.incl_surj b
    rw [transfer_eq SB SA (fun k => (e k).symm) (hcomm_symm SA SB e hcomm) k c,
        transfer_eq SA SB e hcomm k ((e k).symm c),
        OrderIso.apply_symm_apply]

/-- **Two increasing unions with compatible levelwise isomorphisms are
isomorphic.** -/
noncomputable def chainUnionIso
    (hcomm : ∀ (k : ℕ) (a : Ak k), e (k + 1) (SA.step k a) = SB.step k (e k a)) :
    A ≃o B where
  toEquiv := chainUnionEquiv SA SB e hcomm
  map_rel_iff' := by
    intro a a'
    show transfer SA SB e a ≤ transfer SA SB e a' ↔ a ≤ a'
    obtain ⟨n, b, b', rfl, rfl⟩ := exists_common SA a a'
    rw [transfer_eq SA SB e hcomm n b, transfer_eq SA SB e hcomm n b',
        SB.incl_le_iff, (e n).le_iff_le, SA.incl_le_iff]

end Transport

end ChainUnion
