import Dinfty.EpPairTower

/-!
# The tower shift, and what Theorem A reduces to

Theorem A is the self-similarity statement `D∞ ≅ Φ(D∞)`.  The standard bilimit
argument for it has two halves:

1. **the free half** — the tower shifted up one level has the same bilimit;
2. **the content** — `Φ` applied to the bilimit's own colimit cocone is again a
   colimit cocone, this time over the shifted tower.

This module proves (1) in the abstract, for any `EpPairTower`, and assembles the
two into `orderIsoBilim_shift`.  After that, Theorem A is exactly (2): a single
`IsColimitCocone` obligation, not a chain of prose.

Half (1) is genuinely free — `Bilim` mentions only `prj`, and dropping the first
coordinate is inverted by re-deriving it as `prj 0` of the second.  The concrete
`SierpinskiApplication.dBilimitShiftIso` is this construction hard-wired to the
`D`-tower; nothing there used the tower.
-/

universe u

namespace EpPairTower

/-! ## The shifted tower -/

/-- `T.shift` is `T` with level `0` dropped: `carrier k = T.carrier (k+1)`, and
every field re-indexed.  All eight fields are `T`'s at `k+1`. -/
def shift (T : _root_.EpPairTower) : _root_.EpPairTower where
  carrier k := T.carrier (k + 1)
  order k := T.order (k + 1)
  emb k := T.emb (k + 1)
  prj k := T.prj (k + 1)
  emb_mono k := T.emb_mono (k + 1)
  prj_mono k := T.prj_mono (k + 1)
  retraction k := T.retraction (k + 1)
  deflation k := T.deflation (k + 1)

variable (T : _root_.EpPairTower)

@[simp] theorem shift_carrier (k : ℕ) : T.shift.carrier k = T.carrier (k + 1) := rfl
@[simp] theorem shift_prj (k : ℕ) : T.shift.prj k = T.prj (k + 1) := rfl
@[simp] theorem shift_emb (k : ℕ) : T.shift.emb k = T.emb (k + 1) := rfl

/-! ## The bilimit does not see the shift -/

/-- Forget the zeroth coordinate. -/
def shiftFwd (x : T.Bilim) : T.shift.Bilim :=
  ⟨fun k => x.1 (k + 1), fun k => x.2 (k + 1)⟩

/-- Put the zeroth coordinate back — it is forced, as `prj 0` of the first. -/
noncomputable def unshiftSeq (y : T.shift.Bilim) : ∀ k, T.carrier k
  | 0 => T.prj 0 (y.1 0)
  | (n + 1) => y.1 n

theorem unshiftSeq_compat (y : T.shift.Bilim) (k : ℕ) :
    T.prj k (unshiftSeq T y (k + 1)) = unshiftSeq T y k := by
  cases k with
  | zero => rfl
  | succ n => exact y.2 n

noncomputable def unshift (y : T.shift.Bilim) : T.Bilim :=
  ⟨unshiftSeq T y, unshiftSeq_compat T y⟩

/-- **The bilimit of the shifted tower is the bilimit.**  The abstract form of
`SierpinskiApplication.dBilimitShiftIso`. -/
noncomputable def shiftIso : T.Bilim ≃o T.shift.Bilim where
  toFun := shiftFwd T
  invFun := unshift T
  left_inv := by
    intro x
    refine Subtype.ext (funext (fun k => ?_))
    cases k with
    | zero => exact x.2 0
    | succ n => rfl
  right_inv := by
    intro y
    refine Subtype.ext (funext (fun k => ?_))
    rfl
  map_rel_iff' := by
    intro x y
    constructor
    · intro h k
      have h1 : x.1 (k + 1) ≤ y.1 (k + 1) := h k
      have h2 := T.prj_mono k h1
      rwa [x.2 k, y.2 k] at h2
    · intro h k
      exact h (k + 1)

/-! ## Theorem A, reduced to one obligation -/

/-- **The self-similarity reduction.**  Anything carrying a colimit cocone over
the *shifted* tower is order-isomorphic to the bilimit of the tower itself.

Read `X := Φ(Bilim)`: Theorem A is then exactly the hypothesis, namely that `Φ`
applied to the bilimit's colimit cocone is again one.  Nothing else about the
tower, the functor, or the geometry is involved. -/
noncomputable def orderIsoBilim_shift {X : Type u} [PartialOrder X]
    {e : ∀ k, T.shift.carrier k → X} {p : ∀ k, X → T.shift.carrier k}
    (h : T.shift.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k))
    (hsup : ∀ d : T.shift.Bilim, ∃ x : X, IsLUB (Set.range (fun k => e k (d.1 k))) x)
    (hcont : ∀ (d : T.shift.Bilim) (x : X),
      IsLUB (Set.range (fun k => e k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => p j (e k (d.1 k)))) (p j x)) :
    X ≃o T.Bilim :=
  (h.orderIsoBilim hp he hsup hcont).trans (shiftIso T).symm

end EpPairTower
