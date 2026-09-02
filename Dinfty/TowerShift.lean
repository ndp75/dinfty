import Dinfty.EpPairTower

-- [D-2201] §The-tower-shift-and-what-Theorem-A-reduces
universe u

namespace EpPairTower

-- [D-2202] §The-shifted-tower
-- [D-2203] shift
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

-- [D-2204] shift_carrier
@[simp] theorem shift_carrier (k : ℕ) : T.shift.carrier k = T.carrier (k + 1) := rfl
-- [D-2205] shift_prj
@[simp] theorem shift_prj (k : ℕ) : T.shift.prj k = T.prj (k + 1) := rfl
-- [D-2206] shift_emb
@[simp] theorem shift_emb (k : ℕ) : T.shift.emb k = T.emb (k + 1) := rfl

-- [D-2207] §The-bilimit-does-not-see-the-shift
-- [D-2208] shiftFwd
def shiftFwd (x : T.Bilim) : T.shift.Bilim :=
  ⟨fun k => x.1 (k + 1), fun k => x.2 (k + 1)⟩

-- [D-2209] unshiftSeq
noncomputable def unshiftSeq (y : T.shift.Bilim) : ∀ k, T.carrier k
  | 0 => T.prj 0 (y.1 0)
  | (n + 1) => y.1 n

-- [D-2210] unshiftSeq_compat
theorem unshiftSeq_compat (y : T.shift.Bilim) (k : ℕ) :
    T.prj k (unshiftSeq T y (k + 1)) = unshiftSeq T y k := by
  cases k with
  | zero => rfl
  | succ n => exact y.2 n

-- [D-2211] unshift
noncomputable def unshift (y : T.shift.Bilim) : T.Bilim :=
  ⟨unshiftSeq T y, unshiftSeq_compat T y⟩

-- [D-2212] shiftIso
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

-- [D-2213] §Theorem-A-reduced-to-one-obligation
-- [D-2214] orderIsoBilim_shift
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
