/-
  EpPairTower — an abstract ω-tower of embedding/projection pairs and its
  bilimit, with the "any two colimit cocones over the tower are canonically
  order-isomorphic" lemma.

  This is the tower-agnostic form of `SierpinskiApplication.lean`'s
  `section ColimitCoconeIso` (which is hard-wired to the `(D k, iotaD k, pD k)`
  tower and `DBilimit`).  It is `PsiIso`-free and imports only Mathlib.

  Purpose: instantiate it twice — once with the constant-embedding tower
  `(D k, iotaD k, pD k)` (recovering `DBilimit`), once with the F-iterate
  tower `(D k, e'_k, p'_k)` with `e'_{k+1} = glueAA k` — so that
  `D∞^F ≃o F(D∞^F)` becomes a corollary of the shifted-cocone form of the
  lemma below.  See `Meta/Finding - PsiIso tower mismatch (2026-08-26).md`
  (remediation path 1).
-/

import Mathlib.Order.ScottContinuity
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Lattice.Nat

set_option linter.style.show false
set_option linter.style.longLine false

open Set

universe u

/-- An ω-chain of embedding/projection pairs:
    `carrier k ⇄ carrier (k+1)` with `prj k ∘ emb k = id` and
    `emb k ∘ prj k ≤ id`, both maps monotone. -/
structure EpPairTower where
  carrier : ℕ → Type u
  order : ∀ k, PartialOrder (carrier k)
  emb : ∀ k, carrier k → carrier (k + 1)
  prj : ∀ k, carrier (k + 1) → carrier k
  emb_mono : ∀ k, Monotone (emb k)
  prj_mono : ∀ k, Monotone (prj k)
  retraction : ∀ k x, prj k (emb k x) = x
  deflation : ∀ k z, emb k (prj k z) ≤ z

attribute [instance] EpPairTower.order

namespace EpPairTower

variable (T : EpPairTower)

/-- `emb k (prj k z) ≤ z` — deflation, spelled with the instance resolved. -/
theorem emb_prj_le (k : ℕ) (z : T.carrier (k + 1)) : T.emb k (T.prj k z) ≤ z :=
  T.deflation k z

/-! ### Iterated embedding / projection along the chain -/

/-- Transport a point up from level `k` to level `n ≥ k` by iterating `emb`. -/
noncomputable def embLe {k n : ℕ} (h : k ≤ n) : T.carrier k → T.carrier n :=
  Nat.leRecOn h (fun {j} => T.emb j)

/-- Transport a point down from level `n` to level `j ≤ n` by iterating `prj`. -/
noncomputable def prjLe {j n : ℕ} (h : j ≤ n) : T.carrier n → T.carrier j :=
  Nat.leRecOn (C := fun n => T.carrier n → T.carrier j) h
    (fun {n} (f : T.carrier n → T.carrier j) => f ∘ T.prj n) id

variable {T}

@[simp] theorem embLe_self {k : ℕ} (h : k ≤ k) (x : T.carrier k) : T.embLe h x = x :=
  Nat.leRecOn_self x

theorem embLe_succ {k n : ℕ} (h : k ≤ n) (h' : k ≤ n + 1) (x : T.carrier k) :
    T.embLe h' x = T.emb n (T.embLe h x) :=
  Nat.leRecOn_succ h x

theorem embLe_trans {k n m : ℕ} (h1 : k ≤ n) (h2 : n ≤ m) (x : T.carrier k) :
    T.embLe (h1.trans h2) x = T.embLe h2 (T.embLe h1 x) :=
  Nat.leRecOn_trans h1 h2 x

@[simp] theorem prjLe_self (j : ℕ) (h : j ≤ j) (x : T.carrier j) : T.prjLe h x = x := by
  unfold prjLe; rw [Nat.leRecOn_self]; rfl

theorem prjLe_succ {j n : ℕ} (h : j ≤ n) (h' : j ≤ n + 1) (w : T.carrier (n + 1)) :
    T.prjLe h' w = T.prjLe h (T.prj n w) := by
  unfold prjLe; rw [Nat.leRecOn_succ h]; rfl

theorem embLe_mono {k n : ℕ} (h : k ≤ n) : Monotone (T.embLe h) := by
  induction n, h using Nat.le_induction with
  | base => intro x y hxy; rwa [embLe_self, embLe_self]
  | succ n hkn ih =>
      intro x y hxy
      rw [embLe_succ hkn (Nat.le_succ_of_le hkn), embLe_succ hkn (Nat.le_succ_of_le hkn)]
      exact T.emb_mono n (ih hxy)

theorem prjLe_mono {j n : ℕ} (h : j ≤ n) : Monotone (T.prjLe h) := by
  induction n, h using Nat.le_induction with
  | base => intro x y hxy; rwa [prjLe_self, prjLe_self]
  | succ n hjn ih =>
      intro x y hxy
      rw [prjLe_succ hjn (Nat.le_succ_of_le hjn), prjLe_succ hjn (Nat.le_succ_of_le hjn)]
      exact ih (T.prj_mono n hxy)

/-- `prj` commutes with `prjLe` across a change of the bottom index. -/
theorem prj_prjLe_comm {j : ℕ} : ∀ {k : ℕ} (h1 : j + 1 ≤ k) (h2 : j ≤ k) (y : T.carrier k),
    T.prj j (T.prjLe h1 y) = T.prjLe h2 y := by
  intro k h1
  induction k, h1 using Nat.le_induction with
  | base =>
      intro h2 y
      rw [prjLe_self (j + 1) (le_refl _) y, prjLe_succ (le_refl j) h2 y,
        prjLe_self j (le_refl j) (T.prj j y)]
  | succ k hjk ih =>
      intro h2 y
      rw [prjLe_succ hjk (Nat.le_succ_of_le hjk) y, prjLe_succ (Nat.le_of_succ_le hjk) h2 y]
      exact ih (Nat.le_of_succ_le hjk) (T.prj k y)

theorem prjLe_trans {j n m : ℕ} (h1 : j ≤ n) (h2 : n ≤ m) (x : T.carrier m) :
    T.prjLe (h1.trans h2) x = T.prjLe h1 (T.prjLe h2 x) := by
  induction m, h2 using Nat.le_induction with
  | base => rw [prjLe_self n (le_refl n) x]
  | succ m hnm ih =>
      rw [prjLe_succ hnm (Nat.le_succ_of_le hnm) x,
        prjLe_succ (h1.trans hnm) (Nat.le_succ_of_le (h1.trans hnm)) x, ih (T.prj m x)]

theorem prj_embLe {k n : ℕ} (h : k ≤ n) (h' : k ≤ n + 1) (x : T.carrier k) :
    T.prj n (T.embLe h' x) = T.embLe h x := by
  rw [embLe_succ h h', T.retraction]

/-- One-step order reflection: `emb k x ≤ emb k y ↔ x ≤ y`. -/
theorem emb_le_iff (k : ℕ) (x y : T.carrier k) : T.emb k x ≤ T.emb k y ↔ x ≤ y := by
  constructor
  · intro hle
    have := T.prj_mono k hle
    rwa [T.retraction, T.retraction] at this
  · exact fun hle => T.emb_mono k hle

theorem embLe_le_iff {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n) (x y : T.carrier k),
    T.embLe h x ≤ T.embLe h y ↔ x ≤ y := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x y; rw [embLe_self, embLe_self]
  | succ n hkn ih =>
      intro x y
      rw [embLe_succ hkn (Nat.le_succ_of_le hkn), embLe_succ hkn (Nat.le_succ_of_le hkn),
        emb_le_iff]
      exact ih x y

theorem embLe_injective {k n : ℕ} (h : k ≤ n) : Function.Injective (T.embLe h) := by
  intro x y hxy
  exact ((embLe_le_iff h x y).mp hxy.le).antisymm ((embLe_le_iff h y x).mp hxy.ge)

/-! ### The bilimit -/

variable (T)

/-- The bilimit: compatible sequences under the tower's projections. -/
def Bilim : Type u := {x : ∀ k, T.carrier k // ∀ k, T.prj k (x (k + 1)) = x k}

noncomputable instance : PartialOrder T.Bilim := Subtype.partialOrder _

theorem Bilim.le_def {x y : T.Bilim} : x ≤ y ↔ ∀ k, x.1 k ≤ y.1 k := Iff.rfl

variable {T}

/-- Chasing a bilimit point down agrees with reading it off at the lower level. -/
theorem Bilim_prjLe_eq (z : T.Bilim) {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n), T.prjLe h (z.1 n) = z.1 k := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => exact prjLe_self k (le_refl k) (z.1 k)
  | succ n hn ih => rw [prjLe_succ hn (hn.trans (Nat.le_succ n)), z.2 n]; exact ih

theorem Bilim.emb_le (z : T.Bilim) {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n), T.embLe h (z.1 k) ≤ z.1 n := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [embLe_self]
  | succ n hn ih =>
      rw [embLe_succ hn (hn.trans (Nat.le_succ n))]
      refine (T.emb_mono n ih).trans ?_
      rw [show z.1 n = T.prj n (z.1 (n + 1)) from (z.2 n).symm]
      exact T.deflation n (z.1 (n + 1))

/-! ### The staged sequence of a compact -/

variable (T)

/-- The compatible sequence a point `w : carrier N` determines: chase down
    below `N`, chase up above `N`. -/
noncomputable def seqOf (N : ℕ) (w : T.carrier N) (j : ℕ) : T.carrier j :=
  if h : j ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w

variable {T}

theorem seqOf_compat (N : ℕ) (w : T.carrier N) (j : ℕ) :
    T.prj j (T.seqOf N w (j + 1)) = T.seqOf N w j := by
  by_cases h1 : j + 1 ≤ N
  · have h2 : j ≤ N := Nat.le_of_succ_le h1
    show T.prj j (if h : j + 1 ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
       = (if h : j ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
    rw [dif_pos h1, dif_pos h2]
    exact prj_prjLe_comm h1 h2 w
  · by_cases h2 : j ≤ N
    · have hjN : j = N := le_antisymm h2 (Nat.lt_succ_iff.mp (not_le.mp h1))
      show T.prj j (if h : j + 1 ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
         = (if h : j ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
      rw [dif_neg h1, dif_pos h2]
      subst hjN
      rw [prjLe_self j h2 w,
        show T.embLe (not_le.mp h1).le w = T.emb j w from by
          rw [embLe_succ (le_refl j) (not_le.mp h1).le, embLe_self],
        T.retraction]
    · show T.prj j (if h : j + 1 ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
         = (if h : j ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
      rw [dif_neg h1, dif_neg h2]
      have heq : T.embLe (not_le.mp h1).le w = T.emb j (T.embLe (not_le.mp h2).le w) :=
        embLe_succ (not_le.mp h2).le (not_le.mp h1).le w
      rw [heq, T.retraction]

/-- Moving the basepoint up one tower step doesn't change `seqOf`. -/
theorem seqOf_emb_step (N : ℕ) (w : T.carrier N) :
    T.seqOf (N + 1) (T.emb N w) = T.seqOf N w := by
  funext j
  show (if h : j ≤ N + 1 then T.prjLe h (T.emb N w) else T.embLe (not_le.mp h).le (T.emb N w))
     = (if h : j ≤ N then T.prjLe h w else T.embLe (not_le.mp h).le w)
  by_cases h1 : j ≤ N
  · have h2 : j ≤ N + 1 := le_trans h1 (Nat.le_succ N)
    rw [dif_pos h2, dif_pos h1, prjLe_succ h1 h2, T.retraction]
  · by_cases h2 : j = N + 1
    · subst h2
      rw [dif_pos (le_refl (N + 1)), dif_neg h1, prjLe_self (N + 1) (le_refl _) (T.emb N w)]
      have : T.embLe (not_le.mp h1).le w = T.emb N w := by
        rw [embLe_succ (le_refl N) (not_le.mp h1).le, embLe_self]
      rw [this]
    · have h3 : ¬ j ≤ N + 1 := by omega
      rw [dif_neg h3, dif_neg h1]
      have : T.embLe (not_le.mp h1).le w
          = T.embLe (not_le.mp h3).le (T.embLe (Nat.le_succ N) w) := by
        rw [embLe_trans (Nat.le_succ N) (not_le.mp h3).le]
      rw [this, show T.embLe (Nat.le_succ N) w = T.emb N w from by
        rw [embLe_succ (le_refl N) (Nat.le_succ N), embLe_self]]

theorem seqOf_embLe_invariant (N : ℕ) (w : T.carrier N) : ∀ {n : ℕ} (h : N ≤ n),
    T.seqOf n (T.embLe h w) = T.seqOf N w := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [embLe_self]
  | succ n hpn ih =>
      rw [embLe_succ hpn (Nat.le_succ_of_le hpn), seqOf_emb_step n (T.embLe hpn w)]; exact ih

/-! ### `ins` : the canonical embedding of level `k` into the bilimit -/

variable (T)

/-- Insert a point of `carrier k` into the bilimit as the sequence it stages. -/
noncomputable def ins (k : ℕ) (w : T.carrier k) : T.Bilim :=
  ⟨T.seqOf k w, seqOf_compat k w⟩

variable {T}

@[simp] theorem ins_apply (k : ℕ) (w : T.carrier k) (j : ℕ) :
    (T.ins k w).1 j = T.seqOf k w j := rfl

@[simp] theorem ins_self (k : ℕ) (w : T.carrier k) : (T.ins k w).1 k = w := by
  show (if h : k ≤ k then T.prjLe h w else T.embLe (not_le.mp h).le w) = w
  rw [dif_pos (le_refl k), prjLe_self k (le_refl k) w]

theorem ins_emb (k : ℕ) (w : T.carrier k) : T.ins (k + 1) (T.emb k w) = T.ins k w :=
  Subtype.ext (seqOf_emb_step k w)

theorem ins_embLe {k n : ℕ} (h : k ≤ n) (w : T.carrier k) : T.ins n (T.embLe h w) = T.ins k w :=
  Subtype.ext (seqOf_embLe_invariant k w h)

theorem ins_monotone (k : ℕ) : Monotone (T.ins k) := by
  intro w w' hle j
  show (if h : j ≤ k then T.prjLe h w else T.embLe (not_le.mp h).le w)
     ≤ (if h : j ≤ k then T.prjLe h w' else T.embLe (not_le.mp h).le w')
  by_cases h : j ≤ k
  · rw [dif_pos h, dif_pos h]; exact prjLe_mono h hle
  · rw [dif_neg h, dif_neg h]; exact (embLe_le_iff (not_le.mp h).le w w').mpr hle

theorem embLe_bilim_le (y : T.Bilim) {n : ℕ} : ∀ {n' : ℕ} (h : n ≤ n'),
    T.embLe h (y.1 n) ≤ y.1 n' := fun h => Bilim.emb_le y h

/-- `ins n (y.1 n) ≤ y` — exact agreement below `n`, deflation above. -/
theorem ins_le_self (y : T.Bilim) (n : ℕ) : T.ins n (y.1 n) ≤ y := by
  intro j
  show (if h : j ≤ n then T.prjLe h (y.1 n) else T.embLe (not_le.mp h).le (y.1 n)) ≤ y.1 j
  by_cases hjn : j ≤ n
  · rw [dif_pos hjn, Bilim_prjLe_eq y hjn]
  · rw [dif_neg hjn]; exact Bilim.emb_le y (not_le.mp hjn).le

theorem ins_chain_mono (y : T.Bilim) {n n' : ℕ} (h : n ≤ n') :
    T.ins n (y.1 n) ≤ T.ins n' (y.1 n') := by
  intro j
  show (if hj : j ≤ n then T.prjLe hj (y.1 n) else T.embLe (not_le.mp hj).le (y.1 n))
     ≤ (if hj : j ≤ n' then T.prjLe hj (y.1 n') else T.embLe (not_le.mp hj).le (y.1 n'))
  by_cases hjn : j ≤ n
  · have hjn' : j ≤ n' := hjn.trans h
    rw [dif_pos hjn, dif_pos hjn', Bilim_prjLe_eq y hjn, Bilim_prjLe_eq y hjn']
  · rw [dif_neg hjn]
    by_cases hjn' : j ≤ n'
    · rw [dif_pos hjn']
      exact (Bilim.emb_le y (not_le.mp hjn).le).trans_eq (Bilim_prjLe_eq y hjn').symm
    · rw [dif_neg hjn']
      have hnj : n ≤ j := (not_le.mp hjn).le
      have hn'j : n' ≤ j := (not_le.mp hjn').le
      rw [show T.embLe hnj (y.1 n) = T.embLe hn'j (T.embLe h (y.1 n)) from embLe_trans h hn'j (y.1 n)]
      exact (embLe_le_iff hn'j _ _).mpr (Bilim.emb_le y h)

/-! ### dcpo structure -/

variable (T)

/-- Directed-completeness of the levels plus Scott-continuity of the
    projections — the extra hypotheses that make the bilimit a dcpo and the
    colimit-cocone lemma go through. -/
structure IsDcpo : Prop where
  carrier_lub : ∀ (k : ℕ) (S : Set (T.carrier k)), S.Nonempty → DirectedOn (· ≤ ·) S →
    ∃ s, IsLUB S s
  prj_scott : ∀ k, ScottContinuous (T.prj k)

variable {T}

/-- Projecting a directed set of compatible sequences to one level stays directed. -/
theorem Bilim_directed_image (k : ℕ) {S : Set T.Bilim} (hdir : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≤ ·) ((fun x : T.Bilim => x.1 k) '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
  exact ⟨z.1 k, ⟨z, hz, rfl⟩, hxz k, hyz k⟩

/-- A point whose every level is the levelwise LUB is the LUB in the bilimit. -/
theorem Bilim_levelwise_isLUB {S : Set T.Bilim} {a : T.Bilim}
    (hk : ∀ k, IsLUB ((fun x : T.Bilim => x.1 k) '' S) (a.1 k)) : IsLUB S a := by
  constructor
  · intro x hx k; exact (hk k).1 ⟨x, hx, rfl⟩
  · intro z hz k; exact (hk k).2 (by rintro _ ⟨x, hx, rfl⟩; exact hz hx k)

variable (hT : T.IsDcpo)

include hT in
/-- The compatible sequence assembled levelwise from a directed set. -/
theorem exists_levelwise_lub (S : Set T.Bilim) (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) :
    ∃ b : T.Bilim, ∀ k, IsLUB ((fun x : T.Bilim => x.1 k) '' S) (b.1 k) := by
  set Tset : ∀ k, Set (T.carrier k) := fun k => (fun x : T.Bilim => x.1 k) '' S with hTset
  have hne' : ∀ k, (Tset k).Nonempty := fun k => hne.image _
  have hdir' : ∀ k, DirectedOn (· ≤ ·) (Tset k) := fun k => Bilim_directed_image k hdir
  choose sup hsup using fun k => hT.carrier_lub k (Tset k) (hne' k) (hdir' k)
  have himg : ∀ k, Tset k = T.prj k '' Tset (k + 1) := by
    intro k; ext v; simp only [hTset, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.1 (k + 1), ⟨x, hx, rfl⟩, x.2 k⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, (x.2 k).symm⟩
  have hcompat : ∀ k, T.prj k (sup (k + 1)) = sup k := by
    intro k
    have hlub_img : IsLUB (T.prj k '' Tset (k + 1)) (T.prj k (sup (k + 1))) :=
      hT.prj_scott k (hne' (k + 1)) (hdir' (k + 1)) (hsup (k + 1))
    rw [← himg k] at hlub_img
    exact hlub_img.unique (hsup k)
  exact ⟨⟨sup, hcompat⟩, hsup⟩

include hT in
/-- The bilimit is a dcpo. -/
theorem Bilim.exists_isLUB_of_directedOn (S : Set T.Bilim) (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) : ∃ y, IsLUB S y := by
  obtain ⟨b, hb⟩ := exists_levelwise_lub hT S hne hdir
  exact ⟨b, Bilim_levelwise_isLUB hb⟩

/-! ### The approximating chain of a bilimit point -/

variable (T)

/-- `y` is the least upper bound of `{ins n (y.1 n) : n}`. -/
noncomputable def chainSet (y : T.Bilim) : Set T.Bilim :=
  Set.range (fun n => T.ins n (y.1 n))

variable {T}

theorem chainSet_nonempty (y : T.Bilim) : (T.chainSet y).Nonempty := ⟨_, 0, rfl⟩

theorem chainSet_directedOn (y : T.Bilim) : DirectedOn (· ≤ ·) (T.chainSet y) := by
  rintro _ ⟨n1, rfl⟩ _ ⟨n2, rfl⟩
  exact ⟨T.ins (max n1 n2) (y.1 (max n1 n2)), ⟨max n1 n2, rfl⟩,
    ins_chain_mono y (le_max_left n1 n2), ins_chain_mono y (le_max_right n1 n2)⟩

theorem chainSet_isLUB (y : T.Bilim) : IsLUB (T.chainSet y) y := by
  constructor
  · rintro _ ⟨n, rfl⟩; exact ins_le_self y n
  · intro z hz j
    have hzj := hz ⟨j, rfl⟩ j
    show y.1 j ≤ z.1 j
    rwa [show (T.ins j (y.1 j)).1 j = y.1 j from ins_self j (y.1 j)] at hzj

include hT in
/-- The levelwise reading of a directed LUB is the LUB of the levelwise images. -/
theorem isLUB_bilim_apply {S : Set T.Bilim} {a : T.Bilim} (ha : IsLUB S a)
    (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) (k : ℕ) :
    IsLUB ((fun x : T.Bilim => x.1 k) '' S) (a.1 k) := by
  obtain ⟨b, hb⟩ := exists_levelwise_lub hT S hne hdir
  rw [ha.unique (Bilim_levelwise_isLUB hb)]
  exact hb k

theorem seqOf_eq_embLe (N : ℕ) (w : T.carrier N) {n : ℕ} (h : N ≤ n) :
    T.seqOf N w n = T.embLe h w := by
  show (if hh : n ≤ N then T.prjLe hh w else T.embLe (not_le.mp hh).le w) = T.embLe h w
  by_cases hh : n ≤ N
  · have hnN : n = N := le_antisymm hh h
    subst hnN
    rw [dif_pos hh, prjLe_self n hh w, embLe_self h w]
  · rw [dif_neg hh]

/-! ### Colimit cocones over the tower -/

variable (T)

/-- A cocone `(e, p)` over the tower is *colimiting* iff its legs form ep-pairs
    with each level, `e` is compatible with `emb`, and each `z` is the LUB of
    its approximations `e k (p k z)`. -/
structure IsColimitCocone {X : Type u} [PartialOrder X]
    (e : ∀ k, T.carrier k → X) (p : ∀ k, X → T.carrier k) : Prop where
  retraction : ∀ k x, p k (e k x) = x
  deflation : ∀ k z, e k (p k z) ≤ z
  compat : ∀ k w, e (k + 1) (T.emb k w) = e k w
  isLUB : ∀ z, IsLUB (Set.range (fun k => e k (p k z))) z

variable {T}

namespace IsColimitCocone

variable {X : Type u} [PartialOrder X] {e : ∀ k, T.carrier k → X} {p : ∀ k, X → T.carrier k}

/-- `p k z = prj k (p (k+1) z)` — from the four fields + monotone legs. -/
theorem proj_tower (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) (k : ℕ) (x : X) :
    p k x = T.prj k (p (k + 1) x) := by
  apply le_antisymm
  · have h1 : e (k + 1) (T.emb k (p k x)) ≤ x := by
      rw [h.compat k (p k x)]; exact h.deflation k x
    have h2 : T.emb k (p k x) ≤ p (k + 1) x := by
      have := hp (k + 1) h1
      rwa [h.retraction (k + 1) (T.emb k (p k x))] at this
    have := T.prj_mono k h2
    rwa [T.retraction k (p k x)] at this
  · have h1 : e (k + 1) (T.emb k (T.prj k (p (k + 1) x))) ≤ x :=
      le_trans (he (k + 1) (T.deflation k (p (k + 1) x))) (h.deflation (k + 1) x)
    have h2 : e k (T.prj k (p (k + 1) x)) ≤ x := by
      rwa [h.compat k (T.prj k (p (k + 1) x))] at h1
    have := hp k h2
    rwa [h.retraction k (T.prj k (p (k + 1) x))] at this

theorem proj_prjLe (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) {j : ℕ} :
    ∀ {n : ℕ} (hjn : j ≤ n) (x : X), p j x = T.prjLe hjn (p n x) := by
  intro n hjn
  induction n, hjn using Nat.le_induction with
  | base => intro x; rw [prjLe_self j (le_refl j)]
  | succ n hjn ih =>
      intro x
      rw [prjLe_succ hjn (Nat.le_succ_of_le hjn), ← h.proj_tower hp he n x]
      exact ih x

/-- The `Bilim` point a colimit cocone assigns to `x`. -/
noncomputable def toBilim (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) (x : X) : T.Bilim :=
  ⟨fun k => p k x, fun k => (h.proj_tower hp he k x).symm⟩

@[simp] theorem toBilim_apply (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) (x : X) (k : ℕ) :
    (h.toBilim hp he x).1 k = p k x := rfl

theorem toBilim_le_iff (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) (x x' : X) :
    h.toBilim hp he x ≤ h.toBilim hp he x' ↔ x ≤ x' := by
  constructor
  · intro hle
    have hle' : ∀ k, p k x ≤ p k x' := hle
    have hub : x' ∈ upperBounds (Set.range (fun k => e k (p k x))) := by
      rintro _ ⟨k, rfl⟩
      exact le_trans (he k (hle' k)) (h.deflation k x')
    exact (h.isLUB x).2 hub
  · intro hle
    show ∀ k, p k x ≤ p k x'
    exact fun k => hp k hle

theorem toBilim_injective (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k)) :
    Function.Injective (h.toBilim hp he) := by
  intro a b hab
  exact le_antisymm ((h.toBilim_le_iff hp he a b).mp (le_of_eq hab))
    ((h.toBilim_le_iff hp he b a).mp (le_of_eq hab.symm))

theorem toBilim_surjective (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k))
    (hsup : ∀ d : T.Bilim, ∃ x : X, IsLUB (Set.range (fun k => e k (d.1 k))) x)
    (hcont : ∀ (d : T.Bilim) (x : X),
      IsLUB (Set.range (fun k => e k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => p j (e k (d.1 k)))) (p j x)) :
    Function.Surjective (h.toBilim hp he) := by
  intro d
  obtain ⟨x, hx⟩ := hsup d
  refine ⟨x, Subtype.ext (funext (fun j => ?_))⟩
  show p j x = d.1 j
  have himg_ge : ∀ k, j ≤ k → p j (e k (d.1 k)) = d.1 j := by
    intro k hjk
    rw [h.proj_prjLe hp he hjk (e k (d.1 k)), h.retraction k (d.1 k)]
    exact Bilim_prjLe_eq d hjk
  have himg_le : ∀ k, k ≤ j → p j (e k (d.1 k)) ≤ d.1 j := by
    intro k hkj
    have hcompat_chase : ∀ {m : ℕ} (hkm : k ≤ m) (w : T.carrier k),
        e k w = e m (T.embLe hkm w) := by
      intro m hkm
      induction m, hkm using Nat.le_induction with
      | base => intro w; rw [embLe_self]
      | succ m hkm ih =>
          intro w
          rw [embLe_succ hkm (Nat.le_succ_of_le hkm), h.compat m (T.embLe hkm w)]
          exact ih w
    rw [hcompat_chase hkj (d.1 k), h.retraction j (T.embLe hkj (d.1 k))]
    have hval : (T.ins k (d.1 k)).1 j = T.embLe hkj (d.1 k) := seqOf_eq_embLe k (d.1 k) hkj
    have hle := ins_le_self d k j
    rwa [hval] at hle
  have hLUB_dj : IsLUB (Set.range (fun k => p j (e k (d.1 k)))) (d.1 j) := by
    constructor
    · rintro _ ⟨k, rfl⟩
      rcases le_total j k with hjk | hkj
      · exact (himg_ge k hjk).le
      · exact himg_le k hkj
    · intro w hw
      calc d.1 j = p j (e j (d.1 j)) := (himg_ge j (le_refl j)).symm
        _ ≤ w := hw ⟨j, rfl⟩
  exact (hcont d x hx j).unique hLUB_dj

/-- **A colimit cocone with the chain sups is order-isomorphic to `Bilim`.** -/
noncomputable def orderIsoBilim (h : T.IsColimitCocone e p)
    (hp : ∀ k, Monotone (p k)) (he : ∀ k, Monotone (e k))
    (hsup : ∀ d : T.Bilim, ∃ x : X, IsLUB (Set.range (fun k => e k (d.1 k))) x)
    (hcont : ∀ (d : T.Bilim) (x : X),
      IsLUB (Set.range (fun k => e k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => p j (e k (d.1 k)))) (p j x)) :
    X ≃o T.Bilim :=
  { Equiv.ofBijective (h.toBilim hp he)
      ⟨h.toBilim_injective hp he, h.toBilim_surjective hp he hsup hcont⟩ with
    map_rel_iff' := by intro a b; exact h.toBilim_le_iff hp he a b }

end IsColimitCocone

/-- `Bilim`'s own colimit cocone `(ins, proj)`. -/
theorem Bilim_isColimitCocone :
    T.IsColimitCocone (fun k => T.ins k) (fun k (z : T.Bilim) => z.1 k) where
  retraction k w := ins_self k w
  deflation k z := ins_le_self z k
  compat k w := ins_emb k w
  isLUB z := by
    have h := chainSet_isLUB z
    have : T.chainSet z = Set.range (fun k => T.ins k (z.1 k)) := rfl
    rwa [this] at h

/-- **Any two colimit cocones over the tower are canonically order-isomorphic.** -/
noncomputable def isColimitCocone_orderIso
    {X Y : Type u} [PartialOrder X] [PartialOrder Y]
    {eX : ∀ k, T.carrier k → X} {pX : ∀ k, X → T.carrier k}
    {eY : ∀ k, T.carrier k → Y} {pY : ∀ k, Y → T.carrier k}
    (hX : T.IsColimitCocone eX pX) (hY : T.IsColimitCocone eY pY)
    (hpX : ∀ k, Monotone (pX k)) (heX : ∀ k, Monotone (eX k))
    (hpY : ∀ k, Monotone (pY k)) (heY : ∀ k, Monotone (eY k))
    (hsupX : ∀ d : T.Bilim, ∃ x : X, IsLUB (Set.range (fun k => eX k (d.1 k))) x)
    (hcontX : ∀ (d : T.Bilim) (x : X),
      IsLUB (Set.range (fun k => eX k (d.1 k))) x →
      ∀ j, IsLUB (Set.range (fun k => pX j (eX k (d.1 k)))) (pX j x))
    (hsupY : ∀ d : T.Bilim, ∃ y : Y, IsLUB (Set.range (fun k => eY k (d.1 k))) y)
    (hcontY : ∀ (d : T.Bilim) (y : Y),
      IsLUB (Set.range (fun k => eY k (d.1 k))) y →
      ∀ j, IsLUB (Set.range (fun k => pY j (eY k (d.1 k)))) (pY j y)) :
    X ≃o Y :=
  (hX.orderIsoBilim hpX heX hsupX hcontX).trans
    (hY.orderIsoBilim hpY heY hsupY hcontY).symm

end EpPairTower
