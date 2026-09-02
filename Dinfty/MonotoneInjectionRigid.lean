import Dinfty.CopyBFreedom
import Mathlib.GroupTheory.OrderOfElement

open GluingTowerLibrary SierpinskiApplication

/-!
# On a finite poset, a monotone injection is an order isomorphism — and on a
rigid one, the identity

`CopyBFreedom` shows the copy-`B` component of a `Gen`-layer action is free for
an arbitrary monotone `ψ`, and that injectivity does not constrain it *at an
abstract base* — the witness being the four-element diamond twisted by
`Prod.swap`.  The question left open was whether that freedom is realised **at
the tower**, whose glue base at level `k+1` is `EndP (D k)`.

This module supplies the bridge that turns that into a finite-poset question,
and the answer at level 1 is recorded below.

## The bridge

* `le_of_apply_le` — on a **finite** poset, a monotone injection reflects the
  order.  Proof: finite + injective gives a bijection, hence a permutation, hence
  `f ^ orderOf` is the identity; so `f^[n]` is a two-sided inverse for
  `n = orderOf - 1`, and it is monotone as an iterate of a monotone map.
* `orderIsoOfMonotoneInjective` — so such an `f` *is* an order isomorphism.
* `eq_id_of_rigid` — hence on a **rigid** finite poset the only monotone
  injection is the identity.

That last statement is what the copy-`B` question needs: an injective copy-`B`
twist `ψ` is exactly a monotone injection of the glue base, so it exists
nontrivially **iff the base is non-rigid**.

## The verdict at the tower's first level

`D (k+1) = GlueCar (EndP (D k)) id`, so the level-1 glue base is
`EndP (D 0) = EndP (Fin 3)`, ten elements.
`_archive/check_endp_D0_automorphisms.py` computes its automorphism group
exhaustively:

    |EndP(Fin 3)| = 10,  |Aut(EndP(Fin 3))| = 1

and cross-checks the bridge above by enumerating monotone injections
independently — there is exactly one, the identity.

**So the copy-`B` freedom is not realised by any injective action at level 1.**
The diamond counterexample does not transfer: `EndP (Fin 3)` is rigid, and by
`eq_id_of_rigid` that leaves `ψ = id`, i.e. `glueTwist g ψ = baseMapGen g` for
`g = id`.

**CORRECTION (2026-08-31).**  The Birkhoff route named below **does not
exist**: in the normalized tower `D 1` is *not* distributive, and `constHom`
embeds `D 1` in `EndP (D 1)` as a sublattice, so `EndP (D 1)` is not
distributive either (`_archive/check_endp_D1_rigidity_via_birkhoff.py`; the
recorded distributivity was an `id`-tower fact).  Only the **easy half** of
Birkhoff is needed and it is free — see `Dinfty/JoinIrredRigidity.lean`, which
closes level 2: **`EndP (D 1)` is rigid**, so the copy-`B` freedom is not
realised at level 2 either.

**Scope, stated precisely.**  This is level 1 only, and it is a *computation*
recorded in `_archive/`, not a Lean proof — `Aut` of a ten-element poset is not
something the kernel can enumerate here (Update 36).  Higher levels are not
settled: `EndP (D 1)` has 12,301,264,685,471,857 elements and cannot be
enumerated at all.  The plausible route there is the Birkhoff reduction already
on file — `EndP (D 1)` distributive, so its automorphism group is that of its
poset of join-irreducibles, `J(D 1) × D 1ᵒᵖ` at 459 elements — which is within
reach of the same kind of computation, and is *not* done here.
-/

open scoped Classical

universe u

namespace MonotoneInjectionRigid

variable {Q : Type u} [PartialOrder Q] [Finite Q]

/-- **A monotone injection of a finite poset reflects the order.**

`f` is a bijection, hence a permutation of finite order; `f^[orderOf - 1]` is
therefore a two-sided inverse, and it is monotone as an iterate of a monotone
map.  Applying it to `f a ≤ f b` gives `a ≤ b`. -/
theorem le_of_apply_le {f : Q → Q} (hmono : Monotone f) (hinj : Function.Injective f)
    {a b : Q} (h : f a ≤ f b) : a ≤ b := by
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  have hcoe : ⇑(Equiv.ofBijective f hbij) = f := rfl
  have hpos : 0 < orderOf (Equiv.ofBijective f hbij) := orderOf_pos _
  have hpow : (Equiv.ofBijective f hbij) ^ orderOf (Equiv.ofBijective f hbij) = 1 :=
    pow_orderOf_eq_one _
  have hiter : f^[orderOf (Equiv.ofBijective f hbij)] = id := by
    have hc : ⇑((Equiv.ofBijective f hbij) ^ orderOf (Equiv.ofBijective f hbij))
        = ⇑(1 : Equiv.Perm Q) := by rw [hpow]
    rw [Equiv.Perm.coe_pow, hcoe] at hc
    simpa using hc
  obtain ⟨n, hn⟩ : ∃ n, orderOf (Equiv.ofBijective f hbij) = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hstep := (hmono.iterate n) h
  rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply] at hstep
  simp only [Nat.succ_eq_add_one] at hstep
  rw [← hn, hiter] at hstep
  simpa using hstep

/-- A monotone injection of a finite poset **is** an order isomorphism. -/
noncomputable def orderIsoOfMonotoneInjective {f : Q → Q} (hmono : Monotone f)
    (hinj : Function.Injective f) : Q ≃o Q where
  toEquiv := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  map_rel_iff' := ⟨le_of_apply_le hmono hinj, fun h => hmono h⟩

@[simp] theorem orderIsoOfMonotoneInjective_apply {f : Q → Q} (hmono : Monotone f)
    (hinj : Function.Injective f) (a : Q) :
    orderIsoOfMonotoneInjective hmono hinj a = f a := rfl

/-- **On a rigid finite poset the only monotone injection is the identity.**

This is the form the copy-`B` question needs: an injective copy-`B` twist is
exactly a monotone injection of the glue base, so a nontrivial one exists iff
the base fails to be rigid. -/
theorem eq_id_of_rigid (hrigid : Subsingleton (Q ≃o Q)) {f : Q → Q}
    (hmono : Monotone f) (hinj : Function.Injective f) : f = id := by
  funext a
  have := congrArg (fun e : Q ≃o Q => e a)
    (hrigid.elim (orderIsoOfMonotoneInjective hmono hinj) (OrderIso.refl Q))
  simpa using this

end MonotoneInjectionRigid

/-! ## The consequence for `glueTwist`

Spelled out at the level of the counterexample it neutralises. -/

namespace CopyBFreedom

open MonotoneInjectionRigid

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P] [Finite P]

/-- **If the glue base is rigid, an injective copy-`B` twist is no twist at
all.**  `glueTwist g ψ` with `ψ` monotone and injective over a rigid finite base
collapses to `baseMapGen g` — the freedom exhibited on the diamond needs a
non-rigid base, and the tower's level-1 base `EndP (Fin 3)` is rigid
(`_archive/check_endp_D0_automorphisms.py`). -/
theorem glueTwist_eq_baseMapGen_of_rigid (hrigid : Subsingleton (P ≃o P))
    (ψ : P →o P) (hpsi : Function.Injective ψ) :
    glueTwist (OrderHom.id : P →o P) ψ
      = GenContinuity.baseMapGen (OrderHom.id : P →o P) := by
  have hid : (ψ : P → P) = id := eq_id_of_rigid hrigid ψ.monotone hpsi
  funext x
  cases x with
  | inl a => rfl
  | inr x => cases x with
    | inl b =>
      show Sum.inr (Sum.inl (ψ b)) = Sum.inr (Sum.inl b)
      rw [congrFun hid b]; rfl
    | inr c => rfl

/-- The sharper form: over a rigid finite base, a monotone injective `ψ` **is**
the identity, so the only twist available is by `g = id`. -/
theorem twist_trivial_of_rigid (hrigid : Subsingleton (P ≃o P)) (ψ : P →o P)
    (hpsi : Function.Injective ψ) : (ψ : P → P) = id :=
  eq_id_of_rigid hrigid ψ.monotone hpsi

end CopyBFreedom

/-! ## The free consequence at the tower: `D_all_rigid` upgrades to
embedding-rigidity

`D_all_rigid` says each `D k` has no nontrivial order *automorphism*.  The
bridge upgrades that, at no cost, to: no nontrivial monotone *injection* either.
That is strictly stronger — a priori a poset can be rigid while admitting
self-embeddings — and it says the finite levels carry no hidden self-similarity
of any kind, not merely no symmetry. -/

namespace TowerRigidity

/-- **Every monotone injection `D k → D k` is the identity.**  Immediate from
`D_all_rigid` and `eq_id_of_rigid`; the levels are finite by `instFintypeD`. -/
theorem D_monotone_injection_eq_id (k : ℕ) {f : D k → D k}
    (hmono : Monotone f) (hinj : Function.Injective f) : f = id :=
  MonotoneInjectionRigid.eq_id_of_rigid (D_all_rigid k) hmono hinj

/-- Order-hom form. -/
theorem D_orderHom_injection_eq_id (k : ℕ) (f : D k →o D k)
    (hinj : Function.Injective f) : (f : D k → D k) = id :=
  D_monotone_injection_eq_id k f.monotone hinj

end TowerRigidity
