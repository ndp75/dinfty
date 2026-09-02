import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

/-!
# Rigidity through the join-irreducibles — the half of Birkhoff that is free

`MonotoneInjectionRigid` reduced the copy-`B` question of pillar A to: *is the
glue base `EndP (D k)` rigid?*  It settled `k = 0` by enumeration and named the
route to `k = 1` as **Birkhoff** — `EndP (D 1)` distributive, so
`Aut ≅ Aut (J (EndP (D 1)))`, a 432-element problem.

**That route does not exist.**  In the normalized tower `D 1` is *not*
distributive (`_archive/check_endp_D1_rigidity_via_birkhoff.py`), and `constHom`
embeds `D 1` in `EndP (D 1)` as a sublattice, so `EndP (D 1)` is not
distributive either.  (The recorded distributivity was an `id`-tower fact; the
memory ledger already flags the Birkhoff-width numbers as stale.)

But only the **easy half** of Birkhoff is needed, and that half is free:

> For any finite lattice `L`, two automorphisms that agree on the
> join-irreducibles are equal.

because every element is the join of the join-irreducibles below it
(`finite_lattice_eq_sup_joinIrreds`) and an order isomorphism preserves finite
sups.  No distributivity anywhere.  That gives
`|Aut L| ≤ |Aut (J L)|` for free, which is all the copy-`B` question needs.

## The threshold argument

`jiOrderIso` indexes `J (EndP P)` by `Pᵒᵈ × J P`, with `stepMap q ⊥ = constHom q`
(`SliceReduction.stepMap_bot'`).  So an automorphism `Θ` of `EndP P` that
**preserves the threshold coordinate** acts on the constants by some `σ` on
`J P`.  `sigma_eq_id_of_rigid` below shows that if `P` is rigid then `σ` is the
identity: `Θ ∘ constHom = constHom ∘ φ` for `φ x = ⨆ {σ q | q ∈ J P, q ≤ x}`,
which is a monotone injection of `P`, hence an automorphism
(`orderIsoOfMonotoneInjective`), hence the identity.

Threshold preservation is the one input that is *not* general — it is a fact
about the particular poset `Pᵒᵈ × J P`.  At `P = D 1` it is checked exhaustively
in `_archive/check_endp_D1_rigidity_threshold.py`: `|Aut ((D 1)ᵒᵈ × J (D 1))| = 2`
and **both** elements preserve the first coordinate.  With `D_all_rigid` that
closes level 2:

> `EndP (D 1)` is rigid, so the copy-`B` freedom of `CopyBFreedom` is not
> realised by any injective action at level 2 either.

Level 2's verdict is therefore a computation plus the theorems below, exactly as
level 1's was.  Levels `≥ 3` are untouched.
-/

open scoped Classical

universe u

namespace JoinIrredRigidity

/-! ## Order isomorphisms preserve finite sups -/

theorem orderIso_finset_sup {α : Type*} {β γ : Type u} [Lattice β] [OrderBot β]
    [Lattice γ] [OrderBot γ] (e : β ≃o γ) (s : Finset α) (f : α → β) :
    e (s.sup f) = s.sup (fun x => e (f x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using e.map_bot
  | insert a s _ ih => rw [Finset.sup_insert, Finset.sup_insert, e.map_sup, ih]

/-! ## The easy half of Birkhoff -/

section Lattice

variable {P : Type u} [Lattice P] [OrderBot P] [Fintype P] [DecidableEq P]

/-- **An automorphism of a finite lattice is determined by its action on the
join-irreducibles** — the injection `Aut L ↪ Aut (J L)`.

This is Birkhoff's easy half and it needs **no distributivity**. -/
theorem eq_of_agree_on_joinIrred (e e' : P ≃o P)
    (h : ∀ q : P, JoinIrred P q → e q = e' q) : e = e' := by
  have hpt : ∀ a : P, e a = e' a := by
    intro a
    conv_lhs => rw [finite_lattice_eq_sup_joinIrreds a]
    conv_rhs => rw [finite_lattice_eq_sup_joinIrreds a]
    rw [orderIso_finset_sup e _ id, orderIso_finset_sup e' _ id]
    exact Finset.sup_congr rfl
      (fun q hq => h q (Finset.mem_filter.mp hq).2.1)
  exact OrderIso.ext (funext hpt)

/-- **An automorphism fixing every join-irreducible is the identity.** -/
theorem eq_refl_of_fixes_joinIrred (e : P ≃o P)
    (h : ∀ q : P, JoinIrred P q → e q = q) : e = OrderIso.refl P :=
  eq_of_agree_on_joinIrred e (OrderIso.refl P) h

end Lattice

/-! ## The threshold argument at `EndP` -/

section EndP

variable {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P] [DecidableEq P]

/-- `constHom` carries a finite sup to a finite sup. -/
theorem constHom_finset_sup {α : Type*} (s : Finset α) (f : α → P) :
    (constHom (s.sup f) : EndP P) = s.sup (fun x => (constHom (f x) : EndP P)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constHom_bot_eq (L := P))
  | insert a s _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← constHom_sup, ih]

/-- **The threshold argument.**

Suppose a lattice automorphism `Θ` of `EndP P` moves the constants by a monotone
`σ`, i.e. `Θ (constHom q) = constHom (σ q)` for every join-irreducible `q` —
which is exactly what "`Θ` preserves the threshold-`⊥` join-irreducibles" says,
since `stepMap q ⊥ = constHom q`.  If `P` is rigid then `σ` fixes every
join-irreducible, so `Θ` fixes every constant. -/
theorem sigma_eq_id_of_rigid (hrigid : Subsingleton (P ≃o P))
    (σ : P → P) (hmono : Monotone σ) (Θ : EndP P ≃o EndP P)
    (hΘ : ∀ q : P, JoinIrred P q → Θ (constHom q) = constHom (σ q))
    {q : P} (hq : JoinIrred P q) : σ q = q := by
  classical
  set S : P → Finset P :=
    fun x => Finset.univ.filter (fun r : P => JoinIrred P r ∧ r ≤ x) with hS
  set φ : P → P := fun x => (S x).sup σ with hφ
  -- `Θ ∘ constHom = constHom ∘ φ`
  have hcon : ∀ x : P, Θ (constHom x) = constHom (φ x) := by
    intro x
    have h1 : (constHom x : EndP P) = (S x).sup (fun r => (constHom r : EndP P)) := by
      conv_lhs => rw [finite_lattice_eq_sup_joinIrreds x]
      exact constHom_finset_sup (S x) id
    rw [h1, orderIso_finset_sup Θ (S x) (fun r => (constHom r : EndP P))]
    rw [hφ]
    rw [constHom_finset_sup (S x) σ]
    exact Finset.sup_congr rfl
      (fun r hr => hΘ r (Finset.mem_filter.mp hr).2.1)
  -- `φ` is a monotone injection, hence the identity
  have hφmono : Monotone φ := by
    intro x y hxy
    refine Finset.sup_mono ?_
    intro r hr
    obtain ⟨-, hji, hrx⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hji, hrx.trans hxy⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have : Θ (constHom x) = Θ (constHom y) := by rw [hcon, hcon, hxy]
    exact constHom_injective (Θ.injective this)
  have hid : φ = id :=
    MonotoneInjectionRigid.eq_id_of_rigid hrigid hφmono hφinj
  -- and at a join-irreducible `φ` is `σ`
  have hqmem : q ∈ S q := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq, le_refl q⟩
  have hφq : φ q = σ q := by
    refine le_antisymm (Finset.sup_le ?_) (Finset.le_sup (f := σ) hqmem)
    intro r hr
    exact hmono (Finset.mem_filter.mp hr).2.2
  have := congrFun hid q
  rw [hφq] at this
  simpa using this

/-- The packaged form: a threshold-preserving automorphism of `EndP P` over a
rigid base fixes every constant. -/
theorem fixes_constHom_of_rigid (hrigid : Subsingleton (P ≃o P))
    (σ : P → P) (hmono : Monotone σ) (Θ : EndP P ≃o EndP P)
    (hΘ : ∀ q : P, JoinIrred P q → Θ (constHom q) = constHom (σ q))
    (q : P) (hq : JoinIrred P q) : Θ (constHom q) = constHom q := by
  rw [hΘ q hq, sigma_eq_id_of_rigid hrigid σ hmono Θ hΘ hq]

end EndP

end JoinIrredRigidity
