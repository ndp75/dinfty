import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

-- [D-2005] §Rigidity-through-the-join-irreducibles-the-half
open scoped Classical

universe u

namespace JoinIrredRigidity

-- [D-2006] §Order-isomorphisms-preserve-finite-sups
-- [D-2007] orderIso_finset_sup
theorem orderIso_finset_sup {α : Type*} {β γ : Type u} [Lattice β] [OrderBot β]
    [Lattice γ] [OrderBot γ] (e : β ≃o γ) (s : Finset α) (f : α → β) :
    e (s.sup f) = s.sup (fun x => e (f x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using e.map_bot
  | insert a s _ ih => rw [Finset.sup_insert, Finset.sup_insert, e.map_sup, ih]

-- [D-2008] §The-easy-half-of-Birkhoff
section Lattice

variable {P : Type u} [Lattice P] [OrderBot P] [Fintype P] [DecidableEq P]

-- [D-2009] eq_of_agree_on_joinIrred
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

-- [D-2010] eq_refl_of_fixes_joinIrred
theorem eq_refl_of_fixes_joinIrred (e : P ≃o P)
    (h : ∀ q : P, JoinIrred P q → e q = q) : e = OrderIso.refl P :=
  eq_of_agree_on_joinIrred e (OrderIso.refl P) h

end Lattice

-- [D-2011] §The-threshold-argument-at-EndP
section EndP

variable {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P] [DecidableEq P]

-- [D-2012] constHom_finset_sup
theorem constHom_finset_sup {α : Type*} (s : Finset α) (f : α → P) :
    (constHom (s.sup f) : EndP P) = s.sup (fun x => (constHom (f x) : EndP P)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constHom_bot_eq (L := P))
  | insert a s _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← constHom_sup, ih]

-- [D-2013] sigma_eq_id_of_rigid
theorem sigma_eq_id_of_rigid (hrigid : Subsingleton (P ≃o P))
    (σ : P → P) (hmono : Monotone σ) (Θ : EndP P ≃o EndP P)
    (hΘ : ∀ q : P, JoinIrred P q → Θ (constHom q) = constHom (σ q))
    {q : P} (hq : JoinIrred P q) : σ q = q := by
  classical
  set S : P → Finset P :=
    fun x => Finset.univ.filter (fun r : P => JoinIrred P r ∧ r ≤ x) with hS
  set φ : P → P := fun x => (S x).sup σ with hφ
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
  have hqmem : q ∈ S q := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq, le_refl q⟩
  have hφq : φ q = σ q := by
    refine le_antisymm (Finset.sup_le ?_) (Finset.le_sup (f := σ) hqmem)
    intro r hr
    exact hmono (Finset.mem_filter.mp hr).2.2
  have := congrFun hid q
  rw [hφq] at this
  simpa using this

-- [D-2014] fixes_constHom_of_rigid
theorem fixes_constHom_of_rigid (hrigid : Subsingleton (P ≃o P))
    (σ : P → P) (hmono : Monotone σ) (Θ : EndP P ≃o EndP P)
    (hΘ : ∀ q : P, JoinIrred P q → Θ (constHom q) = constHom (σ q))
    (q : P) (hq : JoinIrred P q) : Θ (constHom q) = constHom q := by
  rw [hΘ q hq, sigma_eq_id_of_rigid hrigid σ hmono Θ hΘ hq]

end EndP

end JoinIrredRigidity
