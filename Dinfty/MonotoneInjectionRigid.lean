import Dinfty.CopyBFreedom
import Mathlib.GroupTheory.OrderOfElement

open GluingTowerLibrary SierpinskiApplication

-- [D-1565] §On-a-finite-poset-a-monotone-injection
open scoped Classical

universe u

namespace MonotoneInjectionRigid

variable {Q : Type u} [PartialOrder Q] [Finite Q]

-- [D-1566] le_of_apply_le
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

-- [D-1567] orderIsoOfMonotoneInjective
noncomputable def orderIsoOfMonotoneInjective {f : Q → Q} (hmono : Monotone f)
    (hinj : Function.Injective f) : Q ≃o Q where
  toEquiv := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  map_rel_iff' := ⟨le_of_apply_le hmono hinj, fun h => hmono h⟩

-- [D-1568] orderIsoOfMonotoneInjective_apply
@[simp] theorem orderIsoOfMonotoneInjective_apply {f : Q → Q} (hmono : Monotone f)
    (hinj : Function.Injective f) (a : Q) :
    orderIsoOfMonotoneInjective hmono hinj a = f a := rfl

-- [D-1569] eq_id_of_rigid
theorem eq_id_of_rigid (hrigid : Subsingleton (Q ≃o Q)) {f : Q → Q}
    (hmono : Monotone f) (hinj : Function.Injective f) : f = id := by
  funext a
  have := congrArg (fun e : Q ≃o Q => e a)
    (hrigid.elim (orderIsoOfMonotoneInjective hmono hinj) (OrderIso.refl Q))
  simpa using this

end MonotoneInjectionRigid

-- [D-1570] §The-consequence-for-glueTwist
namespace CopyBFreedom

open MonotoneInjectionRigid

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P] [Finite P]

-- [D-1571] glueTwist_eq_baseMapGen_of_rigid
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

-- [D-1572] twist_trivial_of_rigid
theorem twist_trivial_of_rigid (hrigid : Subsingleton (P ≃o P)) (ψ : P →o P)
    (hpsi : Function.Injective ψ) : (ψ : P → P) = id :=
  eq_id_of_rigid hrigid ψ.monotone hpsi

end CopyBFreedom

-- [D-1573] §The-free-consequence-at-the-tower-D-all-rigid
namespace TowerRigidity

-- [D-1574] D_monotone_injection_eq_id
theorem D_monotone_injection_eq_id (k : ℕ) {f : D k → D k}
    (hmono : Monotone f) (hinj : Function.Injective f) : f = id :=
  MonotoneInjectionRigid.eq_id_of_rigid (D_all_rigid k) hmono hinj

-- [D-1575] D_orderHom_injection_eq_id
theorem D_orderHom_injection_eq_id (k : ℕ) (f : D k →o D k)
    (hinj : Function.Injective f) : (f : D k → D k) = id :=
  D_monotone_injection_eq_id k f.monotone hinj

end TowerRigidity
