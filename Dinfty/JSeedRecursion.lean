import Dinfty.AtomFactorGeneration
import Dinfty.GluingTowerLibrary

open GluingTowerLibrary

-- [D-1506] §The-seed-recursion-machine-checked
open scoped Classical

universe u v

namespace JSeedRecursion

-- [D-1507] §Two-general-facts
-- [D-1508] downSetIso
def downSetIso {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
    (e : X ≃o Y) (x : X) : {u : X // u ≤ x} ≃o {v : Y // v ≤ e x} where
  toFun u := ⟨e u.1, e.monotone u.2⟩
  invFun v := ⟨e.symm v.1, by
    have h := e.symm.monotone v.2
    rwa [e.symm_apply_apply] at h⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.1)
  right_inv v := Subtype.ext (e.apply_symm_apply v.1)
  map_rel_iff' := e.map_rel_iff

-- [D-1509] prodDownSetIso
def prodDownSetIso {A : Type u} {B : Type u} [Preorder A] [Preorder B] (p : A × B) :
    {u : A × B // u ≤ p} ≃o ({a : A // a ≤ p.1} × {b : B // b ≤ p.2}) where
  toFun u := (⟨u.1.1, u.2.1⟩, ⟨u.1.2, u.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv w := rfl
  map_rel_iff' := Iff.rfl

-- [D-1510] prodCongrIso
def prodCongrIso {A A' B B' : Type u} [Preorder A] [Preorder A'] [Preorder B]
    [Preorder B'] (e : A ≃o A') (f : B ≃o B') : (A × B) ≃o (A' × B') where
  toFun p := (e p.1, f p.2)
  invFun p := (e.symm p.1, f.symm p.2)
  left_inv p := Prod.ext (e.symm_apply_apply p.1) (f.symm_apply_apply p.2)
  right_inv p := Prod.ext (e.apply_symm_apply p.1) (f.apply_symm_apply p.2)
  map_rel_iff' := by
    intro p q
    exact ⟨fun h => ⟨e.le_iff_le.mp h.1, f.le_iff_le.mp h.2⟩,
           fun h => ⟨e.monotone h.1, f.monotone h.2⟩⟩

-- [D-1511] §The-recursion
section Seed

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
variable [UniqueAtomCoatom P]

-- [D-1512] jSeedIso
noncomputable def jSeedIso (a : Pᵒᵈ) (q : {x : P // JoinIrred P x}) :
    {g : {f : EndP P // JoinIrred (EndP P) f} // g ≤ jiOrderIso (a, q)}
      ≃o ({a' : Pᵒᵈ // a' ≤ a} × {b : {x : P // JoinIrred P x} // b ≤ q}) :=
  (downSetIso jiOrderIso (a, q)).symm.trans (prodDownSetIso ((a, q) : Pᵒᵈ × _))

-- [D-1513] downSet_toDual_bot
def downSet_toDual_bot : {a' : Pᵒᵈ // a' ≤ OrderDual.toDual (⊥ : P)} ≃o Pᵒᵈ where
  toFun a := a.1
  invFun a := ⟨a, by
    show (⊥ : P) ≤ OrderDual.ofDual a
    exact bot_le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

-- [D-1514] jSeedIso_bot
noncomputable def jSeedIso_bot (q : {x : P // JoinIrred P x}) :
    {g : {f : EndP P // JoinIrred (EndP P) f} //
        g ≤ jiOrderIso (OrderDual.toDual (⊥ : P), q)}
      ≃o (Pᵒᵈ × {b : {x : P // JoinIrred P x} // b ≤ q}) :=
  (jSeedIso (OrderDual.toDual (⊥ : P)) q).trans
    (prodCongrIso downSet_toDual_bot (OrderIso.refl _))

-- [D-1515] downSet_ne_univ_of_ne_bot
theorem downSet_ne_univ_of_ne_bot {p : P} (hp : p ≠ ⊥) :
    ¬ ∀ a' : Pᵒᵈ, a' ≤ OrderDual.toDual p := by
  intro h
  have h1 : p ≤ (⊥ : P) := h (OrderDual.toDual (⊥ : P))
  exact hp (le_bot_iff.mp h1)

end Seed

end JSeedRecursion
