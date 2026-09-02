import Dinfty.JinfReduction

open GluingTowerLibrary SierpinskiApplication

-- [D-1706] §The-two-points-differ-only-in-a-seed
open scoped Classical

namespace SeedContrast

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor TwoPointHypothesis JinfReduction

section General

variable {P : Type*} [Lattice P] [BoundedOrder P]

-- [D-1707] endP_le_constHom_iff
theorem endP_le_constHom_iff (f : EndP P) (c : P) :
    f ≤ (constHom c : EndP P) ↔ f ⊤ ≤ c := by
  constructor
  · intro h
    have := (OrderHom.le_def.mp h) (⊤ : P)
    rwa [constHom_apply] at this
  · intro h
    rw [OrderHom.le_def]
    intro y
    rw [constHom_apply]
    exact le_trans (f.monotone le_top) h

end General

section Step

variable {P : Type*} [DecidableEq P] [Lattice P] [BoundedOrder P] [Fintype P]

-- [D-1708] stepMap_le_constHom_iff
theorem stepMap_le_constHom_iff (x q c : P) :
    (stepMap x q : EndP P) ≤ constHom c ↔ x ≤ c := by
  rw [endP_le_constHom_iff]
  rw [stepMap_apply_of_ge x q (le_top : q ≤ (⊤ : P))]

-- [D-1709] jiEndP_below_constHom
theorem jiEndP_below_constHom (c : P) :
    {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom c}
      = {f : EndP P | ∃ x q : P, JoinIrred P x ∧ x ≤ c ∧ f = stepMap x q} := by
  ext f
  constructor
  · rintro ⟨hji, hle⟩
    obtain ⟨x, q, hx, rfl⟩ := (joinIrred_endP_iff_exists_stepMap f).mp hji
    exact ⟨x, q, hx, (stepMap_le_constHom_iff x q c).mp hle, rfl⟩
  · rintro ⟨x, q, hx, hxc, rfl⟩
    exact ⟨(joinIrred_endP_iff_exists_stepMap _).mpr ⟨x, q, hx, rfl⟩,
           (stepMap_le_constHom_iff x q c).mpr hxc⟩

-- [D-1710] stepMap_param_inj
theorem stepMap_param_inj {x x' q q' : P} (hx : JoinIrred P x) (hx' : JoinIrred P x')
    (h : (stepMap x q : EndP P) = stepMap x' q') : x = x' ∧ q = q' :=
  stepMap_inj_of_ne_bot hx.1 hx'.1 h

-- [D-1711] jiEndP_below_constHom_congr
theorem jiEndP_below_constHom_congr (c d : P)
    (h : ∀ x : P, JoinIrred P x → (x ≤ c ↔ x ≤ d)) :
    {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom c}
      = {f : EndP P | JoinIrred (EndP P) f ∧ f ≤ constHom d} := by
  rw [jiEndP_below_constHom, jiEndP_below_constHom]
  ext f
  constructor
  · rintro ⟨x, q, hx, hxc, rfl⟩; exact ⟨x, q, hx, (h x hx).mp hxc, rfl⟩
  · rintro ⟨x, q, hx, hxd, rfl⟩; exact ⟨x, q, hx, (h x hx).mpr hxd, rfl⟩

end Step

-- [D-1712] §The-two-seeds-at-level-0
-- [D-1713] joinIrred_fin3_iff
theorem joinIrred_fin3_iff (x : Fin 3) : JoinIrred (Fin 3) x ↔ (x = 1 ∨ x = 2) := by
  constructor
  · intro h
    fin_cases x
    · exact absurd (by decide : (0 : Fin 3) = ⊥) h.1
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩

-- [D-1714] seed_mid
theorem seed_mid (x : Fin 3) :
    (JoinIrred (Fin 3) x ∧ x ≤ (1 : Fin 3)) ↔ x = 1 := by
  rw [joinIrred_fin3_iff]
  constructor
  · rintro ⟨rfl | rfl, hle⟩
    · rfl
    · exact absurd hle (by decide)
  · rintro rfl
    exact ⟨Or.inl rfl, le_rfl⟩

-- [D-1715] seed_top
theorem seed_top (x : Fin 3) :
    (JoinIrred (Fin 3) x ∧ x ≤ (2 : Fin 3)) ↔ (x = 1 ∨ x = 2) := by
  rw [joinIrred_fin3_iff]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr rfl, le_rfl⟩

-- [D-1716] seeds_differ
theorem seeds_differ :
    ¬ (∀ x : Fin 3, (JoinIrred (Fin 3) x ∧ x ≤ (1 : Fin 3))
        ↔ (JoinIrred (Fin 3) x ∧ x ≤ (2 : Fin 3))) := by
  intro h
  have h2 := (h 2).mpr ⟨(joinIrred_fin3_iff 2).mpr (Or.inr rfl), le_rfl⟩
  exact absurd h2.2 (by decide)

end SeedContrast
