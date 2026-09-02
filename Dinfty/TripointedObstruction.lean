import Dinfty.SierpinskiApplication

open GluingTowerLibrary SierpinskiApplication

-- [D-1304] §Obstruction-T-the-gluing-tower-s-connecting-map
namespace TripointedObstruction

section General

variable {X Y : Type*} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]

-- [D-1305] iota_top_of_topExact_natural
theorem iota_top_of_topExact_natural
    (iota : X → Y) (G : EndP X → EndP Y)
    (hGtop : G ⊤ = ⊤)
    (hnat : ∀ x : X, G (constHom x) = constHom (iota x)) :
    iota (⊤ : X) = (⊤ : Y) := by
  have h1 : G (constHom (⊤ : X)) = (⊤ : EndP Y) := by
    rw [← endP_top_eq_constHom_top]; exact hGtop
  rw [hnat] at h1
  have h2 := congrArg (fun f : EndP Y => f (⊤ : Y)) h1
  simpa using h2

-- [D-1306] le_iota_top_of_monotone_of_idExact
omit [BoundedOrder Y] in
theorem le_iota_top_of_monotone_of_idExact
    (iota : X → Y) (G : EndP X → EndP Y)
    (hmono : Monotone G)
    (hGid : G OrderHom.id = OrderHom.id)
    (hnat : ∀ x : X, G (constHom x) = constHom (iota x)) :
    ∀ z : Y, z ≤ iota (⊤ : X) := by
  have hle : (OrderHom.id : EndP X) ≤ constHom (⊤ : X) := fun _ => le_top
  have h := hmono hle
  rw [hGid, hnat] at h
  intro z
  simpa using h z

end General

-- [D-1307] no_topExact_natural_action_over_tower
theorem no_topExact_natural_action_over_tower (k : ℕ)
    (G : EndP (D k) → EndP (D (k + 1)))
    (hGtop : G ⊤ = ⊤)
    (hnat : ∀ x : D k, G (constHom x) = constHom (iotaD k x)) : False := by
  have hne := iotaD_ne_top k (⊤ : D k)
  exact hne (iota_top_of_topExact_natural (iotaD k) G hGtop hnat)

-- [D-1308] no_monotone_idExact_natural_action_over_tower
theorem no_monotone_idExact_natural_action_over_tower (k : ℕ)
    (G : EndP (D k) → EndP (D (k + 1)))
    (hmono : Monotone G)
    (hGid : G OrderHom.id = OrderHom.id)
    (hnat : ∀ x : D k, G (constHom x) = constHom (iotaD k x)) : False := by
  have hne := iotaD_ne_top k (⊤ : D k)
  exact hne (top_le_iff.mp
    (le_iota_top_of_monotone_of_idExact (iotaD k) G hmono hGid hnat
      (⊤ : D (k + 1))))

end TripointedObstruction
