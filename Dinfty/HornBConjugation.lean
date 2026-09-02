import Dinfty.TripointedObstruction

open GluingTowerLibrary SierpinskiApplication

-- [D-1309] §Horn-B-with-a-preserving-tower-map-conjugation
namespace HornB

variable {X Y : Type*} [Lattice X] [Lattice Y]

-- [D-1310] conj
def conj (iota : X →o Y) (p : Y →o X) (f : EndP X) : EndP Y :=
  iota.comp (f.comp p)

-- [D-1311] conj_apply
@[simp] theorem conj_apply (iota : X →o Y) (p : Y →o X) (f : EndP X) (z : Y) :
    conj iota p f z = iota (f (p z)) := rfl

-- [D-1312] conj_constHom
@[simp] theorem conj_constHom (iota : X →o Y) (p : Y →o X) (x : X) :
    conj iota p (constHom x) = constHom (iota x) := by
  ext z; simp [conj, constHom]

-- [D-1313] conj_bot
theorem conj_bot [OrderBot X] [OrderBot Y]
    (iota : X →o Y) (p : Y →o X) (h : iota ⊥ = (⊥ : Y)) :
    conj iota p ⊥ = (⊥ : EndP Y) := by
  ext z; simp [conj, h]

-- [D-1314] conj_top
theorem conj_top [OrderTop X] [OrderTop Y]
    (iota : X →o Y) (p : Y →o X) (h : iota ⊤ = (⊤ : Y)) :
    conj iota p ⊤ = (⊤ : EndP Y) := by
  ext z; simp [conj, h]

-- [D-1315] conj_monotone
theorem conj_monotone (iota : X →o Y) (p : Y →o X) :
    Monotone (conj iota p) := by
  intro f g hfg z
  exact iota.monotone (hfg (p z))

-- [D-1316] conj_le_reflect
theorem conj_le_reflect (iota : X →o Y) (p : Y →o X)
    (hsec : ∀ x : X, p (iota x) = x) (f g : EndP X)
    (h : conj iota p f ≤ conj iota p g) : f ≤ g := by
  intro x
  have hx := h (iota x)
  simp only [conj_apply, hsec] at hx
  have hpx := p.monotone hx
  rwa [hsec, hsec] at hpx

-- [D-1317] conj_sup
theorem conj_sup (iota : X →o Y) (p : Y →o X)
    (hjoin : ∀ a b : X, iota (a ⊔ b) = iota a ⊔ iota b) (f g : EndP X) :
    conj iota p (f ⊔ g) = conj iota p f ⊔ conj iota p g := by
  ext z; simp [conj, hjoin]

section Tripointed

variable {X Y : Type*} [Lattice X] [Lattice Y]

-- [D-1318] conj_tripointed
theorem conj_tripointed (iota : X →o Y) (p : Y →o X) (T L R : X) (T' L' R' : Y)
    (hT : iota T = T') (hL : iota L = L') (hR : iota R = R') :
    conj iota p (constHom T) = constHom T' ∧
    conj iota p (constHom L) = constHom L' ∧
    conj iota p (constHom R) = constHom R' :=
  ⟨by rw [conj_constHom, hT], by rw [conj_constHom, hL], by rw [conj_constHom, hR]⟩

-- [D-1319] conj_id_eq_id_iff
theorem conj_id_eq_id_iff (iota : X →o Y) (p : Y →o X) :
    conj iota p OrderHom.id = OrderHom.id ↔ ∀ z : Y, iota (p z) = z := by
  constructor
  · intro h z; exact congrArg (fun f : EndP Y => f z) h
  · intro h; ext z; exact h z

end Tripointed

end HornB
