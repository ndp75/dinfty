import Dinfty.GenContinuityTransport

open GluingTowerLibrary SierpinskiApplication

-- [D-1516] §Gap-2-of-GenContinuity-the-mixed-variance-End
open scoped Classical

open Set

universe u v

namespace EndLocalContinuity

-- [D-1517] §The-mixed-variance-core
section MixedVariance

variable {ι : Type v} [Nonempty ι]
variable {X Y Z W : Type u} [Preorder X] [Preorder Y] [Preorder Z] [Preorder W]

-- [D-1518] comp_isLUB
theorem comp_isLUB
    (F : ι → X → Y) (G : ι → Z → W) (h : Y → Z) (fLim : X → Y) (gLim : Z → W)
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, F i x ≤ F k x) ∧ (∀ x, F j x ≤ F k x)
      ∧ (∀ z, G i z ≤ G k z) ∧ (∀ z, G j z ≤ G k z))
    (hF : ∀ x, IsLUB (Set.range fun i => F i x) (fLim x))
    (hG : ∀ z, IsLUB (Set.range fun i => G i z) (gLim z))
    (hh : ScottContinuous h) (hGc : ∀ i, ScottContinuous (G i)) (x : X) :
    IsLUB (Set.range fun i => G i (h (F i x))) (gLim (h (fLim x))) := by
  have hhm : Monotone h := hh.monotone
  have hGm : ∀ i, Monotone (G i) := fun i => (hGc i).monotone
  have hDne : (Set.range fun i => F i x).Nonempty :=
    ⟨F (Classical.arbitrary ι) x, ⟨_, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) (Set.range fun i => F i x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk, -, -⟩ := hdir i j
    exact ⟨F k x, ⟨k, rfl⟩, hik x, hjk x⟩
  have hhD : IsLUB (h '' Set.range fun i => F i x) (h (fLim x)) := hh hDne hDdir (hF x)
  have hhDne : (h '' Set.range fun i => F i x).Nonempty := hDne.image h
  have hhDdir : DirectedOn (· ≤ ·) (h '' Set.range fun i => F i x) :=
    directedOn_image_of_monotone hhm hDdir
  constructor
  · rintro _ ⟨i, rfl⟩
    exact le_trans (hGm i (hhm ((hF x).1 ⟨i, rfl⟩))) ((hG (h (fLim x))).1 ⟨i, rfl⟩)
  · intro w hw
    refine (hG (h (fLim x))).2 ?_
    rintro _ ⟨j, rfl⟩
    have hjD : IsLUB (G j '' (h '' Set.range fun i => F i x)) (G j (h (fLim x))) :=
      hGc j hhDne hhDdir hhD
    refine hjD.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hy
    obtain ⟨k, hFik, -, -, hGjk⟩ := hdir i j
    calc G j (h (F i x)) ≤ G k (h (F i x)) := hGjk _
      _ ≤ G k (h (F k x)) := hGm k (hhm (hFik x))
      _ ≤ w := hw ⟨k, rfl⟩

-- [D-1519] deflation_isLUB
theorem deflation_isLUB {D : Type u} [Preorder D]
    (δ : ι → D → D) (dLim : D → D) (h : D → D)
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, δ i x ≤ δ k x) ∧ (∀ x, δ j x ≤ δ k x))
    (hδ : ∀ x, IsLUB (Set.range fun i => δ i x) (dLim x))
    (hh : ScottContinuous h) (hδc : ∀ i, ScottContinuous (δ i)) (x : D) :
    IsLUB (Set.range fun i => δ i (h (δ i x))) (dLim (h (dLim x))) :=
  comp_isLUB δ δ h dLim dLim
    (fun i j => by obtain ⟨k, h1, h2⟩ := hdir i j; exact ⟨k, h1, h2, h1, h2⟩)
    hδ hδ hh hδc x

end MixedVariance

-- [D-1520] §The-variance-fact-itself-machine-checked
section Variance

variable {A B : Type u} [PartialOrder A] [PartialOrder B]

-- [D-1521] ep_le_iff
theorem ep_le_iff (e e' : A →o B) (p p' : B →o A)
    (hpe : ∀ a, p (e a) = a) (hep : ∀ b, e (p b) ≤ b)
    (hpe' : ∀ a, p' (e' a) = a) (hep' : ∀ b, e' (p' b) ≤ b) :
    (∀ a, e a ≤ e' a) ↔ (∀ b, p' b ≤ p b) := by
  constructor
  · intro hee b
    calc p' b = p (e (p' b)) := (hpe (p' b)).symm
      _ ≤ p (e' (p' b)) := p.monotone (hee (p' b))
      _ ≤ p b := p.monotone (hep' b)
  · intro hpp a
    calc e a ≤ e (p (e' a)) := e.monotone (by simpa [hpe' a] using hpp (e' a))
      _ ≤ e' a := hep (e' a)

end Variance

-- [D-1522] §The-bridge-pointwise-suprema-are-hom-poset
section Bridge

variable {ι : Type v}
variable {X Y : Type u} [Preorder X] [PartialOrder Y]

-- [D-1523] isLUB_orderHom_of_pointwise
theorem isLUB_orderHom_of_pointwise (u : ι → (X →o Y)) (s : X →o Y)
    (h : ∀ x, IsLUB (Set.range fun i => (u i) x) (s x)) :
    IsLUB (Set.range u) s := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact OrderHom.le_def.mpr fun x => (h x).1 ⟨i, rfl⟩
  · intro w hw
    refine OrderHom.le_def.mpr fun x => (h x).2 ?_
    rintro _ ⟨i, rfl⟩
    exact OrderHom.le_def.mp (hw ⟨i, rfl⟩) x

end Bridge

-- [D-1524] §The-End-action-bundled
section EndAction

variable {ι : Type v} [Nonempty ι]
variable {D D' : Type u} [PartialOrder D] [PartialOrder D']

-- [D-1525] endHom
def endHom (e : D →o D') (p : D' →o D) : (D →o D) →o (D' →o D') where
  toFun h := e.comp (h.comp p)
  monotone' _ _ hab := OrderHom.le_def.mpr fun x => e.monotone (OrderHom.le_def.mp hab (p x))

-- [D-1526] endHom_apply
@[simp] theorem endHom_apply (e : D →o D') (p : D' →o D) (h : D →o D) (x : D') :
    endHom e p h x = e (h (p x)) := rfl

-- [D-1527] endHom_isLUB
theorem endHom_isLUB
    (e : ι → (D →o D')) (p : ι → (D' →o D)) (eLim : D →o D') (pLim : D' →o D)
    (h : D →o D) (gLim : D' →o D')
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, p i x ≤ p k x) ∧ (∀ x, p j x ≤ p k x)
      ∧ (∀ z, e i z ≤ e k z) ∧ (∀ z, e j z ≤ e k z))
    (hp : ∀ x, IsLUB (Set.range fun i => (p i) x) (pLim x))
    (he : ∀ z, IsLUB (Set.range fun i => (e i) z) (eLim z))
    (hh : ScottContinuous (h : D → D)) (hec : ∀ i, ScottContinuous ((e i : D → D')))
    (hgLim : ∀ x, gLim x = eLim (h (pLim x))) :
    IsLUB (Set.range fun i => endHom (e i) (p i) h) gLim := by
  refine isLUB_orderHom_of_pointwise _ _ (fun x => ?_)
  have := comp_isLUB (fun i => (p i : D' → D)) (fun i => (e i : D → D'))
    (h : D → D) (pLim : D' → D) (eLim : D → D') hdir hp he hh hec x
  simpa [hgLim x] using this

end EndAction

-- [D-1528] §The-half-in-GlueCarGen-and-the-composite
section PhiSide

open GenContinuity

variable {ι : Type v} [Nonempty ι]
variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

-- [D-1529] image_range_eq
theorem image_range_eq {α β γ : Type*} (f : α → β) (u : γ → α) :
    f '' (Set.range u) = Set.range fun i => f (u i) := by
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

-- [D-1530] baseMapGen_isLUB_tagA
theorem baseMapGen_isLUB_tagA (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagAGen m' ((g i) a)) (tagAGen m' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagAGen_isLUB m' hm' hmt' hbt' (hg a)
  rwa [image_range_eq] at hlub

-- [D-1531] baseMapGen_isLUB_tagB
theorem baseMapGen_isLUB_tagB (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P)
    (hb : ∀ i, (g i) a ≠ ⊥) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagBGen m' hm' hbt' ((g i) a))
      (tagBGen m' hm' hbt' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagBGen_isLUB m' hm' hmt' hbt' (hg a)
    ⟨(g (Classical.arbitrary ι)) a, ⟨_, rfl⟩⟩ (by rintro _ ⟨i, rfl⟩; exact hb i)
  rwa [image_range_eq] at hlub

-- [D-1532] baseMapGen_isLUB_tagC
theorem baseMapGen_isLUB_tagC (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P)
    (hb : ∀ i, (g i) a ≠ ⊥) (hm : ∀ i, (g i) a ≠ m') :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagCGen m' hm' hbt' ((g i) a))
      (tagCGen m' hm' hbt' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagCGen_isLUB m' hm' hmt' hbt' (hg a)
    ⟨(g (Classical.arbitrary ι)) a, ⟨_, rfl⟩⟩
    (by rintro _ ⟨i, rfl⟩; exact hb i) (by rintro _ ⟨i, rfl⟩; exact hm i)
  rwa [image_range_eq] at hlub

-- [D-1533] phiEnd_isLUB_tagA
theorem phiEnd_isLUB_tagA (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P →o P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagAGen m' ((g i) a)) (tagAGen m' (gLim a))
      ∧ IsLUB (Set.range g) gLim := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  exact ⟨baseMapGen_isLUB_tagA m' hm' hmt' hbt' g (gLim : P → P') hg a,
    isLUB_orderHom_of_pointwise g gLim hg⟩

end PhiSide

end EndLocalContinuity
