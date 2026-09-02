import Dinfty.CopyBCStructure
import Dinfty.CopyBExclusion

open GluingTowerLibrary SierpinskiApplication

-- [D-1979] §The-79-scoping-note-made-a-theorem-both-liftGenM
open scoped Classical

universe u v

namespace JoinPrimality

open CopyBCStructure CopyBExclusion

-- [D-1980] §The-notion
-- [D-1981] JoinPrime
def JoinPrime {P : Type u} [SemilatticeSup P] (x : P) : Prop :=
  ∀ a b : P, x ≤ a ⊔ b → x ≤ a ∨ x ≤ b

-- [D-1982] joinPrime_of_total
theorem joinPrime_of_total {P : Type u} [SemilatticeSup P]
    (htot : ∀ a b : P, a ≤ b ∨ b ≤ a) (x : P) : JoinPrime x := by
  intro a b h
  rcases htot a b with hab | hab
  · exact Or.inr (by rwa [sup_eq_right.mpr hab] at h)
  · exact Or.inl (by rwa [sup_eq_left.mpr hab] at h)

-- [D-1983] §is-join-prime-whenever-the-coatom-is-unique
-- [D-1984] top_joinPrime
theorem top_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [UniqueAtomCoatom P] :
    JoinPrime (⊤ : P) := by
  intro a b h
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have ha : a ≠ (⊤ : P) := fun hh => h1 (le_of_eq hh.symm)
  have hb : b ≠ (⊤ : P) := fun hh => h2 (le_of_eq hh.symm)
  have hsup : a ⊔ b ≤ coatomOf P := sup_le (coatomOf_le ha) (coatomOf_le hb)
  exact coatomOf_ne_top P (top_le_iff.mp (h.trans hsup))

-- [D-1985] §Constants
-- [D-1986] constHom_joinPrime
theorem constHom_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P]
    [DecidableEq P] {c : P} (hc : JoinPrime c) : JoinPrime (constHom c : EndP P) := by
  intro f g h
  have h0 : c ≤ f (⊥ : P) ⊔ g (⊥ : P) := by
    have h1 := OrderHom.le_def.mp h (⊥ : P)
    simpa only [constHom_apply, OrderHom.coe_sup, Pi.sup_apply] using h1
  rcases hc _ _ h0 with h1 | h1
  · refine Or.inl ?_
    rw [OrderHom.le_def]
    intro x
    exact le_trans h1 (f.monotone bot_le)
  · refine Or.inr ?_
    rw [OrderHom.le_def]
    intro x
    exact le_trans h1 (g.monotone bot_le)

-- [D-1987] top_endP_joinPrime
theorem top_endP_joinPrime {P : Type u} [Lattice P] [BoundedOrder P] [Fintype P]
    [DecidableEq P] (hP : JoinPrime (⊤ : P)) : JoinPrime (⊤ : EndP P) := by
  rw [endP_top_eq_constHom_top]
  exact constHom_joinPrime hP

-- [D-1988] §The-inductive-step-at-the-tower
-- [D-1989] dMid_succ_joinPrime
set_option maxHeartbeats 1000000 in
theorem dMid_succ_joinPrime (k : ℕ) (h : JoinPrime (markedPt k)) :
    JoinPrime (dMid (k + 1)) := by
  have hmk : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
  intro a b hab
  rcases dSuccCases k a with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, hxm, rfl⟩
  · rcases dSuccCases k b with ⟨v, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, hym, rfl⟩
    · have hub : (glueA (markedPt k) u ⊔ glueA (markedPt k) v : D (k + 1))
          ≤ glueA (markedPt k) (u ⊔ v) :=
        sup_le ((glueA_le_iff (markedPt k) hmk u (u ⊔ v)).mpr le_sup_left)
          ((glueA_le_iff (markedPt k) hmk v (u ⊔ v)).mpr le_sup_right)
      rw [dMid_eq_glueA k] at hab
      have hm : markedPt k ≤ u ⊔ v :=
        (glueA_le_iff (markedPt k) hmk (markedPt k) (u ⊔ v)).mp (hab.trans hub)
      rcases h u v hm with h1 | h1
      · exact Or.inl (by
          rw [dMid_eq_glueA k]
          exact (glueA_le_iff (markedPt k) hmk (markedPt k) u).mpr h1)
      · exact Or.inr (by
          rw [dMid_eq_glueA k]
          exact (glueA_le_iff (markedPt k) hmk (markedPt k) v).mpr h1)
    · exact Or.inr (dMid_le_glueB k hy)
    · exact Or.inr (dMid_le_glueC k hy hym)
  · exact Or.inl (dMid_le_glueB k hx)
  · exact Or.inl (dMid_le_glueC k hx hxm)

-- [D-1990] dMid_zero_joinPrime
theorem dMid_zero_joinPrime : JoinPrime (dMid 0) := by
  refine joinPrime_of_total ?_ _
  intro a b
  have htot : ∀ x y : Fin 3, x ≤ y ∨ y ≤ x := fun x y => le_total x y
  exact htot a b

-- [D-1991] dMid_joinPrime
theorem dMid_joinPrime : ∀ k : ℕ, JoinPrime (dMid k)
  | 0 => dMid_zero_joinPrime
  | k + 1 => dMid_succ_joinPrime k (constHom_joinPrime (dMid_joinPrime k))

-- [D-1992] markedPt_joinPrime
theorem markedPt_joinPrime (k : ℕ) : JoinPrime (markedPt k) :=
  constHom_joinPrime (dMid_joinPrime k)

-- [D-1993] top_D_joinPrime
theorem top_D_joinPrime (k : ℕ) : JoinPrime (⊤ : D k) := by
  letI := realUniqueAtomCoatom k
  exact top_joinPrime

-- [D-1994] top_endP_D_joinPrime
theorem top_endP_D_joinPrime (k : ℕ) : JoinPrime (⊤ : EndP (D k)) :=
  top_endP_joinPrime (top_D_joinPrime k)

-- [D-1995] §What-join-primality-buys
-- [D-1996] ite_threshold_sup
theorem ite_threshold_sup {P : Type u} {Q : Type v} [SemilatticeSup P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] [SemilatticeSup Q] [OrderBot Q]
    {t : P} (ht : JoinPrime t) (K : Q) (f g : P) :
    (if t ≤ f ⊔ g then K else ⊥) = (if t ≤ f then K else ⊥) ⊔ (if t ≤ g then K else ⊥) := by
  by_cases hf : t ≤ f
  · rw [if_pos hf, if_pos (le_trans hf le_sup_left)]
    by_cases hg : t ≤ g
    · rw [if_pos hg, sup_idem]
    · rw [if_neg hg, sup_bot_eq]
  · rw [if_neg hf]
    by_cases hg : t ≤ g
    · rw [if_pos hg, if_pos (le_trans hg le_sup_right), bot_sup_eq]
    · rw [if_neg hg, sup_bot_eq]
      refine if_neg (fun hcon => ?_)
      rcases ht f g hcon with h1 | h1
      · exact hf h1
      · exact hg h1

-- [D-1997] markedPt_ite_sup
theorem markedPt_ite_sup {Q : Type v} [SemilatticeSup Q] [OrderBot Q]
    (k : ℕ) (K : Q) (f g : EndP (D k)) :
    (if markedPt k ≤ f ⊔ g then K else ⊥)
      = (if markedPt k ≤ f then K else ⊥) ⊔ (if markedPt k ≤ g then K else ⊥) :=
  ite_threshold_sup (markedPt_joinPrime k) K f g

-- [D-1998] top_ite_sup
theorem top_ite_sup {Q : Type v} [SemilatticeSup Q] [OrderBot Q]
    (k : ℕ) (K : Q) (f g : EndP (D k)) :
    (if (⊤ : EndP (D k)) ≤ f ⊔ g then K else ⊥)
      = (if (⊤ : EndP (D k)) ≤ f then K else ⊥) ⊔ (if (⊤ : EndP (D k)) ≤ g then K else ⊥) :=
  ite_threshold_sup (top_endP_D_joinPrime k) K f g

-- [D-1999] §Both-ingredients-of-glueAA-preserve-binary-joins
-- [D-2000] iotaD_sup
theorem iotaD_sup (k : ℕ) (a b : D k) : iotaD k (a ⊔ b) = iotaD k a ⊔ iotaD k b := by
  have hmk : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
  have hmtk : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
  have hbtk : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2
  show glueA (markedPt k) (constHom (a ⊔ b)) = _
  rw [← constHom_sup]
  exact (glueA_sup (markedPt k) hmk hmtk hbtk (constHom a) (constHom b)).symm

-- [D-2001] iotaEndP_sup
theorem iotaEndP_sup (k : ℕ) (f g : EndP (D k)) :
    iotaEndP k (f ⊔ g) = iotaEndP k f ⊔ iotaEndP k g := by
  ext w
  show iotaD k ((f ⊔ g) (pD k w)) = (iotaEndP k f ⊔ iotaEndP k g) w
  simp only [OrderHom.coe_sup, Pi.sup_apply]
  exact iotaD_sup k (f (pD k w)) (g (pD k w))

-- [D-2002] liftVal
noncomputable def liftVal (k : ℕ) (f : EndP (D k)) (w : D (k + 1)) : D (k + 1) :=
  (liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f) w

-- [D-2003] liftVal_sup
set_option maxHeartbeats 2000000 in

theorem liftVal_sup (k : ℕ) (f g : EndP (D k)) (w : D (k + 1)) :
    liftVal k (f ⊔ g) w = liftVal k f w ⊔ liftVal k g w := by
  have hval : ∀ h : EndP (D k), liftVal k h w
      = iotaD k (h (pD k w))
        ⊔ (if (constHom (dMid k) : EndP (D k)) ≤ h then dMid (k + 1) else (⊥ : D (k + 1)))
        ⊔ (if (⊤ : EndP (D k)) ≤ h then (⊤ : D (k + 1)) else (⊥ : D (k + 1))) := fun h =>
    liftGenM_apply (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial h w
  have hI : iotaD k ((f ⊔ g) (pD k w))
      = iotaD k (f (pD k w)) ⊔ iotaD k (g (pD k w)) := by
    simp only [OrderHom.coe_sup, Pi.sup_apply]
    exact iotaD_sup k (f (pD k w)) (g (pD k w))
  have hC : (if (constHom (dMid k) : EndP (D k)) ≤ f ⊔ g then dMid (k + 1)
        else (⊥ : D (k + 1)))
      = (if (constHom (dMid k) : EndP (D k)) ≤ f then dMid (k + 1) else (⊥ : D (k + 1)))
        ⊔ (if (constHom (dMid k) : EndP (D k)) ≤ g then dMid (k + 1)
            else (⊥ : D (k + 1))) :=
    ite_threshold_sup (markedPt_joinPrime k) _ f g
  have hT : (if (⊤ : EndP (D k)) ≤ f ⊔ g then (⊤ : D (k + 1)) else (⊥ : D (k + 1)))
      = (if (⊤ : EndP (D k)) ≤ f then (⊤ : D (k + 1)) else (⊥ : D (k + 1)))
        ⊔ (if (⊤ : EndP (D k)) ≤ g then (⊤ : D (k + 1)) else (⊥ : D (k + 1))) :=
    ite_threshold_sup (top_endP_D_joinPrime k) _ f g
  rw [hval (f ⊔ g), hval f, hval g, hI, hC, hT]
  ac_rfl

-- [D-2004] glueAA_ingredients_sup
theorem glueAA_ingredients_sup (k : ℕ) (f g : EndP (D k)) :
    iotaEndP k (f ⊔ g) = iotaEndP k f ⊔ iotaEndP k g
      ∧ ∀ w : D (k + 1), liftVal k (f ⊔ g) w = liftVal k f w ⊔ liftVal k g w :=
  ⟨iotaEndP_sup k f g, liftVal_sup k f g⟩

end JoinPrimality
