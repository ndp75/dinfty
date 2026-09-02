import Dinfty.JoinIrredRigidity

open GluingTowerLibrary SierpinskiApplication

-- [D-2015] §EndP-P-is-rigid-whenever-P-is-CONJ-was-already
open scoped Classical

universe u

namespace EndPRigid

open JoinIrredRigidity

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
variable [UniqueAtomCoatom P] [Nonempty {x : P // JoinIrred P x}]

-- [D-2016] jiRestrict
noncomputable def jiRestrict (Θ : EndP P ≃o EndP P) :
    {f : EndP P // JoinIrred (EndP P) f} ≃ {f : EndP P // JoinIrred (EndP P) f} where
  toFun x := ⟨Θ x.1, joinIrred_orderIso Θ x.2⟩
  invFun x := ⟨Θ.symm x.1, joinIrred_orderIso Θ.symm x.2⟩
  left_inv x := Subtype.ext (Θ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (Θ.apply_symm_apply x.1)

-- [D-2017] jiRestrict_ord
theorem jiRestrict_ord (Θ : EndP P ≃o EndP P)
    (v w : {f : EndP P // JoinIrred (EndP P) f}) :
    v ≤ w ↔ jiRestrict Θ v ≤ jiRestrict Θ w :=
  (Θ.map_rel_iff (a := v.1) (b := w.1)).symm

-- [D-2018] endP_rigid
theorem endP_rigid [Fintype (EndP P)] [DecidableEq (EndP P)]
    (hrigid : Subsingleton (P ≃o P)) :
    Subsingleton (EndP P ≃o EndP P) := by
  classical
  refine ⟨fun Θ Θ' => ?_⟩
  suffices h : ∀ Ξ : EndP P ≃o EndP P, Ξ = OrderIso.refl (EndP P) by
    rw [h Θ, h Θ']
  intro Ξ
  obtain ⟨γA, γB, hγA, hγB, hsplit⟩ :=
    jh_free (P := P) (jiRestrict Ξ) (jiRestrict_ord Ξ)
  have hγAid : ∀ a : P, γA a = a := by
    intro a
    have h : (⟨γA, fun {a b} => (hγA a b).symm⟩ : P ≃o P) = OrderIso.refl P :=
      hrigid.elim _ _
    exact congrArg (fun e : P ≃o P => e a) h
  have hconst : ∀ q : {x : P // JoinIrred P x},
      Ξ (constHom q.1) = constHom (γB q).1 := by
    intro q
    have h := congrArg Subtype.val (hsplit ((⊥ : P), q))
    simp only [jiRestrict, Equiv.coe_fn_mk] at h
    rw [hγAid ⊥] at h
    have hsb : ∀ x : P, (stepMap x (⊥ : P) : EndP P) = constHom x := by
      intro x
      apply OrderHom.ext
      funext y
      exact stepMap_apply_of_ge x (⊥ : P) bot_le
    have e1 : (jiEquiv ((⊥ : P), q)).1 = constHom q.1 := hsb q.1
    have e2 : (jiEquiv ((⊥ : P), γB q)).1 = constHom (γB q).1 := hsb (γB q).1
    rw [e1] at h
    rw [← e2]
    exact h
  set jext : P → P := fun r => if h : JoinIrred P r then (γB ⟨r, h⟩).1 else ⊥ with hjext
  set σ : P → P :=
    fun x => (Finset.univ.filter (fun r : P => JoinIrred P r ∧ r ≤ x)).sup jext with hσ
  have hσmono : Monotone σ := by
    intro x y hxy
    refine Finset.sup_mono ?_
    intro r hr
    obtain ⟨-, hji, hrx⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hji, hrx.trans hxy⟩
  have hσq : ∀ q : P, (hq : JoinIrred P q) → σ q = (γB ⟨q, hq⟩).1 := by
    intro q hq
    have hmem : q ∈ Finset.univ.filter (fun r : P => JoinIrred P r ∧ r ≤ q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq, le_refl q⟩
    refine le_antisymm (Finset.sup_le ?_) ?_
    · intro r hr
      obtain ⟨-, hji, hrq⟩ := Finset.mem_filter.mp hr
      have : jext r = (γB ⟨r, hji⟩).1 := by rw [hjext]; simp [hji]
      rw [this]
      exact (hγB ⟨r, hji⟩ ⟨q, hq⟩).mp hrq
    · have : jext q = (γB ⟨q, hq⟩).1 := by rw [hjext]; simp [hq]
      rw [← this]
      exact Finset.le_sup (f := jext) hmem
  have hΘσ : ∀ q : P, JoinIrred P q → Ξ (constHom q) = constHom (σ q) := by
    intro q hq
    rw [hσq q hq]
    exact hconst ⟨q, hq⟩
  have hγBid : ∀ q : {x : P // JoinIrred P x}, γB q = q := by
    intro q
    refine Subtype.ext ?_
    have := sigma_eq_id_of_rigid hrigid σ hσmono Ξ hΘσ q.2
    rw [hσq q.1 q.2] at this
    exact this
  refine eq_of_agree_on_joinIrred Ξ (OrderIso.refl (EndP P)) (fun f hf => ?_)
  obtain ⟨p, hp⟩ := jiEquiv.surjective (⟨f, hf⟩ : {f : EndP P // JoinIrred (EndP P) f})
  have hfv : (jiEquiv p).1 = f := congrArg Subtype.val hp
  have h := congrArg Subtype.val (hsplit p)
  simp only [jiRestrict, Equiv.coe_fn_mk] at h
  rw [hγAid p.1, hγBid p.2, hfv] at h
  simpa using h

end EndPRigid
