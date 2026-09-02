import Dinfty.JoinIrredRigidity

open GluingTowerLibrary SierpinskiApplication

/-!
# `EndP P` is rigid whenever `P` is — CONJ′ was already a theorem

§73 named **CONJ′** — "every automorphism of `Pᵒᵈ × J(P)` is a product map, no
coordinate mixing" — as the one open statement standing between the level-2
rigidity computation and a uniform result, and tested it on eleven small
lattices.

**That was a rediscovery.**  CONJ′ is `GluingTowerLibrary.jh_free`, which has
been in this project since the Sabidussi/Vizing axiom was retired: it takes an
order-automorphism of `J(EndP P)`, conjugates it onto `Pᵒᵈ × J(P)`, and splits it
with `ProdAut.prod_decomposition_of_card` — whose hypotheses are a unique atom in
`Pᵒᵈ` (`UniqueAtomCoatom`) and the cardinality gap
`0 < |J(P)| < |P|` (`card_joinIrred_lt`, unconditional).  Nothing is assumed.

So the chain closes with no open statement in it:

```
P rigid  +  UniqueAtomCoatom P
   ⟹ [jh_free]              every automorphism of J(EndP P) is γ_A × γ_B
   ⟹ [P rigid]              γ_A = id, so thresholds are preserved
   ⟹ [sigma_eq_id_of_rigid] γ_B = id
   ⟹ [eq_of_agree_on_joinIrred]  the automorphism of EndP P is the identity
```

`endP_rigid` below.  The level-1 and level-2 computations
(`_archive/check_endp_D0_automorphisms.py`,
`_archive/check_endp_D1_rigidity_threshold.py`) now read as *corroboration* of a
theorem rather than as its evidence — and the eleven-lattice sweep of §73 reads
as a check that `jh_free`'s hypotheses are the right ones.

## The lesson, for the third time

`TowerInstantiation`'s own docstring says it: *"Eleventh instance in this project
of a result that already existed.  Grep the library before proving anything
general about `jiEquiv` or the order on step maps."*  §72 and §73 are the twelfth
and thirteenth.  The library is 27k lines; **grep it before naming something
open.**
-/

open scoped Classical

universe u

namespace EndPRigid

open JoinIrredRigidity

variable {P : Type u} [Fintype P] [DecidableEq P] [Lattice P] [BoundedOrder P]
variable [UniqueAtomCoatom P] [Nonempty {x : P // JoinIrred P x}]

/-- An order-automorphism of `EndP P` restricts to the join-irreducibles. -/
noncomputable def jiRestrict (Θ : EndP P ≃o EndP P) :
    {f : EndP P // JoinIrred (EndP P) f} ≃ {f : EndP P // JoinIrred (EndP P) f} where
  toFun x := ⟨Θ x.1, joinIrred_orderIso Θ x.2⟩
  invFun x := ⟨Θ.symm x.1, joinIrred_orderIso Θ.symm x.2⟩
  left_inv x := Subtype.ext (Θ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (Θ.apply_symm_apply x.1)

theorem jiRestrict_ord (Θ : EndP P ≃o EndP P)
    (v w : {f : EndP P // JoinIrred (EndP P) f}) :
    v ≤ w ↔ jiRestrict Θ v ≤ jiRestrict Θ w :=
  (Θ.map_rel_iff (a := v.1) (b := w.1)).symm

/-- **`EndP P` is rigid whenever `P` is.**

No hypothesis beyond `P`'s own rigidity and `UniqueAtomCoatom` — the product
decomposition that §73 called CONJ′ is `jh_free`, already a theorem. -/
theorem endP_rigid [Fintype (EndP P)] [DecidableEq (EndP P)]
    (hrigid : Subsingleton (P ≃o P)) :
    Subsingleton (EndP P ≃o EndP P) := by
  classical
  refine ⟨fun Θ Θ' => ?_⟩
  suffices h : ∀ Ξ : EndP P ≃o EndP P, Ξ = OrderIso.refl (EndP P) by
    rw [h Θ, h Θ']
  intro Ξ
  -- split the induced automorphism of `J (EndP P)`
  obtain ⟨γA, γB, hγA, hγB, hsplit⟩ :=
    jh_free (P := P) (jiRestrict Ξ) (jiRestrict_ord Ξ)
  -- `γA` is an order-automorphism of `P`, hence the identity
  have hγAid : ∀ a : P, γA a = a := by
    intro a
    have h : (⟨γA, fun {a b} => (hγA a b).symm⟩ : P ≃o P) = OrderIso.refl P :=
      hrigid.elim _ _
    exact congrArg (fun e : P ≃o P => e a) h
  -- so `Ξ` moves the constants by `γB`
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
  -- extend `γB` to `P` and apply the threshold argument
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
  -- so the induced automorphism is the identity, hence so is `Ξ`
  refine eq_of_agree_on_joinIrred Ξ (OrderIso.refl (EndP P)) (fun f hf => ?_)
  obtain ⟨p, hp⟩ := jiEquiv.surjective (⟨f, hf⟩ : {f : EndP P // JoinIrred (EndP P) f})
  have hfv : (jiEquiv p).1 = f := congrArg Subtype.val hp
  have h := congrArg Subtype.val (hsplit p)
  simp only [jiRestrict, Equiv.coe_fn_mk] at h
  rw [hγAid p.1, hγBid p.2, hfv] at h
  simpa using h

end EndPRigid
