import Dinfty.RhoContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-2894] §AddressesConverge-proved
open Set

namespace CodeB

open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2895] §1-The-three-blocked-head-moves
-- [D-2896] not_sig_one_le_zero
theorem not_sig_one_le_zero (x y : B) : ¬ (sig 1 x ≤ sig 0 y) := by
  intro h
  have hraw : leGlueGen markedB
      (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 :=
    sec.le_iff_le.mp h
  by_cases hx : x = ⊥
  · subst hx
    rw [tagVal_one_bot, tagVal_zero] at hraw
    have hle : markedB ≤ strictConst y :=
      (leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mp hraw
    have h1 := scottEndP_le_iff.mp hle (⊥ : B)
    rw [show (strictConst y).1 (⊥ : B) = strictFun y (⊥ : B) from rfl,
      strictFun_bot_case rfl] at h1
    exact midB_ne_botB (le_antisymm h1 bot_le)
  · rw [tagVal_one_ne hx, tagVal_zero] at hraw
    exact not_leGlue_tagB_tagAGen markedB _ _ markedB_ne_bot endPB_bot_ne_top
      (strictConst_ne_bot hx) hraw

-- [D-2897] not_sig_two_le_zero
theorem not_sig_two_le_zero (x y : B) : ¬ (sig 2 x ≤ sig 0 y) := by
  intro h
  have hraw : leGlueGen markedB
      (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 :=
    sec.le_iff_le.mp h
  by_cases hx : x = ⊥
  · subst hx
    rw [tagVal_two_bot, tagVal_zero] at hraw
    have hle : (⊤ : ScottEndP B) ≤ strictConst y :=
      (leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mp hraw
    exact strictConst_ne_top y (le_antisymm le_top hle)
  · rw [tagVal_two_ne hx, tagVal_zero] at hraw
    exact not_leGlue_tagC_tagAGen markedB _ _ (strictConst_ne_bot hx) hraw

-- [D-2898] not_sig_two_le_one
theorem not_sig_two_le_one (x y : B) : ¬ (sig 2 x ≤ sig 1 y) := by
  intro h
  have hraw : leGlueGen markedB
      (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 :=
    sec.le_iff_le.mp h
  by_cases hx : x = ⊥
  · subst hx
    by_cases hy : y = ⊥
    · subst hy
      rw [tagVal_two_bot, tagVal_one_bot] at hraw
      have hle : (⊤ : ScottEndP B) ≤ markedB :=
        (leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mp hraw
      exact markedB_ne_top (le_antisymm le_top hle)
    · rw [tagVal_two_bot, tagVal_one_ne hy] at hraw
      have hle : (⊤ : ScottEndP B) ≤ markedB :=
        (leGlue_tagA_tagB_iffGen markedB _ _ (strictConst_ne_top y)).mp hraw
      exact markedB_ne_top (le_antisymm le_top hle)
  · by_cases hy : y = ⊥
    · subst hy
      rw [tagVal_two_ne hx, tagVal_one_bot] at hraw
      exact not_leGlue_tagC_tagAGen markedB _ _ (strictConst_ne_bot hx) hraw
    · rw [tagVal_two_ne hx, tagVal_one_ne hy] at hraw
      exact not_leGlue_tagC_tagBGen markedB _ _ (strictConst_ne_top y) hraw

-- [D-2899] §2-The-head-can-only-move-up
-- [D-2900] not_codeB_le_one_zero
theorem not_codeB_le_one_zero {u v : ℕ → Fin 3} (h1 : u 0 = 1) (h2 : v 0 = 0) :
    ¬ (codeB u ≤ codeB v) := by
  intro h
  rw [codeB_head u, codeB_head v, h1, h2] at h
  exact not_sig_one_le_zero _ _ h

-- [D-2901] not_codeB_le_two_zero
theorem not_codeB_le_two_zero {u v : ℕ → Fin 3} (h1 : u 0 = 2) (h2 : v 0 = 0) :
    ¬ (codeB u ≤ codeB v) := by
  intro h
  rw [codeB_head u, codeB_head v, h1, h2] at h
  exact not_sig_two_le_zero _ _ h

-- [D-2902] not_codeB_le_two_one
theorem not_codeB_le_two_one {u v : ℕ → Fin 3} (h1 : u 0 = 2) (h2 : v 0 = 1) :
    ¬ (codeB u ≤ codeB v) := by
  intro h
  rw [codeB_head u, codeB_head v, h1, h2] at h
  exact not_sig_two_le_one _ _ h

-- [D-2903] head_le_of_codeB_le
theorem head_le_of_codeB_le {u v : ℕ → Fin 3} (h : codeB u ≤ codeB v) :
    (u 0).val ≤ (v 0).val := by
  rcases fin3_cases (u 0) with h1 | h1 | h1
  · rw [h1]
    exact Nat.zero_le _
  · rcases fin3_cases (v 0) with h2 | h2 | h2
    · exact absurd h (not_codeB_le_one_zero h1 h2)
    · rw [h1, h2]
    · rw [h1, h2]
      decide
  · rcases fin3_cases (v 0) with h2 | h2 | h2
    · exact absurd h (not_codeB_le_two_zero h1 h2)
    · exact absurd h (not_codeB_le_two_one h1 h2)
    · rw [h1, h2]

-- [D-2904] §3-So-the-head-is-eventually-constant
-- [D-2905] head_eventually_const
theorem head_eventually_const {w : ℕ → (ℕ → Fin 3)}
    (hm : Monotone fun n => codeB (w n)) :
    ∃ N, ∀ n, N ≤ n → (w n) 0 = (w N) 0 := by
  have hmono : Monotone (fun n => (((w n) 0 : Fin 3) : ℕ)) := by
    intro a b hab
    exact head_le_of_codeB_le (hm hab)
  obtain ⟨N, hN⟩ := PhiChainSup.exists_eventually_const hmono (b := 2)
    (fun k => tag_le_two ((w k) 0))
  exact ⟨N, fun n hn => Fin.val_injective (hN n hn)⟩

-- [D-2906] §4-The-induction
-- [D-2907] prefix_stabilizes
theorem prefix_stabilizes : ∀ (k : ℕ) (w : ℕ → (ℕ → Fin 3)) (v : ℕ → Fin 3),
    Monotone (fun n => codeB (w n)) →
    IsLUB (Set.range fun n => codeB (w n)) (codeB v) →
    ∃ N, ∀ n, N ≤ n → ∀ i, i < k → (w n) i = v i := by
  intro k
  induction k with
  | zero =>
      intro w v _ _
      exact ⟨0, fun n _ i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
      intro w v hm hlub
      obtain ⟨N0, hN0⟩ := head_eventually_const hm
      have hheads : ∀ n, (w (N0 + n)) 0 = (w N0) 0 := fun n =>
        hN0 (N0 + n) (Nat.le_add_right _ _)
      have hm' : Monotone (fun n => codeB (Gasket.tail (w (N0 + n)))) := by
        intro a b hab
        refine codeB_tail_le (hm (by omega)) ?_
        rw [hheads a, hheads b]
      obtain ⟨c, hc⟩ := PhiChainSup.exists_chain_lub hm'
      have hsig : IsLUB (Set.range fun n => sig ((w N0) 0)
          (codeB (Gasket.tail (w (N0 + n))))) (sig ((w N0) 0) c) :=
        sig_isLUB ((w N0) 0) hm' hc
      have heq : ∀ n, sig ((w N0) 0) (codeB (Gasket.tail (w (N0 + n))))
          = codeB (w (N0 + n)) := by
        intro n
        rw [codeB_head (w (N0 + n)), hheads n]
      have hrange : (Set.range fun n => sig ((w N0) 0)
          (codeB (Gasket.tail (w (N0 + n)))))
          = Set.range fun n => codeB (w (N0 + n)) := by
        ext z
        constructor
        · rintro ⟨n, hn⟩
          exact ⟨n, (heq n).symm.trans hn⟩
        · rintro ⟨n, hn⟩
          exact ⟨n, (heq n).trans hn⟩
      rw [hrange] at hsig
      have htail : IsLUB (Set.range fun n => codeB (w (N0 + n))) (codeB v) :=
        PhiCoconeLUB.isLUB_tail hm hlub N0
      have hcv : sig ((w N0) 0) c = codeB v := IsLUB.unique hsig htail
      have hhead : codeB v = sig (v 0) (codeB (Gasket.tail v)) := codeB_head v
      have hv0 : v 0 = (w N0) 0 := by
        by_contra hne
        refine sig_ne_of_ne ((w N0) 0) (v 0) (fun hc2 => hne hc2.symm) c
          (codeB (Gasket.tail v)) ?_
        rw [hcv, hhead]
      have hctail : c = codeB (Gasket.tail v) := by
        refine sig_injective ((w N0) 0) ?_
        rw [hcv, hhead, hv0]
      obtain ⟨N1, hN1⟩ := ih (fun n => Gasket.tail (w (N0 + n))) (Gasket.tail v) hm'
        (by rw [← hctail]; exact hc)
      refine ⟨N0 + N1, fun n hn i hi => ?_⟩
      cases i with
      | zero =>
          have hz : (w n) 0 = (w N0) 0 := hN0 n (by omega)
          rw [hz, hv0]
      | succ i =>
          have hi' : i < k := Nat.lt_of_succ_lt_succ hi
          have hn' : N1 ≤ n - N0 := by omega
          have hres := hN1 (n - N0) hn' i hi'
          have hnn : N0 + (n - N0) = n := by omega
          rw [hnn] at hres
          exact hres

-- [D-2908] §5-which-is-exactly-AddressesConverge
-- [D-2909] addressesConverge
theorem addressesConverge : RhoContinuity.AddressesConverge :=
  fun w v hm hlub k => prefix_stabilizes k w v hm hlub

-- [D-2910] rho_chainContinuous
theorem rho_chainContinuous : RhoContinuity.ChainContinuous rho :=
  RhoContinuity.chainContinuous_of_addressesConverge addressesConverge

-- [D-2911] §6-Uniqueness-of-transported
-- [D-2912] rho_unique
theorem rho_unique (r : Attractor → Gasket.Gamma)
    (hA : ∀ b : Attractor, r ⟨sig 0 (b : B), mapsTo_sig 0 b.2⟩ = Gasket.fA (r b))
    (hB : ∀ b : Attractor, r ⟨sig 1 (b : B), mapsTo_sig 1 b.2⟩ = Gasket.fB (r b))
    (hC : ∀ b : Attractor, r ⟨sig 2 (b : B), mapsTo_sig 2 b.2⟩ = Gasket.fC (r b)) :
    r = rho := by
  have key : (fun w => r ⟨codeB w, codeB_mem_attractor w⟩) = Gasket.codeGamma := by
    refine Gasket.coding_unique _ ?_ ?_ ?_
    · intro w
      have h1 := hA ⟨codeB w, codeB_mem_attractor w⟩
      have h2 : (⟨sig 0 (codeB w), mapsTo_sig 0 (codeB_mem_attractor w)⟩ : Attractor)
          = ⟨codeB (Gasket.cons 0 w), codeB_mem_attractor _⟩ :=
        Subtype.ext (codeB_cons 0 w).symm
      rw [h2] at h1
      exact h1
    · intro w
      have h1 := hB ⟨codeB w, codeB_mem_attractor w⟩
      have h2 : (⟨sig 1 (codeB w), mapsTo_sig 1 (codeB_mem_attractor w)⟩ : Attractor)
          = ⟨codeB (Gasket.cons 1 w), codeB_mem_attractor _⟩ :=
        Subtype.ext (codeB_cons 1 w).symm
      rw [h2] at h1
      exact h1
    · intro w
      have h1 := hC ⟨codeB w, codeB_mem_attractor w⟩
      have h2 : (⟨sig 2 (codeB w), mapsTo_sig 2 (codeB_mem_attractor w)⟩ : Attractor)
          = ⟨codeB (Gasket.cons 2 w), codeB_mem_attractor _⟩ :=
        Subtype.ext (codeB_cons 2 w).symm
      rw [h2] at h1
      exact h1
  funext b
  obtain ⟨w, hw⟩ := b.2
  have hb : b = ⟨codeB w, codeB_mem_attractor w⟩ := Subtype.ext hw.symm
  rw [hb, rho_codeB]
  exact congrFun key w

end CodeB
