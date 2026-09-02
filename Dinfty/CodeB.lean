import Dinfty.GasketObstruction

open GluingTowerLibrary SierpinskiApplication

-- [D-2805] §The-address-map-into-B
open Set

namespace CodeB

open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2806] §1-The-three-maps-indexed
-- [D-2807] sig
noncomputable def sig (j : Fin 3) (x : B) : B :=
  sec (tagPt (j : ℕ) markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))

-- [D-2808] sig_zero
theorem sig_zero (x : B) : sig 0 x = ifsS.sigmaA x := rfl
-- [D-2809] sig_one
theorem sig_one (x : B) : sig 1 x = ifsS.sigmaB x := rfl
-- [D-2810] sig_two
theorem sig_two (x : B) : sig 2 x = ifsS.sigmaC x := rfl

-- [D-2811] fin3_cases
theorem fin3_cases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide

-- [D-2812] tag_le_two
theorem tag_le_two (j : Fin 3) : (j : ℕ) ≤ 2 := Nat.lt_succ_iff.mp j.isLt

-- [D-2813] §2-The-payload
-- [D-2814] scottEndP_le_iff
theorem scottEndP_le_iff {F G : ScottEndP B} : F ≤ G ↔ ∀ z, F.1 z ≤ G.1 z := Iff.rfl

-- [D-2815] strictConst_mono
theorem strictConst_mono : Monotone (strictConst : B → ScottEndP B) := by
  intro x y h
  refine scottEndP_le_iff.mpr (fun z => ?_)
  show strictFun x z ≤ strictFun y z
  by_cases hz : z = ⊥
  · rw [strictFun_bot_case hz, strictFun_bot_case hz]
  · rw [strictFun_ne_case hz, strictFun_ne_case hz]
    exact h

-- [D-2816] strictConst_eq_bot_iff
theorem strictConst_eq_bot_iff (x : B) : strictConst x = ⊥ ↔ x = ⊥ := by
  constructor
  · intro h
    exact strictConst_injective (h.trans strictConst_bot.symm)
  · intro h
    rw [h]
    exact strictConst_bot

-- [D-2817] strictConst_ne_bot
theorem strictConst_ne_bot {x : B} (hx : x ≠ ⊥) : strictConst x ≠ ⊥ :=
  fun hc => hx ((strictConst_eq_bot_iff x).mp hc)

-- [D-2818] strictConst_ne_marked
theorem strictConst_ne_marked (x : B) : strictConst x ≠ markedB := by
  intro h
  have h1 : strictFun x (⊥ : B) = (markedB : ScottEndP B).1 (⊥ : B) :=
    congrArg (fun F : ScottEndP B => F.1 (⊥ : B)) h
  rw [strictFun_bot_case rfl] at h1
  exact midB_ne_botB h1.symm

-- [D-2819] strictConst_isLUB
theorem strictConst_isLUB {S : Set B} {c : B} (hc : IsLUB S c) :
    IsLUB (strictConst '' S) (strictConst c) := by
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    exact strictConst_mono (hc.1 hs)
  · intro G hG
    refine scottEndP_le_iff.mpr (fun z => ?_)
    show strictFun c z ≤ (G : ScottEndP B).1 z
    by_cases hz : z = ⊥
    · rw [strictFun_bot_case hz]
      exact bot_le
    · rw [strictFun_ne_case hz]
      refine hc.2 (fun s hs => ?_)
      have h2 := scottEndP_le_iff.mp (hG ⟨s, hs, rfl⟩) z
      rwa [show (strictConst s).1 z = strictFun s z from rfl,
        strictFun_ne_case hz] at h2

-- [D-2820] §3-The-seam-inequality-for-tag-B
-- [D-2821] leGlueGen_tagA_tagB_of_le
theorem leGlueGen_tagA_tagB_of_le (m x y : ScottEndP B) (hxm : x ≤ m) :
    leGlueGen m (Sum.inl x) (Sum.inr (Sum.inl y)) :=
  ⟨Sum.inl x, self_mem_occsGen _ _, Sum.inr (Sum.inl y), self_mem_occsGen _ _, hxm⟩

-- [D-2822] §4-Canon-fixedness-of-the-payloads
-- [D-2823] fixed_of_ne_bot
theorem fixed_of_ne_bot {t : ℕ} (ht : t ≤ 2) {s : ScottEndP B}
    (hs : s ≠ ⊥) (hsm : s ≠ markedB) :
    canonGen markedB (tagInj t s) = tagInj t s := by
  rw [CanonFixed.fixed_iff]
  interval_cases t
  · exact trivial
  · exact hs
  · exact ⟨hs, hsm⟩

-- [D-2824] isLUB_pair_of_le
theorem isLUB_pair_of_le {α : Type*} [PartialOrder α] {a b : α} (h : a ≤ b) :
    IsLUB ({a, b} : Set α) b := by
  constructor
  · rintro x (rfl | rfl)
    · exact h
    · exact le_refl _
  · intro u hu
    exact hu (by simp)

-- [D-2825] §5-Supremum-preservation-away-from
-- [D-2826] sig_isLUB_of_ne_bot
theorem sig_isLUB_of_ne_bot (j : Fin 3) {S : Set B} {c : B} (hne : S.Nonempty)
    (hS : ∀ s ∈ S, s ≠ ⊥) (hc : IsLUB S c) : IsLUB (sig j '' S) (sig j c) := by
  have hsc := strictConst_isLUB hc
  have htag := tagPt_isLUB (t := (j : ℕ)) (tag_le_two j) markedB markedB_ne_bot
    markedB_ne_top endPB_bot_ne_top hsc (hne.image _)
    (by
      rintro _ ⟨s, hs, rfl⟩
      exact fixed_of_ne_bot (tag_le_two j) (strictConst_ne_bot (hS s hs))
        (strictConst_ne_marked s))
  have h2 := (OrderIso.isLUB_image' sec).mpr htag
  have himg : sec '' (tagPt (j : ℕ) markedB markedB_ne_bot endPB_bot_ne_top ''
      (strictConst '' S)) = sig j '' S := by
    rw [← Set.image_comp, ← Set.image_comp]
    rfl
  rwa [himg] at h2

-- [D-2827] §6-The-payload-lands-in-copy-A-below-the-copy
-- [D-2828] tagPt_bot_le
theorem tagPt_bot_le (t : ℕ) (ht : t ≤ 2) {y : B} (hy : y ≠ ⊥) :
    tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))
      ≤ tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst y) := by
  have hyb : strictConst y ≠ ⊥ := strictConst_ne_bot hy
  interval_cases t
  · show leGlueGen markedB _ _
    have hL : (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top
        (strictConst (⊥ : B))).1 = Sum.inl (⊥ : ScottEndP B) := by
      rw [strictConst_bot]
      rfl
    have hR : (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1
        = Sum.inl (strictConst y) := rfl
    rw [hL, hR]
    exact (leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mpr bot_le
  · show leGlueGen markedB _ _
    have hL : (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top
        (strictConst (⊥ : B))).1 = Sum.inl markedB := by
      rw [strictConst_bot]
      show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
            else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
      rw [if_pos rfl]
    have hR : (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1
        = Sum.inr (Sum.inl (strictConst y)) := by
      show (if strictConst y = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
            else Sum.inr (Sum.inl (strictConst y))) = _
      rw [if_neg hyb]
    rw [hL, hR]
    exact leGlueGen_tagA_tagB_of_le markedB markedB (strictConst y) (le_refl _)
  · show leGlueGen markedB _ _
    have hL : (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top
        (strictConst (⊥ : B))).1 = Sum.inl (⊤ : ScottEndP B) := by
      rw [strictConst_bot]
      show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
            else if (⊥ : ScottEndP B) = markedB then Sum.inr (Sum.inl ⊤)
            else Sum.inr (Sum.inr (⊥ : ScottEndP B))) = Sum.inl ⊤
      rw [if_pos rfl]
    have hR : (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1
        = Sum.inr (Sum.inr (strictConst y)) := by
      show (if strictConst y = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
            else if strictConst y = markedB then Sum.inr (Sum.inl ⊤)
            else Sum.inr (Sum.inr (strictConst y))) = _
      rw [if_neg hyb, if_neg (strictConst_ne_marked y)]
    rw [hL, hR]
    exact leGlueGen_tagA_tagC markedB (⊤ : ScottEndP B) (strictConst y)

-- [D-2829] §7-Monotonicity
-- [D-2830] sig_mono
theorem sig_mono (j : Fin 3) : Monotone (sig j) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · subst hx
    by_cases hy : y = ⊥
    · subst hy
      exact le_refl _
    · exact sec.monotone (tagPt_bot_le (j : ℕ) (tag_le_two j) hy)
  · have hy : y ≠ ⊥ := fun hc => hx (le_antisymm (hc ▸ hxy) bot_le)
    have h := sig_isLUB_of_ne_bot j (S := ({x, y} : Set B)) ⟨x, by simp⟩
      (by rintro s hs; rcases hs with rfl | rfl <;> assumption) (isLUB_pair_of_le hxy)
    exact h.1 ⟨x, by simp, rfl⟩

-- [D-2831] §8-Supremum-preservation-in-full
-- [D-2832] sig_isLUB
theorem sig_isLUB (j : Fin 3) {y : ℕ → B} (hy : Monotone y) {c : B}
    (hc : IsLUB (Set.range y) c) :
    IsLUB (Set.range fun n => sig j (y n)) (sig j c) := by
  by_cases hcb : c = ⊥
  · have hall : ∀ n, y n = ⊥ := fun n => le_antisymm (hcb ▸ hc.1 ⟨n, rfl⟩) bot_le
    have hset : (Set.range fun n => sig j (y n)) = {sig j c} := by
      ext z
      constructor
      · rintro ⟨n, rfl⟩
        show sig j (y n) = sig j c
        rw [hall n, hcb]
      · rintro rfl
        refine ⟨0, ?_⟩
        show sig j (y 0) = sig j c
        rw [hall 0, hcb]
    rw [hset]
    exact isLUB_singleton
  · obtain ⟨N, hN⟩ : ∃ N, y N ≠ ⊥ := by
      by_contra hcon
      push_neg at hcon
      refine hcb (le_antisymm (hc.2 ?_) bot_le)
      rintro _ ⟨n, rfl⟩
      rw [hcon n]
    have hc' : IsLUB (Set.range fun i => y (N + i)) c :=
      PhiCoconeLUB.isLUB_tail hy hc N
    have hne' : ∀ i, y (N + i) ≠ ⊥ := fun i hcon =>
      hN (le_antisymm (hcon ▸ hy (Nat.le_add_right N i)) bot_le)
    have htail := sig_isLUB_of_ne_bot j (S := Set.range fun i => y (N + i))
      ⟨y (N + 0), ⟨0, rfl⟩⟩ (by rintro _ ⟨i, rfl⟩; exact hne' i) hc'
    rw [← Set.range_comp] at htail
    simp only [Function.comp_def] at htail
    exact PhiSurjective.isLUB_of_tail (fun a b h => sig_mono j (hy h)) htail

-- [D-2833] §9-The-chain-and-the-address-map
-- [D-2834] chainB
noncomputable def chainB : ℕ → (ℕ → Fin 3) → B
  | 0, _ => ⊥
  | (n + 1), w => sig (w 0) (chainB n (Gasket.tail w))

-- [D-2835] chainB_le_succ
theorem chainB_le_succ (n : ℕ) (w : ℕ → Fin 3) : chainB n w ≤ chainB (n + 1) w := by
  induction n generalizing w with
  | zero => exact bot_le
  | succ n ih =>
      show sig (w 0) (chainB n (Gasket.tail w)) ≤ sig (w 0) (chainB (n + 1) (Gasket.tail w))
      exact sig_mono _ (ih (Gasket.tail w))

-- [D-2836] chainB_mono
theorem chainB_mono (w : ℕ → Fin 3) : Monotone (fun n => chainB n w) :=
  monotone_nat_of_le_succ (fun n => chainB_le_succ n w)

-- [D-2837] codeB
noncomputable def codeB (w : ℕ → Fin 3) : B :=
  Classical.choose (PhiChainSup.exists_chain_lub (chainB_mono w))

-- [D-2838] codeB_isLUB
theorem codeB_isLUB (w : ℕ → Fin 3) :
    IsLUB (Set.range fun n => chainB n w) (codeB w) :=
  Classical.choose_spec (PhiChainSup.exists_chain_lub (chainB_mono w))

-- [D-2839] §10-Equivariance
-- [D-2840] chainB_cons
theorem chainB_cons (j : Fin 3) (w : ℕ → Fin 3) (n : ℕ) :
    chainB (n + 1) (Gasket.cons j w) = sig j (chainB n w) := rfl

-- [D-2841] codeB_cons
theorem codeB_cons (j : Fin 3) (w : ℕ → Fin 3) :
    codeB (Gasket.cons j w) = sig j (codeB w) := by
  have hshift : IsLUB (Set.range fun k => chainB (1 + k) (Gasket.cons j w))
      (codeB (Gasket.cons j w)) :=
    PhiCoconeLUB.isLUB_tail (chainB_mono (Gasket.cons j w))
      (codeB_isLUB (Gasket.cons j w)) 1
  have hval : ∀ k, chainB (1 + k) (Gasket.cons j w) = sig j (chainB k w) := by
    intro k
    rw [show 1 + k = k + 1 from Nat.add_comm 1 k]
    exact chainB_cons j w k
  have himg : (Set.range fun k => chainB (1 + k) (Gasket.cons j w))
      = Set.range fun n => sig j (chainB n w) := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hval k).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hval n⟩
  rw [himg] at hshift
  exact IsLUB.unique hshift (sig_isLUB j (chainB_mono w) (codeB_isLUB w))

-- [D-2842] codeB_cons_zero
theorem codeB_cons_zero (w : ℕ → Fin 3) :
    codeB (Gasket.cons 0 w) = ifsS.sigmaA (codeB w) := codeB_cons 0 w

-- [D-2843] codeB_cons_one
theorem codeB_cons_one (w : ℕ → Fin 3) :
    codeB (Gasket.cons 1 w) = ifsS.sigmaB (codeB w) := codeB_cons 1 w

-- [D-2844] codeB_cons_two
theorem codeB_cons_two (w : ℕ → Fin 3) :
    codeB (Gasket.cons 2 w) = ifsS.sigmaC (codeB w) := codeB_cons 2 w

-- [D-2845] §11-The-three-images-are-disjoint-so-the-address
-- [D-2846] strictConst_ne_top
theorem strictConst_ne_top (x : B) : strictConst x ≠ (⊤ : ScottEndP B) := by
  intro h
  have h1 : strictFun x (⊥ : B) = (⊤ : ScottEndP B).1 (⊥ : B) :=
    congrArg (fun F : ScottEndP B => F.1 (⊥ : B)) h
  rw [strictFun_bot_case rfl] at h1
  exact botB_ne_topB h1

-- [D-2847] tagVal_zero
theorem tagVal_zero (x : B) :
    (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      = Sum.inl (strictConst x) := rfl

-- [D-2848] tagVal_one_bot
theorem tagVal_one_bot :
    (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))).1
      = Sum.inl markedB := by
  rw [strictConst_bot]
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
  rw [if_pos rfl]

-- [D-2849] tagVal_one_ne
theorem tagVal_one_ne {x : B} (hx : x ≠ ⊥) :
    (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      = Sum.inr (Sum.inl (strictConst x)) := by
  show (if strictConst x = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (strictConst x))) = _
  rw [if_neg (strictConst_ne_bot hx)]

-- [D-2850] tagVal_two_bot
theorem tagVal_two_bot :
    (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))).1
      = Sum.inl (⊤ : ScottEndP B) := by
  rw [strictConst_bot]
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
        else if (⊥ : ScottEndP B) = markedB then Sum.inr (Sum.inl ⊤)
        else Sum.inr (Sum.inr (⊥ : ScottEndP B))) = Sum.inl ⊤
  rw [if_pos rfl]

-- [D-2851] tagVal_two_ne
theorem tagVal_two_ne {x : B} (hx : x ≠ ⊥) :
    (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      = Sum.inr (Sum.inr (strictConst x)) := by
  show (if strictConst x = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
        else if strictConst x = markedB then Sum.inr (Sum.inl ⊤)
        else Sum.inr (Sum.inr (strictConst x))) = _
  rw [if_neg (strictConst_ne_bot hx), if_neg (strictConst_ne_marked x)]

-- [D-2852] tagVal_zero_ne_one
theorem tagVal_zero_ne_one (x y : B) :
    (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      ≠ (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 := by
  intro hval
  rw [tagVal_zero] at hval
  by_cases hy : y = ⊥
  · subst hy
    rw [tagVal_one_bot] at hval
    exact strictConst_ne_marked x (Sum.inl.inj hval)
  · rw [tagVal_one_ne hy] at hval
    simp at hval

-- [D-2853] tagVal_zero_ne_two
theorem tagVal_zero_ne_two (x y : B) :
    (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      ≠ (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 := by
  intro hval
  rw [tagVal_zero] at hval
  by_cases hy : y = ⊥
  · subst hy
    rw [tagVal_two_bot] at hval
    exact strictConst_ne_top x (Sum.inl.inj hval)
  · rw [tagVal_two_ne hy] at hval
    simp at hval

-- [D-2854] tagVal_one_ne_two
theorem tagVal_one_ne_two (x y : B) :
    (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      ≠ (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 := by
  intro hval
  by_cases hx : x = ⊥ <;> by_cases hy : y = ⊥
  · subst hx; subst hy
    rw [tagVal_one_bot, tagVal_two_bot] at hval
    exact markedB_ne_top (Sum.inl.inj hval)
  · subst hx
    rw [tagVal_one_bot, tagVal_two_ne hy] at hval
    simp at hval
  · subst hy
    rw [tagVal_one_ne hx, tagVal_two_bot] at hval
    simp at hval
  · rw [tagVal_one_ne hx, tagVal_two_ne hy] at hval
    simp at hval

-- [D-2855] sig_ne_of_ne
theorem sig_ne_of_ne (j j' : Fin 3) (hjj : j ≠ j') (x y : B) : sig j x ≠ sig j' y := by
  intro h
  have hval : (tagPt (j : ℕ) markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      = (tagPt (j' : ℕ) markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 :=
    congrArg Subtype.val (sec_injective h)
  rcases fin3_cases j with rfl | rfl | rfl <;> rcases fin3_cases j' with rfl | rfl | rfl
  · exact hjj rfl
  · exact tagVal_zero_ne_one x y hval
  · exact tagVal_zero_ne_two x y hval
  · exact tagVal_zero_ne_one y x hval.symm
  · exact hjj rfl
  · exact tagVal_one_ne_two x y hval
  · exact tagVal_zero_ne_two y x hval.symm
  · exact tagVal_one_ne_two y x hval.symm
  · exact hjj rfl

-- [D-2856] sig_injective
theorem sig_injective (j : Fin 3) : Function.Injective (sig j) := by
  intro x y h
  exact strictConst_injective
    (tagPt_injective (j : ℕ) markedB markedB_ne_bot endPB_bot_ne_top (sec_injective h))

-- [D-2857] §12-codeB-is-injective
-- [D-2858] codeB_head
theorem codeB_head (w : ℕ → Fin 3) : codeB w = sig (w 0) (codeB (Gasket.tail w)) := by
  conv_lhs => rw [← Gasket.cons_head_tail w]
  exact codeB_cons (w 0) (Gasket.tail w)

-- [D-2859] codeB_agree
theorem codeB_agree : ∀ (n : ℕ) (w w' : ℕ → Fin 3), codeB w = codeB w' → w n = w' n := by
  intro n
  induction n with
  | zero =>
      intro w w' h
      by_contra hne
      rw [codeB_head w, codeB_head w'] at h
      exact sig_ne_of_ne (w 0) (w' 0) hne _ _ h
  | succ n ih =>
      intro w w' h
      have h0 : w 0 = w' 0 := by
        by_contra hne
        rw [codeB_head w, codeB_head w'] at h
        exact sig_ne_of_ne (w 0) (w' 0) hne _ _ h
      have htail : codeB (Gasket.tail w) = codeB (Gasket.tail w') := by
        have h1 := h
        rw [codeB_head w, codeB_head w', h0] at h1
        exact sig_injective (w' 0) h1
      exact ih (Gasket.tail w) (Gasket.tail w') htail

-- [D-2860] codeB_injective
theorem codeB_injective : Function.Injective codeB :=
  fun w w' h => funext (fun n => codeB_agree n w w' h)

-- [D-2861] §13-so-exists
-- [D-2862] Attractor
def Attractor : Set B := Set.range codeB

-- [D-2863] codeB_mem_attractor
theorem codeB_mem_attractor (w : ℕ → Fin 3) : codeB w ∈ Attractor := ⟨w, rfl⟩

-- [D-2864] rho
noncomputable def rho (b : Attractor) : Gasket.Gamma :=
  Gasket.codeGamma (Classical.choose b.2)

-- [D-2865] rho_codeB
theorem rho_codeB (w : ℕ → Fin 3) :
    rho ⟨codeB w, codeB_mem_attractor w⟩ = Gasket.codeGamma w := by
  have h := Classical.choose_spec (codeB_mem_attractor w)
  show Gasket.codeGamma (Classical.choose (codeB_mem_attractor w)) = _
  rw [codeB_injective h]

-- [D-2866] rho_surjective
theorem rho_surjective : Function.Surjective rho := by
  intro g
  obtain ⟨w, hw⟩ := Gasket.codeGamma_surjective g
  exact ⟨⟨codeB w, codeB_mem_attractor w⟩, (rho_codeB w).trans hw⟩

-- [D-2867] rho_sigmaA
theorem rho_sigmaA (w : ℕ → Fin 3) :
    rho ⟨ifsS.sigmaA (codeB w), (codeB_cons_zero w) ▸ codeB_mem_attractor (Gasket.cons 0 w)⟩
      = Gasket.fA (rho ⟨codeB w, codeB_mem_attractor w⟩) := by
  rw [rho_codeB w, ← Gasket.codeGamma_cons_zero w]
  have h : ifsS.sigmaA (codeB w) = codeB (Gasket.cons 0 w) := (codeB_cons_zero w).symm
  simp only [h]
  exact rho_codeB (Gasket.cons 0 w)

-- [D-2868] §14-The-attractor-is-closed-under-the-three-maps
-- [D-2869] mapsTo_sig
theorem mapsTo_sig (j : Fin 3) : Set.MapsTo (sig j) Attractor Attractor := by
  rintro _ ⟨w, rfl⟩
  exact ⟨Gasket.cons j w, codeB_cons j w⟩

-- [D-2870] mapsTo_sigmaA
theorem mapsTo_sigmaA : Set.MapsTo ifsS.sigmaA Attractor Attractor := mapsTo_sig 0
-- [D-2871] mapsTo_sigmaB
theorem mapsTo_sigmaB : Set.MapsTo ifsS.sigmaB Attractor Attractor := mapsTo_sig 1
-- [D-2872] mapsTo_sigmaC
theorem mapsTo_sigmaC : Set.MapsTo ifsS.sigmaC Attractor Attractor := mapsTo_sig 2

-- [D-2873] attractorEquiv
noncomputable def attractorEquiv : (ℕ → Fin 3) ≃ Attractor where
  toFun w := ⟨codeB w, codeB_mem_attractor w⟩
  invFun b := Classical.choose b.2
  left_inv w := codeB_injective (Classical.choose_spec (codeB_mem_attractor w))
  right_inv b := Subtype.ext (Classical.choose_spec b.2)

-- [D-2874] codeB_constA
theorem codeB_constA : codeB (fun _ => 0) = (⊥ : B) := by
  refine le_antisymm ((codeB_isLUB _).2 ?_) bot_le
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
      show sig 0 (chainB n (Gasket.tail fun _ => (0 : Fin 3))) ≤ (⊥ : B)
      have h : (Gasket.tail fun _ => (0 : Fin 3)) = fun _ => (0 : Fin 3) := rfl
      rw [h]
      have h2 : chainB n (fun _ => (0 : Fin 3)) = (⊥ : B) := le_antisymm ih bot_le
      rw [h2, sig_zero]
      exact le_of_eq SigmaRebuild.sigmaA_bot

-- [D-2875] bot_mem_attractor
theorem bot_mem_attractor : (⊥ : B) ∈ Attractor := ⟨fun _ => 0, codeB_constA⟩

-- [D-2876] §15-Each-j-is-an-order-embedding
-- [D-2877] strictConst_reflects
theorem strictConst_reflects {x y : B} (h : strictConst x ≤ strictConst y) : x ≤ y := by
  have h1 := scottEndP_le_iff.mp h topB
  rw [show (strictConst x).1 topB = strictFun x topB from rfl,
    show (strictConst y).1 topB = strictFun y topB from rfl,
    strictFun_ne_case topB_ne_bot, strictFun_ne_case topB_ne_bot] at h1
  exact h1

-- [D-2878] sig_reflects
theorem sig_reflects (j : Fin 3) {x y : B} (h : sig j x ≤ sig j y) : x ≤ y := by
  by_cases hx : x = ⊥
  · rw [hx]
    exact bot_le
  have hxb : strictConst x ≠ ⊥ := strictConst_ne_bot hx
  have key : ∀ t : ℕ, t ≤ 2 → leGlueGen markedB
      (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst x)).1
      (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst y)).1 → x ≤ y := by
    intro t ht hraw
    by_cases hy : y = ⊥
    · exfalso
      subst hy
      interval_cases t
      · rw [tagVal_zero, tagVal_zero, strictConst_bot] at hraw
        exact hxb (le_antisymm
          ((leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mp hraw) bot_le)
      · rw [tagVal_one_ne hx, tagVal_one_bot] at hraw
        exact not_leGlue_tagB_tagAGen markedB _ _ markedB_ne_bot endPB_bot_ne_top hxb hraw
      · rw [tagVal_two_ne hx, tagVal_two_bot] at hraw
        exact not_leGlue_tagC_tagAGen markedB _ _ hxb hraw
    · refine strictConst_reflects ?_
      interval_cases t
      · rw [tagVal_zero, tagVal_zero] at hraw
        exact (leGlueGen_tagA_tagA_iff markedB markedB_ne_bot _ _).mp hraw
      · rw [tagVal_one_ne hx, tagVal_one_ne hy] at hraw
        exact le_of_leGlueGen_tagB_tagB markedB _ _ (strictConst_ne_top y) hraw
      · rw [tagVal_two_ne hx, tagVal_two_ne hy] at hraw
        exact (leGlue_tagC_tagC_iffGen markedB _ _).mp hraw
  exact key (j : ℕ) (tag_le_two j) (sec.le_iff_le.mp h)

-- [D-2879] sig_le_iff
theorem sig_le_iff (j : Fin 3) (x y : B) : sig j x ≤ sig j y ↔ x ≤ y :=
  ⟨sig_reflects j, fun h => sig_mono j h⟩

-- [D-2880] codeB_tail_le
theorem codeB_tail_le {u v : ℕ → Fin 3} (h : codeB u ≤ codeB v) (hhead : u 0 = v 0) :
    codeB (Gasket.tail u) ≤ codeB (Gasket.tail v) := by
  rw [codeB_head u, codeB_head v, hhead] at h
  exact sig_reflects (v 0) h

end CodeB
