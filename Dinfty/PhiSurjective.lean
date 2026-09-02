import Dinfty.PhiCoconeLUB
import Dinfty.PhiChainSup
import Dinfty.GlueTag

open GluingTowerLibrary SierpinskiApplication

-- [D-2507] §Surjectivity-PhiSupExists-and-PhiProjContinuous
universe u

namespace PhiSurjective

open PhiIterateTower PhiBilimit EpPairTower PhiTriFunctor GenContinuity PhiChainSup GlueTag
open PhiTriTower

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2508] hmk
private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-2509] hbtk
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-2510] hpm
private theorem hpm : ∀ k, Monotone (PhiCocone.pLeg k) :=
  fun k _ _ hxy => PhiCocone.pLeg_monotone k hxy

-- [D-2511] hem
private theorem hem : ∀ k, Monotone (PhiCocone.eLeg k) :=
  fun k _ _ hxy => PhiCocone.eLeg_monotone k hxy

-- [D-2512] §Two-small-generalities
-- [D-2513] isLUB_of_tail
theorem isLUB_of_tail {α : Type*} [PartialOrder α] {f : ℕ → α} (hmono : Monotone f)
    {c : α} {N : ℕ} (hc : IsLUB (Set.range fun i => f (N + i)) c) : IsLUB (Set.range f) c := by
  constructor
  · rintro _ ⟨j, rfl⟩
    exact le_trans (hmono (Nat.le_add_left j N)) (hc.1 ⟨j, rfl⟩)
  · intro w hw
    refine hc.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hw ⟨N + i, rfl⟩

-- [D-2514] endUp_endDown_le
theorem endUp_endDown_le {k : ℕ} (E : TriEP k) (h : EndP (D (k + 1))) :
    E.endUp.toFun (E.endDown.toFun h) ≤ h := by
  refine OrderHom.le_def.mpr (fun x => ?_)
  show E.emb (E.prj (h (E.emb (E.prj x)))) ≤ h x
  exact le_trans (E.deflation _) (h.monotone (E.deflation x))

-- [D-2515] §The-tower-s-projection-on-values
-- [D-2516] prj_succ
theorem prj_succ (n : ℕ) : (iter (n + 1)).prj = phiTowerD (iter n).endDown := rfl

-- [D-2517] d_val
theorem d_val (d : phiTowerEP.shift.Bilim) (k : ℕ) :
    (d.1 k).1 = canonGen (markedPt (k + 1))
      (baseMapGen ((iter k).endDown).toFun (d.1 (k + 1)).1) := by
  conv_lhs => rw [← d.2 k]
  rfl

-- [D-2518] §pLeg-on-tag-points
-- [D-2519] pLeg_tagPt
theorem pLeg_tagPt (j t : ℕ) (H : ScottEndP B) :
    PhiCocone.pLeg j (tagPt t markedB markedB_ne_bot endPB_bot_ne_top H)
      = tagPt t (markedPt (j + 1)) (hmk (j + 1)) (hbtk (j + 1))
          ((PhiCocone.projEndDown j).toFun H) := by
  refine Subtype.ext ?_
  show canonGen (markedPt (j + 1)) (baseMapGen (PhiCocone.projEndDown j).toFun
        (canonGen markedB (tagInj t H)))
    = canonGen (markedPt (j + 1)) (tagInj t ((PhiCocone.projEndDown j).toFun H))
  rw [canonGen_baseMapGen_canon (PhiCocone.projEndDown j) markedB_ne_bot (hmk (j + 1))
      (hbtk (j + 1)), baseMapGen_tagInj]

-- [D-2520] §insEndUp-is-injective-and-carries-the-canon
-- [D-2521] insEndUp_retract
theorem insEndUp_retract (k : ℕ) (a : EndP (D (k + 1))) :
    (PhiCocone.projEndDown k).toFun ((PhiCocone.insEndUp k).toFun a) = a :=
  congrArg (fun F : EndP (D (k + 1)) →o EndP (D (k + 1)) => F a)
    (PhiCocone.projEndDown_insEndUp k)

-- [D-2522] insEndUp_injective
theorem insEndUp_injective (k : ℕ) :
    Function.Injective (fun a : EndP (D (k + 1)) => (PhiCocone.insEndUp k).toFun a) := by
  intro a b hab
  rw [← insEndUp_retract k a, ← insEndUp_retract k b]
  exact congrArg _ hab

-- [D-2523] fix_transport
theorem fix_transport {k t : ℕ} {p : EndP (D (k + 1))}
    (h : canonGen (markedPt (k + 1)) (tagInj t p) = tagInj t p) :
    canonGen markedB (tagInj t ((PhiCocone.insEndUp k).toFun p))
      = tagInj t ((PhiCocone.insEndUp k).toFun p) := by
  have hinj := insEndUp_injective k
  rw [CanonFixed.fixed_iff] at h ⊢
  by_cases h0 : t = 0
  · subst h0
    trivial
  · by_cases h1 : t = 1
    · subst h1
      have hpb : p ≠ ⊥ := h
      show (PhiCocone.insEndUp k).toFun p ≠ ⊥
      intro hc
      exact hpb (hinj (hc.trans (PhiCocone.insEndUp k).map_bot.symm))
    · have hp2 : tagInj t p = Sum.inr (Sum.inr p) := by
        unfold tagInj; rw [if_neg h0, if_neg h1]
      have hq2 : tagInj t ((PhiCocone.insEndUp k).toFun p)
          = Sum.inr (Sum.inr ((PhiCocone.insEndUp k).toFun p)) := by
        unfold tagInj; rw [if_neg h0, if_neg h1]
      rw [hp2] at h
      rw [hq2]
      obtain ⟨hb, hm⟩ := h
      refine ⟨?_, ?_⟩
      · intro hc
        exact hb (hinj (hc.trans (PhiCocone.insEndUp k).map_bot.symm))
      · intro hc
        exact hm (hinj (hc.trans (PhiCocone.insEndUp k).map_mark.symm))

-- [D-2524] §The-legs-read-the-tower-back
-- [D-2525] himg_ge
theorem himg_ge (d : phiTowerEP.shift.Bilim) {j k : ℕ} (hjk : j ≤ k) :
    PhiCocone.pLeg j (PhiCocone.eLeg k (d.1 k)) = d.1 j := by
  rw [PhiCoconeLUB.isColimitCocone.proj_prjLe hpm hem hjk (PhiCocone.eLeg k (d.1 k)),
    PhiCoconeLUB.isColimitCocone.retraction k (d.1 k)]
  exact Bilim_prjLe_eq d hjk

-- [D-2526] §The-chain-and-its-tag
-- [D-2527] chain_mono
theorem chain_mono (d : phiTowerEP.shift.Bilim) :
    Monotone fun k => PhiCocone.eLeg k (d.1 k) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  have hd : phiTowerEP.emb (k + 1) (d.1 k) ≤ d.1 (k + 1) := by
    rw [← d.2 k]
    exact emb_prj_le phiTowerEP (k + 1) (d.1 (k + 1))
  calc PhiCocone.eLeg k (d.1 k)
      = PhiCocone.eLeg (k + 1) (phiTowerEP.emb (k + 1) (d.1 k)) :=
        (PhiCocone.cocone_compat k (d.1 k)).symm
    _ ≤ PhiCocone.eLeg (k + 1) (d.1 (k + 1)) := hem (k + 1) hd

-- [D-2528] tag_mono
theorem tag_mono (d : phiTowerEP.shift.Bilim) :
    Monotone fun k => tagIdx (d.1 k).1 := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show tagIdx (d.1 k).1 ≤ tagIdx (d.1 (k + 1)).1
  rw [d_val d k]
  refine le_trans (tagIdx_canonGen_le _ _) ?_
  rw [tagIdx_baseMapGen]

-- [D-2529] §The-construction
-- [D-2530] exists_lub_with_proj
set_option maxHeartbeats 2000000 in
theorem exists_lub_with_proj (d : phiTowerEP.shift.Bilim) :
    ∃ x : PhiBilimit.phiB,
      IsLUB (Set.range fun k => PhiCocone.eLeg k (d.1 k)) x ∧
      ∀ j, PhiCocone.pLeg j x = d.1 j := by
  classical
  obtain ⟨N, hN⟩ := exists_eventually_const (tag_mono d) (fun k => tagIdx_le_two _)
  obtain ⟨t, hts⟩ : ∃ t : ℕ, tagIdx (d.1 N).1 = t := ⟨_, rfl⟩
  have ht : t ≤ 2 := by rw [← hts]; exact tagIdx_le_two _
  have htagN : ∀ i, tagIdx (d.1 (N + i)).1 = t := by
    intro i
    have h1 : tagIdx (d.1 (N + i)).1 = tagIdx (d.1 N).1 := hN (N + i) (Nat.le_add_right N i)
    rw [h1, hts]
  have hpay : ∀ i, ∃ pi : EndP (D (N + i + 1)), (d.1 (N + i)).1 = tagInj t pi := by
    intro i
    obtain ⟨pi, hpi⟩ := exists_payload (d.1 (N + i)).1
    exact ⟨pi, by rw [hpi, htagN i]⟩
  choose p hp using hpay
  have hfixp : ∀ i, canonGen (markedPt (N + i + 1)) (tagInj t (p i)) = tagInj t (p i) := by
    intro i
    rw [← hp i]
    exact (d.1 (N + i)).2
  have hstep : ∀ i, p i = ((iter (N + i)).endDown).toFun (p (i + 1)) := by
    intro i
    refine canonGen_tagInj_inj (markedPt (N + i + 1)) t ?_
    have e1 : canonGen (markedPt (N + i + 1)) (tagInj t (p i)) = (d.1 (N + i)).1 := by
      rw [← hp i]
      exact (d.1 (N + i)).2
    have e2 : (d.1 (N + i)).1
        = canonGen (markedPt (N + i + 1)) (baseMapGen ((iter (N + i)).endDown).toFun
            (d.1 (N + i + 1)).1) := d_val d (N + i)
    have e3 : (d.1 (N + i + 1)).1 = tagInj t (p (i + 1)) := hp (i + 1)
    rw [e1, e2, e3, baseMapGen_tagInj]
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ → ScottEndP B,
      ∀ i, q i = (PhiCocone.insEndUp (N + i)).toFun (p i) := ⟨_, fun _ => rfl⟩
  have hq : Monotone q := by
    refine monotone_nat_of_le_succ (fun i => ?_)
    have e1 : q (i + 1) = (PhiCocone.insEndUp (N + i + 1)).toFun (p (i + 1)) := hqdef (i + 1)
    rw [hqdef i, e1, hstep i, ← PhiCocone.insEndUp_comp_emb (N + i)]
    exact (PhiCocone.insEndUp (N + i + 1)).toFun.monotone
      (endUp_endDown_le (iter (N + i)) (p (i + 1)))
  have hfixq : ∀ s ∈ Set.range q, canonGen markedB (tagInj t s) = tagInj t s := by
    rintro _ ⟨i, rfl⟩
    rw [hqdef i]
    exact fix_transport (hfixp i)
  have htail : ∀ i, PhiCocone.eLeg (N + i) (d.1 (N + i))
      = tagPt t markedB markedB_ne_bot endPB_bot_ne_top (q i) := by
    intro i
    rw [hqdef i]
    refine Subtype.ext ?_
    show canonGen markedB (baseMapGen (PhiCocone.insEndUp (N + i)).toFun (d.1 (N + i)).1)
      = canonGen markedB (tagInj t ((PhiCocone.insEndUp (N + i)).toFun (p i)))
    rw [hp i, baseMapGen_tagInj]
  refine ⟨tagPt t markedB markedB_ne_bot endPB_bot_ne_top (chainSup q hq), ?_, ?_⟩
  · have h1 := tagPt_isLUB ht markedB markedB_ne_bot markedB_ne_top endPB_bot_ne_top
      (chainSup_isLUB q hq) (range_nonempty q) hfixq
    have h2 : (tagPt t markedB markedB_ne_bot endPB_bot_ne_top '' Set.range q)
        = Set.range fun i => PhiCocone.eLeg (N + i) (d.1 (N + i)) := by
      ext w
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, htail i⟩
      · rintro ⟨i, rfl⟩
        exact ⟨q i, ⟨i, rfl⟩, (htail i).symm⟩
    rw [h2] at h1
    exact isLUB_of_tail (chain_mono d) h1
  · intro j
    obtain ⟨r, hrdef⟩ : ∃ r : ℕ → EndP (D (j + 1)),
        ∀ i, r i = (PhiCocone.projEndDown j).toFun (q i) := ⟨_, fun _ => rfl⟩
    have hrmono : Monotone r := by
      intro a b hab
      rw [hrdef a, hrdef b]
      exact (PhiCocone.projEndDown j).toFun.monotone (hq hab)
    have hr : IsLUB (Set.range r) ((PhiCocone.projEndDown j).toFun (chainSup q hq)) := by
      have h0 : Set.range r = Set.range fun i => (PhiCocone.projEndDown j).toFun (q i) := by
        ext w
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨i, (hrdef i).symm⟩
        · rintro ⟨i, rfl⟩; exact ⟨i, hrdef i⟩
      rw [h0]
      exact projEndDown_isLUB q hq j
    have hconst : ∀ i, j ≤ N + i →
        tagPt t (markedPt (j + 1)) (hmk (j + 1)) (hbtk (j + 1)) (r i) = d.1 j := by
      intro i hji
      rw [hrdef i, ← pLeg_tagPt j t (q i), ← htail i]
      exact himg_ge d hji
    have hrconst : ∀ i, r (j + i) = r j := by
      intro i
      refine tagPt_injective t (markedPt (j + 1)) (hmk (j + 1)) (hbtk (j + 1)) ?_
      rw [hconst (j + i) (by omega), hconst j (by omega)]
    have hset : (Set.range fun i => r (j + i)) = {r j} := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩
        exact hrconst i
      · rintro rfl
        exact ⟨0, rfl⟩
    have hlt := PhiCoconeLUB.isLUB_tail hrmono hr j
    rw [hset] at hlt
    have heq : (PhiCocone.projEndDown j).toFun (chainSup q hq) = r j :=
      hlt.unique isLUB_singleton
    rw [pLeg_tagPt j t (chainSup q hq), heq]
    exact hconst j (by omega)

-- [D-2531] §The-two-hypotheses-and-Theorem-A-s-order
-- [D-2532] phiSupExists
theorem phiSupExists : PhiCocone.PhiSupExists := by
  intro d
  obtain ⟨x, hx, _⟩ := exists_lub_with_proj d
  exact ⟨x, hx⟩

-- [D-2533] phiProjContinuous
theorem phiProjContinuous : PhiCocone.PhiProjContinuous := by
  intro d x hx j
  obtain ⟨x0, hx0, hproj⟩ := exists_lub_with_proj d
  have hxx : x = x0 := hx.unique hx0
  rw [hxx, hproj j]
  constructor
  · rintro _ ⟨k, rfl⟩
    rcases le_total j k with hjk | hkj
    · exact le_of_eq (himg_ge d hjk)
    · exact le_trans (hpm j (hx0.1 ⟨k, rfl⟩)) (le_of_eq (hproj j))
  · intro w hw
    exact le_trans (le_of_eq (himg_ge d (le_refl j)).symm) (hw ⟨j, rfl⟩)

-- [D-2534] theoremA_orderIso
noncomputable def theoremA_orderIso : PhiBilimit.phiB ≃o phiTowerEP.Bilim :=
  PhiCoconeLUB.theoremA_orderIso phiSupExists phiProjContinuous

end PhiSurjective
