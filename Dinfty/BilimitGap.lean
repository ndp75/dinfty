import Dinfty.CopyCHigh
import Dinfty.PhiBilimit

open GluingTowerLibrary SierpinskiApplication

/-!
# `B` and `DBilimit` are not the same domain

Theorem A is proved about `B = phiTowerEP.Bilim` (the `Φ`-iterate bilimit);
Theorem B is proved about `DBilimit` (the legacy `iotaD` bilimit).  Nothing in
the development identifies them, and this module shows nothing can: **they are
not order-isomorphic.**

## The invariant

The two towers differ at `⊤` — `glueAA` preserves it, `iotaD` does not
(`FTowerTripointed.glueAA_top`, `glueAA_top_ne_iotaD_top`).  That difference is
visible in the bilimits as compactness of the top:

* In `DBilimit`, `⊤ = topSeq` is the supremum of its own approximating chain
  `insertAtLevel n (topSeq.1 n)`, and that chain **never reaches it**
  (`insertAtLevel_topSeq_ne`), because `iotaD n ⊤ ≠ ⊤`.  So `topSeq` is not
  compact.
* In `B`, `z.1 0 = ⊤` already forces `z = topB`: the deflation gives
  `emb k ⊤ ≤ z.1 (k+1)`, and `emb k ⊤ = ⊤` because `glueAA` is tripointed, so
  the top propagates up every level.  With levels finite, `topB` is compact.

Order isomorphisms preserve the top and preserve compactness, so no
`B ≃o DBilimit` exists.

## What this costs

Theorem A and Theorem B are, as they stand, statements about **different
objects**.  `rigid_of_orderIso` below records what an identification would have
bought — Theorem B's rigidity transferred to Theorem A's carrier — and
`no_orderIso` says it is not available.  Whether some *other* relation between
the two (a retraction, an embedding, agreement on a sub-domain) suffices for the
paper's purposes is not settled here.
-/

open Set

namespace BilimitGap

open PhiIterateTower PhiBilimit EpPairTower

/-! ## 1.  ω-compactness, and its invariance -/

/-- Compactness against increasing `ℕ`-chains.  Enough for the argument, and it
avoids needing a complete lattice on either side. -/
def OmegaCompact {α : Type*} [PartialOrder α] (x : α) : Prop :=
  ∀ c : ℕ → α, Monotone c → ∀ s, IsLUB (Set.range c) s → x ≤ s → ∃ n, x ≤ c n

theorem OmegaCompact.map {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {x : α} (h : OmegaCompact x) : OmegaCompact (e x) := by
  intro c hc s hs hxs
  have hc' : Monotone (fun n => e.symm (c n)) := fun a b hab => e.symm.monotone (hc hab)
  have hs' : IsLUB (Set.range fun n => e.symm (c n)) (e.symm s) := by
    have h1 : IsLUB (e.symm '' Set.range c) (e.symm s) :=
      (OrderIso.isLUB_image' e.symm).mpr hs
    rwa [← Set.range_comp] at h1
  have hxs' : x ≤ e.symm s := by
    have := e.symm.monotone hxs
    rwa [e.symm_apply_apply] at this
  obtain ⟨n, hn⟩ := h _ hc' _ hs' hxs'
  refine ⟨n, ?_⟩
  have := e.monotone hn
  rwa [e.apply_symm_apply] at this

/-! ## 2.  In `DBilimit` the top is not compact -/

theorem topSeq_not_omegaCompact : ¬ OmegaCompact topSeq := by
  intro h
  obtain ⟨n, hn⟩ := h (fun n => insertAtLevel n (topSeq.1 n))
    (fun a b hab => insertAtLevel_chain_mono topSeq hab) topSeq
    (chainSet_isLUB topSeq) (le_refl _)
  exact insertAtLevel_topSeq_ne n (le_antisymm (le_topSeq _) hn)

/-! ## 3.  In `B` the top IS compact -/

theorem topB_val (k : ℕ) : (topB : B).1 k = (⊤ : D (k + 1)) := rfl

theorem level_top_succ {z : B} {k : ℕ} (h : z.1 k = (⊤ : D (k + 1))) :
    z.1 (k + 1) = (⊤ : D (k + 2)) := by
  have hp : (iter k).prj (z.1 (k + 1)) = z.1 k := z.2 k
  have hd : (iter k).emb ((iter k).prj (z.1 (k + 1))) ≤ z.1 (k + 1) :=
    (iter k).deflation _
  rw [hp, h, (iter k).emb_top] at hd
  refine le_antisymm ?_ hd
  exact le_top (α := D (k + 2))

theorem eq_topB_of_zero_top {z : B} (h : z.1 0 = (⊤ : D 1)) : z = topB := by
  refine Subtype.ext (funext fun k => ?_)
  rw [topB_val k]
  induction k with
  | zero => exact h
  | succ k ih => exact level_top_succ ih

theorem le_topB (z : B) : z ≤ topB := by
  intro k
  show z.1 k ≤ (⊤ : D (k + 1))
  exact le_top (α := D (k + 1))

theorem topB_omegaCompact : OmegaCompact (topB : B) := by
  intro c hc s hs hts
  have hstop : s = topB := le_antisymm (le_topB s) hts
  subst hstop
  have hdir : DirectedOn (· ≤ ·) (Set.range c) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨c (max a b), ⟨max a b, rfl⟩, hc (le_max_left a b), hc (le_max_right a b)⟩
  have hlvl := EpPairTower.isLUB_bilim_apply phiTowerEP_isDcpo hs ⟨c 0, 0, rfl⟩ hdir 0
  have himg : ((fun x : B => x.1 0) '' Set.range c) = Set.range fun n => (c n).1 0 := by
    rw [← Set.range_comp]
    rfl
  rw [himg, topB_val 0] at hlvl
  -- a monotone chain in a finite poset stabilises
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => (c n).1 0, fun a b hab => (hc hab) 0⟩ : ℕ →o D 1)
  have hub : ∀ b ∈ Set.range fun n => (c n).1 0, b ≤ (c N).1 0 := by
    rintro _ ⟨m, rfl⟩
    rcases le_total N m with hle | hle
    · exact le_of_eq (hN m hle).symm
    · exact (hc hle) 0
  have htop0 : (⊤ : D 1) ≤ (c N).1 0 := hlvl.2 hub
  exact ⟨N, le_of_eq (eq_topB_of_zero_top (le_antisymm (le_top (α := D 1)) htop0)).symm⟩

/-! ## 4.  So there is no order isomorphism -/

theorem no_orderIso : ¬ Nonempty (B ≃o DBilimit) := by
  rintro ⟨e⟩
  have htop : e topB = topSeq := by
    refine le_antisymm (le_topSeq _) ?_
    have := e.monotone (le_topB (e.symm topSeq))
    rwa [e.apply_symm_apply] at this
  exact topSeq_not_omegaCompact (htop ▸ topB_omegaCompact.map e)

/-! ## 5.  What an identification would have bought -/

theorem rigid_of_orderIso (e : B ≃o DBilimit) : Subsingleton (B ≃o B) := by
  haveI := CopyCHigh.DBilimit_rigid
  refine ⟨fun f g => ?_⟩
  have h : (e.symm.trans (f.trans e) : DBilimit ≃o DBilimit)
      = (e.symm.trans (g.trans e)) := Subsingleton.elim _ _
  refine OrderIso.ext (funext fun x => ?_)
  have hx : (e.symm.trans (f.trans e)) (e x) = (e.symm.trans (g.trans e)) (e x) := by
    rw [h]
  simp only [OrderIso.trans_apply, OrderIso.symm_apply_apply] at hx
  exact e.injective hx

end BilimitGap
