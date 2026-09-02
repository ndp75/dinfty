import Dinfty.EmbDImage
import Dinfty.CopyHierarchy

open GluingTowerLibrary SierpinskiApplication

-- [D-3372] §The-tower-s-embeddings-are-tagwise-and-so
open Set

open scoped Classical

namespace EmbTagwise

open PhiTriFunctor GenContinuity

universe u

-- [D-3373] §1-canonGen-is-inert-on-the-image-of-an-injective
section Generic

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {m : P} {m' : P'}

-- [D-3374] ne_mark_of_canon_tagC
theorem ne_mark_of_canon_tagC (c : P) (hc : c ≠ ⊥)
    (hw : canonGen m (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c)) : c ≠ m := by
  intro hcm
  rw [canonGen, if_neg hc, if_pos hcm] at hw
  exact Sum.inl_ne_inr (Sum.inr_injective hw)

-- [D-3375] canonGen_baseMapGen
theorem canonGen_baseMapGen (g : TriHom m m') (hginj : Function.Injective g.toFun)
    {w : GlueBaseGen P} (hw : canonGen m w = w) :
    canonGen m' (baseMapGen g.toFun w) = baseMapGen g.toFun w := by
  cases w with
  | inl a => rfl
  | inr w =>
    cases w with
    | inl b =>
        have hb : b ≠ ⊥ := ne_bot_of_canon_tagBGen m b hw
        have hgb : g.toFun b ≠ ⊥ := fun hc => hb (hginj (hc.trans g.map_bot.symm))
        change canonGen m' (Sum.inr (Sum.inl (g.toFun b))) = _
        rw [canonGen, if_neg hgb]
        rfl
    | inr c =>
        have hc : c ≠ ⊥ := ne_bot_of_canon_tagCGen m c hw
        have hcm : c ≠ m := ne_mark_of_canon_tagC c hc hw
        have hgc : g.toFun c ≠ ⊥ := fun hcon => hc (hginj (hcon.trans g.map_bot.symm))
        have hgcm : g.toFun c ≠ m' := fun hcon => hcm (hginj (hcon.trans g.map_mark.symm))
        change canonGen m' (Sum.inr (Sum.inr (g.toFun c))) = _
        rw [canonGen, if_neg hgc, if_neg hgcm]
        rfl

-- [D-3376] phiFun_val_tagwise
theorem phiFun_val_tagwise (g : TriHom m m') (hm' : m' ≠ ⊥) (hbt' : (⊥ : P') ≠ ⊤)
    (hginj : Function.Injective g.toFun) (x : GlueCarGen (P := P) m) :
    (phiFun g hm' hbt' x).1 = baseMapGen g.toFun x.1 :=
  canonGen_baseMapGen g hginj x.2

-- [D-3377] baseMapGen_copyIdx
theorem baseMapGen_copyIdx (g : P →o P') (w : GlueBaseGen P) :
    CopyHierarchy.copyIdx (baseMapGen g w) = CopyHierarchy.copyIdx w := by
  cases w with
  | inl _ => rfl
  | inr w => cases w with
    | inl _ => rfl
    | inr _ => rfl

end Generic

-- [D-3378] §2-At-the-iterate-tower
open PhiIterateTower PhiTriTower

-- [D-3379] hmk'
private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-3380] hbtk'
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-3381] endDownFun_endUpFun
theorem endDownFun_endUpFun (n : ℕ) (h : EndP (D (n + 1))) :
    (iter n).endDownFun ((iter n).endUpFun h) = h := by
  ext x
  show (iter n).prj ((iter n).emb (h ((iter n).prj ((iter n).emb x)))) = h x
  rw [(iter n).retraction, (iter n).retraction]

-- [D-3382] endUpFun_injective
theorem endUpFun_injective (n : ℕ) : Function.Injective (iter n).endUpFun := by
  intro h h' hh
  rw [← endDownFun_endUpFun n h, ← endDownFun_endUpFun n h', hh]

-- [D-3383] emb_succ_val
theorem emb_succ_val (n : ℕ) (x : D (n + 2)) :
    ((iter (n + 1)).emb x).1 = baseMapGen (iter n).endUp.toFun x.1 :=
  phiFun_val_tagwise (iter n).endUp (hmk' (n + 2)) (hbtk' (n + 2))
    (endUpFun_injective n) x

-- [D-3384] emb_succ_copyIdx
theorem emb_succ_copyIdx (n : ℕ) (x : D (n + 2)) :
    CopyHierarchy.copyIdx ((iter (n + 1)).emb x).1 = CopyHierarchy.copyIdx x.1 := by
  rw [emb_succ_val]
  exact baseMapGen_copyIdx _ _

-- [D-3385] §3-The-image-tagwise
-- [D-3386] mem_range_emb_succ_iff
theorem mem_range_emb_succ_iff (n : ℕ) (z : D (n + 3)) :
    z ∈ Set.range ((iter (n + 1)).emb) ↔
      ∃ w : D (n + 2), baseMapGen (iter n).endUp.toFun w.1 = z.1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (emb_succ_val n w).symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext ((emb_succ_val n w).trans hw)⟩

-- [D-3387] range_val_emb_succ_inl
theorem range_val_emb_succ_inl (n : ℕ) (z : D (n + 3)) (a : EndP (D (n + 2)))
    (hz : z.1 = Sum.inl a) :
    z ∈ Set.range ((iter (n + 1)).emb) ↔ a ∈ Set.range (iter n).endUpFun := by
  constructor
  · rintro ⟨w, rfl⟩
    have hv := emb_succ_val n w
    rw [hz] at hv
    cases hwv : w.1 with
    | inl b =>
        rw [hwv] at hv
        exact ⟨b, (Sum.inl_injective hv).symm⟩
    | inr v =>
        exfalso
        rw [hwv] at hv
        cases v with
        | inl _ => exact Sum.inl_ne_inr hv
        | inr _ => exact Sum.inl_ne_inr hv
  · rintro ⟨b, hb⟩
    refine ⟨glueA (markedPt (n + 1)) b, Subtype.ext ?_⟩
    rw [emb_succ_val, hz, ← hb]
    rfl

end EmbTagwise
