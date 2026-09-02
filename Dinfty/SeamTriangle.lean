import Dinfty.CodeB

open GluingTowerLibrary SierpinskiApplication

-- [D-3554] §CoreIFS-is-a-triangle-not-a-triple
open Set

universe u

namespace SeamTriangle

-- [D-3555] §1-The-abstract-triangle
-- [D-3556] Seamed
def Seamed {X : Type u} (s : Fin 3 → X → X) (p : Fin 3 → X) : Prop :=
  ∀ i j : Fin 3, i ≠ j → s i (p j) = s j (p i)

-- [D-3557] Seamless
def Seamless {X : Type u} (s : Fin 3 → X → X) : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∀ x y : X, s i x ≠ s j y

-- [D-3558] not_seamed_of_seamless
theorem not_seamed_of_seamless {X : Type u} {s : Fin 3 → X → X}
    (h : Seamless s) (p : Fin 3 → X) : ¬ Seamed s p := fun hs =>
  h 0 1 (by decide) (p 1) (p 0) (hs 0 1 (by decide))

-- [D-3559] fix_disjoint_of_seamless
theorem fix_disjoint_of_seamless {X : Type u} {s : Fin 3 → X → X}
    (h : Seamless s) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (Fix (s i)) (Fix (s j)) := by
  rw [Set.disjoint_left]
  intro x hi hj
  have hi' : s i x = x := hi
  have hj' : s j x = x := hj
  exact h i j hij x x (hi'.trans hj'.symm)

-- [D-3560] §2-The-third-seam-at-the-tower
open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild CodeB

-- [D-3561] tagC_mark_eq_tagB_top
theorem tagC_mark_eq_tagB_top :
    tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top markedB
      = tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (⊤ : ScottEndP B) := by
  refine Subtype.ext ?_
  show (if markedB = (⊥ : ScottEndP B) then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
        else if markedB = markedB then Sum.inr (Sum.inl ⊤)
        else Sum.inr (Sum.inr markedB))
      = (if (⊤ : ScottEndP B) = (⊥ : ScottEndP B) then
          (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊤ : ScottEndP B)))
  rw [if_neg markedB_ne_bot, if_pos (rfl : markedB = markedB),
    if_neg (Ne.symm endPB_bot_ne_top)]

-- [D-3562] §3-is-seamed
open Gasket

-- [D-3563] fseq
noncomputable def fseq (j : Fin 3) : Gasket.Gamma → Gasket.Gamma :=
  if j = 0 then Gasket.fA else if j = 1 then Gasket.fB else Gasket.fC

-- [D-3564] gseq
def gseq (j : Fin 3) : Gasket.Gamma :=
  if j = 0 then Gasket.gA else if j = 1 then Gasket.gB else Gasket.gC

-- [D-3565] fseq_zero
theorem fseq_zero : fseq 0 = Gasket.fA := by
  show (if (0 : Fin 3) = 0 then Gasket.fA
        else if (0 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fA
  rw [if_pos (rfl : (0 : Fin 3) = 0)]

-- [D-3566] fseq_one
theorem fseq_one : fseq 1 = Gasket.fB := by
  show (if (1 : Fin 3) = 0 then Gasket.fA
        else if (1 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fB
  rw [if_neg (show (1 : Fin 3) ≠ 0 by decide), if_pos (rfl : (1 : Fin 3) = 1)]

-- [D-3567] fseq_two
theorem fseq_two : fseq 2 = Gasket.fC := by
  show (if (2 : Fin 3) = 0 then Gasket.fA
        else if (2 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fC
  rw [if_neg (show (2 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 1 by decide)]

-- [D-3568] gseq_zero
theorem gseq_zero : gseq 0 = Gasket.gA := by
  show (if (0 : Fin 3) = 0 then Gasket.gA
        else if (0 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gA
  rw [if_pos (rfl : (0 : Fin 3) = 0)]

-- [D-3569] gseq_one
theorem gseq_one : gseq 1 = Gasket.gB := by
  show (if (1 : Fin 3) = 0 then Gasket.gA
        else if (1 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gB
  rw [if_neg (show (1 : Fin 3) ≠ 0 by decide), if_pos (rfl : (1 : Fin 3) = 1)]

-- [D-3570] gseq_two
theorem gseq_two : gseq 2 = Gasket.gC := by
  show (if (2 : Fin 3) = 0 then Gasket.gA
        else if (2 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gC
  rw [if_neg (show (2 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 1 by decide)]

-- [D-3571] seam_AB
theorem seam_AB : Gasket.fA Gasket.gB = Gasket.fB Gasket.gA := by
  refine Subtype.ext ?_
  show Gasket.contract cA Gasket.vB = Gasket.contract cB Gasket.vA
  norm_num [Gasket.contract, Gasket.cA, Gasket.cB, Gasket.vA, Gasket.vB, Prod.ext_iff, smul_eq_mul]

-- [D-3572] seam_AC
theorem seam_AC : Gasket.fA Gasket.gC = Gasket.fC Gasket.gA := by
  refine Subtype.ext ?_
  show Gasket.contract cA Gasket.vC = Gasket.contract cC Gasket.vA
  norm_num [Gasket.contract, Gasket.cA, Gasket.cC, Gasket.vA, Gasket.vC, Prod.ext_iff, smul_eq_mul]

-- [D-3573] seam_BC
theorem seam_BC : Gasket.fB Gasket.gC = Gasket.fC Gasket.gB := by
  refine Subtype.ext ?_
  show Gasket.contract cB Gasket.vC = Gasket.contract cC Gasket.vB
  norm_num [Gasket.contract, Gasket.cB, Gasket.cC, Gasket.vB, Gasket.vC, Prod.ext_iff, smul_eq_mul]

-- [D-3574] gasket_seamed
theorem gasket_seamed : Seamed fseq gseq := by
  intro i j hij
  rcases CodeB.fin3_cases i with rfl | rfl | rfl <;>
    rcases CodeB.fin3_cases j with rfl | rfl | rfl <;>
    simp only [fseq_zero, fseq_one, fseq_two, gseq_zero, gseq_one, gseq_two] <;>
    first
      | exact absurd rfl hij
      | exact seam_AB | exact seam_AB.symm
      | exact seam_AC | exact seam_AC.symm
      | exact seam_BC | exact seam_BC.symm

-- [D-3575] §4-The-address-space-is-seamless
-- [D-3576] cons_const
theorem cons_const (j : Fin 3) : Gasket.cons j (fun _ => j) = (fun _ => j) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

-- [D-3577] cons_eq_self
theorem cons_eq_self (j : Fin 3) {w : ℕ → Fin 3} (h : Gasket.cons j w = w) :
    w = fun _ => j := by
  funext n
  induction n with
  | zero => exact (congrFun h 0).symm
  | succ n ih =>
      have h1 : w n = w (n + 1) := congrFun h (n + 1)
      exact h1.symm.trans ih

-- [D-3578] address_seamless
theorem address_seamless : Seamless (fun j : Fin 3 => Gasket.cons j) := by
  intro i j hij x y h
  exact hij (congrFun h 0)

-- [D-3579] fix_cons
theorem fix_cons (j : Fin 3) : Fix (Gasket.cons j) = {(fun _ => j : ℕ → Fin 3)} := by
  ext w
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (cons_eq_self j h)
  · intro h
    show Gasket.cons j w = w
    rw [Set.mem_singleton_iff.mp h]
    exact cons_const j

-- [D-3580] §5-is-the-map-that-installs-the-seams
-- [D-3581] codeGamma_cons
theorem codeGamma_cons (j : Fin 3) (w : ℕ → Fin 3) :
    codeGamma (Gasket.cons j w) = fseq j (codeGamma w) := by
  rcases CodeB.fin3_cases j with rfl | rfl | rfl
  · rw [fseq_zero]; exact codeGamma_cons_zero w
  · rw [fseq_one]; exact codeGamma_cons_one w
  · rw [fseq_two]; exact codeGamma_cons_two w

-- [D-3582] codeGamma_const
theorem codeGamma_const (j : Fin 3) : codeGamma (fun _ => j) = gseq j := by
  rcases CodeB.fin3_cases j with rfl | rfl | rfl
  · rw [gseq_zero]
    refine fA_fixed_unique ?_
    have h := codeGamma_cons_zero (fun _ => (0 : Fin 3))
    rw [cons_const] at h
    exact h.symm
  · rw [gseq_one]
    refine fB_fixed_unique ?_
    have h := codeGamma_cons_one (fun _ => (1 : Fin 3))
    rw [cons_const] at h
    exact h.symm
  · rw [gseq_two]
    refine fC_fixed_unique ?_
    have h := codeGamma_cons_two (fun _ => (2 : Fin 3))
    rw [cons_const] at h
    exact h.symm

-- [D-3583] codeGamma_seam
theorem codeGamma_seam (i j : Fin 3) (hij : i ≠ j) :
    codeGamma (Gasket.cons i (fun _ => j)) = codeGamma (Gasket.cons j (fun _ => i)) := by
  rw [codeGamma_cons, codeGamma_cons, codeGamma_const, codeGamma_const]
  exact gasket_seamed i j hij

-- [D-3584] codeB_seam_ne
theorem codeB_seam_ne (i j : Fin 3) (hij : i ≠ j) :
    codeB (Gasket.cons i (fun _ => j)) ≠ codeB (Gasket.cons j (fun _ => i)) := by
  rw [codeB_cons, codeB_cons]
  exact CodeB.sig_ne_of_ne i j hij _ _

-- [D-3585] codeB_seamless
theorem codeB_seamless : Seamless CodeB.sig := fun i j hij x y => CodeB.sig_ne_of_ne i j hij x y

-- [D-3586] codeB_not_seamed
theorem codeB_not_seamed (p : Fin 3 → B) : ¬ Seamed CodeB.sig p :=
  not_seamed_of_seamless codeB_seamless p

-- [D-3587] rho_not_injective
theorem rho_not_injective : ¬ Function.Injective CodeB.rho := by
  intro hinj
  refine codeB_seam_ne 0 1 (by decide) ?_
  have h : CodeB.rho ⟨codeB (Gasket.cons 0 (fun _ => 1)),
        codeB_mem_attractor _⟩
      = CodeB.rho ⟨codeB (Gasket.cons 1 (fun _ => 0)), codeB_mem_attractor _⟩ := by
    rw [CodeB.rho_codeB, CodeB.rho_codeB]
    exact codeGamma_seam 0 1 (by decide)
  exact congrArg Subtype.val (hinj h)

-- [D-3588] §6-The-openness-failure-is-at-the-a-b-seam
-- [D-3589] mid_eq_seam
theorem mid_eq_seam : Gasket.mid = ((fseq 0 (gseq 1) : Gasket.Gamma) : Gasket.E) := by
  rw [fseq_zero, gseq_one]
  rfl

-- [D-3590] openness_fails_at_seam
theorem openness_fails_at_seam :
    Gasket.mid = ((fseq 0 (gseq 1) : Gasket.Gamma) : Gasket.E) ∧ ¬ IsOpenMap codeGamma :=
  ⟨mid_eq_seam, Gasket.notOpen⟩

-- [D-3591] §7-fix-card-s-fixB-fixC-unsatisfiable-inside-Core
-- [D-3592] fix_sig_inter_attractor
theorem fix_sig_inter_attractor (j : Fin 3) :
    Fix (CodeB.sig j) ∩ CodeB.Attractor = {codeB (fun _ => j)} := by
  ext x
  constructor
  · rintro ⟨hfix, w, rfl⟩
    have hfix' : CodeB.sig j (codeB w) = codeB w := hfix
    have h : codeB (Gasket.cons j w) = codeB w := by rw [codeB_cons]; exact hfix'
    have hw : w = fun _ => j := cons_eq_self j (codeB_injective h)
    exact Set.mem_singleton_iff.mpr (by rw [hw])
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    refine ⟨?_, codeB_mem_attractor _⟩
    show CodeB.sig j (codeB (fun _ => j)) = codeB (fun _ => j)
    rw [← codeB_cons, cons_const]

-- [D-3593] no_fixData_address
theorem no_fixData_address (P : FixPoints Gasket.addressCoreIFS) [FD : FixData P] :
    False := by
  have key : ∀ x : ℕ → Fin 3, x ∈ Fix Gasket.addressCoreIFS.sigmaB → x = fun _ => 1 :=
    fun x hx => cons_eq_self 1 hx
  have h1 : P.xB = fun _ => 1 := key _ (by rw [FD.fixB]; exact Set.mem_insert _ _)
  have h2 : P.m0 = fun _ => 1 := key _ (by rw [FD.fixB]; exact Set.mem_insert_of_mem _ rfl)
  exact FD.xB_ne_m0 (h1.trans h2.symm)

-- [D-3594] inDeg
def inDeg (j : Fin 3) : ℕ := (Finset.univ.filter (fun i : Fin 3 => i ≤ j)).card

-- [D-3595] inDeg_zero
theorem inDeg_zero : inDeg 0 = 1 := by decide
-- [D-3596] inDeg_one
theorem inDeg_one : inDeg 1 = 2 := by decide
-- [D-3597] inDeg_two
theorem inDeg_two : inDeg 2 = 3 := by decide

-- [D-3598] §8-The-shape-the-redefinition-should-take
-- [D-3599] SeamedIFS
structure SeamedIFS (Core Gamma : Type u) where
  s : Fin 3 → Core → Core
  f : Fin 3 → Gamma → Gamma
  p : Fin 3 → Gamma
  seamed : Seamed f p
  seamless : Seamless s

-- [D-3600] addressSeamedIFS
noncomputable def addressSeamedIFS : SeamedIFS (ℕ → Fin 3) Gasket.Gamma where
  s := fun j => Gasket.cons j
  f := fseq
  p := gseq
  seamed := gasket_seamed
  seamless := address_seamless

end SeamTriangle
