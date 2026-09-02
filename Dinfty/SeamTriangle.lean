import Dinfty.CodeB

open GluingTowerLibrary SierpinskiApplication

/-!
# `CoreIFS` is a triangle, not a triple

`CoreIFS` currently carries three self-maps `σ_A, σ_B, σ_C` and three gasket
maps `f_A, f_B, f_C` with **no relation between them**.  That is the wrong
generality, and it is why `TheoremAData` cannot be inhabited as written.

The structure the development actually runs on is *pairwise*: the glued level
identifies the three copies along **three seams, one per unordered pair**, and
they are exactly the three clauses of `canonGen`:

| pair | seam | Lean |
|---|---|---|
| `a`/`b` | tag `B` at `⊥` **is** tag `A` at `m` | `Gasket.tagB_bot_eq_mark` |
| `c`/`a` | tag `C` at `⊥` **is** tag `A` at `⊤` | `Gasket.tagC_bot_eq_top` |
| `b`/`c` | tag `C` at `m` **is** tag `B` at `⊤` | `tagC_mark_eq_tagB_top` (below) |

`CopyHierarchy`'s digraph `a→{a,b,c}`, `b→{b,c}`, `c→{c}` is the *transitive*
shadow of those three edges; the seams are the edges themselves.

## The one predicate

For a three-map system `s : Fin 3 → X → X`,

* `Seamed s p` — the three images **meet**, pairwise, at prescribed points:
  `s i (p j) = s j (p i)` for `i ≠ j`;
* `Seamless s` — the three images are pairwise **disjoint**.

These are exact opposites (`not_seamed_of_seamless`), and the whole `Γ`/`ρ`
picture is that the two sides of `ρ` sit on opposite sides of that line:

* **`Γ` is seamed** (`gasket_seamed`): `f_i(v_j) = f_j(v_i)`, the midpoint of the
  edge `v_i v_j`, three elementary computations in `ℝ²`.
* **the address space is seamless** (`address_seamless`), and so is `𝒦 ⊆ B`
  (`codeB_seamless`, i.e. `CodeB.sig_ne_of_ne`) — `strictConst` never takes the
  values `m` or `⊤`, so the tower's own seams are *never reached by its IFS*.

So `ρ` is exactly the quotient that installs the three seams, and every
`TheoremAData` field that failed, failed at a seam.

## What that settles

1. **`IsOpenMap` (already refuted).**  `GasketNotOpen`'s counterexample point is
   `mid = contract cA vB` — literally the `a`/`b` seam point
   (`mid_eq_seam`).  The refutation is not an accident of the witness: it is the
   seam.
2. **`fix_card`'s `fixB`/`fixC` — the pending item, and the answer is negative.**
   `FixData` demands `|Fix σ_B| = 2` and `|Fix σ_C| = 3` *inside `Core`*.  But
   inside `Core` each `σ_j` has **exactly one** fixed point
   (`fix_cons`, `fix_sig_inter_attractor`), so `FixData` is **unsatisfiable** for
   the address `CoreIFS` (`no_fixData_address`).  The counts `1/2/3` are the
   in-degrees of the copy hierarchy (`inDeg`), i.e. they count the *seam points
   inherited from the copies below* — and those live in the ambient glued level,
   not in the attractor.  `FixData` conflates the two.  G2 is a theorem about
   `D_{k+1}`, not about `𝒦`.

Nothing here redefines `CoreIFS`; `SeamedIFS` below records the shape the
redefinition should take, and is deliberately not instantiated.
-/

open Set

universe u

namespace SeamTriangle

/-! ## 1.  The abstract triangle -/

/-- **Seamed**: the three images meet pairwise, at the prescribed points. -/
def Seamed {X : Type u} (s : Fin 3 → X → X) (p : Fin 3 → X) : Prop :=
  ∀ i j : Fin 3, i ≠ j → s i (p j) = s j (p i)

/-- **Seamless**: the three images are pairwise disjoint. -/
def Seamless {X : Type u} (s : Fin 3 → X → X) : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∀ x y : X, s i x ≠ s j y

theorem not_seamed_of_seamless {X : Type u} {s : Fin 3 → X → X}
    (h : Seamless s) (p : Fin 3 → X) : ¬ Seamed s p := fun hs =>
  h 0 1 (by decide) (p 1) (p 0) (hs 0 1 (by decide))

/-- A seamless system has pairwise disjoint fixed-point sets — the general form
of `Gasket.ifsS_fix_disjoint_AB`/`_AC`, now covering `B`/`C` too. -/
theorem fix_disjoint_of_seamless {X : Type u} {s : Fin 3 → X → X}
    (h : Seamless s) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (Fix (s i)) (Fix (s j)) := by
  rw [Set.disjoint_left]
  intro x hi hj
  have hi' : s i x = x := hi
  have hj' : s j x = x := hj
  exact h i j hij x x (hi'.trans hj'.symm)

/-! ## 2.  The third seam, at the tower

Two of the three are already in `GasketObstruction`.  This is the missing one,
and it completes `a`/`b`, `b`/`c`, `c`/`a`. -/

open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild CodeB

/-- **The `b`/`c` seam.**  The tag-`C` copy of the marked point is the tag-`B`
copy of `⊤`. -/
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

/-! ## 3.  `Γ` is seamed -/

open Gasket

noncomputable def fseq (j : Fin 3) : Gasket.Gamma → Gasket.Gamma :=
  if j = 0 then Gasket.fA else if j = 1 then Gasket.fB else Gasket.fC

def gseq (j : Fin 3) : Gasket.Gamma :=
  if j = 0 then Gasket.gA else if j = 1 then Gasket.gB else Gasket.gC

theorem fseq_zero : fseq 0 = Gasket.fA := by
  show (if (0 : Fin 3) = 0 then Gasket.fA
        else if (0 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fA
  rw [if_pos (rfl : (0 : Fin 3) = 0)]

theorem fseq_one : fseq 1 = Gasket.fB := by
  show (if (1 : Fin 3) = 0 then Gasket.fA
        else if (1 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fB
  rw [if_neg (show (1 : Fin 3) ≠ 0 by decide), if_pos (rfl : (1 : Fin 3) = 1)]

theorem fseq_two : fseq 2 = Gasket.fC := by
  show (if (2 : Fin 3) = 0 then Gasket.fA
        else if (2 : Fin 3) = 1 then Gasket.fB else Gasket.fC) = Gasket.fC
  rw [if_neg (show (2 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 1 by decide)]

theorem gseq_zero : gseq 0 = Gasket.gA := by
  show (if (0 : Fin 3) = 0 then Gasket.gA
        else if (0 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gA
  rw [if_pos (rfl : (0 : Fin 3) = 0)]

theorem gseq_one : gseq 1 = Gasket.gB := by
  show (if (1 : Fin 3) = 0 then Gasket.gA
        else if (1 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gB
  rw [if_neg (show (1 : Fin 3) ≠ 0 by decide), if_pos (rfl : (1 : Fin 3) = 1)]

theorem gseq_two : gseq 2 = Gasket.gC := by
  show (if (2 : Fin 3) = 0 then Gasket.gA
        else if (2 : Fin 3) = 1 then Gasket.gB else Gasket.gC) = Gasket.gC
  rw [if_neg (show (2 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 1 by decide)]

/-- The `a`/`b` seam on `Γ`: the midpoint of `v_A v_B`. -/
theorem seam_AB : Gasket.fA Gasket.gB = Gasket.fB Gasket.gA := by
  refine Subtype.ext ?_
  show Gasket.contract cA Gasket.vB = Gasket.contract cB Gasket.vA
  norm_num [Gasket.contract, Gasket.cA, Gasket.cB, Gasket.vA, Gasket.vB, Prod.ext_iff, smul_eq_mul]

/-- The `c`/`a` seam on `Γ`: the midpoint of `v_A v_C`. -/
theorem seam_AC : Gasket.fA Gasket.gC = Gasket.fC Gasket.gA := by
  refine Subtype.ext ?_
  show Gasket.contract cA Gasket.vC = Gasket.contract cC Gasket.vA
  norm_num [Gasket.contract, Gasket.cA, Gasket.cC, Gasket.vA, Gasket.vC, Prod.ext_iff, smul_eq_mul]

/-- The `b`/`c` seam on `Γ`: the midpoint of `v_B v_C`. -/
theorem seam_BC : Gasket.fB Gasket.gC = Gasket.fC Gasket.gB := by
  refine Subtype.ext ?_
  show Gasket.contract cB Gasket.vC = Gasket.contract cC Gasket.vB
  norm_num [Gasket.contract, Gasket.cB, Gasket.cC, Gasket.vB, Gasket.vC, Prod.ext_iff, smul_eq_mul]

/-- **`Γ` is seamed.** -/
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

/-! ## 4.  The address space is seamless -/

theorem cons_const (j : Fin 3) : Gasket.cons j (fun _ => j) = (fun _ => j) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem cons_eq_self (j : Fin 3) {w : ℕ → Fin 3} (h : Gasket.cons j w = w) :
    w = fun _ => j := by
  funext n
  induction n with
  | zero => exact (congrFun h 0).symm
  | succ n ih =>
      have h1 : w n = w (n + 1) := congrFun h (n + 1)
      exact h1.symm.trans ih

/-- **The address space is seamless** — the head symbol is readable. -/
theorem address_seamless : Seamless (fun j : Fin 3 => Gasket.cons j) := by
  intro i j hij x y h
  exact hij (congrFun h 0)

/-- Inside the address space each `σ_j` has **exactly one** fixed point. -/
theorem fix_cons (j : Fin 3) : Fix (Gasket.cons j) = {(fun _ => j : ℕ → Fin 3)} := by
  ext w
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (cons_eq_self j h)
  · intro h
    show Gasket.cons j w = w
    rw [Set.mem_singleton_iff.mp h]
    exact cons_const j

/-! ## 5.  `ρ` is the map that installs the seams -/

theorem codeGamma_cons (j : Fin 3) (w : ℕ → Fin 3) :
    codeGamma (Gasket.cons j w) = fseq j (codeGamma w) := by
  rcases CodeB.fin3_cases j with rfl | rfl | rfl
  · rw [fseq_zero]; exact codeGamma_cons_zero w
  · rw [fseq_one]; exact codeGamma_cons_one w
  · rw [fseq_two]; exact codeGamma_cons_two w

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

/-- **The seam, in addresses**: `i j j j …` and `j i i i …` name the same point
of `Γ`. -/
theorem codeGamma_seam (i j : Fin 3) (hij : i ≠ j) :
    codeGamma (Gasket.cons i (fun _ => j)) = codeGamma (Gasket.cons j (fun _ => i)) := by
  rw [codeGamma_cons, codeGamma_cons, codeGamma_const, codeGamma_const]
  exact gasket_seamed i j hij

/-- …and they do **not** name the same point of `𝒦`. -/
theorem codeB_seam_ne (i j : Fin 3) (hij : i ≠ j) :
    codeB (Gasket.cons i (fun _ => j)) ≠ codeB (Gasket.cons j (fun _ => i)) := by
  rw [codeB_cons, codeB_cons]
  exact CodeB.sig_ne_of_ne i j hij _ _

/-- **`𝒦 ⊆ B` is seamless** — `CodeB.sig_ne_of_ne`, named. -/
theorem codeB_seamless : Seamless CodeB.sig := fun i j hij x y => CodeB.sig_ne_of_ne i j hij x y

theorem codeB_not_seamed (p : Fin 3 → B) : ¬ Seamed CodeB.sig p :=
  not_seamed_of_seamless codeB_seamless p

/-- **`ρ` is not injective, and the seam is why.** -/
theorem rho_not_injective : ¬ Function.Injective CodeB.rho := by
  intro hinj
  refine codeB_seam_ne 0 1 (by decide) ?_
  have h : CodeB.rho ⟨codeB (Gasket.cons 0 (fun _ => 1)),
        codeB_mem_attractor _⟩
      = CodeB.rho ⟨codeB (Gasket.cons 1 (fun _ => 0)), codeB_mem_attractor _⟩ := by
    rw [CodeB.rho_codeB, CodeB.rho_codeB]
    exact codeGamma_seam 0 1 (by decide)
  exact congrArg Subtype.val (hinj h)

/-! ## 6.  The openness failure is at the `a`/`b` seam -/

/-- `GasketNotOpen`'s counterexample point **is** the `a`/`b` seam point. -/
theorem mid_eq_seam : Gasket.mid = ((fseq 0 (gseq 1) : Gasket.Gamma) : Gasket.E) := by
  rw [fseq_zero, gseq_one]
  rfl

theorem openness_fails_at_seam :
    Gasket.mid = ((fseq 0 (gseq 1) : Gasket.Gamma) : Gasket.E) ∧ ¬ IsOpenMap codeGamma :=
  ⟨mid_eq_seam, Gasket.notOpen⟩

/-! ## 7.  `fix_card`'s `fixB`/`fixC`: unsatisfiable inside `Core` -/

/-- Inside `𝒦 ⊆ B` each `σ_j` has exactly one fixed point, namely `codeB (jjj…)`. -/
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

/-- **`FixData` is unsatisfiable for the address `CoreIFS`.**  `fixB` asks for
two distinct fixed points of `σ_B` in `Core`; there is only one. -/
theorem no_fixData_address (P : FixPoints Gasket.addressCoreIFS) [FD : FixData P] :
    False := by
  have key : ∀ x : ℕ → Fin 3, x ∈ Fix Gasket.addressCoreIFS.sigmaB → x = fun _ => 1 :=
    fun x hx => cons_eq_self 1 hx
  have h1 : P.xB = fun _ => 1 := key _ (by rw [FD.fixB]; exact Set.mem_insert _ _)
  have h2 : P.m0 = fun _ => 1 := key _ (by rw [FD.fixB]; exact Set.mem_insert_of_mem _ rfl)
  exact FD.xB_ne_m0 (h1.trans h2.symm)

/-- The in-degree of copy `j` in the copy hierarchy `a→{a,b,c}`, `b→{b,c}`,
`c→{c}` — how many copies can sit below it.  This is `1/2/3`, the companion
note's G2 counts, and it counts points of the **glued level**, not of `𝒦`. -/
def inDeg (j : Fin 3) : ℕ := (Finset.univ.filter (fun i : Fin 3 => i ≤ j)).card

theorem inDeg_zero : inDeg 0 = 1 := by decide
theorem inDeg_one : inDeg 1 = 2 := by decide
theorem inDeg_two : inDeg 2 = 3 := by decide

/-! ## 8.  The shape the redefinition should take

Not instantiated, and `CoreIFS` is not touched: this only records what §1–§7
say the missing structure is.  A `CoreIFS` should carry, for each unordered
pair, the point at which the two copies are glued — on the `Γ` side as an
equation (`Seamed`), on the `Core` side as its negation (`Seamless`), and `ρ`
as the map that turns the second into the first. -/
structure SeamedIFS (Core Gamma : Type u) where
  s : Fin 3 → Core → Core
  f : Fin 3 → Gamma → Gamma
  p : Fin 3 → Gamma
  /-- the three seams of `Γ`, one per unordered pair -/
  seamed : Seamed f p
  /-- `Core` has none of them -/
  seamless : Seamless s

/-- The gasket side of `addressCoreIFS`, with its seams made explicit. -/
noncomputable def addressSeamedIFS : SeamedIFS (ℕ → Fin 3) Gasket.Gamma where
  s := fun j => Gasket.cons j
  f := fseq
  p := gseq
  seamed := gasket_seamed
  seamless := address_seamless

end SeamTriangle
