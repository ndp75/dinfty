import Dinfty.JoinIrredDInfty

open GluingTowerLibrary SierpinskiApplication

/-!
# "Distance to `D_0`" has no foothold at either end of `DInfty`

The residue is `StageFixed` — can an automorphism raise a join-irreducible's
level?  Equivalently: is *distance down the hierarchy to `D_0`* an order
invariant?  It is exactly the quantity `lev z := min {k | z ∈ toD k '' D k}`,
and asking for it to be order-theoretic is asking for `StageFixed` itself, so
the question is only useful if some order-theoretic **proxy** for `lev` exists.

The two obvious proxies are height above the bottom and depth below the top.
This module rules out both, by theorem rather than by remark.

* **`DInfty` is atomless** (`no_isAtom`): every non-`⊥` element strictly
  dominates a non-`⊥` element.  The witness is explicit — the *spike*
  `s_x(t) = if t = ⊤ then x else ⊥`, which sits strictly between `⊥` and
  `constHom x` in `EndP (D k)`, hence `glueA m s_x` strictly between `⊥` and
  `iotaD k x` in `D (k+1)`.  So `iotaD` does not preserve atoms, atoms shrink at
  every level, and none survives to the colimit.  No height function exists.
* **`DInfty` has no greatest element** (`no_top`): `toD k ⊤ < toD (k+1) ⊤`,
  because `iotaD_ne_top`.  So there are no coatoms either, and no depth
  function.

Both ends are structureless.  That is the precise reason rank-, cover- and
counting-based invariants are dead here, and why `StageFixed` needs an invariant
that is order-theoretic **and finiteness-free** — a kind nothing in the corpus
supplies.

Note the contrast with the finite levels, where all of this works: every `D k`
has a unique atom and coatom (`UniqueAtomCoatom`).  The structure is destroyed
precisely by passing to the colimit, and `iotaD`'s failure to preserve atoms is
the mechanism.
-/

open scoped Classical

namespace DInftyNoFootholds

open JoinIrredDInfty ColimitCompatPipe Assembly

/-! ## The spike -/

/-- `s_x(t) = if t = ⊤ then x else ⊥` — the endomorphism that witnesses
atomlessness one level up. -/
noncomputable def spike (k : ℕ) (x : D k) : EndP (D k) :=
  ⟨fun t => if t = (⊤ : D k) then x else (⊥ : D k), by
    intro a b hab
    dsimp only
    by_cases ha : a = (⊤ : D k)
    · have hb : b = (⊤ : D k) := le_antisymm le_top (ha ▸ hab)
      rw [if_pos ha, if_pos hb]
    · rw [if_neg ha]; exact bot_le⟩

@[simp] theorem spike_apply_top (k : ℕ) (x : D k) : spike k x (⊤ : D k) = x := by
  show (if (⊤ : D k) = (⊤ : D k) then x else ⊥) = x
  rw [if_pos rfl]

theorem spike_apply_bot (k : ℕ) (x : D k) : spike k x (⊥ : D k) = (⊥ : D k) := by
  show (if (⊥ : D k) = (⊤ : D k) then x else ⊥) = ⊥
  rw [if_neg bot_ne_top_of_nontrivial]

theorem spike_le_constHom (k : ℕ) (x : D k) : spike k x ≤ (constHom x : EndP (D k)) := by
  rw [OrderHom.le_def]
  intro t
  rw [constHom_apply]
  show (if t = (⊤ : D k) then x else ⊥) ≤ x
  split_ifs with h
  · exact le_rfl
  · exact bot_le

theorem spike_ne_bot (k : ℕ) {x : D k} (hx : x ≠ (⊥ : D k)) :
    spike k x ≠ (⊥ : EndP (D k)) := by
  intro h
  have := congrArg (fun f : EndP (D k) => f (⊤ : D k)) h
  rw [spike_apply_top] at this
  exact hx this

theorem spike_ne_constHom (k : ℕ) {x : D k} (hx : x ≠ (⊥ : D k)) :
    spike k x ≠ (constHom x : EndP (D k)) := by
  intro h
  have := congrArg (fun f : EndP (D k) => f (⊥ : D k)) h
  rw [spike_apply_bot, constHom_apply] at this
  exact hx this.symm

/-! ## Atomlessness -/

/-- **Every non-`⊥` element of `DInfty` strictly dominates a non-`⊥` element.**
The witness lives one level up: `glueA m (spike k x)`. -/
theorem exists_lt_lt_of_ne_bot {z : DInfty} (hz : z ≠ (⊥ : DInfty)) :
    ∃ w : DInfty, (⊥ : DInfty) < w ∧ w < z := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    have hx : x ≠ (⊥ : D k) := fun h => hz (by
      rw [show (Quotient.mk dInftySetoid (⟨k, x⟩ : Σ n, D n)) = toD k x from rfl, h]
      exact (bot_eq_toD k).symm)
    have hnd := D_marked_point_nondegenerate k
    refine ⟨toD (k + 1) (glueA (markedPt k) (spike k x)), ?_, ?_⟩
    · -- `⊥ = toD (k+1) (glueA m ⊥) < toD (k+1) (glueA m (spike k x))`
      rw [bot_eq_toD (k + 1)]
      refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr bot_le) ?_
      intro hcon
      exact spike_ne_bot k hx
        (glueA_injective (markedPt k)
          ((glueA_bot (markedPt k) hnd.1 hnd.2.1 hnd.2.2).trans
            (toD_inj (k + 1) hcon))).symm
    · show toD (k + 1) (glueA (markedPt k) (spike k x)) < toD k x
      rw [← toD_iotaD k x]
      refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr ?_) ?_
      · exact (glueA_le_iff (markedPt k) hnd.1 _ _).mpr (spike_le_constHom k x)
      · intro hcon
        exact spike_ne_constHom k hx
          (glueA_injective (markedPt k) (toD_inj (k + 1) hcon))

/-- **`DInfty` is atomless.**  No height function above `⊥` exists, so no
rank-, cover- or atom-based invariant can detect the hierarchy. -/
theorem no_isAtom (a : DInfty) : ¬ IsAtom a := by
  rintro ⟨hne, hmin⟩
  obtain ⟨w, hw0, hwa⟩ := exists_lt_lt_of_ne_bot hne
  exact absurd (hmin w hwa) (ne_of_gt hw0)

/-! ## No top -/

/-- **`DInfty` has no greatest element**, since `iotaD k ⊤ ≠ ⊤`.  So there are
no coatoms and no depth function either. -/
theorem no_top (z : DInfty) : ∃ w : DInfty, z < w := by
  induction z using Quotient.inductionOn with
  | _ p =>
    obtain ⟨k, x⟩ := p
    refine ⟨toD (k + 1) (⊤ : D (k + 1)), ?_⟩
    show toD k x < toD (k + 1) (⊤ : D (k + 1))
    rw [← toD_iotaD k x]
    refine lt_of_le_of_ne ((toD_le_iff' (k + 1) _ _).mpr le_top) ?_
    intro hcon
    exact iotaD_ne_top k x (toD_inj (k + 1) hcon)

/-- **Both ends are structureless**, stated together — the answer to "is
distance to `D_0` reachable from the order?" at the two places one would try. -/
theorem no_footholds :
    (∀ a : DInfty, ¬ IsAtom a) ∧ (∀ z : DInfty, ∃ w : DInfty, z < w) :=
  ⟨no_isAtom, no_top⟩

end DInftyNoFootholds
