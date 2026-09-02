import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

/-!
# Level-stability of join-irreducibility — clause (3b) of the join-recoverability
bridge

`Colimit Compat Handoff.md` §9.2 states, for the first time, the third
sub-problem of Angle A (order-definability of the stages inside `DInfty`).  Its
substantive clause is:

> **(3b) Join-irreducibility is level-stable.**  For `x ∈ D k`,
> `JoinIrred DInfty (toD k x) ↔ JoinIrred (D k) x` — equivalently
> `J(S_k) = S_k ∩ J(DInfty)`.

§9.3 observed that every ingredient was already on file and only the composition
was missing.  This module is that composition, at the tower level.

**Why it is two lemmas.**  `iotaD k x` is *definitionally*
`glueA (OrderHom.id : EndP (D k)) (constHom x)`, so one step of the tower factors
through `EndP`:

    JoinIrred (D (k+1)) (iotaD k x)
      ↔ JoinIrred (EndP (D k)) (constHom x)     -- joinIrred_glueA_iff, at m := id
      ↔ JoinIrred (D k) x                       -- joinIrred_constHom_iff

Both are general, sorry-free library results; the marked-point side conditions
come from `D_marked_point_nondegenerate`, and `joinIrred_constHom_iff`'s
`UniqueAtomCoatom` hypothesis from `realUniqueAtomCoatom`.

**Why it matters beyond #3.**  §9.2 records that (3b) is also a *precondition*
for sub-problem #1 to be about the right objects: `NoCrossFiberTie` is a
levelwise statement about `J(D_k)` and its fibres, and without level-stability
those are not the join-irreducibles an automorphism of `DInfty` actually sees.

**Scope.**  What is proved here is the tower-level statement — stability along
`iotaD` and along `iotaLe` at any chase distance.  The `DInfty`-level form quoted
above additionally needs that a colimit join may be evaluated in a common stage
(`DInftySupRep_atLevel`); that step is **not** taken here, and (3b) as stated in
§9.2 is therefore not yet fully closed.  See the note at the end of this file.
-/

open scoped Classical

namespace JoinIrredLevelStable

/-- **One step of the tower preserves and reflects join-irreducibility.**

The composition §9.3 identified: `glueA` at the marked point `markedPt k`, then
`constHom`.  Nothing here is new mathematics — both halves were already in the
library, general and sorry-free; they had simply never been put together. -/
theorem joinIrred_iotaD_iff (k : ℕ) (x : D k) :
    JoinIrred (D (k + 1)) (iotaD k x) ↔ JoinIrred (D k) x := by
  letI := realUniqueAtomCoatom k
  have h := D_marked_point_nondegenerate k
  have hglue : JoinIrred (D (k + 1)) (iotaD k x)
      ↔ JoinIrred (EndP (D k)) (constHom x) :=
    joinIrred_glueA_iff (markedPt k) h.1 h.2.1 h.2.2 (constHom x)
  exact hglue.trans (joinIrred_constHom_iff x)

/-- **Level-stability at any chase distance.**  Induction on the gap, with the
one-step lemma at each rung. -/
theorem joinIrred_iotaLe_iff {k n : ℕ} (h : k ≤ n) (x : D k) :
    JoinIrred (D n) (iotaLe h x) ↔ JoinIrred (D k) x := by
  induction n, h using Nat.le_induction with
  | base => rw [iotaLe_self]
  | succ n hn ih =>
      rw [iotaLe_succ hn]
      exact (joinIrred_iotaD_iff n (iotaLe hn x)).trans ih

/-- Contrapositive form, for the direction the order-definability argument
actually consumes: a stage element that is *not* join-irreducible at its own
level is not join-irreducible at any later level either. -/
theorem not_joinIrred_iotaLe {k n : ℕ} (h : k ≤ n) (x : D k)
    (hx : ¬ JoinIrred (D k) x) : ¬ JoinIrred (D n) (iotaLe h x) :=
  fun hcon => hx ((joinIrred_iotaLe_iff h x).mp hcon)

/-!
## What remains for (3b) as stated in §9.2

The `DInfty`-level statement `JoinIrred DInfty (toD k x) ↔ JoinIrred (D k) x`
needs one further step on top of the above: that a decomposition
`toD k x = a ⊔ b` in `DInfty` can be evaluated in a common stage, so that
`DInfty`-join-irreducibility is levelwise join-irreducibility at every stage
above `k`.  The ingredient for that is `DInftySupRep_atLevel`
(`SierpinskiApplication.lean:1081`), which says a `DInfty` join agrees with the
join computed at any level dominating both representatives.

That step is deliberately **not** taken in this module: it is a statement about
`DInfty`'s lattice structure rather than about the tower, and it deserves to be
proved rather than assumed to follow.  Until it is, cite this module as
*"level-stability along the tower"*, not as clause (3b).
-/

end JoinIrredLevelStable
