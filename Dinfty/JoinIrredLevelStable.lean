import Dinfty.MonotoneInjectionRigid

open GluingTowerLibrary SierpinskiApplication

-- [D-1576] §Level-stability-of-join-irreducibility-clause-3b
open scoped Classical

namespace JoinIrredLevelStable

-- [D-1577] joinIrred_iotaD_iff
theorem joinIrred_iotaD_iff (k : ℕ) (x : D k) :
    JoinIrred (D (k + 1)) (iotaD k x) ↔ JoinIrred (D k) x := by
  letI := realUniqueAtomCoatom k
  have h := D_marked_point_nondegenerate k
  have hglue : JoinIrred (D (k + 1)) (iotaD k x)
      ↔ JoinIrred (EndP (D k)) (constHom x) :=
    joinIrred_glueA_iff (markedPt k) h.1 h.2.1 h.2.2 (constHom x)
  exact hglue.trans (joinIrred_constHom_iff x)

-- [D-1578] joinIrred_iotaLe_iff
theorem joinIrred_iotaLe_iff {k n : ℕ} (h : k ≤ n) (x : D k) :
    JoinIrred (D n) (iotaLe h x) ↔ JoinIrred (D k) x := by
  induction n, h using Nat.le_induction with
  | base => rw [iotaLe_self]
  | succ n hn ih =>
      rw [iotaLe_succ hn]
      exact (joinIrred_iotaD_iff n (iotaLe hn x)).trans ih

-- [D-1579] not_joinIrred_iotaLe
theorem not_joinIrred_iotaLe {k n : ℕ} (h : k ≤ n) (x : D k)
    (hx : ¬ JoinIrred (D k) x) : ¬ JoinIrred (D n) (iotaLe h x) :=
  fun hcon => hx ((joinIrred_iotaLe_iff h x).mp hcon)

-- [D-1580] §What-remains-for-3b-as-stated-in-9-2
end JoinIrredLevelStable
