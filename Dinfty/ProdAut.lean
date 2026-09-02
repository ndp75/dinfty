import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Hom.Order
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.UniformSpace.Closeds
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Atoms

open scoped Classical

namespace ProdAut

-- [D-0018] card_axis_obstruction
theorem card_axis_obstruction {nJ nP nUp : ℕ} (h1 : 0 < nJ) (h2 : nJ < nP)
    (_h3 : nUp ≤ nJ) : nJ * (nP - 1) ≠ nUp * nP := by
  intro heq
  obtain ⟨m, rfl⟩ : ∃ m, nP = m + 1 := ⟨nP - 1, by omega⟩
  rw [Nat.add_sub_cancel] at heq
  have hcop : Nat.Coprime (m + 1) m := by
    first
      | exact Nat.coprime_succ_self_left
      | exact Nat.coprime_succ_self m
      | exact Nat.coprime_comm.mp Nat.coprime_succ_self_right
      | simp [Nat.Coprime, Nat.succ_sub_one, Nat.gcd_comm]
  have hdvd : (m + 1) ∣ nJ * m := ⟨nUp, by rw [heq]; ring⟩
  have h4 : (m + 1) ∣ nJ := hcop.dvd_of_dvd_mul_right hdvd
  have h5 := Nat.le_of_dvd h1 h4
  omega

-- [D-0019] axes_never_match
theorem axes_never_match {nJ nP nUp : ℕ} (hpos : 0 < nJ) (hsize : nJ < nP)
    (hup : nUp ≤ nJ) : nJ * (nP - 1) ≠ nUp * nP :=
  card_axis_obstruction hpos hsize hup

variable {A B : Type*} [PartialOrder A] [OrderBot A] [PartialOrder B] [OrderBot B]

-- [D-0020] §Step-1-the-axes-from-the-atoms
-- [D-0021] prod_le_iff
theorem prod_le_iff (p q : A × B) : p ≤ q ↔ p.1 ≤ q.1 ∧ p.2 ≤ q.2 := Iff.rfl

-- [D-0022] botB_le_iff
theorem botB_le_iff (b : B) (x : A × B) : ((⊥ : A), b) ≤ x ↔ b ≤ x.2 :=
  ⟨fun h => h.2, fun h => ⟨bot_le, h⟩⟩

-- [D-0023] axisA_iff
theorem axisA_iff [IsAtomic B] (x : A × B) :
    (∀ b : B, IsAtom b → ¬ (((⊥ : A), b) : A × B) ≤ x) ↔ x.2 = ⊥ := by
  constructor
  · intro h
    rcases (eq_bot_or_exists_atom_le x.2) with hb | ⟨b, hb, hble⟩
    · exact hb
    · exact absurd ((botB_le_iff b x).mpr hble) (h b hb)
  · intro h b hb hle
    rw [botB_le_iff, h] at hle
    exact hb.1 (le_bot_iff.mp hle)

-- [D-0024] botA_le_iff
theorem botA_le_iff (a : A) (x : A × B) : ((a, (⊥ : B)) : A × B) ≤ x ↔ a ≤ x.1 :=
  ⟨fun h => h.1, fun h => ⟨h, bot_le⟩⟩

-- [D-0025] axisB_iff
theorem axisB_iff [IsAtomic A] (x : A × B) :
    (∀ a : A, IsAtom a → ¬ ((a, (⊥ : B)) : A × B) ≤ x) ↔ x.1 = ⊥ := by
  constructor
  · intro h
    rcases (eq_bot_or_exists_atom_le x.1) with ha | ⟨a, ha, hale⟩
    · exact ha
    · exact absurd ((botA_le_iff a x).mpr hale) (h a ha)
  · intro h a ha hle
    rw [botA_le_iff, h] at hle
    exact ha.1 (le_bot_iff.mp hle)

-- [D-0026] §Step-2-every-point-is-the-join-of-its-two
-- [D-0027] isLUB_pair
theorem isLUB_pair (a : A) (b : B) :
    IsLUB {((a, (⊥ : B)) : A × B), (((⊥ : A), b) : A × B)} ((a, b) : A × B) := by
  constructor
  · rintro x (rfl | rfl)
    · exact ⟨le_rfl, bot_le⟩
    · exact ⟨bot_le, le_rfl⟩
  · intro u hu
    exact ⟨(hu (Set.mem_insert _ _)).1,
           (hu (Set.mem_insert_of_mem _ rfl)).2⟩

-- [D-0028] §Step-3-decomposition
-- [D-0029] prod_decomposition_of_axis_preserving
theorem prod_decomposition_of_axis_preserving (φ : (A × B) ≃o (A × B))
    (hA : ∀ a : A, (φ (a, (⊥ : B))).2 = ⊥)
    (hB : ∀ b : B, (φ ((⊥ : A), b)).1 = ⊥)
    (a : A) (b : B) :
    φ (a, b) = ((φ (a, (⊥ : B))).1, (φ ((⊥ : A), b)).2) := by
  have h := (OrderIso.isLUB_image' φ).mpr (isLUB_pair (A := A) (B := B) a b)
  have himg : φ '' {((a, (⊥ : B)) : A × B), (((⊥ : A), b) : A × B)}
      = {φ (a, (⊥ : B)), φ ((⊥ : A), b)} := by
    ext z; constructor
    · rintro ⟨w, (rfl | rfl), rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · rintro (rfl | rfl)
      · exact ⟨(a, (⊥ : B)), Set.mem_insert _ _, rfl⟩
      · exact ⟨((⊥ : A), b), Set.mem_insert_of_mem _ rfl, rfl⟩
  rw [himg] at h
  have h2 : IsLUB {φ (a, (⊥ : B)), φ ((⊥ : A), b)}
      (((φ (a, (⊥ : B))).1, (φ ((⊥ : A), b)).2) : A × B) := by
    constructor
    · rintro x (rfl | rfl)
      · exact ⟨le_rfl, by rw [hA a]; exact bot_le⟩
      · exact ⟨by rw [hB b]; exact bot_le, le_rfl⟩
    · intro u hu
      exact ⟨(hu (Set.mem_insert _ _)).1,
             (hu (Set.mem_insert_of_mem _ rfl)).2⟩
  exact h.unique h2

-- [D-0030] §Closing-the-loop-no-atom-crossing-axes-preserved
-- [D-0031] prod_eq_bot_iff
theorem prod_eq_bot_iff (x : A × B) : x = ⊥ ↔ x.1 = ⊥ ∧ x.2 = ⊥ := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h; exact Prod.ext_iff.mpr ⟨h.1, h.2⟩

-- [D-0032] axisA_preserved
theorem axisA_preserved [IsAtomic B] (φ : (A × B) ≃o (A × B))
    (hsym : ∀ b : B, IsAtom b → (φ.symm (((⊥ : A), b) : A × B)).1 = ⊥)
    (a : A) : (φ ((a, (⊥ : B)) : A × B)).2 = ⊥ := by
  rw [← axisA_iff]
  intro b hb hle
  have h1 : φ.symm (((⊥ : A), b) : A × B) ≤ (a, (⊥ : B)) := by
    have h := φ.symm.monotone hle
    rwa [φ.symm_apply_apply] at h
  have hbot : φ.symm (((⊥ : A), b) : A × B) = ⊥ :=
    (prod_eq_bot_iff _).mpr ⟨hsym b hb, le_bot_iff.mp h1.2⟩
  have : (((⊥ : A), b) : A × B) = ⊥ := by
    have := congrArg φ hbot
    rwa [φ.apply_symm_apply, φ.map_bot] at this
  exact hb.1 (congrArg Prod.snd this)

-- [D-0033] axisB_preserved
theorem axisB_preserved [IsAtomic A] (φ : (A × B) ≃o (A × B))
    (hsym : ∀ a : A, IsAtom a → (φ.symm ((a, (⊥ : B)) : A × B)).2 = ⊥)
    (b : B) : (φ (((⊥ : A), b) : A × B)).1 = ⊥ := by
  rw [← axisB_iff]
  intro a ha hle
  have h1 : φ.symm ((a, (⊥ : B)) : A × B) ≤ ((⊥ : A), b) := by
    have h := φ.symm.monotone hle
    rwa [φ.symm_apply_apply] at h
  have hbot : φ.symm ((a, (⊥ : B)) : A × B) = ⊥ :=
    (prod_eq_bot_iff _).mpr ⟨le_bot_iff.mp h1.1, hsym a ha⟩
  have : ((a, (⊥ : B)) : A × B) = ⊥ := by
    have := congrArg φ hbot
    rwa [φ.apply_symm_apply, φ.map_bot] at this
  exact ha.1 (congrArg Prod.fst this)

-- [D-0034] prod_decomposition_of_no_crossing
theorem prod_decomposition_of_no_crossing [IsAtomic A] [IsAtomic B]
    (φ : (A × B) ≃o (A × B))
    (hB : ∀ b : B, IsAtom b → (φ.symm (((⊥ : A), b) : A × B)).1 = ⊥)
    (hA : ∀ a : A, IsAtom a → (φ.symm ((a, (⊥ : B)) : A × B)).2 = ⊥)
    (a : A) (b : B) :
    φ (a, b) = ((φ ((a, (⊥ : B)) : A × B)).1, (φ (((⊥ : A), b) : A × B)).2) :=
  prod_decomposition_of_axis_preserving φ (axisA_preserved φ hB) (axisB_preserved φ hA) a b

variable {A B : Type*} [PartialOrder A] [OrderBot A] [Fintype A]
  [PartialOrder B] [OrderBot B] [Fintype B]

-- [D-0035] §Up-sets-of-the-two-atom-classes
-- [D-0036] upAatomEquiv
def upAatomEquiv (k : A) : {x : A × B // (k, (⊥ : B)) ≤ x} ≃ {a : A // k ≤ a} × B where
  toFun z := (⟨z.1.1, z.2.1⟩, z.1.2)
  invFun p := ⟨(p.1.1, p.2), ⟨p.1.2, bot_le⟩⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

-- [D-0037] upBatomEquiv
def upBatomEquiv (b : B) : {x : A × B // ((⊥ : A), b) ≤ x} ≃ A × {b' : B // b ≤ b'} where
  toFun z := (z.1.1, ⟨z.1.2, z.2.2⟩)
  invFun p := ⟨(p.1, p.2.1), ⟨bot_le, p.2.2⟩⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

-- [D-0038] card_up_Aatom
theorem card_up_Aatom (k : A) :
    Fintype.card {x : A × B // (k, (⊥ : B)) ≤ x}
      = Fintype.card {a : A // k ≤ a} * Fintype.card B := by
  rw [Fintype.card_congr (upAatomEquiv (B := B) k), Fintype.card_prod]

-- [D-0039] card_up_Batom
theorem card_up_Batom (b : B) :
    Fintype.card {x : A × B // ((⊥ : A), b) ≤ x}
      = Fintype.card A * Fintype.card {b' : B // b ≤ b'} := by
  rw [Fintype.card_congr (upBatomEquiv (A := A) b), Fintype.card_prod]

-- [D-0040] §The-unique-atom-s-up-set-is-everything
-- [D-0041] le_uniqueAtom_iff
theorem le_uniqueAtom_iff [IsAtomic A] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k) (a : A) : k ≤ a ↔ a ≠ ⊥ := by
  constructor
  · intro h hb
    exact hk.1 (le_bot_iff.mp (hb ▸ h))
  · intro ha
    rcases eq_bot_or_exists_atom_le a with h | ⟨k', hk', hle⟩
    · exact absurd h ha
    · rw [← huniq k' hk']; exact hle

-- [D-0042] card_up_uniqueAtom
theorem card_up_uniqueAtom [IsAtomic A] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k) :
    Fintype.card {a : A // k ≤ a} = Fintype.card A - 1 := by
  have h : ∀ a : A, k ≤ a ↔ a ≠ ⊥ := le_uniqueAtom_iff hk huniq
  have h2 : Fintype.card {a : A // a ≠ ⊥} = Fintype.card A - 1 := by
    simpa using Fintype.card_subtype_compl (p := fun a : A => a = ⊥)
  rw [← h2]
  exact Fintype.card_congr (Equiv.subtypeEquivRight h)

-- [D-0043] §No-crossing-from-cardinality
-- [D-0044] up_card_ne
theorem up_card_ne [IsAtomic A] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k)
    (hpos : 0 < Fintype.card B) (hsize : Fintype.card B < Fintype.card A) (b : B) :
    Fintype.card {x : A × B // (k, (⊥ : B)) ≤ x}
      ≠ Fintype.card {x : A × B // ((⊥ : A), b) ≤ x} := by
  rw [card_up_Aatom, card_up_Batom, card_up_uniqueAtom hk huniq]
  have hup : Fintype.card {b' : B // b ≤ b'} ≤ Fintype.card B :=
    Fintype.card_subtype_le _
  intro heq
  refine card_axis_obstruction hpos hsize hup ?_
  calc Fintype.card B * (Fintype.card A - 1)
      = (Fintype.card A - 1) * Fintype.card B := by ring
    _ = Fintype.card A * Fintype.card {b' : B // b ≤ b'} := heq
    _ = Fintype.card {b' : B // b ≤ b'} * Fintype.card A := by ring

-- [D-0045] §Two-facts-Mathlib-does-not-have-atoms
-- [D-0046] prod_ne_bot_iff
theorem prod_ne_bot_iff (p : A × B) : p ≠ ⊥ ↔ (p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (Prod.ext hc.1 hc.2)
  · rintro (h | h) hb <;> rw [hb] at h <;> exact h rfl

-- [D-0047] prod_isAtom_iff
theorem prod_isAtom_iff (p : A × B) :
    IsAtom p ↔ (IsAtom p.1 ∧ p.2 = ⊥) ∨ (p.1 = ⊥ ∧ IsAtom p.2) := by
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨hne, hmin⟩
    rcases (prod_ne_bot_iff ((a, b) : A × B)).mp hne with ha | hb
    · have hb0 : b = ⊥ := by
        have hlt : ((⊥ : A), b) < ((a, b) : A × B) :=
          lt_of_le_of_ne ⟨bot_le, le_rfl⟩ (fun hc => ha (congrArg Prod.fst hc).symm)
        exact congrArg Prod.snd (hmin _ hlt)
      refine Or.inl ⟨⟨ha, ?_⟩, hb0⟩
      intro c hc
      have hlt : ((c, (⊥ : B)) : A × B) < (a, b) := by
        rw [hb0]
        exact lt_of_le_of_ne ⟨hc.le, le_rfl⟩ (fun hcon => hc.ne (congrArg Prod.fst hcon))
      exact congrArg Prod.fst (hmin _ hlt)
    · have ha0 : a = ⊥ := by
        have hlt : ((a, (⊥ : B)) : A × B) < (a, b) :=
          lt_of_le_of_ne ⟨le_rfl, bot_le⟩ (fun hc => hb (congrArg Prod.snd hc).symm)
        exact congrArg Prod.fst (hmin _ hlt)
      refine Or.inr ⟨ha0, ⟨hb, ?_⟩⟩
      intro d hd
      have hlt : (((⊥ : A), d) : A × B) < (a, b) := by
        rw [ha0]
        exact lt_of_le_of_ne ⟨le_rfl, hd.le⟩ (fun hcon => hd.ne (congrArg Prod.snd hcon))
      exact congrArg Prod.snd (hmin _ hlt)
  · rintro (⟨ha, rfl⟩ | ⟨rfl, hb⟩)
    · refine ⟨(prod_ne_bot_iff _).mpr (Or.inl ha.1), ?_⟩
      rintro ⟨c, d⟩ hlt
      have hd : d = ⊥ := le_bot_iff.mp hlt.le.2
      have hca : c < a := lt_of_le_of_ne hlt.le.1
        (fun hcon => hlt.ne (Prod.ext hcon hd))
      exact Prod.ext (ha.2 c hca) hd
    · refine ⟨(prod_ne_bot_iff _).mpr (Or.inr hb.1), ?_⟩
      rintro ⟨c, d⟩ hlt
      have hc : c = ⊥ := le_bot_iff.mp hlt.le.1
      have hdb : d < b := lt_of_le_of_ne hlt.le.2
        (fun hcon => hlt.ne (Prod.ext hc hcon))
      exact Prod.ext hc (hb.2 d hdb)

-- [D-0048] orderIso_isAtom
theorem orderIso_isAtom (φ : (A × B) ≃o (A × B)) {p : A × B} (hp : IsAtom p) :
    IsAtom (φ p) := by
  refine ⟨fun h => hp.1 (φ.injective (h.trans φ.map_bot.symm)), ?_⟩
  intro q hq
  have h1 : φ.symm q < p := by
    have := φ.symm.lt_iff_lt.mpr hq
    rwa [φ.symm_apply_apply] at this
  have h2 : φ.symm q = ⊥ := hp.2 _ h1
  have := congrArg φ h2
  rwa [φ.apply_symm_apply, φ.map_bot] at this

-- [D-0049] §Assembly-no-crossing-then-decomposition
-- [D-0050] upEquivOfOrderIso
def upEquivOfOrderIso (φ : (A × B) ≃o (A × B)) (p : A × B) :
    {x : A × B // p ≤ x} ≃ {y : A × B // φ p ≤ y} where
  toFun z := ⟨φ z.1, φ.monotone z.2⟩
  invFun z := ⟨φ.symm z.1, by
    have h := φ.symm.monotone z.2
    rwa [φ.symm_apply_apply] at h⟩
  left_inv z := Subtype.ext (φ.symm_apply_apply z.1)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.1)

-- [D-0051] card_up_eq
theorem card_up_eq (φ : (A × B) ≃o (A × B)) (p : A × B) :
    Fintype.card {x : A × B // p ≤ x} = Fintype.card {y : A × B // φ p ≤ y} :=
  Fintype.card_congr (upEquivOfOrderIso φ p)

-- [D-0052] no_crossing_B
theorem no_crossing_B [IsAtomic A] [IsAtomic B] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k)
    (hpos : 0 < Fintype.card B) (hsize : Fintype.card B < Fintype.card A)
    (φ : (A × B) ≃o (A × B)) (b : B) (hb : IsAtom b) :
    (φ (((⊥ : A), b) : A × B)).1 = ⊥ := by
  have hatom : IsAtom (φ (((⊥ : A), b) : A × B)) := orderIso_isAtom φ ((prod_isAtom_iff _).mpr (Or.inr ⟨rfl, hb⟩))
  rcases (prod_isAtom_iff _).mp hatom with ⟨hka, hbot⟩ | ⟨hbot, -⟩
  · exfalso
    refine up_card_ne hk huniq hpos hsize b ?_
    have hk' : (φ (((⊥ : A), b) : A × B)).1 = k := huniq _ hka
    have : ((k, (⊥ : B)) : A × B) = φ (((⊥ : A), b) : A × B) :=
      Prod.ext hk'.symm hbot.symm
    rw [this, ← card_up_eq φ]
  · exact hbot

-- [D-0053] no_crossing_A
theorem no_crossing_A [IsAtomic A] [IsAtomic B] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k)
    (hpos : 0 < Fintype.card B) (hsize : Fintype.card B < Fintype.card A)
    (φ : (A × B) ≃o (A × B)) (a : A) (ha : IsAtom a) :
    (φ ((a, (⊥ : B)) : A × B)).2 = ⊥ := by
  have hatom : IsAtom (φ ((a, (⊥ : B)) : A × B)) := orderIso_isAtom φ ((prod_isAtom_iff _).mpr (Or.inl ⟨ha, rfl⟩))
  rcases (prod_isAtom_iff _).mp hatom with ⟨-, hbot⟩ | ⟨hbot, hb2⟩
  · exact hbot
  · exfalso
    have hak : a = k := huniq a ha
    refine up_card_ne hk huniq hpos hsize (φ ((a, (⊥ : B)) : A × B)).2 ?_
    have hka : ((k, (⊥ : B)) : A × B) = (a, (⊥ : B)) := by rw [hak]
    have heq : φ ((a, (⊥ : B)) : A × B)
        = (((⊥ : A), (φ ((a, (⊥ : B)) : A × B)).2) : A × B) := by rw [← hbot]
    rw [hka, card_up_eq φ ((a, (⊥ : B)) : A × B), heq]

-- [D-0054] prod_decomposition_of_card
theorem prod_decomposition_of_card [IsAtomic A] [IsAtomic B] {k : A} (hk : IsAtom k)
    (huniq : ∀ k' : A, IsAtom k' → k' = k)
    (hpos : 0 < Fintype.card B) (hsize : Fintype.card B < Fintype.card A)
    (φ : (A × B) ≃o (A × B)) (a : A) (b : B) :
    φ (a, b) = ((φ ((a, (⊥ : B)) : A × B)).1, (φ (((⊥ : A), b) : A × B)).2) :=
  prod_decomposition_of_no_crossing φ
    (fun b' hb' => no_crossing_B hk huniq hpos hsize φ.symm b' hb')
    (fun a' ha' => no_crossing_A hk huniq hpos hsize φ.symm a' ha')
    a b

end ProdAut
