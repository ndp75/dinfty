import Dinfty.GlueMapContinuity

open GluingTowerLibrary SierpinskiApplication

-- [D-1377] §Local-continuity-in-the-infinite-case
open scoped Classical

universe u v

namespace GenContinuity

-- [D-1378] §The-tagwise-action-finiteness-free
section BaseMapGen

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

-- [D-1379] baseMapGen
def baseMapGen (g : P →o P') : GlueBaseGen P → GlueBaseGen P'
  | Sum.inl x => Sum.inl (g x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (g x))
  | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (g x))

-- [D-1380] baseMapGen_inl
@[simp] theorem baseMapGen_inl (g : P →o P') (a : P) :
    baseMapGen g (Sum.inl a) = Sum.inl (g a) := rfl

-- [D-1381] baseMapGen_leGlueGen_of_le
theorem baseMapGen_leGlueGen_of_le (m' : P') {g g' : P →o P'} (hgg : g ≤ g')
    (x : GlueBaseGen P) :
    leGlueGen m' (baseMapGen g x) (baseMapGen g' x) := by
  have hpt : ∀ a : P, g a ≤ g' a := fun a => OrderHom.le_def.mp hgg a
  cases x with
  | inl a =>
    exact ⟨Sum.inl (g a), self_mem_occsGen _ _, Sum.inl (g' a), self_mem_occsGen _ _, hpt a⟩
  | inr x =>
    cases x with
    | inl a =>
      exact ⟨Sum.inr (Sum.inl (g a)), self_mem_occsGen _ _,
             Sum.inr (Sum.inl (g' a)), self_mem_occsGen _ _, hpt a⟩
    | inr a =>
      exact ⟨Sum.inr (Sum.inr (g a)), self_mem_occsGen _ _,
             Sum.inr (Sum.inr (g' a)), self_mem_occsGen _ _, hpt a⟩

end BaseMapGen

-- [D-1382] §The-reduction
section Reduction

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']
variable {ι : Type v}

-- [D-1383] baseMapGen_range_eq
theorem baseMapGen_range_eq (g : ι → (P →o P')) (a : P) :
    (Set.range fun i => baseMapGen (g i) (Sum.inl a))
      = Set.range fun i => (Sum.inl ((g i) a) : GlueBaseGen P') := rfl

end Reduction

-- [D-1384] §The-three-obligations-named
section Obligations

variable (P : Type u) [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-1385] ScottContinuousTagA
def ScottContinuousTagA (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) : Prop :=
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  ∀ (S : Set P) (c : P), S.Nonempty → DirectedOn (· ≤ ·) S → IsLUB S c →
    IsLUB (tagAGen m '' S) (tagAGen m c)

end Obligations

-- [D-1386] §The-gateway-lemma-for-obligation-1
section Gateway

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-1387] leGlueGen_tagA_tagA_iff
theorem leGlueGen_tagA_tagA_iff (m : P) (hm : m ≠ ⊥) (x y : P) :
    leGlueGen m (Sum.inl x) (Sum.inl y) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hocc : ∀ (z : P) (w : GlueBaseGen P), w ∈ occsGen m (Sum.inl z) →
        w = Sum.inl z ∨ (z = m ∧ w = Sum.inr (Sum.inl ⊥))
          ∨ (z = ⊤ ∧ w = Sum.inr (Sum.inr ⊥)) := by
      intro z w hw
      simp only [occsGen] at hw
      split_ifs at hw with h1 h2 <;> simp at hw <;> tauto
    rcases hocc x u hu with rfl | ⟨hxm, rfl⟩ | ⟨hxt, rfl⟩ <;>
      rcases hocc y v hv with rfl | ⟨hym, rfl⟩ | ⟨hyt, rfl⟩
    · exact huv
    · subst hym; exact huv
    · subst hyt; exact le_top
    · exact huv.elim
    · subst hxm; subst hym; exact le_rfl
    · exact absurd (le_bot_iff.mp huv) hm
    · exact huv.elim
    · exact huv.elim
    · subst hxt; subst hyt; exact le_rfl
  · intro h
    exact ⟨Sum.inl x, self_mem_occsGen _ _, Sum.inl y, self_mem_occsGen _ _, h⟩

-- [D-1388] leGlueGen_tagA_tagC
theorem leGlueGen_tagA_tagC (m x c' : P) :
    leGlueGen m (Sum.inl x) (Sum.inr (Sum.inr c')) :=
  ⟨Sum.inl x, self_mem_occsGen _ _, Sum.inr (Sum.inr c'), self_mem_occsGen _ _, trivial⟩

-- [D-1389] le_marked_of_leGlueGen_tagB
theorem le_marked_of_leGlueGen_tagB (m x b : P) (hbt : b ≠ ⊤)
    (h : leGlueGen m (Sum.inl x) (Sum.inr (Sum.inl b))) : x ≤ m := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  have hv' : v = Sum.inr (Sum.inl b) := by
    simp only [occsGen] at hv
    rw [if_neg hbt] at hv
    simpa using hv
  subst hv'
  have hocc : u = Sum.inl x ∨ (x = m ∧ u = Sum.inr (Sum.inl ⊥))
      ∨ (x = ⊤ ∧ u = Sum.inr (Sum.inr ⊥)) := by
    simp only [occsGen] at hu
    split_ifs at hu with h1 h2 <;> simp at hu <;> tauto
  rcases hocc with rfl | ⟨hxm, rfl⟩ | ⟨_, rfl⟩
  · exact huv
  · exact le_of_eq hxm
  · exact huv.elim

-- [D-1390] tagAGen_isLUB
theorem tagAGen_isLUB (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLUB (tagAGen m '' S) (tagAGen m c) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  constructor
  · rintro _ ⟨s, hs, rfl⟩
    show leGlueGen m (Sum.inl s) (Sum.inl c)
    exact (leGlueGen_tagA_tagA_iff m hm s c).mpr (hS.1 hs)
  · intro w hw
    show leGlueGen m (Sum.inl c) w.1
    obtain ⟨wv, hwv⟩ := w
    have hub : ∀ s ∈ S, leGlueGen m (Sum.inl s) wv := by
      intro s hs
      exact hw ⟨s, hs, rfl⟩
    rcases wv with d | b | c'
    · have : ∀ s ∈ S, s ≤ d := fun s hs =>
        (leGlueGen_tagA_tagA_iff m hm s d).mp (hub s hs)
      exact (leGlueGen_tagA_tagA_iff m hm c d).mpr (hS.2 this)
    · by_cases hbtop : b = ⊤
      · subst hbtop
        exact ⟨Sum.inl c, self_mem_occsGen _ _, Sum.inr (Sum.inr m),
               by simp [occsGen], trivial⟩
      · have hsm : ∀ s ∈ S, s ≤ m := fun s hs =>
          le_marked_of_leGlueGen_tagB m s b hbtop (hub s hs)
        have hcm : c ≤ m := hS.2 hsm
        exact ⟨Sum.inl c, self_mem_occsGen _ _, Sum.inr (Sum.inl b),
               self_mem_occsGen _ _, hcm⟩
    · exact leGlueGen_tagA_tagC m c c'

-- [D-1391] scottContinuousTagA
theorem scottContinuousTagA (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    ScottContinuousTagA P m hm hmt hbt :=
  fun _S _c _hne _hdir hlub => tagAGen_isLUB m hm hmt hbt hlub

-- [D-1392] §Obligations-2-and-3-with-a-correction-to-how
section CopiesBC

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-1393] occsGen_tagB
theorem occsGen_tagB (m x : P) (w : GlueBaseGen P)
    (hw : w ∈ occsGen m (Sum.inr (Sum.inl x))) :
    w = Sum.inr (Sum.inl x) ∨ (x = ⊤ ∧ w = Sum.inr (Sum.inr m)) := by
  simp only [occsGen] at hw
  split_ifs at hw with h1 <;> simp at hw <;> tauto

-- [D-1394] occsGen_tagC
theorem occsGen_tagC (m x : P) (w : GlueBaseGen P)
    (hw : w ∈ occsGen m (Sum.inr (Sum.inr x))) : w = Sum.inr (Sum.inr x) := by
  simpa [occsGen] using hw

-- [D-1395] leGlueGen_tagB_tagBtop
theorem leGlueGen_tagB_tagBtop (m b : P) :
    leGlueGen m (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inl (⊤ : P))) :=
  ⟨Sum.inr (Sum.inl b), self_mem_occsGen _ _, Sum.inr (Sum.inr m),
   by simp [occsGen], le_rfl⟩

-- [D-1396] le_of_leGlueGen_tagB_tagB
theorem le_of_leGlueGen_tagB_tagB (m x b : P) (hbt : b ≠ ⊤)
    (h : leGlueGen m (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl b))) : x ≤ b := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  rcases occsGen_tagB m b v hv with rfl | ⟨hb, _⟩
  · rcases occsGen_tagB m x u hu with rfl | ⟨_, rfl⟩
    · exact huv
    · exact huv.elim
  · exact absurd hb hbt

-- [D-1397] marked_le_of_leGlueGen_tagB_tagC
theorem marked_le_of_leGlueGen_tagB_tagC (m x c' : P)
    (h : leGlueGen m (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr c'))) : m ≤ c' := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  rcases occsGen_tagC m c' v hv with rfl
  rcases occsGen_tagB m x u hu with rfl | ⟨_, rfl⟩
  · exact huv
  · exact huv

-- [D-1398] tagB_isLUB_raw
theorem tagB_isLUB_raw (m : P) (hm : m ≠ ⊥) (hbt : (⊥ : P) ≠ ⊤)
    {S : Set P} {c : P} (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inl c)))
      ∧ (∀ w : GlueBaseGen P, (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inl s)) w) →
          leGlueGen m (Sum.inr (Sum.inl c)) w) := by
  obtain ⟨s0, hs0⟩ := hne
  refine ⟨fun s hs => ⟨Sum.inr (Sum.inl s), self_mem_occsGen _ _,
      Sum.inr (Sum.inl c), self_mem_occsGen _ _, hS.1 hs⟩, ?_⟩
  intro w hw
  rcases w with d | b | c'
  · exact absurd (hw s0 hs0)
      (not_leGlue_tagB_tagAGen m s0 d hm hbt (hSb s0 hs0))
  · by_cases hbtop : b = ⊤
    · subst hbtop; exact leGlueGen_tagB_tagBtop m c
    · have hsb : ∀ s ∈ S, s ≤ b := fun s hs =>
        le_of_leGlueGen_tagB_tagB m s b hbtop (hw s hs)
      exact ⟨Sum.inr (Sum.inl c), self_mem_occsGen _ _,
             Sum.inr (Sum.inl b), self_mem_occsGen _ _, hS.2 hsb⟩
  · have hmc : m ≤ c' := marked_le_of_leGlueGen_tagB_tagC m s0 c' (hw s0 hs0)
    exact ⟨Sum.inr (Sum.inl c), self_mem_occsGen _ _,
           Sum.inr (Sum.inr c'), self_mem_occsGen _ _, hmc⟩

-- [D-1399] tagC_isLUB_raw
theorem tagC_isLUB_raw (m : P) {S : Set P} {c : P}
    (hS : IsLUB S c) (hne : S.Nonempty) (hSb : ∀ s ∈ S, s ≠ ⊥) :
    (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inr s)) (Sum.inr (Sum.inr c)))
      ∧ (∀ w : GlueBaseGen P, (∀ s ∈ S, leGlueGen m (Sum.inr (Sum.inr s)) w) →
          leGlueGen m (Sum.inr (Sum.inr c)) w) := by
  obtain ⟨s0, hs0⟩ := hne
  refine ⟨fun s hs => ⟨Sum.inr (Sum.inr s), self_mem_occsGen _ _,
      Sum.inr (Sum.inr c), self_mem_occsGen _ _, hS.1 hs⟩, ?_⟩
  intro w hw
  rcases w with d | b | c'
  · exact absurd (hw s0 hs0) (not_leGlue_tagC_tagAGen m s0 d (hSb s0 hs0))
  · have hsm : ∀ s ∈ S, s ≤ m := by
      intro s hs
      obtain ⟨u, hu, v, hv, huv⟩ := hw s hs
      rcases occsGen_tagC m s u hu with rfl
      rcases occsGen_tagB m b v hv with rfl | ⟨_, rfl⟩
      · exact huv.elim
      · exact huv
    have hbtop : b = ⊤ := by
      obtain ⟨u, hu, v, hv, huv⟩ := hw s0 hs0
      rcases occsGen_tagC m s0 u hu with rfl
      rcases occsGen_tagB m b v hv with rfl | ⟨hb, _⟩
      · exact huv.elim
      · exact hb
    subst hbtop
    exact ⟨Sum.inr (Sum.inr c), self_mem_occsGen _ _, Sum.inr (Sum.inr m),
           by simp [occsGen], hS.2 hsm⟩
  · have hsc : ∀ s ∈ S, s ≤ c' := by
      intro s hs
      obtain ⟨u, hu, v, hv, huv⟩ := hw s hs
      rcases occsGen_tagC m s u hu with rfl
      rcases occsGen_tagC m c' v hv with rfl
      exact huv
    exact ⟨Sum.inr (Sum.inr c), self_mem_occsGen _ _,
           Sum.inr (Sum.inr c'), self_mem_occsGen _ _, hS.2 hsc⟩

end CopiesBC

end Gateway

end GenContinuity
