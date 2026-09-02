import Dinfty.WeakProductAbsorption

/-!
# A natural-valued height, and its additivity on products

§63 measured that **height** is the invariant that closes the level-1 first
slice: of the 13,616 candidate pairs, cardinality leaves 30, the atom count
leaves 16, and height leaves none.  It was the one piece carrying real weight
that was still only measured.

Mathlib has `Order.height`, but valued in `ℕ∞`, and the additivity we need would
have to fight that arithmetic.  For finite posets a natural-valued height is
cleaner:

```lean
ht x = sup over y < x of (ht y + 1)
```

recursing on the size of the strict down-set.  The two facts wanted are

* `ht_orderIso` — height is an isomorphism invariant, so it is admissible as a
  criterion at all;
* `ht_prod : ht (a, b) = ht a + ht b` — height is **additive on direct products**,
  which is what makes `S ≅ D n × … × D k × T` refutable by a number.
-/

open scoped Classical

universe u v

namespace Height

section Def

variable {L : Type u} [PartialOrder L] [Fintype L]

/-- The strict down-set, as a finset. -/
noncomputable def below (x : L) : Finset L := Finset.univ.filter (fun z => z < x)

theorem mem_below {x y : L} : y ∈ below x ↔ y < x := by
  simp [below]

theorem below_card_lt {x y : L} (h : y < x) : (below y).card < (below x).card := by
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_of_subset (fun z hz => ?_) |>.mpr ⟨y, mem_below.mpr h, ?_⟩
  · exact mem_below.mpr ((mem_below.mp hz).trans h)
  · simp [mem_below]

/-- The height of an element: the length of the longest strictly increasing chain
below it. -/
noncomputable def ht (x : L) : ℕ :=
  (below x).attach.sup (fun y => ht y.1 + 1)
  termination_by (below x).card
  decreasing_by exact below_card_lt (mem_below.mp y.2)

theorem ht_eq (x : L) : ht x = (below x).attach.sup (fun y => ht y.1 + 1) := by
  rw [ht.eq_def]

/-- Everything strictly below `x` has strictly smaller height. -/
theorem ht_lt_of_lt {x y : L} (h : x < y) : ht x < ht y := by
  have hle : ht x + 1 ≤ (below y).attach.sup (fun z => ht z.1 + 1) :=
    Finset.le_sup (f := fun z : {z // z ∈ below y} => ht z.1 + 1)
      (b := (⟨x, mem_below.mpr h⟩ : {z // z ∈ below y}))
      (Finset.mem_attach _ _)
  rw [ht_eq y]
  omega

theorem ht_mono {x y : L} (h : x ≤ y) : ht x ≤ ht y := by
  rcases h.lt_or_eq with h | rfl
  · exact (ht_lt_of_lt h).le
  · exact le_refl _

end Def

section Iso

variable {L : Type u} {L' : Type v}
variable [PartialOrder L] [Fintype L] [PartialOrder L'] [Fintype L']

/-- A strictly monotone map cannot decrease height. -/
theorem ht_le_of_strictMono (f : L → L') (hf : StrictMono f) (x : L) :
    ht x ≤ ht (f x) := by
  induction x using WellFoundedLT.induction with
  | _ x IH =>
    rw [ht_eq x]
    refine Finset.sup_le ?_
    rintro ⟨y, hy⟩ -
    have hlt : y < x := mem_below.mp hy
    have h1 : ht y ≤ ht (f y) := IH y hlt
    have h2 : ht (f y) < ht (f x) := ht_lt_of_lt (hf hlt)
    change ht y + 1 ≤ ht (f x)
    omega

/-- **Height is an isomorphism invariant.** -/
theorem ht_orderIso (e : L ≃o L') (x : L) : ht (e x) = ht x := by
  refine le_antisymm ?_ (ht_le_of_strictMono e e.strictMono x)
  have := ht_le_of_strictMono e.symm e.symm.strictMono (e x)
  rwa [e.symm_apply_apply] at this

end Iso

/-! ## The sup is attained -/

section Attained

variable {L : Type u} [PartialOrder L] [Fintype L]

theorem exists_lt_ht_succ {x : L} (h : 0 < ht x) : ∃ y, y < x ∧ ht x = ht y + 1 := by
  have hne : (below x).attach.Nonempty := by
    rw [Finset.attach_nonempty_iff, Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [ht_eq x, hemp] at h
    simp at h
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_mem_eq_sup _ hne (fun z : {z // z ∈ below x} => ht z.1 + 1)
  exact ⟨y.1, mem_below.mp y.2, by rw [ht_eq x]; exact hy⟩

end Attained

/-! ## Additivity on direct products -/

section Prod

variable {L : Type u} {L' : Type u}
variable [PartialOrder L] [Fintype L] [PartialOrder L'] [Fintype L']

theorem prod_lt_left {a a' : L} {b : L'} (h : a' < a) :
    ((a', b) : L × L') < (a, b) :=
  lt_iff_le_not_ge.mpr ⟨⟨h.le, le_refl b⟩, fun hcon => absurd hcon.1 h.not_ge⟩

theorem prod_lt_right {a : L} {b b' : L'} (h : b' < b) :
    ((a, b') : L × L') < (a, b) :=
  lt_iff_le_not_ge.mpr ⟨⟨le_refl a, h.le⟩, fun hcon => absurd hcon.2 h.not_ge⟩

/-- **Height is additive on direct products.**  This is what makes the finite
equation `S ≅ D n × … × D k × T` refutable by a single number. -/
theorem ht_prod (p : L × L') : ht p = ht p.1 + ht p.2 := by
  induction p using WellFoundedLT.induction with
  | _ p IH =>
    obtain ⟨a, b⟩ := p
    dsimp only
    refine le_antisymm ?_ ?_
    · rw [ht_eq (a, b)]
      refine Finset.sup_le ?_
      rintro ⟨q, hq⟩ -
      have hlt : q < (a, b) := mem_below.mp hq
      have hIH : ht q = ht q.1 + ht q.2 := IH q hlt
      have h1 : q.1 ≤ a := hlt.le.1
      have h2 : q.2 ≤ b := hlt.le.2
      have hstrict : q.1 < a ∨ q.2 < b := by
        rcases lt_or_eq_of_le h1 with h | h
        · exact Or.inl h
        · rcases lt_or_eq_of_le h2 with h' | h'
          · exact Or.inr h'
          · exact absurd (Prod.ext h h') hlt.ne
      change ht q + 1 ≤ ht a + ht b
      rcases hstrict with h | h
      · have hA := ht_lt_of_lt h
        have hB := ht_mono h2
        omega
      · have hA := ht_mono h1
        have hB := ht_lt_of_lt h
        omega
    · rcases Nat.eq_zero_or_pos (ht a) with ha | ha
      · rcases Nat.eq_zero_or_pos (ht b) with hb | hb
        · omega
        · obtain ⟨b', hb', hbeq⟩ := exists_lt_ht_succ hb
          have hlt := prod_lt_right (a := a) hb'
          have hIH := IH (a, b') hlt
          have hmono := ht_lt_of_lt hlt
          dsimp only at hIH
          omega
      · obtain ⟨a', ha', haeq⟩ := exists_lt_ht_succ ha
        have hlt := prod_lt_left (b := b) ha'
        have hIH := IH (a', b) hlt
        have hmono := ht_lt_of_lt hlt
        dsimp only at hIH
        omega

/-- The height of a finite poset: the largest element height. -/
noncomputable def htP (L : Type u) [PartialOrder L] [Fintype L] : ℕ :=
  Finset.univ.sup (fun x : L => ht x)

theorem le_htP {L : Type u} [PartialOrder L] [Fintype L] (x : L) : ht x ≤ htP L :=
  Finset.le_sup (Finset.mem_univ x)

theorem exists_ht_eq_htP {L : Type u} [PartialOrder L] [Fintype L] [Nonempty L] :
    ∃ x : L, ht x = htP L := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun x : L => ht x)
  exact ⟨x, hx.symm⟩

/-- **The height of a poset is an isomorphism invariant.** -/
theorem htP_orderIso {L : Type u} {L' : Type v} [PartialOrder L] [Fintype L]
    [PartialOrder L'] [Fintype L'] (e : L ≃o L') : htP L = htP L' := by
  simp only [htP]
  refine le_antisymm (Finset.sup_le fun x _ => ?_) (Finset.sup_le fun y _ => ?_)
  · rw [← ht_orderIso e x]
    exact Finset.le_sup (f := fun z : L' => ht z) (Finset.mem_univ (e x))
  · rw [← ht_orderIso e.symm y]
    exact Finset.le_sup (f := fun z : L => ht z) (Finset.mem_univ (e.symm y))

/-- **The height of a product is the sum of the heights.** -/
theorem htP_prod [Nonempty L] [Nonempty L'] : htP (L × L') = htP L + htP L' := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro p _
    rw [ht_prod p]
    exact Nat.add_le_add (le_htP p.1) (le_htP p.2)
  · obtain ⟨a, ha⟩ := exists_ht_eq_htP (L := L)
    obtain ⟨b, hb⟩ := exists_ht_eq_htP (L := L')
    have hle := le_htP ((a, b) : L × L')
    rw [ht_prod (a, b)] at hle
    dsimp only at hle
    omega

end Prod

end Height
