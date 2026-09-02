import Dinfty.PatchedEmbedding
import Dinfty.StageCofinal
import Dinfty.AtomlessBilimit

open GluingTowerLibrary SierpinskiApplication

/-!
# Hunting the automorphism instead of the invariant

Two builds in a row died to counterexamples found only after the theory was
built.  So this time the counterexample is hunted first: **is the §117 freedom
invertible?**

`patched k x = if x = ⊤ then ⊤ else iotaD (k+1) x` is a bounded join-embedding
of one level into the next that is not `embD`.  If the family `{patched k}` were
*coherent* with the tower, it would define a map on `B`; if that map were onto,
`Subsingleton (B ≃o B)` would be refuted.

## It is coherent — and for the §119 reason

`endUpFun` transports constants exactly as it transports spikes:

```lean
endUpFun_constHom : E.endUpFun (constHom x) = constHom (E.emb x)
```

so `iotaD` commutes with the tower's own embeddings, and

```lean
patched_coherent : (iter (k+1)).emb (patched k x) = patched (k+1) ((iter k).emb x)
```

with the `⊤` branch matching because every embedding is `⊤`-preserving.  So the
family really is a morphism of the whole stage filtration — the obligation
`isStageMap_coherent` imposes — and this is a genuine self-embedding direction,
not an artefact.

## But it is not invertible

The necessary condition bites here, and this is the useful output of the hunt.
An automorphism's stage maps are **jointly surjective onto the filtration**:
`θ⁻¹` has a stage map too, so every stage point is *hit*.

```lean
stage_map_covers (θ : B ≃o B) (y : D 2) :
  ∃ (m : ℕ) (h : 1 ≤ m + 1) (z : D (m+1)) (m'' : ℕ) (hm : m ≤ m'')
    (f : D (m+1) → D (m''+1)),
    IsStageMap θ m m'' f ∧ insD m'' (f z) = insD (m+1) (embD h y)
```

`patched`'s range is confined to copy `A` together with `⊤`, while the tower's
embeddings preserve the copy index (`emb_succ_copyIdx`).  Evaluate at the
copy-`B` point `wB : D 2` of §117: it is never hit.

```lean
no_patched_automorphism :
  ¬ ∃ θ : B ≃o B, ∀ k x, θ (insD k x) = insD (k+1) (patched k x)
```

## The verdict, and what it leaves

`Subsingleton (B ≃o B)` is **not** refuted, and the freedom that refuted the
sufficient condition is now known to be one-directional: it embeds `B` properly
into itself rather than permuting it.

What the hunt yields positively is a constraint that does not mention seeds or
levels: **an automorphism's stage maps must meet copy `B`.**  A copy-`A`-confined
family cannot be one, whatever else it satisfies.  That is the first necessary
condition on `Aut(B)` that rules out a concrete candidate rather than merely
restating the goal.
-/

open scoped Classical

namespace StageCover

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open StageCofinal PatchedEmbedding AtomlessBilimit CopyHierarchy

/-! ## 1.  `endUpFun` transports constants -/

theorem endUpFun_constHom {k : ℕ} (E : TriEP k) (x : D k) :
    E.endUpFun (constHom x) = constHom (E.emb x) := by
  apply OrderHom.ext
  funext w
  show E.emb ((constHom x) (E.prj w)) = constHom (E.emb x) w
  rfl

theorem emb_eq_top_iff {k : ℕ} (E : TriEP k) (x : D k) : E.emb x = ⊤ ↔ x = ⊤ := by
  constructor
  · intro h
    have h1 := E.retraction x
    rw [h, E.prj_top] at h1
    exact h1.symm
  · rintro rfl
    exact E.emb_top

/-! ## 2.  `patched` is coherent with the tower -/

theorem patched_coherent (k : ℕ) (x : D (k + 1)) :
    (iter (k + 1)).emb (patched k x) = patched (k + 1) ((iter k).emb x) := by
  rcases eq_or_ne x (⊤ : D (k + 1)) with hx | hx
  · subst hx
    rw [patched_top, (iter (k + 1)).emb_top, (iter k).emb_top, patched_top]
  · have hex : (iter k).emb x ≠ ⊤ := fun hc => hx ((emb_eq_top_iff (iter k) x).mp hc)
    rw [patched_of_ne_top hx, patched_of_ne_top hex]
    show (iter (k + 1)).emb (glueA (markedPt (k + 1)) (constHom x))
      = glueA (markedPt (k + 2)) (constHom ((iter k).emb x))
    rw [AtomlessBilimit.emb_succ_glueA k (constHom x), endUpFun_constHom (iter k) x]

/-! ## 3.  The tower's embeddings preserve the copy index, level to level -/

theorem embD_copyIdx : ∀ (m : ℕ) (h : 1 ≤ m) (y : D 2),
    copyIdx (embD h y).1 = copyIdx y.1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro h y
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · have hn : n = 0 := by omega
        subst hn
        show copyIdx (phiTowerEP.embLe h y).1 = _
        rw [EpPairTower.embLe_self (T := phiTowerEP) h y]
      · have h1 : (1 : ℕ) ≤ n := by omega
        obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
        show copyIdx (phiTowerEP.embLe h y).1 = _
        rw [EpPairTower.embLe_succ (T := phiTowerEP) h1 h y]
        show copyIdx ((iter (p + 1)).emb (phiTowerEP.embLe h1 y)).1 = _
        rw [EmbTagwise.emb_succ_copyIdx p _]
        exact ih h1 y

/-! ## 4.  The stage maps of an automorphism cover the filtration -/

/-- **Every stage point is hit.**  `θ⁻¹` has a stage map too, so a point of
stage `1` is the `θ`-image of a stage point, and pushing both sides to a common
level turns that into an equation between level maps. -/
theorem stage_map_covers (θ : B ≃o B) (y : D 2) :
    ∃ (m : ℕ) (h : 1 ≤ m + 1) (z : D (m + 1)) (m'' : ℕ) (hm : m ≤ m'')
      (f : D (m + 1) → D (m'' + 1)),
      IsStageMap θ m m'' f ∧ insD m'' (f z) = insD (m + 1) (embD h y) := by
  obtain ⟨m, hm1, g, hg⟩ := stage_map_exists' θ.symm 1
  obtain ⟨m'', hmm, f, hf⟩ := stage_map_exists' θ m
  refine ⟨m, by omega, g y, m'', hmm, f, hf, ?_⟩
  rw [← hf (g y), ← hg y, OrderIso.apply_symm_apply]
  exact (insD_embD (by omega : (1 : ℕ) ≤ m + 1) y).symm

/-! ## 5.  The verdict: the §117 freedom is not invertible -/

/-- **No automorphism of `B` has `patched` as its family of stage maps.**  Its
range is confined to copy `A` and `⊤`; the copy-`B` point `wB` of §117 is never
hit. -/
theorem no_patched_automorphism :
    ¬ ∃ θ : B ≃o B, ∀ (k : ℕ) (x : D (k + 1)), θ (insD k x) = insD (k + 1) (patched k x) := by
  rintro ⟨θ, hθ⟩
  obtain ⟨m, hm1, g, hg⟩ := stage_map_exists' θ.symm 1
  have hkey : insD (m + 1) (patched m (g wB)) = insD (m + 1) (embD (by omega : (1:ℕ) ≤ m + 1) wB) := by
    rw [← hθ m (g wB), ← hg wB, OrderIso.apply_symm_apply,
      insD_embD (by omega : (1:ℕ) ≤ m + 1) wB]
  have heq : patched m (g wB) = embD (by omega : (1:ℕ) ≤ m + 1) wB :=
    insD_injective (m + 1) hkey
  rcases eq_or_ne (g wB) (⊤ : D (m + 1)) with hgt | hgt
  · -- the whole of `patched`'s image outside copy `A` is `⊤`, and `wB ≠ ⊤`
    rw [hgt, patched_top] at heq
    refine wB_ne_top ?_
    refine insD_injective 1 ?_
    rw [← insD_embD (by omega : (1:ℕ) ≤ m + 1) wB, ← heq, insD_top (m + 1), insD_top 1]
  · -- otherwise `patched` lands in copy `A`, but `embD` keeps `wB` in copy `B`
    obtain ⟨a, ha⟩ := patched_val_ne_top hgt
    have h0 : copyIdx (patched m (g wB)).1 = 0 := by rw [ha]; rfl
    rw [heq, embD_copyIdx (m + 1) (by omega) wB, copyIdx_wB] at h0
    exact absurd h0 (by decide)

end StageCover
