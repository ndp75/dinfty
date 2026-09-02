import Dinfty.SierpinskiApplication

open GluingTowerLibrary SierpinskiApplication

/-!
# Obstruction (T) — the gluing tower's connecting map must preserve `⊤`

`Meta/Finding - PsiIso tower mismatch (2026-08-26).md`, Update 19.

`Φ(P) = GlueCar(P, m)` glues its three copies at **three** points — `⊥`, the
marked point `m`, and `⊤` — so a tagwise morphism action
`G : EndP X → EndP (F X)` for `F X = GlueCar(EndP X, m)` has to be
*tripointed*: `G ⊥ = ⊥`, `G m = m'`, `G ⊤ = ⊤`.

Combining the `⊤` half with **naturality of the tower map `ι`** — which for a
tagwise action is exactly `G (constHom x) = constHom (ι x)`, i.e. what makes
`ι ∘ e = F e ∘ ι` commute — forces `ι ⊤ = ⊤`. No monotonicity,
join-preservation or order-embedding hypothesis is used anywhere.

The project's connecting map `iotaD k x = glueA id (constHom x)` lands in copy
`A`, and `glueA_ne_top` (`GluingTowerLibrary`) says copy `A` *never* hits
`Φ(P)`'s top. So over the real tower **no such `G` exists at all** —
`no_topExact_natural_action_over_tower` below. This is strictly stronger than
Updates 3/7, which ruled out only the conjugation action and its `liftGen`
repairs, and it needs no join-closure argument.

## SCOPE (Update 22, 2026-08-27) — read this before citing

This obstruction is about the **Lean encoding** of the tower, not about the
project's mathematics. It applies exactly when the marked point is `id` and
the tower map is the copy-`A` inclusion `iotaD` — which is what
`towerLevelSucc` builds.

The vault's `Φ_tri_v2` tower uses a **different** marked point: `const_L`,
the constant at the base 3-chain's middle point, and its tower map is
tripointed, hence `⊥`- and `⊤`-preserving. That tower therefore
*satisfies* the hypothesis `iota ⊤ = ⊤` below rather than violating it,
and is not obstructed. (Update 7 had identified the two towers; that was read
off a 2-chain base, where `id` and `const_L` coincide.)

So: the theorems here are correct and unconditional, but the corollaries
`no_*_over_tower` are statements about `iotaD`/`m = id` specifically.
Retargeting `towerLevelSucc`'s marked point to `constHom L` would move the
Lean tower off this obstruction; scoped as separate work.

Everything here is fully general: no `decide`, no `Fintype`, no distributivity,
and independent of the refuted `axiom PsiIso`.
-/

namespace TripointedObstruction

section General

variable {X Y : Type*} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]

/-- **Obstruction (T), top half.** A `⊤`-exact action that is natural on
constants forces the tower map `iota` to preserve `⊤`. -/
theorem iota_top_of_topExact_natural
    (iota : X → Y) (G : EndP X → EndP Y)
    (hGtop : G ⊤ = ⊤)
    (hnat : ∀ x : X, G (constHom x) = constHom (iota x)) :
    iota (⊤ : X) = (⊤ : Y) := by
  have h1 : G (constHom (⊤ : X)) = (⊤ : EndP Y) := by
    rw [← endP_top_eq_constHom_top]; exact hGtop
  rw [hnat] at h1
  have h2 := congrArg (fun f : EndP Y => f (⊤ : Y)) h1
  simpa using h2

omit [BoundedOrder Y] in
/-- **Obstruction (T), monotone half.** Marked-point exactness at `m = id`
plus naturality already forces `iota ⊤` to dominate all of `Y`, for any
*monotone* `G` — no `⊤`-exactness needed. -/
theorem le_iota_top_of_monotone_of_idExact
    (iota : X → Y) (G : EndP X → EndP Y)
    (hmono : Monotone G)
    (hGid : G OrderHom.id = OrderHom.id)
    (hnat : ∀ x : X, G (constHom x) = constHom (iota x)) :
    ∀ z : Y, z ≤ iota (⊤ : X) := by
  have hle : (OrderHom.id : EndP X) ≤ constHom (⊤ : X) := fun _ => le_top
  have h := hmono hle
  rw [hGid, hnat] at h
  intro z
  simpa using h z

end General

/-- **Corollary — the real gluing tower admits no such action, at any level.**
`iotaD k` lands in copy `A`, which never reaches `D (k+1)`'s top, so
tripointedness and naturality are outright incompatible over this tower. -/
theorem no_topExact_natural_action_over_tower (k : ℕ)
    (G : EndP (D k) → EndP (D (k + 1)))
    (hGtop : G ⊤ = ⊤)
    (hnat : ∀ x : D k, G (constHom x) = constHom (iotaD k x)) : False := by
  have hne := iotaD_ne_top k (⊤ : D k)
  exact hne (iota_top_of_topExact_natural (iotaD k) G hGtop hnat)

/-- The same conclusion from the weaker monotone hypotheses. -/
theorem no_monotone_idExact_natural_action_over_tower (k : ℕ)
    (G : EndP (D k) → EndP (D (k + 1)))
    (hmono : Monotone G)
    (hGid : G OrderHom.id = OrderHom.id)
    (hnat : ∀ x : D k, G (constHom x) = constHom (iotaD k x)) : False := by
  have hne := iotaD_ne_top k (⊤ : D k)
  exact hne (top_le_iff.mp
    (le_iota_top_of_monotone_of_idExact (iotaD k) G hmono hGid hnat
      (⊤ : D (k + 1))))

end TripointedObstruction
