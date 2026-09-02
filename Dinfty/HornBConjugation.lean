import Dinfty.TripointedObstruction

open GluingTowerLibrary SierpinskiApplication

/-!
# Horn B: with a `⊥`/`⊤`-preserving tower map, conjugation is tripointed

`Meta/Finding - PsiIso tower mismatch (2026-08-26).md`, Update 21.

Obstruction (T) (`Dinfty/TripointedObstruction.lean`) says a tagwise morphism
action for `F` forces the tower map `ι` to preserve `⊤` — and the project's
copy-`A` inclusion `iotaD` does not, so no action exists over the tower as
currently defined (*horn A*).

*Horn B* re-bases the tower on an `ι` that preserves `⊥` **and** `⊤`. This
file proves the positive counterpart of (T): for such an `ι`, the plain
conjugation action

  `conj ι p f := ι ∘ f ∘ p`

is exact at both extreme gluing points, natural on constants, monotone,
order-reflecting and join-preserving — i.e. everything `Φ`'s tagwise action
needs, with **no distributivity hypothesis, no finiteness, no search, and no
ad-hoc choice**, at every level and for an arbitrary base.

The middle gluing point is handled by letting the marked point *drift*:
taking `m' := conj ι p m` makes marked-point exactness hold **definitionally**.
Updates 19's repair (i) tried exactly this and failed at `⊤`-exactness — and
failed there *precisely because* its `ι` was the copy-`A` inclusion. With a
`⊤`-preserving `ι` the obstruction is gone; `conj_top` below is the theorem
that was missing.

## Update 22 (2026-08-27): this is what the vault tower already does

The vault's `Φ_tri_v2` tower takes the marked point to be `const_L` (a
*constant*), and its tower map to be the tripointed one, which is `⊥`- and
`⊤`-preserving. `conj_bot`/`conj_top` below therefore apply to it directly.
Better still, a marked point that is a constant needs **no drift at all**:
`conj_constHom` pins it exactly, since `conj iota p (constHom L) =
constHom (iota L)` and `iota L` is the next level's own middle basepoint. The
drift discussed below is only needed when the marked point is `id`, which is
not a constant.

Note what is NOT claimed: the drift means the limit self-similarity is at a
deflation marked point rather than at `id`, so this establishes functoriality
of the re-based tower, not the original Claim 3(b) statement. See the Finding
note for the accounting.
-/

namespace HornB

variable {X Y : Type*} [Lattice X] [Lattice Y]

/-- Conjugation by an ep-pair `(iota, p)`: the morphism action
`f ↦ iota ∘ f ∘ p`. -/
def conj (iota : X →o Y) (p : Y →o X) (f : EndP X) : EndP Y :=
  iota.comp (f.comp p)

@[simp] theorem conj_apply (iota : X →o Y) (p : Y →o X) (f : EndP X) (z : Y) :
    conj iota p f z = iota (f (p z)) := rfl

/-- **Naturality on constants** — unconditional. This is exactly the square
`ι ∘ e = F e ∘ ι` that makes the Adámek chain a chain. -/
@[simp] theorem conj_constHom (iota : X →o Y) (p : Y →o X) (x : X) :
    conj iota p (constHom x) = constHom (iota x) := by
  ext z; simp [conj, constHom]

/-- **`⊥`-exactness**, given `iota ⊥ = ⊥`. -/
theorem conj_bot [OrderBot X] [OrderBot Y]
    (iota : X →o Y) (p : Y →o X) (h : iota ⊥ = (⊥ : Y)) :
    conj iota p ⊥ = (⊥ : EndP Y) := by
  ext z; simp [conj, h]

/-- **`⊤`-exactness**, given `iota ⊤ = ⊤`. *This is the theorem Update 19's
repair (i) was missing*: with the copy-`A` tower map `iota ⊤ ≠ ⊤`, so
conjugation was never `⊤`-exact; obstruction (T) says that is unfixable there,
and here it is simply a hypothesis that a re-based tower satisfies. -/
theorem conj_top [OrderTop X] [OrderTop Y]
    (iota : X →o Y) (p : Y →o X) (h : iota ⊤ = (⊤ : Y)) :
    conj iota p ⊤ = (⊤ : EndP Y) := by
  ext z; simp [conj, h]

/-- **Monotone** — unconditional. -/
theorem conj_monotone (iota : X →o Y) (p : Y →o X) :
    Monotone (conj iota p) := by
  intro f g hfg z
  exact iota.monotone (hfg (p z))

/-- **Order-reflecting**, given `p ∘ iota = id` (the ep-pair section law) —
so `conj` is an order-embedding, hence injective. -/
theorem conj_le_reflect (iota : X →o Y) (p : Y →o X)
    (hsec : ∀ x : X, p (iota x) = x) (f g : EndP X)
    (h : conj iota p f ≤ conj iota p g) : f ≤ g := by
  intro x
  have hx := h (iota x)
  simp only [conj_apply, hsec] at hx
  have hpx := p.monotone hx
  rwa [hsec, hsec] at hpx

/-- **Join-preserving**, given that `iota` preserves binary joins.  This is
what supplies the ep-pair partner at the next level. -/
theorem conj_sup (iota : X →o Y) (p : Y →o X)
    (hjoin : ∀ a b : X, iota (a ⊔ b) = iota a ⊔ iota b) (f g : EndP X) :
    conj iota p (f ⊔ g) = conj iota p f ⊔ conj iota p g := by
  ext z; simp [conj, hjoin]

section Tripointed

variable {X Y : Type*} [Lattice X] [Lattice Y]

/-- **The induction step Update 7 denied.**

With the *constants* convention for `[X→X]`'s basepoints —
`(T_H, L_H, R_H) := (constHom T, constHom L, constHom R)`, which is what
`Φ_tri_v2` uses at the real 3-chain base — conjugation by a **tripointed**
`iota` is itself tripointed, immediately, with no side conditions.

This is the whole content of the `2026-08-26` scope flag's refutation: the
F-tower's connecting maps *are* tripointed, so the tripointed-only
functoriality and local-continuity proofs do cover them. Combined with the
(equally immediate) fact that `Φ` sends tripointed maps to tripointed maps,
it gives the mutual induction `iota_k` tripointed ⇒ `conj iota_k` tripointed
⇒ `iota_{k+1} = Φ (conj iota_k)` tripointed, from a tripointed `iota₀`. -/
theorem conj_tripointed (iota : X →o Y) (p : Y →o X) (T L R : X) (T' L' R' : Y)
    (hT : iota T = T') (hL : iota L = L') (hR : iota R = R') :
    conj iota p (constHom T) = constHom T' ∧
    conj iota p (constHom L) = constHom L' ∧
    conj iota p (constHom R) = constHom R' :=
  ⟨by rw [conj_constHom, hT], by rw [conj_constHom, hL], by rw [conj_constHom, hR]⟩

/-- **Why `id` is the wrong middle basepoint, in one line.**  Had the middle
basepoint of `[X→X]` been `id` (as Update 7 read off a 2-chain base, where
`id` and `constHom L` are the same element), tripointedness of conjugation
would demand `iota ∘ p = id`, i.e. the ep-pair embedding is surjective — an
isomorphism.  That is exactly the "strict deflation" failure recorded in
Updates 1/7, and it is specific to `id`: nothing like it arises for a
*constant* middle basepoint, which `conj_constHom` pins for free. -/
theorem conj_id_eq_id_iff (iota : X →o Y) (p : Y →o X) :
    conj iota p OrderHom.id = OrderHom.id ↔ ∀ z : Y, iota (p z) = z := by
  constructor
  · intro h z; exact congrArg (fun f : EndP Y => f z) h
  · intro h; ext z; exact h z

end Tripointed

end HornB
