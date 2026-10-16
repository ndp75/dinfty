# Rigidity and self-similarity in a three-copy gluing tower — Lean 4

[![Verify](https://github.com/ndp75/dinfty/actions/workflows/ci.yml/badge.svg)](https://github.com/ndp75/dinfty/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

**Paper:** [`paper/main.tex`](paper/) — *Rigidity and self-similarity in a
three-copy gluing tower of finite lattices, machine-checked in Lean 4*
(arXiv: to appear). It gives the definitions, theorem statements and proof
sketches in ordinary mathematical notation; its Appendix A maps every notion to
the Lean declaration that proves it. Read that first if you want the
mathematics; read on here for the build.


This directory is a **self-contained release**: 116 Lean modules whose import
closure is exactly what the headline theorems depend on. Nothing here is
optional, and nothing outside it is needed.

Everything is checked by Lean's kernel. There are no `sorry`s, no
`native_decide`, and no project-specific axioms — every result rests only on
Lean's three standard axioms.

| | |
|---|---|
| Modules | 116 |
| Lines of Lean | 37,109 |
| Toolchain | `leanprover/lean4:v4.32.2` |
| Mathlib | `v4.32.2` (rev `905b95818eb3`) |
| Entry point | `Dinfty.Verify` |
| Axiom checks | 195 |
| Status | builds clean; verified 2026-09-21 |

---

## What is proved

Two independent results, plus a machine-checked internal IFS and two negative
results. All of them are re-stated and re-checked in
[`Dinfty/Verify.lean`](Dinfty/Verify.lean), which is the single file a reviewer
needs to read.

### Theorem A — the bilimit is a fixed point of Φ

```lean
noncomputable example : PhiBilimit.phiB ≃o PhiIterateTower.phiTowerEP.Bilim :=
  PhiSurjective.theoremA_orderIso
```

`Φ_σ(B) ≃o B`: the bilimit `B` of the Φ-iterate tower is a fixed point, up to
order-isomorphism, of the gluing built from Scott-continuous self-maps.

### Theorem B — rigidity

```lean
example : Subsingleton (DInfty ≃o DInfty) := CopyCHigh.colimit_compat
example : Subsingleton (DBilimit ≃o DBilimit) := CopyCHigh.DBilimit_rigid
```

Two different objects are rigid: `DInfty`, the colimit of the constant-embedding
tower, and `DBilimit`, the ep-pair bilimit of the same tower. They are **not**
two presentations of one object: `toDBilimit : DInfty ↪o DBilimit` is an order
embedding whose image is exactly the compact elements of `DBilimit`
(`mem_range_toDBilimit_iff_isCompactElement`), and `topSeq` is not in it.
Rigidity of `DBilimit` is derived from rigidity of `DInfty` through that fact.

### Theorem A and Theorem B are about different objects

```lean
example : ¬ Nonempty (PhiBilimit.B ≃o DBilimit) := BilimitGap.no_orderIso
example : ¬ Nonempty (PhiBilimit.B ≃o DInfty) := BilimitGap.no_orderIso_DInfty
```

`B`'s top is ω-compact and `DBilimit`'s is not; `DInfty` has no top at all. Rigidity of `B` itself is not
proved; `Verify.lean`'s `*Check` sections record the conditional reductions and
the refutations that are.

### The internal IFS, and two refutations

The development also builds an honest internal IFS on the carrier with all
three copy-maps **injective**, and machine-checks two *negative* results — that
`Fix σ_A = {⊥}` fails for the first IFS, and that the address coding map
`codeGamma` onto the Sierpiński gasket is not an open map, so that field of the
interface is weakened to `IsQuotientMap`. Negative results are stated as theorems, not as
absent lemmas.

---

## 1. Installing the dependencies

You need **`elan`** (the Lean toolchain manager). Everything else — the exact
Lean version and all Mathlib sources — is pinned by the files in this
directory and fetched by `lake`.

<details open>
<summary><b>Linux / macOS / WSL</b></summary>

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"
```
</details>

<details>
<summary><b>Windows (PowerShell)</b></summary>

```powershell
curl.exe -sSfL https://elan.lean-lang.org/elan-init.ps1 -o elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
```
</details>

`elan` reads [`lean-toolchain`](lean-toolchain) and installs Lean `v4.32.2`
automatically the first time you run `lake` in this directory — you do not
install Lean by hand.

Confirm it picked up the right version:

```bash
lake --version
# Lake version 5.0.0-src+f3b06c7 (Lean version 4.32.2)
```

### Fetch Mathlib

```bash
lake exe cache get     # downloads prebuilt Mathlib .olean files
```

> [!IMPORTANT]
> Do not skip `lake exe cache get`. Without it, `lake build` compiles all of
> Mathlib from source, which takes **hours** instead of minutes. If the cache
> download fails, re-run it — it is resumable.

Requirements: roughly 10 GB of free disk for Mathlib's sources and oleans, and
a network connection for this step only. The build itself is offline.

---

## 2. Building

```bash
lake build Dinfty.Verify
```

This is the acceptance target. It elaborates both headline theorems and prints
the axioms each one depends on.

```bash
lake build
```

The default target. It builds every one of the 116 modules — a superset of
`Dinfty.Verify`, and it also passes. Use this if you want the whole corpus
checked rather than just the closure of the headline results.

**Expected cost.** On a warm Mathlib cache the 116 modules take roughly
**15–20 minutes** of wall clock. The build parallelises, but one module is on
the critical path and cannot be split:

| Module | Elapsed |
|---|---:|
| `GluingTowerLibrary` | 583 s |
| `GlueAAGenReflectM` | 113 s |
| `ProjectionTripointed` | 51 s |
| all 113 others | < 20 s each |

Budget separately for `lake exe cache get`, which is network-bound and depends
on your connection. The build is incremental: if it is interrupted, re-running
resumes where it stopped rather than starting over.

You will see a large number of **style-linter warnings** (`open Classical`,
`show` vs `change`, line length). These are Mathlib house-style advisories, not
errors, and they do not affect correctness. **Warnings are expected; `error:`
lines are not.**

---

## 3. Verification

### Acceptance criteria

A clean run satisfies all five:

| # | Check | Expected |
|---|---|---|
| 1 | Build outcome | `Build completed successfully` — 3119 jobs for `Dinfty.Verify`, 3121 for `lake build` |
| 2 | `error:` lines | **0** |
| 3 | `declaration uses 'sorry'` | **0** |
| 4 | `sorryAx` / `Lean.ofReduceBool` | **0** |
| 5 | `#print axioms` results | **195**, all standard |

### The exact expected output

The 195 `#print axioms` commands do **not** all produce the same form. Three of
them report no axioms at all, so only 192 lines contain the phrase
`depends on axioms`. A clean run gives exactly this distribution:

| Result | Count | Meaning |
|---|---:|---|
| `depends on axioms: [propext, Classical.choice, Quot.sound]` | 177 | all three standard axioms |
| `depends on axioms: [propext, Quot.sound]` | 9 | choice-free |
| `depends on axioms: [propext]` | 6 | choice- and quotient-free |
| `does not depend on any axioms` | 3 | fully axiom-free |
| **total** | **195** | |

Every one of these is acceptable: `propext`, `Classical.choice` and
`Quot.sound` are Lean's three standard axioms, and the last three rows are
*stronger* results, not weaker ones — they depend on strictly fewer. The
acceptance rule is therefore **"the axiom set is a subset of the three
standard axioms"**, not "equals one of two specific lists".

The three declarations that need no axioms whatsoever are:

```
SigmaRebuild.base_pin_of_mem
SeamTriangle.address_seamless
EmbTagwise.canonGen_baseMapGen
```

Two markers would signal failure, and neither occurs anywhere in the build
output:

- **`sorryAx`** — a `sorry` reached the kernel. The proof has a hole.
- **`Lean.ofReduceBool`** — a `native_decide`, which trusts the compiler
  outside the kernel.

Both are absent from the log entirely, so even a bare
`grep -c sorryAx build.log` returns `0`.

### Run the checks

Capture the build output, then check it:

```bash
lake build Dinfty.Verify 2>&1 | tee build.log
```

Lake replays cached messages, so the 195 axiom results are re-emitted on every
run — you do not need a clean rebuild to re-check them.

Then summarise every axiom result:

```bash
grep -o "depends on axioms: \[[^]]*\]" build.log | sort | uniq -c
grep -c "does not depend on any axioms" build.log
```

Expected output — these four numbers and nothing else:

```
    177 depends on axioms: [propext, Classical.choice, Quot.sound]
      9 depends on axioms: [propext, Quot.sound]
      6 depends on axioms: [propext]
3
```

> [!TIP]
> When you read `#print axioms` output in a **terminal** rather than a
> redirected file, long axiom lists wrap across lines and a naive `grep` can
> truncate one — so a bad line may read as clean. Redirect to a file first, as
> above, or pipe through `tr '\n' ' '` before grepping.

### One-shot acceptance script

[`scripts/acceptance.sh`](scripts/acceptance.sh) runs the build and all five
checks above, prints the axiom distribution, and exits non-zero on any failure:

```bash
bash scripts/acceptance.sh
```

The same script runs in CI on every push ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)).

### What the 195 checks cover

`Verify.lean` is organised into 25 sections. Each re-states a result as an
anonymous `example` — so the statement in `Verify.lean` is type-checked against
the real theorem and cannot drift from it — and then prints its axioms.

| Section | What it pins down |
|---|---|
| `PillarA` | Theorem A: `Φ_σ(B) ≃o B` |
| `PillarB` | Theorem B: rigidity of `DInfty` and `DBilimit` |
| `InternalIFS` | The internal IFS exists; all three σ-maps injective |
| `Escape` | **Refutation**: `Fix σ_A = {⊥}` is false for this IFS |
| `Rebuilt` | The repaired IFS, with the coincidence removed |
| `Projection` | `qAA` is explicit — a greatest element, never a `choice` |
| `EscapeHolds` | `Fix σ_A = {⊥}` for the rebuilt σ_A |
| `Gasket` | Γ is constructed, not assumed; the coding map is a quotient map |
| | **Refutation**: `codeGamma` is not an open map |
| `Link`, `Continuity` | The address map into `B` and the map `rho` onto Γ |
| `TwoObjects` | `B ≄o DBilimit` and `B ≄o DInfty`: the two pillars are about different objects |
| 14 further `*Check` sections | Stage, embedding, seam, cover, chain and ideal invariants |

An `example` that failed to typecheck would be a build error, so criterion 2
already covers the statements; the axiom reports cover the proofs.

---

## 4. The import DAG

The dependency graph is **deep and narrow** rather than broad: 116 modules with
a longest import chain of 54 edges, ending at `Verify`. Every module is
reachable from the root [`Dinfty.lean`](Dinfty.lean), and exactly one module —
`Verify` — is imported by nothing.

The diagram below is the *transitive reduction* of the dependencies between the
headline modules, so every arrow is a real dependency and no arrow is implied
by another.

```mermaid
graph TD
  subgraph Core["Core — the gluing tower"]
    ProdAut[ProdAut]
    GTL["GluingTowerLibrary<br/>10,386 ln"]
    SA["SierpinskiApplication<br/>4,858 ln"]
    NGM[NormalizedGlueMap]
    GC[GenContinuity]
  end

  subgraph PB["Pillar B — rigidity"]
    ELC[EndLocalContinuity]
    CCP[ColimitCompatPipe]
    SSP[SeedShapeProof]
    FSC[FirstSliceCut]
    CCH["CopyCHigh<br/><b>Theorem B</b>"]
  end

  subgraph PA["Pillar A — the Φ-iterate tower"]
    EPT[EpPairTower]
    PTF[PhiTriFunctor]
    PIT[PhiIterateTower]
    PBL[PhiBilimit]
    PCL[PhiCoconeLUB]
    PS["PhiSurjective<br/><b>Theorem A</b>"]
  end

  subgraph IFS["Internal IFS and gasket"]
    CIFS[CoreIFS]
    GK[Gasket]
    GKC[GasketCoding]
    IFSI[InternalIFSInstance]
    SR[SigmaRebuild]
    EP[EscapeProof]
  end

  V(["<b>Verify</b><br/>195 axiom checks"])

  ProdAut --> GTL --> SA --> NGM --> GC
  GC --> ELC --> CCP --> SSP --> FSC --> CCH
  GC --> PTF --> PIT
  EPT --> PIT
  SSP --> PIT
  PIT --> PBL --> PCL --> PS
  CIFS --> IFSI
  PS --> IFSI --> SR --> EP
  GK --> GKC

  CCH --> V
  EP --> V
  GKC --> V

  style V fill:#1f6feb,stroke:#1f6feb,color:#fff
  style CCH fill:#238636,stroke:#238636,color:#fff
  style PS fill:#238636,stroke:#238636,color:#fff
```

Two structural facts worth noting, both visible above:

- **The pillars are not independent all the way down.** `PhiIterateTower`
  imports `SeedShapeProof` — Pillar A's tower construction reuses Pillar B's
  seed machinery. Only the *statements* are independent.
- **The IFS sits on top of Theorem A**, not beside it: `InternalIFSInstance`
  imports `PhiSurjective`, because injectivity of the copy-maps is exactly what
  the earlier retract construction could not supply.

### Regenerating the full graph

The full 116-node graph is too dense to read here, but you can generate it —
the `importGraph` tool is already among the pinned dependencies:

```bash
lake exe graph --to Dinfty.Verify dag.dot     # or .pdf, .svg, .png
```

That emits all 116 nodes, transitively reduced to 148 edges. (`.pdf`, `.svg`
and `.png` additionally need Graphviz on your `PATH`; `.dot` never does.)

To recompute the shape directly from the sources, without building:

```bash
ls Dinfty/*.lean | wc -l                           # modules ........... 116
cat Dinfty/*.lean | wc -l                          # lines ........... 37109
grep -h '^import Dinfty\.' Dinfty/*.lean | wc -l   # import statements .. 189
```

---

## 5. Layout

```
.
├── README.md              this file
├── LICENSE                Apache-2.0
├── CITATION.cff           how to cite this repository
├── lean-toolchain         pins Lean v4.32.2 (read by elan)
├── lakefile.toml          pins Mathlib v4.32.2; defaultTargets = ["Dinfty"]
├── lake-manifest.json     pins the exact Mathlib revision (905b95818eb3)
├── REFERENCE_INDEX.md     [D-NNNN] label → declaration and file
├── reference_index.json   the same index, machine-readable
├── Dinfty.lean            root module — imports all 116, the default target
├── Dinfty/                the 116 release modules
│   ├── Verify.lean               start here: every headline result + 195 axiom checks
│   ├── GluingTowerLibrary.lean   the general theory (10,386 ln)
│   ├── SierpinskiApplication.lean  the concrete tower (4,858 ln)
│   └── ...
├── paper/                 LaTeX source of the paper (main.tex, refs.bib)
├── scripts/acceptance.sh  build + axiom acceptance check
└── .github/workflows/     CI: build, acceptance check, paper PDF
```

### Reading guide

The sources carry no prose comments, only `-- [D-NNNN] name` labels, so this is
the map. Each row is one module; read them in this order.

| Module | What it contains | Paper |
|---|---|---|
| `Verify` | Every headline result restated as an `example`, with `#print axioms` | all |
| `GluingTowerLibrary` | Gluing `GlueCarGen`, its order (`rawRule`, `leGlue`), `EndP`, `ScottEndP`, join-irreducibles, `jiOrderIso` | §3 |
| `SierpinskiApplication` | The tower `D`, `dMid`, `markedPt`, `iotaD`/`pD`, `DInfty`, `DBilimit`, `D_all_rigid`, compact elements | §3–§5 |
| `PhiTriFunctor`, `PhiTriTower` | `Φ` on tripointed maps; functor laws; `D (k+1) = Φ(D k)` by `rfl` | §3 |
| `GlueAAJoin`, `QAAExplicit` | The first Φ-iterate embedding `glueAA`, its lift, its explicit upper adjoint | §4.2 |
| `PhiIterateTower`, `PhiBilimit` | The Φ-iterate tower and its bilimit `B`, `midB`, `topB`, `phiB` | §4.2, §6 |
| `BilimitGap` | `B ≄o DBilimit`, `B ≄o DInfty` | §4.3 |
| `DInftyNoFootholds` | `DInfty` has no atom and no top | §4.1 |
| `ProdAut`, `EndPRigid` | Product automorphisms split; `EndP` of a rigid lattice is rigid | §5.1 |
| `SeedShapeProof`, `Truncation`, `Height`, `FinishLine`, `CutObstruction`, `FirstSliceCut` | The colimit step of Theorem B | §5.2 |
| `CopyCHigh` | The divisibility case, and **Theorem B**: `colimit_compat`, `DBilimit_rigid` | §5.2 |
| `PhiCocone`, `PhiCoconeLUB`, `PhiSurjective` | The colimit cocone and **Theorem A**: `theoremA_orderIso` | §6 |
| `InternalIFSInstance`, `EscapeAnalysis`, `SigmaRebuild`, `EscapeProof` | The internal IFS, its refutation, the repair | §7 |
| `Gasket`, `GasketCoding`, `GasketCoreIFS`, `GasketNotOpen` | The gasket `Γ`, `codeGamma`, not an open map | §7.1 |
| `CodeB`, `AddressConvergence`, `SeamTriangle`, `RhoContinuity` | Addresses in `B`, `rho`, and the refutations about it | §7.2 |
| `StageRigidity`, `PhiStagePipe`, `StageCofinal`, `StageEmbedding`, `EmbDImage`, `PatchedEmbedding`, `StageCover`, `SeamCut`, `IdealInvariant` | What is proved about automorphisms of `B` | §8 |

### A note on scope

This repository is the release closure only. The research history (a further
axiom audit of 325 declarations, and archived modules recording refutations,
measurements and abandoned routes) is not included; none of it is needed to
check the theorems above.

## Reproducibility

`lean-toolchain` and `lake-manifest.json` pin the compiler and every dependency
to an exact revision, so this build is reproducible: a peer running the two
commands in §2 gets the same 195 axiom reports.

## Citing

If you use this development, please cite the paper (arXiv identifier to follow)
or the repository; [`CITATION.cff`](CITATION.cff) has the details, and GitHub's
"Cite this repository" button reads it.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). This is the license Mathlib uses.
