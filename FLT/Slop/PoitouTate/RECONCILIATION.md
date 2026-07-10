# Poitou–Tate: reconciliation of the two partial developments

*Status: 2026-07-10.  Goal: a **sorry-free statement** of the Poitou–Tate nine-term exact
sequence with **explicit maps**, i.e. every definition appearing in
`NumberField.PoitouTate.poitouTateSeq` (and hence in the exactness statement
`NumberField.PoitouTate.poitouTate`) compiles with no `sorry` in its dependency closure;
only the *theorems* (exactness, perfectness, finiteness, local CFT) remain sorried.*

> **Note on the blueprint.** Every docstring in this folder cites
> `FLT/Slop/PoitouTate/PTblueprint.tex`, which was deleted in commit `68f7a3f`
> ("deleted blueprint"). The folder's design follows it exactly (checked 2026-07-10).
> Recover it with `git show 68f7a3f^:FLT/Slop/PoitouTate/PTblueprint.tex` if needed,
> or restore it if the doc references should stop dangling.

## The two bodies of work

1. **`FLT/Slop/PoitouTate/` (this folder)** — the canonical development. Organized,
   committed, compiles in CI (imported from `FLT.lean`). Built on Mathlib's
   `continuousCohomology` (homogeneous cochains, `TopRep k G`,
   `Action (TopModuleCat k) G`), on `NumberField.unramifiedOutsideGaloisGroup`
   (`GKSDefn.lean`), and on the repo's `Field.absoluteGaloisGroup` /
   `localInertiaGroup` (`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`).
   Headline: `NumberField.PoitouTate.poitouTate` in `PoitouTateStatement.lean`, stated as
   exactness of a `ComposableArrows (ModuleCat 𝔽) 10`.

2. **`FLT/Slop/PoitouTateLogos.lean`** — an untracked 3 800-line single-file draft produced
   in a different environment (`import LeanProject`; **does not compile in this repo**).
   Self-contained framework: inhomogeneous locally-constant cochains
   (`contCochain n = LocallyConstant (Fin n → G) A`), hand-rolled coboundary/cocycles/
   cohomology, cochain-level cup products, and — crucially — **explicit constructions of
   the maps the folder leaves as sorried definitions** (local invariant map, local Tate
   pairing, β, the kernel pairing, ψ/φ connecting maps).

**Decision: the folder framework wins everywhere the two overlap.** It compiles, matches
Mathlib, and its `G_{F,S}` is already consumed downstream (`REqualsT/Patching.lean`). The
Logos file is kept only as a **quarry** for the constructions the folder is missing; each
item below marked "port" should be translated into the folder framework, after which the
Logos file should be deleted.

## Item-by-item map (Logos → folder)

### Covered by the folder — discard the Logos version

| Logos | Folder | Notes |
|---|---|---|
| `sRamifiedSubgroup`, `sGaloisGroup` (G_K/N_S via inertia images) | `unramifiedOutsideGaloisGroup` (`GKSDefn.lean`) | Folder version proved Galois + cached profinite instances |
| `PoitouTateSetup` (bundled structure; totally real K, p > 2, S ⊇ ∞) | unbundled variables + hypotheses `h2 : (2 : 𝔽) ≠ 0`, `hS` | Folder's deviations are deliberate & documented (archimedean places dropped via `isZero_tateCohomology_of_invertible_card`; totally-real unneeded) |
| `sMaximalExtension` | `maximalUnramifiedOutside` | |
| `dualModule`, `dualModuleRep`, `dualFinite` | `dualRep`, `finite_dualRep` (proved), `homUnitsRep` | |
| `setupRho`, `decompositionMap`, `localRho` | `toGKS`, `localToGlobal`, `localRes` | |
| `existsCompatibleEmbedding`, `globalToLocalEmbedding` (sorried in Logos) | already in repo: `Field.absoluteGaloisGroup.map` is built from `IsAlgClosed.lift` with `restrictNormal_commutes` | no work needed |
| choice-independence of local restriction | `ConjInvariance.lean` + `continuousCohomology_map_conjAux` — **proved** (0 sorries) | Logos's `h1ConjActionWellDefined` route superseded |
| hand-rolled cochain complex (`contCochain`, `contCoboundary`, `contCocycles`, `contCohomologyGrp`) | Mathlib `continuousCohomology`; degree-1 cochain access in `phipmap.lean` | |
| `contCochainComap`, `contCohomologyRes`, `contCohomologyCoeffMap` | `ContinuousCohomology.map` (`inflmap.lean`, Mathlib) | |
| inflation | `ContinuousCohomology.inflApp` (`inflmap.lean`) — **proved** (0 sorries) | |
| `contCupProduct` (cochain level) + `contCupCocycle` | `cupprod.lean`: `cupComplex` + Leibniz `cup_d_comm` — **proved** (0 sorries) | missing only the final `cup` on cohomology (TODO in file) |
| `ratCircle` | `AddCircle (1 : ℚ)` / `CharacterModule` | |
| `sAlpha` / `alphaI` / `KerI` | `alpha` / `kerAlpha` — **done** | |
| `noTorsionH3` | `eq_zero_of_smul_continuousCohomology_three_ksUnitsRep` (sorried theorem — global CFT) | |
| `unramifiedDual` (M^d), `unramifiedDualClosed`, `unramifiedAnnihilators` | `unramifiedClasses` (via inflation image) + `mem_unramifiedClasses_localDualRep_iff` (Milne 2.6) | folder phrasing is cleaner |
| `localTateDuality`, `localFiniteness` | `localTatePairing_bijective_left/right`, `finite_continuousCohomology_local`, `isZero_continuousCohomology_local` | |
| `H2H1Finite` | `finite_continuousCohomology_two`, `finite_continuousCohomology_one_dualRep` | |
| `inflationRestriction` (five-term) | `InfRes.lean` (three-term, per blueprint red note) | |
| nine-term statement (9 iff-clauses) | `poitouTateSeq` + `poitouTate` (`ComposableArrows`) | folder statement is the keeper |

### Missing from the folder — port from Logos (this is the real work)

These are the folder's **sorried definitions**; the Logos file contains the explicit
constructions, to be translated into the `TopRep`/`continuousCohomology` framework:

| Folder sorried def | Logos source (line refs in `PoitouTateLogos.lean`) |
|---|---|
| `ContRepresentation.cup` on cohomology (cupprod TODO) | `contCohomologyCup` (~941) |
| `LocalTateDuality.localInvariantMap` | the whole chain `invGv` (~2232): `localUnramifiedQuotient` (~1602), `existsFrobeniusGen`/`frobeniusGen` (~1621), `unramifiedUnitsRep` (~1752), `unramifiedOrd` (~1804), `bockstein` machinery (~1284–1500), `evalH1` (~1447), `invOfGen`/`invU` (~1501), `inflationKvUn` (~2106) |
| `LocalTateDuality.localTatePairing` | `localEvalPairing` (~974) + `localTatePairing` (~2296): cup with the evaluation pairing, then `invGv` |
| `LocalTateDuality.normal_localInertiaGroup` | `localInertiaNormal` (~1561, sorried there too — needs a real proof) |
| `PoitouTateStatement.beta` | `betaI` (~2605): `β_i(x)(y) = ∑ᶠ_{v∈S} ⟨res_v y, x_v⟩_v` — note it uses the evaluation pairing pushed along `K_S ↪ K̄_v` directly, **avoiding `localDualCompat` in the definition** (the iso is only needed in proofs) |
| `PoitouTateStatement.kerPairing` | `cupProductZero` (Claim 4.4, ~2846), `kernelPairingChoices` (~2735), `cocycleClaim` (4.5(i), ~2882), `cocycleClaimDiff` (4.5(ii), ~3713), `kernelPairing` (~2946), `explicitPairing` (~2994): `⟨f,g⟩ = ∑_{v∈S} inv_v(res_v f ∪ ψ_v − res_v h)` for cochain choices `f∪g = dh`, `d⁰ψ_v = res_v g` |
| `PoitouTateStatement.psi` | `psiMap` (~3220) — **but see the sorry-freeness warning below** |
| `PoitouTateStatement.connectTwo` | `phiMap` (~3248) precomposed with the kernel inclusion (clause 6 of Logos `poitouTate`, ~3335) |

### Sorry-freeness warning about the Logos definitions

Several Logos definitions are *not* actually sorry-free even in their own environment:
they apply `Classical.choose` / `Equiv.ofBijective` to **sorried theorems**
(`psiMap` ← `dualPairingPerfect`, `phiMap` ← `pairingNonDegenerate`,
`invGv` ← `inflationKvUnBijective`, `frobeniusGen` ← `existsFrobeniusGen`, and every
def whose carrier proof (`IsLocallyConstant`, membership) is a sorried lemma).
When porting, use **junk-total patterns** so the definitions never depend on unproven
propositions:
* inverse of a map whose bijectivity is a (sorried) theorem → `Function.invFun`, not
  `Equiv.ofBijective`;
* a choice witnessed by a (sorried) existence lemma → `if h : ∃ …  then Classical.choose h else 0`
  (junk default), with the existence lemma only invoked in *proofs*;
* the topological generator of `G_v/I_v` → either prove existence honestly
  (`Gal(𝔽̄_q/𝔽_q) ≅ Ẑ`) or thread it as junk-total choice.

## Finishing plan

Ordered so that each phase unblocks the next; phases 1–5 reach the goal
(sorry-free statement, explicit maps); phase 6 is the long tail of actual proofs.

1. **Cup product on cohomology** (`cupprod.lean` TODO). Define
   `ContRepresentation.cup : Hᵐ(G, ρ₁) → Hⁿ(G, ρ₂) → H^{m+n}(G, ρ₃)` from the
   already-proved `cupComplex` + `cup_d_comm`. Unblocks 2–4.
2. **Explicit local invariant map** (new file `LocalInvariantMap.lean`), porting the
   Logos `invGv` chain: `normal_localInertiaGroup` (prove it — also discharges the
   LocalTateDuality instance), unramified quotient `G_v/I_v`, Frobenius generator,
   `(K_v^{un})ˣ` as a discrete module (reuse `unitsAddRep`), the `ord` valuation map,
   Bockstein `H¹(−, ℚ/ℤ) ≅ H²(−, ℤ)`, inflation iso from the unramified quotient
   (bijectivity = Hilbert 90 + `Br(K^{un}) = 0`, stays a sorried *theorem*; use
   `Function.invFun` in the def). Fill `localInvariantMap`;
   `localInvariantMap_bijective` stays sorried.
3. **Local Tate pairing + β.** Evaluation intertwiner
   `res_v(M*) →ⁱL linHom (res_v M) K̄ᵥˣ` (evaluation pushed along `K_S ↪ K̄ᵥ`, which the
   repo already provides via `IsAlgClosed.lift`); `localTatePairing := inv_v ∘ cup`;
   `beta` by the explicit finite sum over `v ∈ S`. `localDualCompat` is *not* needed for
   the definitions — keep it (sorried) for the perfectness proofs. Risk item:
   𝔽-linearity of `beta` (the pairing must be 𝔽-balanced); if it stalls, state `beta`
   as an `AddMonoidHom` first and upgrade later.
4. **Kernel pairing + connecting maps.** Port the cochain-level
   `kernelPairing`/`explicitPairing` using junk-total choices for `h` and `ψ_v`
   (existence = Claim 4.4 / local triviality, sorried theorems used only in
   well-definedness proofs); then `psi := Function.invFun Ψ`-style and
   `connectTwo := phiMap ∘ (− ∘ ker-inclusion)`. This is the hardest translation —
   it needs inhomogeneous-cochain access to Mathlib's `continuousCohomology`
   (extend the degree-1 dictionary in `phipmap.lean` to degrees 2–3).
5. **Assemble and audit.** `poitouTateSeq` becomes fully explicit. Check
   `#print axioms NumberField.PoitouTate.poitouTateSeq` contains no `sorryAx`.
   Delete `FLT/Slop/PoitouTateLogos.lean` (fully mined) and this file's "port" table.
6. **The remaining mathematics** (sorried theorems, roughly increasing depth):
   easy instances (`finite_localDualRep` etc. — done 2026-07-10); inflation–restriction
   three-term exactness (`InfRes.lean`); `isZero_tateCohomology_of_invertible_card`;
   Mazur `Φ_p` layers (`H1GSfinite.lean`) and Hermite–Minkowski →
   `finite_continuousCohomology_two`/`_one_dualRep`; local finiteness + vanishing
   (Milne 2.1/2.3); `localInvariantMap_bijective` (local CFT);
   local duality perfectness (Milne 2.3(1)); Milne 2.6 (unramified annihilators);
   `H³` torsion vanishing (global CFT); kernel-pairing perfectness (Prop 4.8);
   **exactness of the nine-term sequence** (Milne I.4.10).
