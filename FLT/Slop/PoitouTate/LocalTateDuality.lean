/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.LocalGlobalMaps
public import FLT.Slop.PoitouTate.DualModule
public import FLT.Slop.PoitouTate.inflmap
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Local Tate duality (blueprint §"Local–Tate duality")

This file scaffolds the local statements of `PTblueprint.tex` needed for Poitou–Tate, for a
finite place `v` of a number field `F` with local field `Fᵥ = v.adicCompletion F` and local
absolute Galois group `G_v = Gal(F̄ᵥ/Fᵥ)`. Throughout, `N : TopRep 𝔽 G_v` is a finite discrete
module over a finite field `𝔽` of characteristic `p`.

## Main declarations

* `NumberField.PoitouTate.algClosureUnitsRep` — `K̄ᵥ^×` as a discrete `TopRep ℤ G_v`.
* `NumberField.PoitouTate.localDualRep N` — the local dual `N* = Hom_ℤ(N, K̄ᵥ^×)`.
* `NumberField.PoitouTate.finite_continuousCohomology_local` — **Milne, Theorem 2.1**:
  `Hⁱ(G_v, N)` is finite for all `i`.
* `NumberField.PoitouTate.isZero_continuousCohomology_local` — **Milne, Corollary 2.3(2)**:
  `Hⁱ(G_v, N) = 0` for `i ≥ 3`.
* `NumberField.PoitouTate.localInvariantMap` — **Milne, Example 1.6**: the invariant map
  `inv_{G_v} : H²(G_v, K̄ᵥ^×) → ℚ/ℤ`. Per the project's instruction this is a bare `sorry`d
  definition (its construction — inflation from the unramified quotient, the valuation map, and
  `inv` of `Ẑ` — is local class field theory); only the property we use,
  `localInvariantMap_bijective`, is stated.
* `NumberField.PoitouTate.localTatePairing` — the cup-product pairing
  `Hⁱ(G_v, N*) × H^{2-i}(G_v, N) → H²(G_v, K̄ᵥ^×) → ℚ/ℤ`. The intended construction is
  `ContRepresentation.cup` from `cupprod.lean` (applied over `ℤ`, via the evaluation
  intertwiner `N* → Hom(N, K̄ᵥ^×)`), composed with `localInvariantMap`; the definition is
  `sorry`d here because the statement layer works `𝔽`-linearly.
* `NumberField.PoitouTate.localTatePairing_bijective_left` / `_right` — **Milne,
  Corollary 2.3(1)**: the pairing is perfect.
* `NumberField.PoitouTate.unramifiedClasses` — the unramified classes
  `H¹(G_v/I_v, N^{I_v}) ⊆ H¹(G_v, N)`, i.e. the image of inflation; to be defined via the
  forthcoming inflation map in `FLT/Slop/PoitouTate/inflmap.lean`.
* `NumberField.PoitouTate.mem_unramifiedClasses_localDualRep_iff` — **Milne, Theorem 2.6**:
  for `N` unramified with torsion prime to the residue characteristic, the unramified classes
  of `N` and of `N*` are the exact annihilators of each other under the pairing. (Milne states
  this with `N^d = Hom(N, R^{un,×})`; for finite `N` of order prime to `char k(v)` this equals
  `(N*)^{I_v}`, whose `H¹(G_v/I_v, ·)` gives the unramified classes used here.)

All theorem bodies are `sorry`; this file only fixes the statements.
-/

@[expose] public section

universe u

open IsDedekindDomain

namespace NumberField.PoitouTate

variable (𝔽 : Type*) [Field 𝔽] [Finite 𝔽] [TopologicalSpace 𝔽] [DiscreteTopology 𝔽]
variable (F : Type u) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (RingOfIntegers F))

/-- The units `K̄ᵥ^×` of an algebraic closure of the local field `Fᵥ`, as a discrete
topological `ℤ`-representation of the local absolute Galois group `G_v` (the coefficients of
local Tate duality). -/
noncomputable def algClosureUnitsRep :
    TopRep ℤ (Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  unitsAddRep (Field.absoluteGaloisGroup (v.adicCompletion F))
    (AlgebraicClosure (v.adicCompletion F))

variable (N : TopRep 𝔽 (Field.absoluteGaloisGroup (v.adicCompletion F)))

/-- The local dual `N* = Hom_ℤ(N, K̄ᵥ^×)` of a finite discrete `G_v`-module `N`, with
`G_v`-action `(g • f) (n) = g (f (g⁻¹ n))` (blueprint §"Local–Tate duality"). -/
noncomputable def localDualRep : TopRep 𝔽 (Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  homUnitsRep 𝔽 N (AlgebraicClosure (v.adicCompletion F))

/-- The local dual of a finite module is finite (values are roots of unity of order dividing
`#N`). -/
instance finite_localDualRep [Finite N] : Finite ↥(localDualRep 𝔽 F v N) :=
  inferInstanceAs (Finite (↥N →+ Additive (AlgebraicClosure (v.adicCompletion F))ˣ))

/-- The local dual carries the discrete topology by construction. -/
instance discreteTopology_localDualRep : DiscreteTopology ↥(localDualRep 𝔽 F v N) :=
  ⟨rfl⟩

/-- **Milne, Theorem 2.1**: for a finite discrete `G_v`-module `N`, the continuous cohomology
`Hⁱ(G_v, N)` is finite for all `i`. -/
theorem finite_continuousCohomology_local [Finite N] [DiscreteTopology N] (i : ℕ) :
    Finite ↥(continuousCohomology i N) :=
  sorry

/-- **Milne, Corollary 2.3(2)**: for a finite discrete `G_v`-module `N`, the continuous
cohomology `Hⁱ(G_v, N)` vanishes for `i ≥ 3`. -/
theorem isZero_continuousCohomology_local [Finite N] [DiscreteTopology N] {i : ℕ}
    (hi : 3 ≤ i) : CategoryTheory.Limits.IsZero (continuousCohomology i N) :=
  sorry

/-- **Milne, Example 1.6**: the invariant map `inv_{G_v} : H²(G_v, K̄ᵥ^×) → ℚ/ℤ` of local
class field theory (the composite of the inverse of inflation from the unramified quotient,
the valuation map, and the invariant map of `Ẑ`). The construction is deliberately left as
`sorry`; the property used downstream is `localInvariantMap_bijective`. -/
noncomputable def localInvariantMap :
    ↥(continuousCohomology 2 (algClosureUnitsRep F v)) →+ AddCircle (1 : ℚ) :=
  sorry

/-- **Milne, Example 1.6**: the invariant map is an isomorphism `H²(G_v, K̄ᵥ^×) ≅ ℚ/ℤ` — the
only property of `localInvariantMap` used in this development. -/
theorem localInvariantMap_bijective : Function.Bijective (localInvariantMap F v) :=
  sorry

/-- **Milne, Corollary 2.3** (the pairing): for `i + j = 2`, the cup-product pairing
`Hⁱ(G_v, N*) × Hʲ(G_v, N) → H²(G_v, K̄ᵥ^×) → ℚ/ℤ`.

The intended construction is `ContRepresentation.cup` of `cupprod.lean` — applied over `ℤ` to
the evaluation intertwiner `N* →ⁱL linHom N K̄ᵥ^×` — composed with `localInvariantMap`; it is
`sorry`d at the `𝔽`-linear statement layer. -/
noncomputable def localTatePairing (i j : ℕ) (hij : i + j = 2) :
    ↥(continuousCohomology i (localDualRep 𝔽 F v N)) →+
      ↥(continuousCohomology j N) →+ AddCircle (1 : ℚ) :=
  sorry

/-- **Milne, Corollary 2.3(1)**, left perfectness: cup product followed by the invariant map
identifies `Hⁱ(G_v, N*)` with the `ℚ/ℤ`-dual of `H^{2-i}(G_v, N)`. -/
theorem localTatePairing_bijective_left [Finite N] [DiscreteTopology N] (i j : ℕ)
    (hij : i + j = 2) : Function.Bijective (localTatePairing 𝔽 F v N i j hij) :=
  sorry

/-- **Milne, Corollary 2.3(1)**, right perfectness: the flipped pairing identifies
`Hʲ(G_v, N)` with the `ℚ/ℤ`-dual of `H^{2-j}(G_v, N*)`. -/
theorem localTatePairing_bijective_right [Finite N] [DiscreteTopology N] (i j : ℕ)
    (hij : i + j = 2) : Function.Bijective (localTatePairing 𝔽 F v N i j hij).flip :=
  sorry

/-! ### Unramified classes and Milne's Theorem 2.6 -/

/-- The local inertia subgroup is normal in the local absolute Galois group (it is the kernel
of the action on the residue field of the integral closure). Needed to form the unramified
quotient `G_v/I_v`. -/
instance normal_localInertiaGroup : (localInertiaGroup v).Normal :=
  sorry

/-- **Unramified cohomology** (blueprint §"Local–Tate duality"): the submodule of unramified
classes `H¹(G_v/I_v, Y^{I_v}) ⊆ H¹(G_v, Y)`, the image of the inflation map
`ContinuousCohomology.inflApp` of `FLT/Slop/PoitouTate/inflmap.lean` at the inertia
subgroup. -/
noncomputable def unramifiedClasses
    (Y : TopRep 𝔽 (Field.absoluteGaloisGroup (v.adicCompletion F))) :
    Submodule 𝔽 ↥(continuousCohomology 1 Y) :=
  LinearMap.range (ContinuousCohomology.inflApp (localInertiaGroup v) 1 Y).hom.toLinearMap

/-- **Milne, Theorem 2.6**: let `N` be a finite discrete `G_v`-module, unramified (inertia
acts trivially) and of order prime to the residue characteristic (automatic here: `N` is an
`𝔽`-module of characteristic `p` and `v ∤ p`). Then the unramified classes of `N*` and of `N`
are the exact annihilators of each other under the local Tate pairing on `H¹ × H¹`. -/
theorem mem_unramifiedClasses_localDualRep_iff [Finite N] [DiscreteTopology N]
    (p : ℕ) [Fact p.Prime] [CharP 𝔽 p]
    (hv : (p : RingOfIntegers F) ∉ v.asIdeal)
    (hunr : ∀ g ∈ localInertiaGroup v, ∀ n : ↥N, N.ρ g n = n)
    (x : ↥(continuousCohomology 1 (localDualRep 𝔽 F v N))) :
    x ∈ unramifiedClasses 𝔽 F v (localDualRep 𝔽 F v N) ↔
      ∀ y ∈ unramifiedClasses 𝔽 F v N, localTatePairing 𝔽 F v N 1 1 rfl x y = 0 :=
  sorry

end NumberField.PoitouTate
