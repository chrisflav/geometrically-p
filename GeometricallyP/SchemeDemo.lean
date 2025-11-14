/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Schemes in mathlib

This file contains an introduction to scheme theory in mathlib.
-/

universe u

-- Most declarations are in the `AlgebraicGeometry` namespace
open AlgebraicGeometry CategoryTheory Limits

section PrimeSpectrum

/-! ## Prime spectrum of a ring -/

variable {R S : Type*} [CommRing R] [CommRing S]

-- The `PrimeSpectrum` of a ring is a type.
#check PrimeSpectrum R

-- To provide a term of type `PrimeSpectrum R`, we need to give an ideal of `R`
-- with a proof that `p` is a prime ideal.
example (p : Ideal R) [p.IsPrime] : PrimeSpectrum R := ⟨p, (inferInstance : p.IsPrime)⟩

-- It is endowed with a structure of topological space.
example : TopologicalSpace (PrimeSpectrum R) :=
  inferInstance

-- `PrimeSpectrum` is functorial wrt. to ring homomorphisms.
example (f : R →+* S) : PrimeSpectrum S → PrimeSpectrum R :=
  f.specComap

-- This is the set `V(s) ∩ D(f)`.
example (s : Set R) (f : R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus s ∩ PrimeSpectrum.basicOpen f

/-!
### The unbundled vs. bundled barrier.

The composition of two ring homomorphisms can be expressed as:
-/
example (R S T : Type) [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    R →+* T :=
  RingHom.comp g f

/- or as: -/
example (R S T : CommRingCat) (f : R ⟶ S) (g : S ⟶ T) : R ⟶ T :=
  f ≫ g

/-!
The first approach is called *unbundled* and the second one *bundled*: In the first version,
the `CommRing` structure on `R` is provided as a separate argument. It is unbundled from the
type `R`. In the second version, the `CommRing` structure is bundled with the type in a term
`R : CommRingCat`.

Note that we have to write `R →+* S` in the first case to talk about a *ring homomorphism* `f`. This
is because `R S : Type`. In the case of `R S : CommRingCat`, the types contain enough information
to *infer* that `R ⟶ S` denotes a ring homomorphism.

Moreover, in the bundled version we can use the notation `f ≫ g` to denote composition of the
ring homomorphisms `f` and `g`.
-/

/-!
Most of the topology and commutative algebra library is written in the unbundled style. But
to talk about the *category* of commutative rings or the *category* of topological spaces, this
category needs a *type of objects*.
-/

-- The category of commutative rings.
example : Type 1 := CommRingCat

-- The category of topological spaces.
example : Type 1 := TopCat

-- The type of commutative rings is endowed with a category structure.
example : Category CommRingCat := inferInstance

-- This allows us to write `𝟙 _` for the identity and `_ ≫ _` for composition:
example (R S : CommRingCat) (f : R ⟶ S) : R ⟶ S := 𝟙 R ≫ f ≫ 𝟙 S

-- We can still apply a morphism in `CommRingCat` to an element.
example (R S : CommRingCat) (f : R ⟶ S) (x : R) : S := f x

-- A morphism in `CommRingCat` has an underlying ring homomorphism.
example (R S : CommRingCat) (f : R ⟶ S) : R →+* S := f.hom

/-! Note: This requires `open CategoryTheory`! -/

/- If `R` is a commutative ring, `Spec R` is the affine *scheme* whose underlying topological space
is `PrimeSpectrum R`. -/
example (R : CommRingCat) : Scheme := Spec R

end PrimeSpectrum

section Definition

/-! ## Definition of `Scheme` -/

/- Use `F12` to go to definition. -/
#check Scheme

/-!
As you would expect, a `Scheme` is defined as a locally ringed space that is locally isomorphic
to the spectrum of a ring.
-/

-- We can apply a morphism of schemes to an element.
example (X Y : Scheme) (f : X ⟶ Y) (x : X) : Y := f x

-- As before, we can compose morphisms of schemes in the same way as we can compose
-- morphisms of commutative rings:
example (X Y : Scheme) (f : X ⟶ Y) : X ⟶ Y := f ≫ 𝟙 Y

/-
Sections of `𝒪 = 𝒪_X` over an open can be written with the notation `Γ(X, U)`.
-/
example (X : Scheme) (U : X.Opens) : CommRingCat := Γ(X, U)

/- If `U` is contained in `V`, we get a restriction map `𝒪(V) ⟶ 𝒪(U)` -/
example (X : Scheme) (U V : X.Opens) (hUV : U ≤ V) : Γ(X, V) ⟶ Γ(X, U) :=
  X.presheaf.map (homOfLE hUV).op

variable {X Y : Scheme}

/- Given a morphism `f` and an open of `U`, we obtain a morphism `𝒪_Y(U) ⟶ 𝒪_X(f⁻¹(U))`. -/
example (f : X ⟶ Y) (U : Y.Opens) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.app U

/- A variant we often encounter is the composition `𝒪_Y(U) ⟶ 𝒪_X(f⁻¹(U)) ⟶ 𝒪_X(V)` -/
example (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.appLE U V h

/- -/

/-!
One of the reasons we use the bundled approach for `Scheme`s, is the heavy reliance on category
theoretical constructions.
-/

/- The fibre product of schemes is simply the application of the general `pullback` to the
category of `Schemes`. -/
noncomputable example (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) : Scheme :=
  pullback f g

end Definition

noncomputable section

namespace Stalks

/-! ## Stalks, residue fields and fibres -/

/-
To get acquainted with the scheme API, let us consider an example: Let us define
the fibre of a morphism of schemes.
-/

variable {X Y : Scheme} (f : X ⟶ Y)

-- The stalk `𝒪_Y,y` of `𝒪_Y` at the point `y`.
example (y : Y) : CommRingCat := Y.presheaf.stalk y

-- The stalk `𝒪_Y,y` is a local ring.
#synth ∀ y, IsLocalRing (Y.presheaf.stalk y)

-- And we may consider its residue field.
example (y : Y) : Type := IsLocalRing.ResidueField (Y.presheaf.stalk y)

-- The morphism `Spec κ(y) ⟶ Y`.
example (y : Y) : Spec (Y.residueField y) ⟶ Y :=
  Y.fromSpecResidueField y

/-- The fibre of `f` over `y` is, by definition, the fibre product
```
X ×[Y] Spec κ(y) ------> Spec κ(y)
      |                       |
      |                       |
      v                       |
      X --------------------> Y
```
-/
def fiber (y : Y) : Scheme :=
  pullback f (Y.fromSpecResidueField y)

/-- The immersion `X ×[Y] Spec κ(y) ⟶ X`. -/
def fiberι (y : Y) : fiber f y ⟶ X :=
  pullback.fst f (Y.fromSpecResidueField y)

/-- The projection `X ×[Y] Spec κ(y) ⟶ Spec κ(y)`. -/
def fiberToSpecResidueField (y : Y) : fiber f y ⟶ Spec (Y.residueField y) :=
  pullback.snd f (Y.fromSpecResidueField y)

/-!
In `mathlib` these are called `Hom.fiber`, `Hom.fiberι` and `Hom.fiberToSpecResidueField` and we can
for example write `f.fiber`.
-/

end Stalks

section CategoryTheory

/-!
## Category theory
-/

/-
- isomorphisms
- functors
- natural transformations?
-/

end CategoryTheory

section Subschemes

/-! ## Subschemes -/

/-! ### Open subschemes -/

variable {U X Y : Scheme}

-- Given an open subset of `X`, we can naturally regard it as a scheme.
example (U : X.Opens) : Scheme := U
example (U : X.Opens) : (U : Scheme) ⟶ X := U.ι

/-!
Instead of working with `U : X.Opens`, it is often convenient to allow arbitrary
open immersions instead.
-/
example (f : U ⟶ X) [IsOpenImmersion f] : X.Opens := f.opensRange

/-! ### Closed subschemes -/

example (f : Y ⟶ X) [IsClosedImmersion f] : IsClosed (Set.range f) :=
  f.isClosedEmbedding.isClosed_range

/- A closed immersion determines an ideal sheaf. -/
example (f : Y ⟶ X) [IsClosedImmersion f] : X.IdealSheafData := f.ker

/- And conversely, every ideal sheaf determines a closed immersion. -/
example : (MorphismProperty.Over @IsClosedImmersion ⊤ X)ᵒᵖ ≌ X.IdealSheafData :=
  IsClosedImmersion.overEquivIdealSheafData X

end Subschemes

section Properties

/-! ## Properties of morphisms -/

/-! ### Open subschemes -/

/-
- open immersions
- separated
- universally injective
-/

end Properties

section ReductionToAffine

/-! ## Reduction to affine case -/

variable (P : MorphismProperty Scheme)
variable (X : Scheme) (𝒰 : X.OpenCover)

end ReductionToAffine

/-! ## Schemes over a base -/

-- in particular the special case of a scheme over a field

/-! ## Varieties -/
