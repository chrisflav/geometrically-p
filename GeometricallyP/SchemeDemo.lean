/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.DepRewrite

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

-- As before, we can compose morphisms of schemes in the same way as we can compose
-- morphisms of commutative rings:
example (X Y : Scheme) (f : X ⟶ Y) : X ⟶ Y := f ≫ 𝟙 Y

-- We can apply a morphism of schemes to an element.
example (X Y : Scheme) (f : X ⟶ Y) (x : X) : Y := f x

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

/- Restriction of a morphism of schemes along an open of the target. -/
noncomputable example (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U : Scheme) ⟶ U :=
  f ∣_ U

/-!
One of the reasons we use the bundled approach for `Scheme`s, is the heavy reliance on category
theoretical constructions.
-/

/- The fibre product of schemes is simply the application of the general `pullback` to the
category of `Schemes`. -/
noncomputable example (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) : Scheme :=
  pullback f g

/-
Note: `f ∣_ U` is *not* the projection `X ×[Y] U ⟶ U`, but sometimes
using `X ×[Y] U` is convenient.
-/

/-! ### Affine schemes -/

/-- `Spec R` is affine. -/
example (R : CommRingCat) : IsAffine (Spec R) :=
  inferInstance

/-- If `X` is an affine scheme, it is isomorphic to `Spec Γ(X, ⊤)`. -/
noncomputable example (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  X.isoSpec

/-- Some proofs of being affine can be found by instance synthesis. -/
example {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g) :=
  inferInstance

end Definition

section CategoriesAndFunctors

/-! ## Categories and functors

We have already seen examples of categories, but not yet examples of functors.
-/

/- The `Spec` functor `CommRingCatᵒᵖ ⥤ Scheme`. -/
#check AlgebraicGeometry.Scheme.Spec

example (R : CommRingCat) : Scheme.Spec.obj (Opposite.op R) = Spec R := rfl

/- In this language, the `Γ`-`Spec`-adjunction is phrased as: -/
noncomputable
example : Scheme.Γ.rightOp ⊣ Scheme.Spec := ΓSpec.adjunction

end CategoriesAndFunctors

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

/-- We rely on typeclass inference to automatically fill proofs using stability properties. -/
example {V : Scheme} (f : U ⟶ V) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) :=
  inferInstance

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

/-!
## Properties of morphisms

Mathlib knows many properties of morphisms. Browsing the `AlgebraicGeometry/Morphisms` folder
gives an overview. The properties are defined as type classes.
-/

example {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [IsProper f] :
    IsSeparated (pullback.snd f g) :=
  inferInstance

/-- Properties of morphisms obtained from typeclass instances, usually have handy shortcuts. -/
example {X Y : Scheme} (f : X ⟶ Y) [UniversallyInjective f] : Function.Injective f :=
  f.injective

/-! ### Morphism properties -/

/- A `MorphismProperty` is a property of morphisms. -/
variable (P : MorphismProperty Scheme)

/- There exist meta properties for morphism properties, for example
being stable under composition, base change, etc. -/
#check MorphismProperty.IsStableUnderComposition
#check MorphismProperty.IsStableUnderBaseChange
#check MorphismProperty.RespectsIso

/- But also some more technical ones: -/
#check MorphismProperty.HasOfPostcompProperty

example : MorphismProperty.HasOfPostcompProperty
    @IsEtale (@LocallyOfFiniteType ⊓ @FormallyUnramified) :=
  inferInstance

/- There are analogues for these in the language of commutative rings: -/
#check RingHom.StableUnderComposition
#check RingHom.IsStableUnderBaseChange
#check RingHom.RespectsIso

/-
Besides properties of properties, we also use abstract constructions of properties.
-/
#check MorphismProperty.universally
#check MorphismProperty.diagonal
#check topologically

end Properties

section ReductionToAffine

/-! ## Reduction to affine case -/

/-!
### (Open) covers

Any reduction to a local problem starts with an (affine) open cover. These
can be pulled back along morphisms, refined, etc.
-/

variable (X : Scheme)

#check Scheme.OpenCover

/-- Pullback an open cover along an arbitrary morphism. -/
example {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover) : X.OpenCover :=
  𝒰.pullback₁ f

/-- Refine every component of an open cover by an open cover. -/
example {X : Scheme} (𝒰 : X.OpenCover) (𝒱 : ∀ i, (𝒰.X i).OpenCover) : X.OpenCover :=
  𝒰.bind 𝒱

/-- A choice of affine cover of `X`. -/
example (X : Scheme) : X.OpenCover :=
  X.affineCover

/-- The components of `X.affineCover` are *definitionally equal* to some `Spec R` for
`R : CommRingCat`. -/
example (X : Scheme) (i : X.affineCover.I₀) :
    ∃ R, X.affineCover.X i = Spec R :=
  ⟨_, rfl⟩

/-! ### Properties of properties -/

variable (P : MorphismProperty Scheme)

#check IsZariskiLocalAtTarget
#check IsZariskiLocalAtSource

#check IsZariskiLocalAtTarget.iff_of_openCover
#check IsZariskiLocalAtSource.iff_of_openCover

section

variable {X Y : Scheme.{u}}

/-! ### Example: Flat morphisms -/

@[mk_iff]
class Flat (f : X ⟶ Y) : Prop where
  flat_of_isAffineOpen :
    ∀ (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U),
      IsAffineOpen U → IsAffineOpen V → (f.appLE U V e).hom.Flat

instance : HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff, affineLocally_iff_affineOpens_le]
    simp only [Scheme.affineOpens, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall]
    grind

example : IsZariskiLocalAtTarget @Flat :=
  inferInstance

-- this should be in mathlib
/-- If `P = X ×[Z] Y` and `Y ⟶ Z` is an open immersion, then the stalk map
of `P ⟶ Y` at some `x : P` is isomorphic to the stalk map of `X ⟶ Z` at the image of `x`. -/
def stalkMapIsoOfIsPullback {X Y Z P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} (g : Y ⟶ Z) (h : IsPullback fst snd f g) [IsOpenImmersion g] (x : P) :
    Arrow.mk (snd.stalkMap x) ≅ Arrow.mk (f.stalkMap <| fst x) :=
  haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Iso.symm <| Arrow.isoMk' _ _
    ((TopCat.Presheaf.stalkCongr _ <| .of_eq (congr($(h.1.1).base x))) ≪≫
      (asIso (g.stalkMap <| (snd x))))
    (asIso (fst.stalkMap <| x)) <| TopCat.Presheaf.stalk_hom_ext _ fun V hxV ↦ by
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply, Iso.trans_hom,
        TopCat.Presheaf.stalkCongr_hom, asIso_hom, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap_assoc,
        Scheme.Hom.germ_stalkMap]
      simp only [← Scheme.Hom.comp_app_assoc, ← Scheme.Hom.comp_preimage]
      rw! [h.1.1]

theorem flat_of_flat_stalkMap (f : X ⟶ Y) (H : ∀ x, (f.stalkMap x).hom.Flat) :
    Flat f := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) Y.affineCover]
    intro i
    refine this _ ?_ ⟨_, rfl⟩
    intro x
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff]
    · apply H
      dsimp at x
      exact pullback.fst f _ x
    · dsimp [Scheme.Cover.pullbackHom]
      apply stalkMapIsoOfIsPullback (Y.affineCover.f i)
      apply IsPullback.of_hasPullback
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X f
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) X.affineCover]
    intro i
    refine this _ ?_ ⟨_, rfl⟩
    intro x
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    apply H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  apply RingHom.Flat.ofLocalizationPrime
  intro P hP
  specialize H ⟨P, hP⟩
  rwa [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ _)] at H

end

end ReductionToAffine

/-!
## Schemes over a base

We have multiple ways of talking about a scheme over a base.
-/

/- Version 1: A scheme over `Y` is simply a morphism `X ⟶ Y`. -/
variable {X S : Scheme} (f : X ⟶ S)

/- Version 2: There exists a typeclass `Scheme.Over` that bundles a preferred choice of morphism. -/
variable {X S : Scheme} [X.Over S]
example : X ⟶ S := X ↘ S

/- Version 3: As a last resort, we can also use the over category. -/
variable {S : Scheme} (X : Over S)
example : X.left ⟶ S := X.hom

/- In particular, we can take the base change. -/

/- In version 1: -/
variable {X S : Scheme} (f : X ⟶ S)
example {T : Scheme} (g : T ⟶ S) : pullback f g ⟶ T := pullback.snd _ _

/- In version 3 -/
variable {S : Scheme} (X : Over S)
example {T : Scheme} (g : T ⟶ S) : ((Over.pullback g).obj X).left ⟶ T :=
  ((Over.pullback g).obj X).hom

/- In particular, we can do the above in the special case where `S = Spec k` for some field `k`. -/

/-! ## Varieties

There is no `AlgebraicGeometry.Variety` and there will most likely never be such a definition.
-/

/-- But you are free to create your local definition of variety (downstream of mathlib). -/
class Variety {X : Scheme} {k : Type} [Field k] (s : X ⟶ Spec (.of k)) : Prop
    extends IsSeparated s, LocallyOfFiniteType s


/-! ## More topics -/

/- Function field of a scheme. -/
#check Scheme.functionField

/- (Locally) Noetherian schemes. -/
#check IsLocallyNoetherian
#check IsNoetherian

/- Projective spectrum of a graded ring. -/
variable {σ : Type} {A : Type}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
#check Proj 𝒜
