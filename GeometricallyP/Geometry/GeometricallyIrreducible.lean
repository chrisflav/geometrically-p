/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Geometry.Basic
import GeometricallyP.Algebra.GeometricallyIrreducible
import GeometricallyP.Mathlib.Topology.Irreducible
import GeometricallyP.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically irreducible schemes over a field

A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
for a field extension `K` of `k` is irreducible.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
is irreducible for a field extension `K` of `k`. -/
abbrev GeometricallyIrreducible {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop :=
  Geometrically (fun X ↦ IrreducibleSpace X) s

instance : ObjectProperty.InheritedFromSource
    (fun (X : Scheme) ↦ IrreducibleSpace X)
    @Surjective := by
  constructor
  intro X Y f hf hX
  exact f.surjective.irreducibleSpace _ f.continuous

instance : ObjectProperty.IsClosedUnderIsomorphisms
      (fun (X : Scheme) ↦ IrreducibleSpace X) :=
  .of_inheritedFromSource _ @Surjective

namespace GeometricallyIrreducible

variable {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))

lemma iff_irreducibleSpace_pullback :
    GeometricallyIrreducible s ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ _)) :=
  Geometrically.iff_of_isClosedUnderIsomorphisms _

/-- The affine scheme `Spec R` is geometrically irreducible over `k` if and only if
the `k`-algebra `R` is geometrically irreducible. -/
-- Note: this is nontrivial, because the definition of `Algebra.GeometricallyIrreducible` is
-- quite different.
lemma iff_spec (R : Type u) [CommRing R] [Algebra k R] :
    GeometricallyIrreducible (Spec (.of R) ↘ Spec (.of k)) ↔
      Algebra.GeometricallyIrreducible k R :=
  -- Timo
  sorry

/-- Every nonempty open subscheme of a geometrically irreducible scheme is geometrically
irreducible. -/
@[stacks 038G "Final statement."]
lemma of_isOpenImmersion (U : Scheme.{u}) (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
    [GeometricallyIrreducible s] :
    GeometricallyIrreducible (i ≫ s) :=
  -- Alireza
  sorry

/-- If `X` is geometrically irreducible over `k` and `U` is an affine open, `Γ(X, U)` is
geometrically irreducible over `k`. -/
@[stacks 038G "(1) => (2)"]
lemma geometricallyIrreducible_of_isAffineOpen [GeometricallyIrreducible s]
    (U : X.Opens) (hU : IsAffineOpen U) (hU : U.carrier.Nonempty) :
    letI : Algebra k Γ(X, U) := algebraOfHomSpec s U
    Algebra.GeometricallyIrreducible k Γ(X, U) :=
  -- use `of_isOpenImmersion` to reduce to the affine case
  -- Cheni
  sorry

/-- If `X` is covered by geometrically irreducible open subschemes with pairwise
non-empty intersections, `X` is geometrically irreducible. -/
@[stacks 038G "(4) => (1)"]
lemma of_openCover (𝒰 : X.OpenCover) [Nonempty 𝒰.I₀]
    (hn : ∀ i j, Nonempty ↑(pullback (𝒰.f i) (𝒰.f j)))
    (h : ∀ i, GeometricallyIrreducible (𝒰.f i ≫ s)) :
    GeometricallyIrreducible s :=
  -- Bryan
  sorry

/-- Being geometrically irreducible can be checked on finite extensions. -/
lemma of_finite
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))) :
    GeometricallyIrreducible s :=
  sorry



/-- Being geometrically irreducible can be checked on a separably closed field. -/
lemma of_isSepClosed (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    [IrreducibleSpace ↑(pullback s (Spec (.of Ω) ↘ Spec (.of k)))] :
    GeometricallyIrreducible s := by


      have : Nonempty X := by
        apply Nonempty.intro
        let h : IrreducibleSpace _ := by assumption
        apply  (pullback.fst s  (Spec (.of Ω) ↘ Spec (.of k))) ( Classical.choice h.toNonempty)

      have : Nonempty X.affineCover.I₀ := by
        apply Scheme.Cover.nonempty_of_nonempty X.affineCover

      have : IrreducibleSpace X := by
        let f := (pullback.fst s  (Spec (.of Ω) ↘ Spec (.of k))).base.hom'.toFun
        apply Function.Surjective.irreducibleSpace f

        · apply ContinuousMap.continuous_toFun
        · --suffices Epi (pullback.fst s  (Spec (.of Ω) ↘ Spec (.of k))) by sorry
          --apply CategoryTheory.Abelian.epi_pullback_of_epi_g

          #check Spec.map_surjective
          sorry

      apply of_openCover s X.affineCover
      · intro i j
        have : Nonempty <| X.affineCover.X i := by
          apply Nonempty.intro


          sorry
        have : Nonempty <| X.affineCover.X j := by sorry

        let xi := Scheme.Cover.nonempty_of_nonempty X.affineCover
        -- the intersection of two nonempty opens of X wich is irreducible

        sorry
      · intro i
        obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineCover.f i ≫ s)
        rw [← hφ]
        let : Algebra k _ := φ.hom.toAlgebra
        apply  (@iff_spec _ _ _ _ this).2
        apply Algebra.GeometricallyIrreducible.of_irreducibleSpace_of_isSepClosed k _ Ω


        have : IrreducibleSpace (pullback (Spec.map φ) (Spec (CommRingCat.of Ω) ↘ Spec (CommRingCat.of k))).carrier.carrier := by
          have : GeometricallyIrreducible <| Spec.map φ := by
            rw [hφ]

            #check IsPreirreducible.open_subset
            --apply AlgebraicGeometry.GeometricallyIrreducible.of_isOpenImmersion
            sorry

          #check AlgebraicGeometry.GeometricallyIrreducible.of_isOpenImmersion
          sorry


        refine @IsHomeomorph.irreducibleSpace (pullback (Spec.map φ) (Spec (CommRingCat.of Ω) ↘ Spec (CommRingCat.of k))).carrier.carrier _ _ _ _ (Homeomorph.isHomeomorph ?_) _


        --let  : PrimeSpectrum Ω ≅ (Spec (CommRingCat.of (TensorProduct k Ω _))) := by
          --exact Iso.refl (PrimeSpectrum Ω)
          --sorry
        --apply (_).trans _
        --apply Homeomorph.trans
        --apply Scheme.homeOfIso
        --#check Scheme.homeoOfIso
        #check PrimeSpectrum (TensorProduct k Ω _)
        #check (AlgebraicGeometry.pullbackSpecIso k _ Ω)

        refine (Scheme.homeoOfIso <| (AlgebraicGeometry.pullbackSpecIso k _ Ω)).trans ?_





        #check (Scheme.homeoOfIso <| (AlgebraicGeometry.pullbackSpecIso k Ω _).trans <| Iso.refl <| (Spec (CommRingCat.of (TensorProduct k Ω _))))


        sorry

/-- `X` is geometrically irreducible over `s` if and only if `X_K` is irreducible
for `K` a separable closure of `k`. -/
theorem iff_irreducibleSpace_separableClosure :
    GeometricallyIrreducible s ↔
      IrreducibleSpace ↑(pullback s (Spec (.of <| SeparableClosure k) ↘ Spec (.of k))) :=
  sorry

/-- If `X` is geometrically irreducible over `k` and `Y` is any `k`-scheme, then
`X ×[k] Y ⟶ Y` induces an order preserving bijection between irreducible components. -/
@[stacks 0364]
def irreducibleComponentsOrderIsoPullback [GeometricallyIrreducible s] {Y : Scheme.{u}}
    (t : Y ⟶ Spec (.of k)) :
    irreducibleComponents Y ≃o irreducibleComponents ↑(pullback s t) :=
  irreducibleComponentsEquivOfIsPreirreducibleFiber _ (pullback.snd s t).continuous
    -- use `AlgebraicGeometry.universallyOpen_Spec_field`
    sorry
    sorry
    sorry

end GeometricallyIrreducible

end AlgebraicGeometry
