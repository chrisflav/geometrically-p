/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import GeometricallyP.Geometry.Basic
import GeometricallyP.Algebra.GeometricallyIrreducible
import GeometricallyP.Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically irreducible schemes over a field

A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
for a field extension `K` of `k` is irreducible.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Every morphism `X ⟶ Spec (.of R)` induces an `R`-algebra structure on
`Γ(X, U)` for every `U`. -/
noncomputable def algebraOfHomSpec {R : Type u} [CommRing R] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((s.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso <| .of R).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

/-- A scheme `X` over a field `k` is geometrically irreducible if any base change `X_K`
is irreducible for a field extension `K` of `k`. -/
abbrev GeometricallyIrreducible {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) : Prop :=
  Geometrically (fun X ↦ IrreducibleSpace X) s

namespace GeometricallyIrreducible

variable {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))

/-- The affine scheme `Spec R` is geometrically irreducible over `k` if and only if
the `k`-algebra `R` is geometrically irreducible. -/
-- Note: this is nontrivial, because the definition of `Algebra.GeometricallyIrreducible` is
-- quite different.
lemma iff_spec (R : Type u) [CommRing R] [Algebra k R] :
    GeometricallyIrreducible (Spec (.of R) ↘ Spec (.of k)) ↔ Algebra.GeometricallyIrreducible k R :=
  sorry

/-- Every nonempty open subscheme of a geometrically irreducible scheme is geometrically
irreducible. -/
@[stacks 038G "Final statement."]
lemma of_isOpenImmersion (U : Scheme.{u}) (i : U ⟶ X) [IsOpenImmersion i] [Nonempty U]
    [GeometricallyIrreducible s] :
    GeometricallyIrreducible (i ≫ s) :=
  sorry

/-- If `X` is geometrically irreducible over `k` and `U` is an affine open, `Γ(X, U)` is
geometrically irreducible over `k`. -/
@[stacks 038G "(1) => (2)"]
lemma geometricallyIrreducible_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    (hU : U.carrier.Nonempty) :
    letI : Algebra k Γ(X, U) := algebraOfHomSpec s U
    Algebra.GeometricallyIrreducible k Γ(X, U) :=
  -- use `of_isOpenImmersion` to reduce to the affine case
  sorry

/-- If `X` is covered by geometrically irreducible open subschemes with pairwise
non-empty intersections, `X` is geometrically irreducible. -/
@[stacks 038G "(4) => (1)"]
lemma of_openCover (𝒰 : X.OpenCover) [Nonempty 𝒰.I₀]
    (hn : ∀ i j, Nonempty ↑(pullback (𝒰.f i) (𝒰.f j)))
    (h : ∀ i, GeometricallyIrreducible (𝒰.f i ≫ s)) :
    GeometricallyIrreducible s :=
  sorry

/-- Being geometrically irreducible can be checked on finite extensions. -/
lemma of_finite
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))) :
    GeometricallyIrreducible s :=
  sorry

/-- Being geometrically irreducible can be checked on a separable closure. -/
lemma of_isSepClosure (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    [IrreducibleSpace ↑(pullback s (Spec (.of K) ↘ Spec (.of k)))] :
    GeometricallyIrreducible s :=
  sorry

/-- `X` is geometrically irreducible over `s` if and only if `X_K` is irreducible
for `K` a separable closure of `k`. -/
theorem iff_irreducibleSpace_separableClosure :
    GeometricallyIrreducible s ↔
      IrreducibleSpace ↑(pullback s (Spec (.of <| SeparableClosure k) ↘ Spec (.of k))) :=
  sorry

end GeometricallyIrreducible

end AlgebraicGeometry
