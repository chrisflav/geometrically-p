/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import GeometricallyP.Algebra.Connected

/-!
# Geometrically connected algebras

In this file we develop the theory of geometrically connected algebras over a field.

## References

- https://stacks.math.columbia.edu/tag/05DV
-/

universe u

open TensorProduct

namespace Algebra

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

/--
A `k`-algebra `R` is geometrically connected if `Spec (AlgebraicClosure k ⊗[k] R)` is
connected. In this case, `Spec (K ⊗[k] R)` is connected for every field extension `K` of `k`
(see `Algebra.GeometricallyConnected.connectedSpace`).
Note: The stacks project definition is the latter condition, which is equivalent to the former by
the above. The reason for choosing this definition is that it does not quantify over types.
-/
@[stacks 037L, mk_iff]
class GeometricallyConnected (k R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  connectedSpace_tensorProduct : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R))

namespace GeometricallyConnected

variable (k : Type u) (R : Type*) [CommRing R] [Field k] [Algebra k R]

lemma iff_connectedSpace_separableClosure :
    GeometricallyConnected k R ↔
      ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) :=
  sorry

/-- If `Spec (K ⊗[k] R)` is connected for every finite separable extension `K` of `k`, then
`R` is geometrically connected over `k`. -/
theorem of_forall_connectedSpace_of_isSeparable
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] R))) :
    Algebra.GeometricallyConnected k R :=
  /- Use `PrimeSpectrum.connectedSpace_of_forall_connectedSpace_of_isSeparable` -/
  sorry

@[stacks 037S "part of the proof of (2) => (1)"]
theorem connectedSpace [GeometricallyConnected k R] (K : Type*) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) := by
  -- use `PrimeSpectrum.connectedSpace_tensorProduct_of_isSepClosed`
  sorry

/-- If `Ω` is a separably closed extension of `k` such that `Spec (Ω ⊗[k] R)` is connected,
`R` is geometrically connected over `k`. -/
theorem of_connectedSpace_of_isSepClosed (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (H : ConnectedSpace (PrimeSpectrum (Ω ⊗[k] R))) :
    Algebra.GeometricallyConnected k R :=
  /-
  use `iff_connectedSpace_separableClosure` and `PrimeSpectrum.connectedSpace_of_isScalarTower`
  -/
  sorry

end GeometricallyConnected

end Algebra
