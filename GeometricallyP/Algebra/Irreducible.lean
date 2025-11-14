/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

open TensorProduct

namespace Algebra

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- A `k`-algebra `R` is geometrically irreducible if `Spec (AlgebraicClosure k ⊗[k] R)` is
irreducible. In this case, `Spec (K ⊗[k] R)` is irreducible for every field extension `K` of `k`
(see `Algebra.GeometricallyIrreducible.irreducibleSpace`). -/
class GeometricallyIrreducible (k R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  irreducibleSpace_tensorProduct : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R))

namespace GeometricallyIrreducible

variable (k R : Type*) [CommRing R] [Field k] [Algebra k R]

@[stacks 00I7 "For algebraically closed fields."]
lemma PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed [IsAlgClosed k] {S : Type*}
    [CommRing S] [Algebra k S] (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) : IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) :=
  sorry

/-- If `Ω` is a separably closed extension of `k` such that `Spec (Ω ⊗[k] R)` is irreducible,
`R` is geometrically irreducible over `k`. -/
@[stacks 037K "(4) => (1)"]
theorem of_irreducibleSpace_of_isSepClosed (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (H : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R :=
  sorry

/-- If `R` is geometrically irreducible over `k`, for every field extension `K` of `k`, the
prime spectrum `Spec (K ⊗[k] R)` is irreducible. -/
@[stacks 037K "(4) => (1)"]
theorem irreducibleSpace (K : Type*) [Field K] [Algebra k K]
    [Algebra.GeometricallyIrreducible k R] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) :=
  -- uses `PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed`
  sorry

/-- If `K` is geometrically irreducible over `k` and `R` is geometrically irreducible over `K`,
then `R` is geometrically irreducible over `k`. -/
@[stacks 0G30]
lemma trans (K : Type*) [Field K] [Algebra k K] [Algebra K R] [IsScalarTower k K R]
    [GeometricallyIrreducible k K] [GeometricallyIrreducible K R] :
    GeometricallyIrreducible k R :=
  sorry

/-- Let `K` over k` be a field extension. Then `K` is geometrically irreducible over `k`
if and only if every `k`-separable, algebraic element `x : K` is contained in `k`. -/
@[stacks 0G33]
theorem iff_of_forall_isSeparable_mem (K : Type*) [Field K] [Algebra k K] :
    GeometricallyIrreducible k K ↔
      ∀ x : K, IsSeparable k x → x ∈ Set.range (algebraMap k K) :=
  sorry

end GeometricallyIrreducible

end Algebra
