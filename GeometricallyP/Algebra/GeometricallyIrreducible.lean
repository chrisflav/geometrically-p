/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import GeometricallyP.Mathlib.Topology.Homeomorph.Lemmas
import GeometricallyP.Algebra.Irreducible

/-!
# Geometrically irreducible algebras

In this file we develop the theory of geometrically irreducible algebras over a field.

## References

- https://stacks.math.columbia.edu/tag/00I2
-/

universe u

open TensorProduct

namespace Algebra

variable {k : Type u} {R : Type*} [Field k] [CommRing R] [Algebra k R]

/--
A `k`-algebra `R` is geometrically irreducible if `Spec (AlgebraicClosure k ⊗[k] R)` is
irreducible. In this case, `Spec (K ⊗[k] R)` is irreducible for every field extension `K` of `k`
(see `Algebra.GeometricallyIrreducible.irreducibleSpace`).
Note: The stacks project definition is the latter condition, which is equivalent to the former by
the above. The reason for choosing this definition is that it does not quantify over types.
-/
@[stacks 037L, mk_iff]
class GeometricallyIrreducible (k R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  irreducibleSpace_tensorProduct :
    IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R))

namespace GeometricallyIrreducible

variable (k : Type u) (R : Type*) [CommRing R] [Field k] [Algebra k R]

@[stacks 037K "(3) <=> (4)"]
lemma iff_irreducibleSpace_separableClosure :
    GeometricallyIrreducible k R ↔
      IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) := by
  rw [geometricallyIrreducible_iff]
  exact (PrimeSpectrum.irreducibleSpace_iff_of_isAlgClosure_of_isSepClosure _ _ _ _).symm

/-- If `Spec (K ⊗[k] R)` is irreducible for every finite separable extension `K` of `k`, then
`R` is geometrically irreducible over `k`. -/
@[stacks 037K "(2) => (3) => (4)"]
theorem of_forall_irreducibleSpace_of_isSeparable
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [Algebra.IsSeparable k K],
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R := by
  /-
  uses `PrimeSpectrum.irreducibleSpace_of_isSeparable` and `iff_irreducibleSpace_separableClosure`
  -/
  rw [iff_irreducibleSpace_separableClosure]
  exact PrimeSpectrum.irreducibleSpace_of_isSeparable H (SeparableClosure k)

/-- If `R` is geometrically irreducible over `k`, for every field extension `K` of `k`, the
prime spectrum `Spec (K ⊗[k] R)` is irreducible. -/
@[stacks 037K "(4) => (1)"]
theorem irreducibleSpace [Algebra.GeometricallyIrreducible k R]
    (K : Type*) [Field K] [Algebra k K] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) := by
  let : Algebra (AlgebraicClosure k) (K ⊗[k] AlgebraicClosure k) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra K (K ⊗[k] AlgebraicClosure k) :=
    Algebra.TensorProduct.leftAlgebra

  obtain ⟨m, mm⟩ := Ideal.exists_maximal (K ⊗[k] AlgebraicClosure k)
  let F :=  (K ⊗[k] AlgebraicClosure k) ⧸ m
  let : Field F := Ideal.Quotient.field m
  let : Algebra (K ⊗[k] R) (F ⊗[k] R) := RingHom.toAlgebra <| AlgHom.toRingHom <|
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K F) (AlgHom.id k R)
  let hR : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R)) := by
    rw [← geometricallyIrreducible_iff]
    infer_instance
  let hF : IrreducibleSpace (PrimeSpectrum F) := inferInstance
  let : IrreducibleSpace (PrimeSpectrum
    (F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R))) :=
      PrimeSpectrum.irreducibleSpace_tensorProduct_of_isAlgClosed (k:=AlgebraicClosure k) hF hR
  let homeo : PrimeSpectrum (F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R)) ≃ₜ PrimeSpectrum (F ⊗[k] R) :=
    PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) (AlgebraicClosure k) F R)
  have : IrreducibleSpace (PrimeSpectrum (F ⊗[k] R)) := IsHomeomorph.irreducibleSpace homeo.toFun (Homeomorph.isHomeomorph homeo)
  exact PrimeSpectrum.irreducibleSpace_of_isScalarTower K F

/-- If `Ω` is a separably closed extension of `k` such that `Spec (Ω ⊗[k] R)` is irreducible,
`R` is geometrically irreducible over `k`. -/
theorem of_irreducibleSpace_of_isSepClosed (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (H : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] R))) :
    Algebra.GeometricallyIrreducible k R := by
  /-
  use `iff_irreducibleSpace_separableClosure` and `PrimeSpectrum.irreducibleSpace_of_isScalarTower`
  -/
  -- Alireza
  sorry

/-- If `K` is geometrically irreducible over `k` and `R` is geometrically irreducible over `K`,
then `R` is geometrically irreducible over `k`. -/
@[stacks 0G30]
lemma trans (K : Type*) [Field K] [Algebra k K] [Algebra K R] [IsScalarTower k K R]
    [GeometricallyIrreducible k K] [GeometricallyIrreducible K R] :
    GeometricallyIrreducible k R :=
  -- Yannis
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
