import Mathlib.FieldTheory.PurelyInseparable.Basic

lemma IsPurelyInseparable.of_surjective {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (h : Function.Surjective (algebraMap F E)) :
    IsPurelyInseparable F E where
  isIntegral := Algebra.isIntegral_of_surjective h
  inseparable' _ _ := h _

/-- If `k` is a field, `K` is a separable closure of `k` and `L` is an algebraic closure of `k`,
then there exists an embedding of `K` into `L` and `L` is a purely inseparable extension of `K`. -/
lemma exists_algebra_isPurelyInseparable_of_isSepClosure_of_isAlgClosure (k : Type*) [Field k]
    (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosure k L] :
    ∃ (_ : Algebra K L) (_ : IsScalarTower k K L), IsPurelyInseparable K L := by
  let eK := IsSepClosure.equiv k (SeparableClosure k) K
  let _ : Algebra K (SeparableClosure k) := eK.symm.toAlgHom.toAlgebra
  let eL := IsAlgClosure.equiv k (AlgebraicClosure k) L
  have : IsPurelyInseparable K (SeparableClosure k) := .of_surjective eK.symm.surjective
  let _ : Algebra (AlgebraicClosure k) L := eL.toAlgHom.toAlgebra
  have : IsPurelyInseparable (SeparableClosure k) (AlgebraicClosure k) := inferInstance
  have : IsPurelyInseparable (AlgebraicClosure k) L := .of_surjective eL.surjective
  let _ : Algebra K L :=
    (eL.toAlgHom.comp <| (IsScalarTower.toAlgHom k _ _).comp eK.symm.toAlgHom).toAlgebra
  have : IsScalarTower K (SeparableClosure k) L := .of_algebraMap_eq' rfl
  have : IsPurelyInseparable (SeparableClosure k) L :=
    IsPurelyInseparable.trans (SeparableClosure k) (AlgebraicClosure k) L
  have : IsPurelyInseparable K L :=
    IsPurelyInseparable.trans K (SeparableClosure k) L
  use inferInstance, inferInstance
