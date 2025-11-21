import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import GeometricallyP.Mathlib.Topology.Homeomorph.Lemmas
import GeometricallyP.Algebra.Irreducible

universe u

open TensorProduct

namespace Algebra

variable {k K L : Type u} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]

lemma exists_field_isScalarTower : ∃ (M : Type u) (_ : Field M) ( _ : Algebra k M ) ( _ : Algebra K M )
( _ : Algebra L M ), IsScalarTower k K M := by
  obtain ⟨m, mm⟩ := Ideal.exists_maximal (K ⊗[k] L)
  let M := (K ⊗[k] L) ⧸ m
  use M
  use (Ideal.Quotient.field m)
  use inferInstance
  use inferInstance
  let : Algebra L (K ⊗[k] L) :=
    Algebra.TensorProduct.rightAlgebra
  use inferInstance
  infer_instance

end Algebra
