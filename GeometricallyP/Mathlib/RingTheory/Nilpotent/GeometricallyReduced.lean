import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

universe u

open TensorProduct

namespace Algebra.IsGeometricallyReduced

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- If `R` is geometrically reduced over `k` and `S` is any reduced `k`-algebra,
then `R ⊗[k] S` is reduced. -/
@[stacks 05DS]
lemma isReduced_tensorProduct [IsGeometricallyReduced k R] {S : Type*} [CommRing S] [Algebra k S] :
    IsReduced (S ⊗[k] R) :=
  -- leave this as is, this is hard
  sorry

end Algebra.IsGeometricallyReduced
