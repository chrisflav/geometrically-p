import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

universe u

namespace AlgebraicGeometry

/-- If `k` is a field, any morphism `X ⟶ Spec k` is universally open. -/
@[stacks 0383]
instance universallyOpen_Spec_field {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) :
    UniversallyOpen f :=
  sorry

end AlgebraicGeometry
