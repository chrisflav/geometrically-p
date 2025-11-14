import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.IsMultiplicative @Surjective where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

end AlgebraicGeometry
