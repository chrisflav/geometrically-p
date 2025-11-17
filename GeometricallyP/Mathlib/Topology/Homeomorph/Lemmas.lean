import Mathlib.Topology.Homeomorph.Lemmas
import GeometricallyP.Mathlib.Topology.Irreducible

lemma IsHomeomorph.irreducibleSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : IsHomeomorph f)
    [IrreducibleSpace X] : IrreducibleSpace Y := by
  have := hf.surjective.preirreducibleSpace _ hf.continuous
  exact ⟨(hf.homeomorph).symm.surjective.nonempty⟩
