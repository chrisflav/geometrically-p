import Mathlib.Topology.Irreducible

lemma IsPreirreducible.of_isOpen {X : Type*} [TopologicalSpace X]
    [PreirreducibleSpace X] (U : Set X) (h : IsOpen U) :
    IsPreirreducible U :=
  .open_subset PreirreducibleSpace.isPreirreducible_univ h U.subset_univ
