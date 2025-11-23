import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sets.OpenCover

lemma IsPreirreducible.of_subtype {X : Type*} [TopologicalSpace X] (s : Set X)
    [PreirreducibleSpace s] : IsPreirreducible s := by
  rw [← Subtype.range_coe (s := s), ← Set.image_univ]
  refine PreirreducibleSpace.isPreirreducible_univ.image Subtype.val ?_
  exact continuous_subtype_val.continuousOn

lemma IsIrreducible.of_subtype {X : Type*} [TopologicalSpace X] (s : Set X)
    [IrreducibleSpace s] : IsIrreducible s := by
  exact ⟨.of_subtype, .of_subtype s⟩

lemma IsPreirreducible.of_isOpen {X : Type*} [TopologicalSpace X]
    [PreirreducibleSpace X] (U : Set X) (h : IsOpen U) :
    IsPreirreducible U :=
  .open_subset PreirreducibleSpace.isPreirreducible_univ h U.subset_univ

instance (priority := 100) PreirreducibleSpace.of_isEmpty (X : Type*) [TopologicalSpace X]
    [IsEmpty X] : PreirreducibleSpace X := by
  constructor
  convert isPreirreducible_empty
  exact Set.eq_empty_of_isEmpty Set.univ

lemma isIrreducible_of_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : s ∈ irreducibleComponents X) :
    IsIrreducible s :=
  hs.1

lemma irreducibleComponents_eq_singleton_iff {X : Type*} [TopologicalSpace X] :
    irreducibleComponents X = {Set.univ} ↔ IrreducibleSpace X := by
  refine ⟨fun h ↦ ?_, fun h ↦ irreducibleComponents_eq_singleton⟩
  rw [irreducibleSpace_def]
  apply isIrreducible_of_mem_irreducibleComponents
  simp [h]

lemma irreducibleSpace_iff_nonempty_and_subsingleton {X : Type*} [TopologicalSpace X] :
    IrreducibleSpace X ↔
      Nonempty X ∧ (irreducibleComponents X).Subsingleton := by
  refine ⟨fun hX ↦?_ , fun ⟨hS, hN⟩ ↦ ?_⟩
  · rw [irreducibleComponents_eq_singleton]
    simp only [Set.subsingleton_singleton, and_true]
    infer_instance
  · let x : X := Classical.arbitrary X
    have : irreducibleComponent x = Set.univ := by
      rw [← Set.univ_subset_iff]
      rintro y -
      rw [hN (irreducibleComponent_mem_irreducibleComponents x)
        (irreducibleComponent_mem_irreducibleComponents y)]
      exact mem_irreducibleComponent
    suffices PreirreducibleSpace X by constructor; infer_instance
    constructor
    rw [← this]
    exact isIrreducible_irreducibleComponent.2

lemma preirreducibleSpace_iff_subsingleton_irreducibleComponents {X : Type*} [TopologicalSpace X] :
    PreirreducibleSpace X ↔ (irreducibleComponents X).Subsingleton := by
  obtain (h | hN) := isEmpty_or_nonempty X
  · simp only [PreirreducibleSpace.of_isEmpty, true_iff]
    intros s _ t _
    subsingleton
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : IrreducibleSpace X := ⟨‹_›⟩
      simp [irreducibleComponents_eq_singleton]
    · exact (irreducibleSpace_iff_nonempty_and_subsingleton.mpr ⟨hN, h⟩).1

lemma Function.Surjective.preirreducibleSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hfc : Continuous f) (hf : Function.Surjective f)
    [PreirreducibleSpace X] : PreirreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn

lemma Function.Surjective.irreducibleSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hfc : Continuous f) (hf : Function.Surjective f)
    [IrreducibleSpace X] : IrreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
  toNonempty := Nonempty.map f inferInstance

/-- Irreducibility can be checked on an open cover with pairwise non-empty intersections. -/
theorem IrreducibleSpace.of_openCover {X ι : Type*} [TopologicalSpace X] [hι : Nonempty ι]
    {U : ι → TopologicalSpace.Opens X} (hU : TopologicalSpace.IsOpenCover U)
    (hn : ∀ i j, ((U i).carrier ∩ (U j).carrier).Nonempty)
    (h : ∀ i, IrreducibleSpace ↥(U i)) :
    IrreducibleSpace X := by
  have h' (i : _) : IsIrreducible (U i).carrier :=
    IsIrreducible.of_subtype _
  let i : ι := Classical.choice (α := ι) hι
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier (h' i)
    with ⟨u, hu, hUu⟩
  by_cases huniv : u = Set.univ
  · rw [huniv] at hu
    exact (irreducibleSpace_def _).mpr hu.1
  · have huo : IsOpen uᶜ :=
      IsClosed.isOpen_compl (self := isClosed_of_mem_irreducibleComponents u hu)
    push_neg at huniv
    rw [u.ne_univ_iff_exists_notMem] at huniv
    choose a ha using huniv
    choose j haj using hU.exists_mem a
    rcases Set.inter_nonempty_iff_exists_left.mp
      ((h' j).2 (U i) uᶜ (U i).isOpen huo (hn j i) ⟨a, ⟨haj, ha⟩⟩).right
      with ⟨x, hx₁, hx₂⟩
    exfalso; exact hx₂ <| hUu hx₁
