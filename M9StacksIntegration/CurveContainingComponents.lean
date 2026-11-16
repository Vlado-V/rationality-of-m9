module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.Topology.Dimension.MaximalPointDrop

/-!
# The component-containment step for transverse projective curves

A closed set meeting an irreducible curve in dimension at least one contains
the whole curve. If every irreducible component of an actual scheme contains
one point with domain local ring, the actual scheme is irreducible. The latter
uses the genuine spectrum of that local ring, whose image is precisely the
generizations of the chosen point.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace

universe u
namespace M9Native.CurveContainingComponents

/-- The positive-dimensional intersection with an irreducible curve cannot
be a proper closed subset of the curve. -/
theorem curve_subset_of_one_le_dimension_inter
    {T : Type u} [TopologicalSpace T] {C Z : Set T}
    (hC : IsIrreducible C) (hZ : IsClosed Z)
    (hCdim : topologicalKrullDim C = (1 : WithBot ℕ∞))
    (hinter : (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(C ∩ Z)) : C ⊆ Z := by
  by_contra hn
  have hne : (C ∩ Z).Nonempty := by
    by_contra he
    have hempty : IsEmpty ↥(C ∩ Z) := ⟨fun x => he ⟨x.1, x.2⟩⟩
    have hb := (topologicalKrullDim_eq_bot_iff_isEmpty ↥(C ∩ Z)).mpr hempty
    rw [hb] at hinter
    simp at hinter
  obtain ⟨_, hbound⟩ :=
    topologicalKrullDim_inter_le_pred_of_not_subset hC hZ hn hne hCdim.le
  norm_num at hbound
  exact (show ¬ ((1 : WithBot ℕ∞) ≤ 0) by norm_num) (hinter.trans hbound)

/-- All components through a point with domain stalk must form one
irreducible scheme. No irreducibility or reducedness of the scheme is given. -/
theorem irreducibleSpace_of_domain_stalk_of_components
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)]
    (hx : ∀ Z ∈ irreducibleComponents X, x ∈ Z) : IrreducibleSpace X := by
  let f := X.fromSpecStalk x
  have hR : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        f f.continuous.continuousOn
  have hd : closure (Set.range f) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    let Z := irreducibleComponent y
    have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents y
    obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    have hηrange : η ∈ Set.range f := by
      dsimp only [f]
      rw [Scheme.range_fromSpecStalk]
      exact hη.specializes (hx Z hZ)
    have hZsub : Z ⊆ closure (Set.range f) := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (subset_closure hηrange)) isClosed_closure
    exact hZsub mem_irreducibleComponent
  apply (irreducibleSpace_def X).mpr
  change IsIrreducible (Set.univ : Set X)
  rw [← hd]
  exact hR.closure

end M9Native.CurveContainingComponents
