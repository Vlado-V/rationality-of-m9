module

public import M9StacksIntegration.ProjectivePrefixDimensionBounds
public import M9StacksIntegration.SerreCommonPointIntegral

/-!
# Projective component geometry and actual integrality

This is the genuine component step used after the actual Cartier-dimension
theorem: every component of the prefix meets the remaining linear space in
dimension one, hence contains the entire actual irreducible final curve.
An actual regular point on that curve and S1 then force actual integrality.
The linear-equation intersection inclusion is a separate producer obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace M9Native.ProjectiveCurveComponentIntegral

private theorem image_dimension {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : Topology.IsEmbedding f) (S : Set A) :
    topologicalKrullDim (f '' S) = topologicalKrullDim S := by
  let g : S → B := fun x => f x.1
  have hg : Topology.IsEmbedding g := hf.comp Topology.IsEmbedding.subtypeVal
  have hr : Set.range g = f '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact (hg.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm

theorem integral_of_component_dimensions_and_tail_intersection
    (K : Type u) [Field K] (i : ℕ) (hi : i ≤ 5)
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (hS : HasPropertySk Y 1)
    (j : Y ⟶ projectiveSpaceOverRing 13 (.of K)) [IsClosedImmersion j]
    (C : Scheme.{u}) [IsIntegral C] (c : C ⟶ Y) [IsClosedImmersion c]
    (hCdim : topologicalKrullDim C = (1 : WithBot ℕ∞))
    (z : C) (hz : IsRegularLocalRing (Y.presheaf.stalk (c z)))
    (T : Set (projectiveSpaceOverRing 13 (.of K))) (hT : IsClosed T) (hTne : T.Nonempty)
    (hTdim : topologicalKrullDim T = ((8 + i : ℕ) : WithBot ℕ∞))
    (hcomponents : ∀ W ∈ irreducibleComponents Y,
      topologicalKrullDim W = ((6 - i : ℕ) : WithBot ℕ∞))
    (hinter : Set.range j ∩ T ⊆ Set.range (c ≫ j)) : IsIntegral Y := by
  apply SerreCommonPointIntegral.integral_of_s1_of_components_common_regular_point Y hS (c z) hz
  intro W hW
  let Z : Set (projectiveSpaceOverRing 13 (.of K)) := j '' W
  let CI : Set (projectiveSpaceOverRing 13 (.of K)) := Set.range (c ≫ j)
  have hZc : IsClosed Z := j.isClosedEmbedding.isClosedMap W
    (isClosed_of_mem_irreducibleComponents W hW)
  have hZn : Z.Nonempty := hW.1.nonempty.image j
  have hZd : topologicalKrullDim Z = ((6 - i : ℕ) : WithBot ℕ∞) :=
    (image_dimension j.isClosedEmbedding.isEmbedding W).trans (hcomponents W hW)
  have hCirr : IsIrreducible CI := by
    simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C).image
      (c ≫ j) (c ≫ j).continuous.continuousOn
  have hCd : topologicalKrullDim CI = (1 : WithBot ℕ∞) := by
    have h := image_dimension (c ≫ j).isClosedEmbedding.isEmbedding Set.univ
    rw [Set.image_univ] at h
    exact h.trans ((IsHomeomorph.topologicalKrullDim_eq
      (fun a : (Set.univ : Set C) => a.1)
      (Homeomorph.Set.univ C).isHomeomorph).trans hCdim)
  have hsub : Z ∩ T ⊆ CI := by
    rintro _ ⟨⟨w, _, rfl⟩, hwT⟩
    exact hinter ⟨⟨w, rfl⟩, hwT⟩
  have hd := (ProjectivePrefixDimensionBounds.dimension_squeeze K i (6 - i) (8 + i) hi
    Z T CI hZc hT hZn hTne hZd hTdim le_rfl le_rfl hCd hsub).2.2.2
  have hsub' : Z ∩ T ⊆ CI ∩ Z := fun x hx => ⟨hsub hx, hx.1⟩
  have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(CI ∩ Z) := by
    rw [← hd]
    exact (Topology.IsEmbedding.inclusion hsub').isInducing.topologicalKrullDim_le
  have hCZ : CI ⊆ Z :=
    CurveContainingComponents.curve_subset_of_one_le_dimension_inter hCirr hZc hCd hone
  obtain ⟨w, hw, he⟩ := hCZ (show (c ≫ j) z ∈ CI from ⟨z, rfl⟩)
  have hwe : w = c z := j.isClosedEmbedding.injective (by
    simpa only [Scheme.Hom.comp_apply] using he)
  simpa only [hwe] using hw

end M9Native.ProjectiveCurveComponentIntegral
