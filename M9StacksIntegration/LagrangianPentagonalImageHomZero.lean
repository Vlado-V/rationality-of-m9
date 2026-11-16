module

public import M9StacksIntegration.LagrangianImageKernelVector
public import M9StacksIntegration.LineSectionVectorZeroDegree
public import M9StacksIntegration.CurveRankTwoSectionKernel
public import M9StacksIntegration.LagrangianSectionZeroBoundApplications

/-! The original rank-two subsystem has no nonzero map to a pencil line
of degree at most five. Its actual determinant degree eight remains an
explicit intermediate hypothesis until the geometric degree producer is
assembled. The kernel line, its section, divisor containment and length
contradiction are all derived from the genuine original maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
universe u

namespace M9Native.LagrangianPentagonalImageHomZero

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles LagrangianRankTwoSubsystemExistence

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- The full original section-zero bound excludes the first Hom branch,
including basepointed pencils and lines of degree less than five. -/
theorem hom_eq_zero (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s)
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (ξ : (model K M hM).Modules)
    [SheafOfModules.IsInvertible (model K M hM).presheaf
      (model K M hM).ringCatSheaf.property ξ]
    (hβ : letI := model_isCurve K M hM
      letI := beta_isInvertible K M hM s hr
      invertibleCurveDegree K (modelProjection K M hM)
        (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le
        (beta K M hM s) = 8)
    (hξ : letI := model_isCurve K M hM
      invertibleCurveDegree K (modelProjection K M hM)
        (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le ξ ≤ 5)
    (h2 : finrank K (cohomologyOverField K (modelProjection K M hM) ξ 0) = 2)
    (g : imageBundle K M hM s ⟶ ξ) : g = 0 := by
  letI := model_isCurve K M hM
  letI : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  letI := (ranks K M hM s hr).2.1
  letI := beta_isInvertible K M hM s hr
  letI := MukaiTwistBounds.exterior_two_isInvertible (imageBundle K M hM s)
  by_contra hg
  obtain ⟨a, ha, hvec, hv, hgv⟩ :=
    LagrangianImageKernelVector.exists_nonzero_original_kernel_vector K M hM s hs ξ g h2
  obtain ⟨L, N, j, p, w, hL, hN, t, z, hS, hj, ht, hpt, hz, hjz, hjg, hdeg⟩ :=
    CurveRankTwoSectionKernel.exists_line_kernel K (modelProjection K M hM)
      (imageBundle K M hM s) ξ g hg
      (LagrangianImageKernelVector.imageCombination K M hM s a) hv hgv
  letI := hL
  letI := hN
  let k : L ⟶ bundle K (modelInclusion K M hM) := j ≫ image.ι (originalMap K M hM s)
  have hk : k.app ⊤ z = LagrangianHyperplaneEvaluation.originalSection K
      (modelProjection K M hM) (modelInclusion K M hM)
      (Fintype.linearCombination K s a) := by
    change (image.ι (originalMap K M hM s)).app ⊤ (j.app ⊤ z) = _
    rw [hjz]
    have hn := (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap K
      (modelProjection K M hM) (image.ι (originalMap K M hM s))
      (LagrangianImageKernelVector.imageCombination K M hM s a)).symm
    have hm := congrArg (fun u =>
      (cohomologyOverFieldZeroLinearIso K (modelProjection K M hM)
        (bundle K (modelInclusion K M hM))).hom u)
      (LagrangianImageKernelVector.imageCombination_maps_to_original K M hM s a)
    exact hn.trans (hm.trans (sectionMap_constantVector K (modelProjection K M hM)
      (modelInclusion K M hM) (Fintype.linearCombination K s a)))
  have hraw : LagrangianHyperplaneEvaluation.originalSection K
      (modelProjection K M hM) (modelInclusion K M hM)
      (Fintype.linearCombination K s a) ≠ 0 := by
    intro hzq
    have hq := (sectionMap_ker_iff K (modelProjection K M hM)
      (modelInclusion K M hM) (Fintype.linearCombination K s a)).mpr hzq
    exact hvec ((LagrangianImageKernelVector.model_sectionMap_injective K M hM)
      (hq.trans (map_zero _).symm))
  letI := bundle_rank K (modelInclusion K M hM)
  have hbound := LineSectionVectorZeroDegree.line_degree_le_zero_H0 K
    (modelProjection K M hM) L (bundle K (modelInclusion K M hM)) 3 k z hz
    (by rw [hk]; exact hraw)
  rw [hk] at hbound
  have htwo := LagrangianSectionZeroBoundApplications.model_zero_H0_le_two K M hM
    (Fintype.linearCombination K s a) hvec
  have hLtwo : invertibleCurveDegree K (modelProjection K M hM)
      (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le L ≤ 2 :=
    hbound.trans (by exact_mod_cast htwo)
  have hExt : invertibleCurveDegree K (modelProjection K M hM)
      (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le
      (Scheme.Modules.exteriorPower (imageBundle K M hM s) 2) = 8 :=
    (invertibleCurveDegree_eq_of_iso K (modelProjection K M hM)
      (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le
      (betaExteriorIso K M hM s hr)).symm.trans hβ
  rw [hExt] at hdeg
  omega

end M9Native.LagrangianPentagonalImageHomZero
