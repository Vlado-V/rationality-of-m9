module

public import M9StacksIntegration.LagrangianRankOneQuotientHyperplane
public import M9StacksIntegration.VectorSectionCokernelSupport
public import M9StacksIntegration.LagrangianSectionZeroBoundApplications
public import M9StacksIntegration.LagrangianRankTwoQuotientSections

/-!
# An actual rank-one original quotient image has at most two H0 classes

On the literal transverse model, an actual coherent quotient of the
original universal rank-three bundle whose original six-section image
has rank at most one has H0 at most two. Its actual original symplectic
hyperplane and the epimorphism from that hyperplane cokernel are derived.
Nonzero original sections, zero-dimensional support, and the original
K-linear cohomology comparison are also derived. No finite support,
length, target zero-scheme, or cokernel identification is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianRankOneQuotientBound

open LagrangianOrderedFibre LagrangianUniversalSections LagrangianHyperplaneEvaluation
open LagrangianRankTwoSubsystemBundles

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- The actual original restricted universal section is nonzero for a nonzero vector. -/
theorem originalSection_ne_zero (v : Fin 6 → K) (hv : v ≠ 0) :
    originalSection K (modelProjection K M hM) (modelInclusion K M hM) v ≠ 0 := by
  have hinj : Function.Injective
      (LagrangianUniversalSections.sectionMap K (modelProjection K M hM)
        (modelInclusion K M hM)) := by
    apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
      K (modelProjection K M hM) (modelInclusion K M hM) rfl
    rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM]
    norm_num
  intro hz
  apply hv
  exact hinj ((LagrangianUniversalSections.sectionMap_ker_iff K
    (modelProjection K M hM) (modelInclusion K M hM) v).mpr hz |>.trans (map_zero _).symm)

/-- A genuine coherent quotient with original image rank at most one satisfies the full bound. -/
theorem quotient_H0_le_two {T : (model K M hM).Modules} [T.IsCoherent]
    (p : bundle K (modelInclusion K M hM) ⟶ T) [Epi p]
    (hp : Module.finrank K (LinearMap.range
      (LagrangianRankOneQuotientHyperplane.originalQuotientSections K
        (modelProjection K M hM) (modelInclusion K M hM) p)) ≤ 1) :
    Module.finrank K (cohomologyOverField K (modelProjection K M hM) T 0) ≤ 2 := by
  obtain ⟨v,hv,a,ha⟩ := LagrangianRankOneQuotientHyperplane.exists_hyperplaneCokernel_epi K
    (modelProjection K M hM) (modelInclusion K M hM) p hp
  let := ha
  let := bundle_rank K (modelInclusion K M hM)
  let := VectorSectionCokernelSupport.evaluationCokernel_isCoherent K (modelProjection K M hM)
    (bundle K (modelInclusion K M hM)) 3
    (originalSection K (modelProjection K M hM) (modelInclusion K M hM) v)
  let e := LagrangianHyperplaneZeroCokernel.evaluationCokernelIso K
    (modelProjection K M hM) (modelInclusion K M hM) v hv
  have hsupp := VectorSectionCokernelSupport.evaluationCokernel_support_le_zero K
    (modelProjection K M hM)
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (modelProjection K M hM) 1).le
    (bundle K (modelInclusion K M hM)) 3
    (originalSection K (modelProjection K M hM) (modelInclusion K M hM) v)
    (originalSection_ne_zero K M hM v hv)
  have hb := VectorSectionCokernelSupport.quotient_H0_le K (modelProjection K M hM)
    (inferInstance : (cokernel (dualEvalHom (bundle K (modelInclusion K M hM))
      (originalSection K (modelProjection K M hM) (modelInclusion K M hM) v))).IsCoherent)
    (inferInstance : T.IsCoherent) (e.inv ≫ a) hsupp
  have he := (cohomologyOverFieldIso K (modelProjection K M hM) e 0).toLinearEquiv.finrank_eq
  have htwo := LagrangianSectionZeroBoundApplications.model_hyperplaneCokernel_H0_le_two
    K M hM v hv
  omega

end M9Native.LagrangianRankOneQuotientBound
