module

public import M9StacksIntegration.LagrangianFiveCutQuotientTransport
public import M9StacksIntegration.NativeVectorSectionZeroTransport
public import M9StacksIntegration.LagrangianStandardSectionZeroBound
public import M9StacksIntegration.LagrangianHyperplaneZeroCokernel

/-!
# Actual full native zero and hyperplane-cokernel bounds for every original vector

Genuine symplectic transitivity, original cut and quotient transport, and
native full zero-scheme transport reduce every nonzero original vector
to the proved standard-section bound. The original structural field map
is retained by the actual scheme isomorphism. Actual good-open geometry
supplies finiteness. The independent true cokernel/zero comparison then
gives the same bound for the original hyperplane subsystem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianUniversalSectionZeroBound

open LagrangianUniversalSections LagrangianStandardSectionZeroModel
open LagrangianFiveCutTransport LagrangianFiveCutQuotientTransport

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- The original native q(firstVector)-zero scheme is actually
isomorphic to the original standard-section zero scheme of the genuinely
transported original five-cut. -/
def zeroIsoStandard (g : Matrix.symplecticGroup (Fin 3) K) :
    (LagrangianHyperplaneEvaluation.zeroIdeal K (curveProjection K M hM) (toLG K M hM)
      (firstVector K g)).subscheme ≅
        zeroCurve K (transformedMatrix K M g) (transformed_surjective K M hM g) := by
  let F := bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))
  let G := bundle K (toLG K M hM)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3 := bundle_rank K _
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 3 := bundle_rank K _
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 3
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G 3
  exact NativeVectorSectionZeroTransport.zeroSchemeIso F G 3 (cutIso K M hM g)
    (targetIso K M hM g)
    (curveSection K (transformedMatrix K M g) (transformed_surjective K M hM g))
    (LagrangianHyperplaneEvaluation.originalSection K (curveProjection K M hM)
      (toLG K M hM) (firstVector K g)) (targetIso_firstSection K M hM g)

/-- The full-zero isomorphism preserves the original field projection,
not merely the underlying topological support. -/
theorem zeroIsoStandard_over (g : Matrix.symplecticGroup (Fin 3) K) :
    (zeroIsoStandard K M hM g).hom ≫
        zeroCurveProjection K (transformedMatrix K M g) (transformed_surjective K M hM g) =
      LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
        (toLG K M hM) (firstVector K g) := by
  let F := bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))
  let G := bundle K (toLG K M hM)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3 := bundle_rank K _
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 3 := bundle_rank K _
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 3
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G 3
  exact NativeVectorSectionZeroTransport.zeroSchemeIso_over F G 3 (cutIso K M hM g)
    (targetIso K M hM g)
    (curveSection K (transformedMatrix K M g) (transformed_surjective K M hM g))
    (LagrangianHyperplaneEvaluation.originalSection K (curveProjection K M hM)
      (toLG K M hM) (firstVector K g)) (targetIso_firstSection K M hM g)
    (curveProjection K M hM)
    (curveProjection K (transformedMatrix K M g) (transformed_surjective K M hM g))
    (cutIso_hom_projection K M hM g)

/-- The genuine geometric bound for any original nonzero vector whose
full native zero scheme is actually finite. No smoothness or reducedness
premise is used in this intermediate theorem. -/
theorem h0_le_two_of_isFinite (v : Fin 6 → K) (hv : v ≠ 0)
    [IsFinite (LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
      (toLG K M hM) v)] :
    finrank K (structureSheafCohomology
      (LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
        (toLG K M hM) v) 0) ≤ 2 := by
  obtain ⟨g,rfl⟩ := exists_firstVector_eq K v hv
  let e := zeroIsoStandard K M hM g
  let p := LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
    (toLG K M hM) (firstVector K g)
  let q := zeroCurveProjection K (transformedMatrix K M g) (transformed_surjective K M hM g)
  have he : e.hom ≫ q = p := zeroIsoStandard_over K M hM g
  letI : IsFinite q := SplitQuadricQuotientCoordinates.finite_target_of_iso K e p q he
  have hcoh := (SplitQuadricQuotientCoordinates.structureCohomologyIso K e p q he 0).toLinearEquiv.finrank_eq
  exact hcoh.trans_le (LagrangianStandardSectionZeroBound.h0_le_two_of_isFinite K
    (transformedMatrix K M g) (transformed_surjective K M hM g))

variable [IsAlgClosed K]

/-- Actual original good-open geometry supplies full scheme finiteness
for every nonzero original quotient section. -/
theorem goodOpen_zero_isFinite
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) (v : Fin 6 → K) (hv : v ≠ 0) :
    IsFinite (LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
      (toLG K M hM) v) :=
  LagrangianTransverseSixSections.goodOpen_zeroScheme_isFinite K
    (LagrangianMatrixPointRows.matrixPoint K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM) hg v hv

/-- Cited Mukai II4.4(1), on the SAME full native zero scheme and the
original structural field map, for every original nonzero six-vector. -/
theorem goodOpen_zero_h0_le_two
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (structureSheafCohomology
      (LagrangianHyperplaneEvaluation.zeroProjection K (curveProjection K M hM)
        (toLG K M hM) v) 0) ≤ 2 := by
  letI := goodOpen_zero_isFinite K M hM hg v hv
  exact h0_le_two_of_isFinite K M hM v hv

/-- Cited Mukai II4.4(2), for the actual canonical symplectic-hyperplane
evaluation SHEAF cokernel, via the proved SAME-full-zero comparison. -/
theorem goodOpen_hyperplaneCokernel_H0_le_two
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (cohomologyOverField K (curveProjection K M hM)
      (LagrangianHyperplaneEvaluation.hyperplaneCokernel K (curveProjection K M hM)
        (toLG K M hM) v) 0) ≤ 2 := by
  rw [LagrangianHyperplaneZeroCokernel.finrank_hyperplaneCokernel_H0 K
    (curveProjection K M hM) (toLG K M hM) v hv]
  exact goodOpen_zero_h0_le_two K M hM hg v hv

end M9Native.LagrangianUniversalSectionZeroBound
