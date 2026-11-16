module

public import M9StacksIntegration.MukaiCurveIsoLagrangianAction
public import M9StacksIntegration.LagrangianPrimitiveRestrictionAction
public import M9StacksIntegration.LagrangianRestrictionIso
public import M9StacksIntegration.LagrangianParameterFieldMatrixAction
public import M9StacksIntegration.LagrangianMatrixPointRows

/-!
# Conditional actual original-cut parameter orbit converse

The original curve isomorphism and actual canonical bundle properties
give the genuine native LG action by the previous theorem. Actual
primitive-section covariance transports the defining five-row spaces.
The native Grassmannian quotient classifier then gives equality of the
actual original parameter points under the genuine raw Sp6 action.

The true source genus nine, nonpentagonality and actual restricted-Q
canonical properties remain honest intermediate geometry. No bundle
isomorphism, H0/polarization compatibility, row-space relation, parameter
orbit, or dominance is a hypothesis of the final converse.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators Matrix

universe u
namespace M9Native.MukaiParameterOrbitConverse

open LagrangianTransverseRestriction LagrangianUniversalSections
open MukaiCanonicalBundleFromNet LagrangianParameterFieldMatrixAction
open LagrangianSigmaInvariance PrimitiveRingMatrices

variable (K : Type u) [Field K] [CharZero K]

/-- The actual raw primitive representation supplies a genuine unit,
with its actual group inverse. -/
def rawUnit (g : Matrix.symplecticGroup (Fin 3) K) : Matrix.GeneralLinearGroup (Fin 14) K where
  val := matrix14 K K (RingHom.id K) g
  inv := matrix14 K K (RingHom.id K) g⁻¹
  val_inv := by rw [← matrix14_mul, mul_inv_cancel, matrix14_one]
  inv_val := by rw [← matrix14_mul, inv_mul_cancel, matrix14_one]

theorem rawUnit_one : rawUnit K 1 = 1 := by
  apply Units.ext
  exact matrix14_one K K (RingHom.id K)

theorem rawUnit_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    rawUnit K (g * h) = rawUnit K g * rawUnit K h := by
  apply Units.ext
  exact matrix14_mul K K (RingHom.id K) g h

/-- The raw primitive kernel action is genuine inverse quotient
precomposition on the original native parameter scheme. -/
def rawAction (g : Matrix.symplecticGroup (Fin 3) K) :
    LagrangianLinearSections.parameter K ⟶ LagrangianLinearSections.parameter K :=
  LagrangianParameterLinearAction.action K (rawUnit K g⁻¹)

theorem rawAction_one : rawAction K 1 = 𝟙 _ := by
  rw [rawAction, inv_one, rawUnit_one, LagrangianParameterLinearAction.action_one]

theorem rawAction_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    rawAction K g ≫ rawAction K h = rawAction K (h * g) := by
  simp only [rawAction, _root_.mul_inv_rev, rawUnit_mul, LagrangianParameterLinearAction.action_mul]

/-- Every test scheme sees the literal original quotient
precomposition. This is not an assumed action identification. -/
theorem rawAction_pointClass {T : Scheme.{u}}
    (p : T ⟶ LagrangianLinearSections.parameter K) (g : Matrix.symplecticGroup (Fin 3) K) :
    LagrangianParameterLinearAction.pointClass K (p ≫ rawAction K g) =
      LagrangianParameterLinearAction.transformPoints K
        (p ≫ LagrangianLinearSections.parameterProjection K) (rawUnit K g⁻¹)
        (LagrangianParameterLinearAction.pointClass K p) :=
  LagrangianParameterLinearAction.pointClass_action K p (rawUnit K g⁻¹)

omit [CharZero K] in
/-- Literal row multiplication is the image of the original row span
under the actual transpose coefficient map. -/
theorem rowSpan_mul_right {m n p : ℕ} (M : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) :
    rowSpan K (M * B) = (rowSpan K M).map B.transpose.mulVecLin := by
  have hr : (M * B).row = B.transpose.mulVecLin ∘ M.row := by
    funext i j
    change (∑ k : Fin n, M i k * B k j) = ∑ k : Fin n, B k j * M i k
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  unfold rowSpan
  rw [Submodule.map_span, ← Set.range_comp, ← hr]

variable [IsAlgClosed K]
  (M N : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
  [IsIntegral (curve K N)] [SmoothOfRelativeDimension 1 (curveProjection K N)]

local instance sourceSmooth : Smooth (curveProjection K M) :=
  SmoothOfRelativeDimension.smooth 1 _
local instance targetSmooth : Smooth (curveProjection K N) :=
  SmoothOfRelativeDimension.smooth 1 _

set_option maxHeartbeats 1600000 in
/-- The original matrices have the actual raw primitive orbit relation,
derived from the curve isomorphism and canonical uniqueness. -/
theorem exists_matrix_orbit_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve K M ≅ curve K N)
    (he : e.hom ≫ curveProjection K N = curveProjection K M)
    (hg : genus (curveProjection K M) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (curveProjection K M)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection K M) (bundle K (inclusion K M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection K N) (bundle K (inclusion K N))) :
    ∃ h : Matrix.symplecticGroup (Fin 3) K,
      rowSpan K (M * matrix14 K K (RingHom.id K) h⁻¹) = rowSpan K N := by
  obtain ⟨g, hLG⟩ := MukaiCurveIsoLagrangianAction.exists_lagrangian_action_of_curveIso
    K M N hM hN e he hg hnp hQC hQD
  let U := rawUnit K (transposeSymplectic K g)
  have hbase : (inclusion K N ≫ LagrangianSymplecticAction.action K g) ≫
      LagrangianGrassmannian.projection K = curveProjection K N := by
    rw [Category.assoc, LagrangianSymplecticAction.action_projection]
  have hker := LagrangianRestrictionIso.primitiveRestriction_kernel_iso K
    (curveProjection K M) (curveProjection K N) (inclusion K M)
    (inclusion K N ≫ LagrangianSymplecticAction.action K g) rfl hbase e hLG.symm
  have hv (v : Fin 14 → K) :
      v ∈ rowSpan K M ↔ U.val.transpose.mulVecLin v ∈ rowSpan K N := by
    change v ∈ Submodule.span K (Set.range M) ↔
      U.val.transpose.mulVecLin v ∈ Submodule.span K (Set.range N)
    rw [← LagrangianTransverseRestriction.primitiveRestriction_kernel K M hM,
      ← LagrangianTransverseRestriction.primitiveRestriction_kernel K N hN]
    have hi : LagrangianPrimitiveRestriction.primitiveRestriction K (curveProjection K M)
        (inclusion K M) v = 0 ↔
      LagrangianPrimitiveRestriction.primitiveRestriction K (curveProjection K N)
        (inclusion K N ≫ LagrangianSymplecticAction.action K g) v = 0 := by
      change v ∈ LinearMap.ker _ ↔ v ∈ LinearMap.ker _
      rw [hker]
    exact hi.trans (LagrangianPrimitiveRestrictionAction.restriction_zero_iff
      K (curveProjection K N) (inclusion K N) rfl g v)
  have hrows : rowSpan K (M * U.val) = rowSpan K N := by
    rw [rowSpan_mul_right]
    ext v
    constructor
    · rintro ⟨w, hw, hEq⟩
      rw [← hEq]
      exact (hv w).mp hw
    · intro hvN
      let w : Fin 14 → K := (U⁻¹).val.transpose *ᵥ v
      have hInv : U.val.transpose * (U⁻¹).val.transpose = 1 := by
        rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
      have hwv : U.val.transpose.mulVecLin w = v := by
        change U.val.transpose *ᵥ ((U⁻¹).val.transpose *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
      refine ⟨w, (hv w).mpr ?_, hwv⟩
      rw [hwv]
      exact hvN
  refine ⟨(transposeSymplectic K g)⁻¹, ?_⟩
  change rowSpan K (M * matrix14 K K (RingHom.id K) (transposeSymplectic K g)) =
    rowSpan K N at hrows
  simpa only [inv_inv] using hrows

/-- The actual ORIGINAL native parameter points are in the genuine raw
Sp6 orbit. The output is scheme-morphism equality, with no orbit premise. -/
theorem exists_raw_parameter_orbit_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve K M ≅ curve K N)
    (he : e.hom ≫ curveProjection K N = curveProjection K M)
    (hg : genus (curveProjection K M) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (curveProjection K M)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection K M) (bundle K (inclusion K M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection K N) (bundle K (inclusion K N))) :
    ∃ h : Matrix.symplecticGroup (Fin 3) K,
      LagrangianMatrixPointRows.matrixPoint K M hM ≫ rawAction K h =
        LagrangianMatrixPointRows.matrixPoint K N hN := by
  obtain ⟨h, hh⟩ := exists_matrix_orbit_of_curveIso K M N hM hN e he hg hnp hQC hQD
  exact ⟨h, LagrangianParameterFieldMatrixAction.fieldPoint_action_eq_of_rowSpan_eq
    K (rawUnit K h⁻¹) M N hM hN hh⟩

end M9Native.MukaiParameterOrbitConverse
