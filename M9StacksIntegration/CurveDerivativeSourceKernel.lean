module

public import M9StacksIntegration.CurveDerivativeCohomology
public import M9StacksIntegration.CurveDerivativeTargetSections
public import M9StacksIntegration.CurveP1NormalSections

/-!
# Actual normal sections surject onto the kernel of the source tangent map

The source kernel is literally the kernel of H1 of the original sheaf
cotangent derivative dual. The genuine normal long exact sequence gives
a surjection from normal sections modulo original target vector fields.
Consequently its dimension is bounded by that actual quotient. No
relation to a moduli or morphism-deformation tangent space is assumed.
That geometric necessary-image comparison is a separate application.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9Native.CurveTangentLineGeometry M9Native.CurveDerivativeNormal
open M9Native.CurveDerivativeCohomology M9Native.CurveDerivativeTargetSections

universe u

namespace M9Native.CurveDerivativeSourceKernel

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
variable [Smooth pX] [Smooth pY]
variable (g : X ⟶ Y) (hg : g ≫ pY = pX)

/-- The literal kernel of the original H1 tangent derivative. -/
abbrev sourceKernel : Submodule k (cohomologyOverField k pX (tangentLine pX) 1) :=
  LinearMap.ker (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 1).hom

variable (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

/-- The actual normal boundary, with codomain restricted by its proved exactness. -/
def normalToSourceKernel :
    cohomologyOverField k pX (normalSheaf pX pY g hg) 0 →ₗ[k]
      sourceKernel pX pY g hg :=
  (normalBoundary pX pY g hg hnc).hom.codRestrict _ fun x =>
    (normalBoundary_exact_after pX pY g hg hnc _).mpr ⟨x, rfl⟩

/-- The original target vector fields have zero actual normal boundary. -/
theorem target_range_le_boundary_kernel :
    LinearMap.range (targetNormalSections pX pY g hg) ≤
      LinearMap.ker (normalToSourceKernel pX pY g hg hnc) := by
  rintro x ⟨t, rfl⟩
  apply Subtype.ext
  exact (normalBoundary_exact_before pX pY g hg hnc _).mpr
    ⟨targetPullback pX pY g hg t, rfl⟩

/-- The actual quotient by the actual target-vector-field range maps to
the literal source H1 kernel. -/
def quotientToSourceKernel :
    ((cohomologyOverField k pX (normalSheaf pX pY g hg) 0) ⧸
      LinearMap.range (targetNormalSections pX pY g hg)) →ₗ[k]
        sourceKernel pX pY g hg :=
  (LinearMap.range (targetNormalSections pX pY g hg)).liftQ
    (normalToSourceKernel pX pY g hg hnc)
    (target_range_le_boundary_kernel pX pY g hg hnc)

/-- Every original source H1 class killed by the derivative is the
boundary of a normal section, already after quotienting target fields. -/
theorem quotientToSourceKernel_surjective :
    Function.Surjective (quotientToSourceKernel pX pY g hg hnc) := by
  intro x
  obtain ⟨a, ha⟩ := (normalBoundary_exact_after pX pY g hg hnc x.val).mp x.property
  refine ⟨(LinearMap.range (targetNormalSections pX pY g hg)).mkQ a, ?_⟩
  apply Subtype.ext
  exact ha

include hnc in
/-- Finite-dimensionality follows from the original proper coherent normal sheaf. -/
theorem sourceKernel_finrank_le_normal_quotient :
    Module.finrank k (sourceKernel pX pY g hg) ≤
      Module.finrank k
        ((cohomologyOverField k pX (normalSheaf pX pY g hg) 0) ⧸
          LinearMap.range (targetNormalSections pX pY g hg)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let := normal_isCoherent pX pY g hg
  let := finiteDimensional_cohomologyOverField_of_isProper k pX
    (normalSheaf pX pY g hg) 0
  exact LinearMap.finrank_le_finrank_of_surjective
    (quotientToSourceKernel_surjective pX pY g hg hnc)

section ProjectiveLine

open M9Native.PencilProjectiveLineGeometry
attribute [local instance] isCurve_projectiveSpaceOver_one CurveP1NormalSections.line_smooth

variable [IsAlgClosed k]

/-- Actual source H1 kernel dimension is bounded by the original
cotangent degree plus twice the actual map degree minus three. -/
theorem sourceKernel_p1_finrank_degree_le
    (gP1 : X ⟶ Line k) (hgP1 : gP1 ≫ toBase k = pX)
    (hncP1 : ¬ ∃ y : Line k, ∀ x : X, gP1.base x = y)
    (hpos : letI := differentials_rank_one pX
      0 < curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1) :
    letI := differentials_rank_one pX
    (Module.finrank k (sourceKernel pX (toBase k) gP1 hgP1) : ℤ) ≤
      curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1 +
      2 * (PencilDegreePullback.curveMapDegree pX (toBase k) gP1 hgP1 hncP1 : ℤ) - 3 := by
  let := differentials_rank_one pX
  have hle := sourceKernel_finrank_le_normal_quotient pX (toBase k) gP1 hgP1 hncP1
  have hq := CurveP1NormalSections.target_quotient_degree_formula pX gP1 hgP1 hncP1 hpos
  have hz : (Module.finrank k (sourceKernel pX (toBase k) gP1 hgP1) : ℤ) ≤
      (Module.finrank k
        ((cohomologyOverField k pX (normalSheaf pX (toBase k) gP1 hgP1) 0) ⧸
          LinearMap.range (targetNormalSections pX (toBase k) gP1 hgP1)) : ℤ) := by
    exact_mod_cast hle
  exact hz.trans_eq hq

end ProjectiveLine

end M9Native.CurveDerivativeSourceKernel
