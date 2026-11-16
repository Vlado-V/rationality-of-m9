module

public import M9StacksIntegration.CurveDerivativeNormal
public import M9StacksIntegration.MukaiCohomologyParity
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Original target vector fields in the actual derivative normal sections

The linear map is the original native H0 pullback, followed by the
canonical actual dual/pullback comparison and the literal normal
quotient. Exactness of the original normal sequence proves injectivity
when the original source has no tangent sections. Positive actual
cotangent degree derives that vanishing without a supplied H0 count.

The quotient is the vector-space quotient by the image of these
original target vector fields. Identification with a deformation or
Hurwitz tangent quotient is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9Native.CurveTangentLineGeometry M9Native.CurveDerivativeNormal

universe u

namespace M9Native.CurveDerivativeTargetSections

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Positive original differential degree makes original tangent H0 vanish. -/
theorem tangentH0_subsingleton_of_differential_degree_pos [IsAlgClosed k]
    (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] [IsProper pX]
    (hpos : letI := differentials_rank_one pX
      0 < curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1) :
    Subsingleton (cohomologyOverField k pX (tangentLine pX) 0) := by
  let := differentials_rank_one pX
  let := tangent_isInvertible pX
  have hn : invertibleCurveDegree k pX
      (IsCurve.topologicalKrullDim_eq_one (f := pX)).le (tangentLine pX) < 0 := by
    rw [tangent_degree pX]
    exact neg_neg_of_pos hpos
  exact ModuleCat.subsingleton_of_isZero
    (isZero_cohomologyOverField_zero_of_invertibleCurveDegree_neg k pX
      (IsCurve.topologicalKrullDim_eq_one (f := pX)).le (tangentLine pX) hn)

variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pY] [Smooth pY]
variable (g : X ⟶ Y) (hg : g ≫ pY = pX)

/-- The original scalar-compatible pullback of target tangent sections,
followed by the actual canonical dual-base-change arrow. -/
def targetPullback : cohomologyOverField k pY (tangentLine pY) 0 →ₗ[k]
    cohomologyOverField k pX (pulledTangentLine pY g) 0 := by
  subst hg
  exact (cohomologyOverFieldMap k (g ≫ pY) (pulledTangentIso pY g).hom 0).hom ∘ₗ
    PencilPullbackSections.cohomologyPullback k pY g (tangentLine pY)

/-- The original target vector fields map into the actual normal sections
by the original native cokernel projection. -/
def targetNormalSections : cohomologyOverField k pY (tangentLine pY) 0 →ₗ[k]
    cohomologyOverField k pX (normalSheaf pX pY g hg) 0 :=
  (cohomologyOverFieldMap k pX (cokernel.π (tangentMap pX pY g hg)) 0).hom ∘ₗ
    targetPullback pX pY g hg

/-- Original target vector fields pull back injectively under a nonconstant curve map. -/
theorem targetPullback_injective [IsCurve k pX]
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    Function.Injective (targetPullback pX pY g hg) := by
  subst hg
  let := isDominant_of_not_constant k (g ≫ pY) pY g hnc
  let := tangent_isInvertible pY
  change Function.Injective
    ((cohomologyOverFieldMap k (g ≫ pY) (pulledTangentIso pY g).hom 0).hom ∘ₗ
      PencilPullbackSections.cohomologyPullback k pY g (tangentLine pY))
  let : IsIso (cohomologyOverFieldMap k (g ≫ pY) (pulledTangentIso pY g).hom 0) :=
    ⟨⟨cohomologyOverFieldMap k (g ≫ pY) (pulledTangentIso pY g).inv 0,
      by rw [← cohomologyOverFieldMap_comp, Iso.hom_inv_id, cohomologyOverFieldMap_id],
      by rw [← cohomologyOverFieldMap_comp, Iso.inv_hom_id, cohomologyOverFieldMap_id]⟩⟩
  have he : Function.Injective
      (cohomologyOverFieldMap k (g ≫ pY) (pulledTangentIso pY g).hom 0).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact he.comp (PencilPullbackSections.cohomologyPullback_injective k pY g (tangentLine pY))

variable [CharZero k] [IsCurve k pX] [IsProper pX] [IsProper pY] [Smooth pX]
variable (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

include hnc

/-- Original normal projection is injective on H0 when source tangent H0 vanishes,
by actual native long-exact-sequence exactness. -/
theorem normalProjection_injective
    (hT : Subsingleton (cohomologyOverField k pX (tangentLine pX) 0)) :
    Function.Injective
      (cohomologyOverFieldMap k pX (cokernel.π (tangentMap pX pY g hg)) 0).hom := by
  have he := MukaiCohomologyParity.cohomologyBoundary_exact_left k pX
    (normal_shortExact pX pY g hg hnc) 0
  intro a b hab
  have hz : (cohomologyOverFieldMap k pX
      (cokernel.π (tangentMap pX pY g hg)) 0) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (he (a-b)).mp hz
  have hc0 : c = 0 := hT.elim _ _
  rw [hc0, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- The original target vector fields inject into actual normal H0. -/
theorem targetNormalSections_injective
    (hT : Subsingleton (cohomologyOverField k pX (tangentLine pX) 0)) :
    Function.Injective (targetNormalSections pX pY g hg) :=
  (normalProjection_injective pX pY g hg hnc hT).comp
    (targetPullback_injective pX pY g hg hnc)

/-- The range has the actual original target tangent-section dimension. -/
theorem targetNormalSections_range_finrank
    (hT : Subsingleton (cohomologyOverField k pX (tangentLine pX) 0)) :
    Module.finrank k (LinearMap.range (targetNormalSections pX pY g hg)) =
      Module.finrank k (cohomologyOverField k pY (tangentLine pY) 0) :=
  LinearMap.finrank_range_of_inj (targetNormalSections_injective pX pY g hg hnc hT)

/-- Actual finite-dimensional quotient by original target vector fields. -/
theorem quotient_finrank
    (hT : Subsingleton (cohomologyOverField k pX (tangentLine pX) 0)) :
    Module.finrank k
      ((cohomologyOverField k pX (normalSheaf pX pY g hg) 0) ⧸
        LinearMap.range (targetNormalSections pX pY g hg)) =
      Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) -
        Module.finrank k (cohomologyOverField k pY (tangentLine pY) 0) := by
  let := normal_isCoherent pX pY g hg
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (normalSheaf pX pY g hg) 0
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (targetNormalSections pX pY g hg))
  rw [targetNormalSections_range_finrank pX pY g hg hnc hT] at h
  omega

/-- Positive original cotangent degree supplies all source vanishing
needed for the actual target-vector-field quotient formula. -/
theorem quotient_finrank_of_positive_differentials [IsAlgClosed k]
    (hpos : letI := differentials_rank_one pX
      0 < curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1) :
    Module.finrank k
      ((cohomologyOverField k pX (normalSheaf pX pY g hg) 0) ⧸
        LinearMap.range (targetNormalSections pX pY g hg)) =
      Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) -
        Module.finrank k (cohomologyOverField k pY (tangentLine pY) 0) :=
  quotient_finrank pX pY g hg hnc
    (tangentH0_subsingleton_of_differential_degree_pos pX hpos)

end M9Native.CurveDerivativeTargetSections
