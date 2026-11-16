module

public import M9StacksIntegration.MukaiGenusNineParameterOrbitConverse
public import M9StacksIntegration.LagrangianQuotientFactoryApplications

@[expose] public section

/-! Actual native parameter orbits from actual nonpentagonal section
curves. Genus nine and both original quotient-bundle properties are
derived from the genuine section geometry. The target no-pencil
condition is transported across the original over-field isomorphism.
No genus, canonical-bundle, bundle-isomorphism, H0, polarization, row-span
or parameter-orbit hypothesis remains. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open MonoidalCategory CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj
universe u

namespace M9Native.MukaiNonpentagonalParameterOrbitConverse
open LagrangianTransverseRestriction LagrangianUniversalSections
open MukaiCanonicalBundleFromNet LagrangianExtensionParameterCoordinates

section Ordered
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
local instance orderedSmooth : Smooth (curveProjection K M) :=
  SmoothOfRelativeDimension.smooth 1 _

/-- On the original ordered cut, the actual genus and complete
canonical quotient properties are consequences of its no-pencil condition. -/
theorem ordered_quotient_isCanonicalGeneratedSemi
    (hM : Function.Surjective M.mulVec)
    (hnp : ¬ Nonempty (LinearSeries K (curveProjection K M)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le 5 1)) :
    IsCanonicalGeneratedSemi (curveProjection K M) (bundle K (inclusion K M)) :=
  LagrangianQuotientFactoryApplications.ordered_isCanonicalGeneratedSemi K M hM
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le
    (LagrangianTransverseGenusNine.genus_eq_nine K M hM) hnp
end Ordered

section OriginalBase
variable (L : Type) [Field L] [Algebra ℂ L] [IsAlgClosed L]
local instance extensionCharZero : CharZero L := PrimitiveExtensionFieldBridge.charZero_extension L
variable (M N : Matrix (Fin 5) (Fin 14) L)
  [IsIntegral (curve L M)] [SmoothOfRelativeDimension 1 (curveProjection L M)]
  [IsIntegral (curve L N)] [SmoothOfRelativeDimension 1 (curveProjection L N)]
local instance sourceSmooth : Smooth (curveProjection L M) := SmoothOfRelativeDimension.smooth 1 _
local instance targetSmooth : Smooth (curveProjection L N) := SmoothOfRelativeDimension.smooth 1 _

/-- The actual original native parameter orbit is derived from a
genuine over-field curve isomorphism and the source no-pencil condition. -/
theorem exists_native_parameter_orbit_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1)) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g (originalPoint L M hM)
        (originalPoint_projection L M hM) = originalPoint L N hN := by
  have hnpN : ¬ Nonempty (LinearSeries L (curveProjection L N)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L N)).le 5 1) :=
    (MukaiCurveIsoLinearSeries.no_degree_five_pencil_iff L
      (curveProjection L M) (curveProjection L N) e he
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L N)).le).mp hnp
  exact MukaiGenusNineParameterOrbitConverse.exists_native_parameter_orbit_of_curveIso
    L M N hM hN e he hnp
    (ordered_quotient_isCanonicalGeneratedSemi L M hM hnp)
    (ordered_quotient_isCanonicalGeneratedSemi L N hN hnpN)

/-- The literal actual native Sp6 action on the same original complex
parameter space, with all genus and quotient properties derived. -/
theorem exists_original_native_action_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1)) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
        (PrimitiveFieldMatrixAction.overPoint L (originalPoint L M hM)
          (originalPoint_projection L M hM)) ≫ PrimitiveGrassmannianAction.nativeAction.act).left =
        originalPoint L N hN :=
  exists_native_parameter_orbit_of_curveIso L M N hM hN e he hnp
end OriginalBase
end M9Native.MukaiNonpentagonalParameterOrbitConverse
