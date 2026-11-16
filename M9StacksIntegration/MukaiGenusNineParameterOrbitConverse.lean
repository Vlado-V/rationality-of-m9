module

public import M9StacksIntegration.MukaiOriginalParameterOrbitConverse
public import M9StacksIntegration.LagrangianTransverseGenusNine

@[expose] public section

/-! The actual original native parameter-orbit converse now derives
genus nine from the genuine ordered section. Source nonpentagonality
and canonical generated semi-irreducible properties remain the honest
geometric gates. No genus, bundle-isomorphism, H0, polarization or
parameter-orbit premise is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open MonoidalCategory CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace M9Native.MukaiGenusNineParameterOrbitConverse
open LagrangianTransverseRestriction LagrangianUniversalSections
open MukaiCanonicalBundleFromNet LagrangianExtensionParameterCoordinates

variable (L : Type) [Field L] [Algebra ℂ L] [IsAlgClosed L]
local instance extensionCharZero : CharZero L := PrimitiveExtensionFieldBridge.charZero_extension L

variable (M N : Matrix (Fin 5) (Fin 14) L)
  [IsIntegral (curve L M)] [SmoothOfRelativeDimension 1 (curveProjection L M)]
  [IsIntegral (curve L N)] [SmoothOfRelativeDimension 1 (curveProjection L N)]

local instance sourceSmooth : Smooth (curveProjection L M) :=
  SmoothOfRelativeDimension.smooth 1 _
local instance targetSmooth : Smooth (curveProjection L N) :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The genuine original native orbit, with genus nine derived. -/
theorem exists_native_parameter_orbit_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection L M) (bundle L (inclusion L M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection L N) (bundle L (inclusion L N))) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g (originalPoint L M hM)
        (originalPoint_projection L M hM) = originalPoint L N hN :=
  MukaiOriginalParameterOrbitConverse.exists_native_parameter_orbit_of_curveIso
    L M N hM hN e he (LagrangianTransverseGenusNine.genus_eq_nine L M hM) hnp hQC hQD

/-- The literal original native group-scheme action, with genus nine derived. -/
theorem exists_original_native_action_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection L M) (bundle L (inclusion L M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection L N) (bundle L (inclusion L N))) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
        (PrimitiveFieldMatrixAction.overPoint L (originalPoint L M hM)
          (originalPoint_projection L M hM)) ≫ PrimitiveGrassmannianAction.nativeAction.act).left =
        originalPoint L N hN :=
  exists_native_parameter_orbit_of_curveIso L M N hM hN e he hnp hQC hQD

end M9Native.MukaiGenusNineParameterOrbitConverse
