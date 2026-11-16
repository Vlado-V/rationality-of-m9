module

public import M9StacksIntegration.MukaiParameterOrbitConverse
public import M9StacksIntegration.LagrangianExtensionParameterAction

@[expose] public section

/-!
# The actual original-C native Sp6 parameter orbit converse

Over every algebraically closed extension of the original complex
field, the original cut-curve isomorphism and honest canonical-bundle
properties produce the actual original native group-scheme orbit.
The raw/native coordinate change and inverse quotient precomposition
are derived by the true all-extension parameter-presentation theorem.

Neither a bundle isomorphism, H0/polarization compatibility, parameter
orbit, nor a coordinate-action identification is assumed. Actual genus
nine, source nonpentagonality, and the actual canonical properties of
the two original restricted quotient bundles remain intermediate
geometric inputs; this is not an unconditional good-open converse.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open MonoidalCategory CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace M9Native.MukaiOriginalParameterOrbitConverse

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

/-- Actual original native parameter points are related by the actual
native Sp6 group-scheme action. All raw/C coordinate comparisons and
the original quotient-kernel action are derived, not premises. -/
theorem exists_native_parameter_orbit_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hg : genus (curveProjection L M) = 9)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection L M) (bundle L (inclusion L M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection L N) (bundle L (inclusion L N))) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g (originalPoint L M hM)
        (originalPoint_projection L M hM) = originalPoint L N hN := by
  obtain ⟨h, hh⟩ := MukaiParameterOrbitConverse.exists_matrix_orbit_of_curveIso
    L M N hM hN e he hg hnp hQC hQD
  exact ⟨PrimitiveExtensionFieldBridge.toOriginal L h,
    LagrangianExtensionParameterAction.native_action_eq_of_rowSpan_eq L h M N hM hN hh⟩

/-- The literal group-scheme action expression used by the genuine
coarse-field orbit-fibre comparison, on the same original complex base. -/
theorem exists_original_native_action_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve L M ≅ curve L N)
    (he : e.hom ≫ curveProjection L N = curveProjection L M)
    (hg : genus (curveProjection L M) = 9)
    (hnp : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection L M) (bundle L (inclusion L M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection L N) (bundle L (inclusion L N))) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
        (PrimitiveFieldMatrixAction.overPoint L (originalPoint L M hM)
          (originalPoint_projection L M hM)) ≫ PrimitiveGrassmannianAction.nativeAction.act).left =
        originalPoint L N hN :=
  exists_native_parameter_orbit_of_curveIso L M N hM hN e he hg hnp hQC hQD

end M9Native.MukaiOriginalParameterOrbitConverse
