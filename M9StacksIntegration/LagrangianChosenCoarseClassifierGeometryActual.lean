module

public import M9StacksIntegration.LagrangianChosenCoarseClassifierGeometry
public import M9StacksIntegration.LagrangianNonpentagonal

@[expose] public section

/-! STAGED ONLY, outside the active lean_lib. Do not promote or compile
until the actual universal ordered-section No5 producer is SAFE. This
actual specialization derives all-field source no5 from the genuine
constructed ordered models and returns ClassifierGeometry with no
geometry, no5, model or curve-isomorphism premise. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianChosenCoarseClassifierGeometryActual
open PrimitiveGenericOpenPoints PrimitiveUniversalExtensionPoints
open LagrangianTransverseRestriction LagrangianChosenCoarseClassifierGeometry

/-- Every original coordinate-good field point has a genuinely no5
original whole raw fibre, by the actual universal ordered-cut theorem.
No genus, no-lower-pencil, bundle, rank or degree premise remains. -/
theorem allFieldSourceNoFive : AllFieldSourceNoFive := by
  intro L _ _ _ x
  letI : CharZero L := PrimitiveExtensionFieldBridge.charZero_extension L
  let p := x.left ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap
  have hp : p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι ≫
      LagrangianLinearSections.parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
    simpa only [p, Category.assoc] using
      LagrangianGoodFieldOrbit.coordinateGoodPoint_projection L x.left (field_projection L x)
  obtain ⟨M,hM,e,_,he,hI,hS,_⟩ :=
    LagrangianGoodOpenOrderedModel.exists_ordered_model ℂ L (algebraMap ℂ L) p hp
  letI : IsIntegral (curve L M) := hI
  letI : SmoothOfRelativeDimension 1 (curveProjection L M) := hS
  have hMdim : topologicalKrullDim (curve L M) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le
  have hnoM := LagrangianNonpentagonal.no_g1_five_at_dimension L M hM hMdim
  change LagrangianGoodFieldOrbit.SourceNoFivePencil L p
  exact (MukaiCurveIsoLinearSeries.no_degree_five_pencil_iff L
    (curveProjection L M) (LagrangianGoodFieldOrbit.fibreProjection L p) e he
    hMdim (LagrangianGoodFieldOrbit.fibre_dimension L p).le).mp hnoM

/-- Actual exact chosen classifier geometry, with every original ACL
field and the genuine native/raw C-conjugacy retained. No geometry or
source no5 assertion is supplied as a premise. -/
theorem classifierGeometry
    (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ))) (hZ : B.Contains integerBase) :
    PrimitiveNativeClassifierRationalOpen.ClassifierGeometry B hC
      (LagrangianChosenCoarseFamily.target ℂ B hC hZ)
      LagrangianChosenCoarseCoordinateShift.goodOpen
      (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom :=
  classifierGeometry_of_sourceNoFive B hC hZ allFieldSourceNoFive

end M9Native.LagrangianChosenCoarseClassifierGeometryActual
