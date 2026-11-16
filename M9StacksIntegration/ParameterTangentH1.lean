module

public import M9StacksIntegration.ParameterTangentDeformation

/-!
# The original family tangent class in the standard Ext and H¹ models

The source is the canonical scheme tangent space of the parameter.
The target is the exact native ULift endpoint used by the scheme-morphism
six-term sequence. Its value is the class of the actual pulled family;
the standard-model and H¹ formulas keep the genuine coefficient maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples
attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.ParameterTangentH1

open ParameterTangentDeformation

variable {X T S : Scheme.{u}} (p : X ⟶ T) [Flat p] (s : T ⟶ S) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

local instance residueTangentModule : Module κ (DottedTangentArrow s x) :=
  inferInstanceAs (Module (T.residueField x) (DottedTangentArrow s x))

/-- The actual lifted coefficient change used by the original six-term endpoint. -/
def liftCoefficients :
    coordBase (Λ := κ)
        (FGModuleCat.of κ κ) ⟶
      coordBase (Λ := κ)
        (FGModuleCat.of κ (ULift.{u} κ)) :=
  (squareZeroExtensionArtinian κ κ).map
    (fgModuleCatULiftSelfIso (k := κ)).inv

/-- The original tangent arrow on the literal lifted dual-number base. -/
def liftedArrow (θ : DottedTangentArrow s x) :
    PointedArrow x
      (FGModuleCat.of κ (ULift.{u} κ)) :=
  ⟨baseSpecMap (liftCoefficients x) ≫ (tangentArrow s x θ).val, by
    rw [← Category.assoc, residueSpecMap_naturality]
    exact (tangentArrow s x θ).property⟩

/-- The actual lifted family deformation, in the exact native endpoint fibre. -/
def liftedObject (θ : DottedTangentArrow s x) :=
  coordinateObject p x
    (FGModuleCat.of κ (ULift.{u} κ))
    (liftedArrow s x θ)

/-- Its total space is the original family pulled back along the specified
native coefficient change and the original tangent arrow. -/
theorem liftedObject_scheme (θ : DottedTangentArrow s x) :
    (liftedObject p s x θ).val.scheme =
      pullback p (baseSpecMap (liftCoefficients x) ≫ (tangentArrow s x θ).val) := rfl

/-- The canonical parameter tangent map to the exact native endpoint tangent module. -/
def tangentEndpointLinearMap :
    DottedTangentArrow s x →ₗ[κ]
      ↥(StandardSchemeTangent.endpointTangentModule (Λ := κ)
        (fibre p x).hom) :=
  (tangentModuleMapAt
    (schemeDeformationBased (Λ := κ) (fibre p x))
    (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x))
    (fgModuleCatULiftSelfIso (k := κ)).inv).comp
      (tangentLinearMap p s x)

/-- The endpoint value is the original native class of the actual pulled family. -/
theorem tangentEndpointLinearMap_apply (θ : DottedTangentArrow s x) :
    tangentEndpointLinearMap p s x θ =
      tangentClassAt
        (schemeDeformationBased (Λ := κ) (fibre p x))
        (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x))
        (FGModuleCat.of κ (ULift.{u} κ))
        (liftedObject p s x θ) :=
  coordinateClass_map p x (fgModuleCatULiftSelfIso (k := κ)).inv
    (tangentArrow s x θ) (liftedArrow s x θ) rfl

/-- The actual standard extension class of the pulled family, retaining the
native ULift-to-rank-one coefficient transport. -/
theorem tangentEndpointStd_apply (θ : DottedTangentArrow s x) :
    letI := StandardCurveCotangentExt.nativeExtModule (fibre p x).hom
      (InvertibleExtCancellation.unit (fibre p x).left)
    StandardSchemeTangent.endpointTangentLinearEquivStd (Λ := κ)
        (fibre p x).hom (tangentEndpointLinearMap p s x θ) =
      schemeTangentExtRankOneLinearEquiv (fibre p x)
        ((schemeTangentExtFunctor (fibre p x)).map
          (fgModuleCatULiftSelfIso (k := κ)).hom
          (fiberExtClassAt (fibre p x)
            (FGModuleCat.of κ (ULift.{u} κ))
            (liftedObject p s x θ))) := by
  rw [tangentEndpointLinearMap_apply]
  exact StandardSchemeTangent.endpointTangentLinearEquivStd_tangentClassAt _ _

/-- The actual family class as a linear map to original tangent H¹. -/
def tangentH1LinearMap [IsCurve κ (fibre p x).hom]
    [Smooth (fibre p x).hom] :
    DottedTangentArrow s x →ₗ[κ]
      cohomologyOverField κ (fibre p x).hom
        (CurveTangentLineGeometry.tangentLine (fibre p x).hom) 1 :=
  (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
    (fibre p x).hom).toLinearMap.comp (tangentEndpointLinearMap p s x)

set_option maxRecDepth 1024 in
/-- Its value is the original standard H¹ classifier applied to the
genuine native pulled-family class. The coefficient-level standard Ext
formula is retained separately in `tangentEndpointStd_apply`. -/
theorem tangentH1LinearMap_apply [IsCurve κ (fibre p x).hom]
    [Smooth (fibre p x).hom] (θ : DottedTangentArrow s x) :
    tangentH1LinearMap p s x θ =
      StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
        (fibre p x).hom
        (tangentClassAt
          (schemeDeformationBased (Λ := κ) (fibre p x))
          (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x))
          (FGModuleCat.of κ (ULift.{u} κ)) (liftedObject p s x θ)) :=
  congrArg (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
    (fibre p x).hom) (tangentEndpointLinearMap_apply p s x θ)

end M9Native.ParameterTangentH1
