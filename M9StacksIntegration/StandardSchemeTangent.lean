module

public import M9StacksIntegration.StandardCurveCotangentExt
public import M9StacksIntegration.NativeHomScalars
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquivExt
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact

/-!
# The original standard scheme tangent classifier

The native rank-one classifier and its genuine change of coefficients give
the original standard-model extension class. Its value on a deformation
is the native 08UC difference class against the actual trivial deformation.
The checked smooth-curve comparison then identifies this class with tangent
H¹, preserving the original scalar structures. No relation on tangent
images, cotangent derivatives, or generators is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples
open AlgebraicGeometry.RingedSpaceThickening

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.StandardSchemeTangent

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

/-- The canonical predeformation hypothesis is proved by the native scheme category. -/
local instance nativePredeformation :
    Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
  ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩

/-- The native scheme category supplies the canonical Schlessinger condition. -/
local instance nativeS2 :
    Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
  ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩

/-- The original coefficient sheaf is the actual tensor unit. -/
theorem structureSheaf_eq_unit :
    structureSheafModules X = InvertibleExtCancellation.unit X := rfl

/-- The two original standard Ext module structures agree definitionally. -/
theorem originalExtModule_eq (G : X.Modules) :
    schemeTangentExtStdModule (Over.mk f) G =
      StandardCurveCotangentExt.nativeExtModule f G := rfl

/-- Their actual scalar multiplications agree, with no replacement action. -/
theorem originalExt_smul_eq (G : X.Modules) (c : k)
    (ξ : extOneNaiveCotangent f.toLRSHom.toShHom G) :
    (letI : Module k (extOneNaiveCotangent f.toLRSHom.toShHom G) :=
        schemeTangentExtStdModule (Over.mk f) G;
      (c • ξ : extOneNaiveCotangent f.toLRSHom.toShHom G)) =
      (letI : Module k (extOneNaiveCotangent f.toLRSHom.toShHom G) :=
          StandardCurveCotangentExt.nativeExtModule f G;
        (c • ξ : extOneNaiveCotangent f.toLRSHom.toShHom G)) := rfl

/-- The actual pulled ideal is identified with the structure sheaf in two native steps. -/
def coefficientIso :
    SchemeDeformationCategory.pulledIdeal
      (coordBase (Λ := Λ) (FGModuleCat.of k k)) (Over.mk f) ≅
        InvertibleExtCancellation.unit X :=
  coordPulledIdealIso (Λ := Λ) (FGModuleCat.of k k) (Over.mk f) ≪≫
    coefficientSheafRankOneIso (Over.mk f)

/-- The actual native coefficient transport on original standard extension classes. -/
def coefficientExtAddEquiv :
    extOneNaiveCotangent f.toLRSHom.toShHom
        (SchemeDeformationCategory.pulledIdeal
          (coordBase (Λ := Λ) (FGModuleCat.of k k)) (Over.mk f)) ≃+
      extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X) := by
  letI : Module k (extOneNaiveCotangent (Over.mk f).hom.toLRSHom.toShHom
      (structureSheafModules (Over.mk f).left)) :=
    schemeTangentExtStdModule (Over.mk f) (structureSheafModules (Over.mk f).left)
  exact (coordExtCoefficientsAddEquiv (Λ := Λ) (Over.mk f) (FGModuleCat.of k k)).trans
    (schemeTangentExtRankOneLinearEquiv (Over.mk f)).toAddEquiv

/-- Both native coefficient changes are literal postcomposition by their composite. -/
theorem coefficientExtAddEquiv_apply
    (ξ : extOneNaiveCotangent f.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal
        (coordBase (Λ := Λ) (FGModuleCat.of k k)) (Over.mk f))) :
    coefficientExtAddEquiv (Λ := Λ) f ξ =
      ξ ≫ ((DerivedCategory.singleFunctor X.Modules 0).map
        (coefficientIso (Λ := Λ) f).hom)⟦(1 : ℤ)⟧' := by
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    modulesLinear k (Over.mk f)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0
  let T := shiftFunctor
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (1 : ℤ)
  let a := coordPulledIdealIso (Λ := Λ) (FGModuleCat.of k k) (Over.mk f)
  let b := coefficientSheafRankOneIso (Over.mk f)
  have h₁ := Linear.homCongr_apply k (Iso.refl _) (T.mapIso (S.mapIso b))
    (coordExtCoefficientsAddEquiv (Λ := Λ) (Over.mk f) (FGModuleCat.of k k) ξ)
  have h₂ : T.map (S.map a.hom) ≫ T.map (S.map b.hom) =
      T.map (S.map (a.hom ≫ b.hom)) :=
    (T.map_comp (S.map a.hom) (S.map b.hom)).symm.trans
      (congrArg T.map (S.map_comp a.hom b.hom).symm)
  exact h₁.trans
    ((congrArg (fun z => z ≫ T.map (S.map b.hom))
      ((Category.id_comp _).trans
        (coordExtCoefficientsAddEquiv_apply (Λ := Λ) (Over.mk f) (FGModuleCat.of k k) ξ))).trans
      ((Category.assoc ξ (T.map (S.map a.hom)) (T.map (S.map b.hom))).trans
        (congrArg (fun z => ξ ≫ z) h₂)))

/-- The original native tangent classifier in the standard derived model. -/
def tangentLinearEquivStd :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f) ≃ₗ[k]
      extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X) :=
  (schemeTangentSpaceLinearEquivExtRankOne (Λ := Λ) (Over.mk f)).trans
    (schemeTangentExtRankOneLinearEquiv (Over.mk f))

/-- This is precisely the two original native standard-model linear maps. -/
theorem tangentLinearEquivStd_eq :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivStd (Λ := Λ) f =
      (schemeTangentSpaceLinearEquivExtRankOne (Λ := Λ) (Over.mk f)).trans
        (schemeTangentExtRankOneLinearEquiv (Over.mk f)) := rfl

/-- The original standard classifier is the native class map on every tangent vector. -/
theorem tangentLinearEquivStd_apply
    (v : schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f)) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivStd (Λ := Λ) f v =
      schemeTangentExtRankOneLinearEquiv (Over.mk f)
        (tangentExtClassAt (Over.mk f) (FGModuleCat.of k k) v) :=
  congrArg (schemeTangentExtRankOneLinearEquiv (Over.mk f))
    (tangentSpaceLinearEquivOfNaturalBijection_apply
      (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation
      (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
      (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
      (fun g z => tangentExtClassAt_naturality (Over.mk f) g z)
      (bijective_tangentExtClassAt (Over.mk f) (FGModuleCat.of k k)) v)

/-- The class of a deformation is the original 08UC difference against the
native trivial deformation, followed by the actual coefficient transport. -/
theorem tangentLinearEquivStd_classOf
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)).Fiber
      (coordBase (FGModuleCat.of k k))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivStd (Λ := Λ) f
        (classOf (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (schemeDeformation_cofibered (Over.mk f)) x) =
      coefficientExtAddEquiv (Λ := Λ) f
        (differenceClass
          (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _) x)
          (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _)
            (trivialFiberAt (Over.mk f) (FGModuleCat.of k k)))) := by
  exact congrArg (schemeTangentExtRankOneLinearEquiv (Over.mk f))
    ((tangentSpaceLinearEquivOfNaturalBijection_apply
      (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation
      (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
      (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
      (fun g z => tangentExtClassAt_naturality (Over.mk f) g z)
      (bijective_tangentExtClassAt (Over.mk f) (FGModuleCat.of k k))
      (classOf (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f)) x)).trans
      (tangentExtClassAt_classOf (Over.mk f) _ x))

/-- The same formula records the actual coefficient-sheaf map explicitly. -/
theorem tangentLinearEquivStd_classOf_hom
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)).Fiber
      (coordBase (FGModuleCat.of k k))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivStd (Λ := Λ) f
        (classOf (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (schemeDeformation_cofibered (Over.mk f)) x) =
      differenceClass
          (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _) x)
          (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _)
            (trivialFiberAt (Over.mk f) (FGModuleCat.of k k))) ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map
          (coefficientIso (Λ := Λ) f).hom)⟦(1 : ℤ)⟧' :=
  (tangentLinearEquivStd_classOf (Λ := Λ) f x).trans
    (coefficientExtAddEquiv_apply (Λ := Λ) f _)

/-- The actual native scheme deformation tangent space identifies with actual tangent H¹. -/
def tangentLinearEquivH1 [IsCurve k f] [Smooth f] :
    schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  let := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
  exact (tangentLinearEquivStd (Λ := Λ) f).trans
    (StandardCurveCotangentExt.tangentOneLinearEquiv f)

/-- The H¹ comparison uses exactly the original standard extension class. -/
theorem tangentLinearEquivH1_apply [IsCurve k f] [Smooth f]
    (v : schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f)) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivH1 (Λ := Λ) f v =
      StandardCurveCotangentExt.tangentOneLinearEquiv f
        (tangentLinearEquivStd (Λ := Λ) f v) := rfl

/-- A genuine deformation is sent to the H¹ image of its actual 08UC difference class. -/
theorem tangentLinearEquivH1_classOf [IsCurve k f] [Smooth f]
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)).Fiber
      (coordBase (FGModuleCat.of k k))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivH1 (Λ := Λ) f
        (classOf (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (schemeDeformation_cofibered (Over.mk f)) x) =
      StandardCurveCotangentExt.tangentOneLinearEquiv f
        (coefficientExtAddEquiv (Λ := Λ) f
          (differenceClass
            (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _) x)
            (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _)
              (trivialFiberAt (Over.mk f) (FGModuleCat.of k k))))) :=
  congrArg (StandardCurveCotangentExt.tangentOneLinearEquiv f)
    (tangentLinearEquivStd_classOf (Λ := Λ) f x)

/-- The lifted dual-number tangent space retains the native rank-one comparison. -/
def liftedTangentLinearEquivStd :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentSpaceArtinian Λ k
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))) ≃ₗ[k]
      extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X) :=
  (tangentSpaceArtinianLinearEquivUnlifted
    (schemeDeformationBased (Λ := Λ) (Over.mk f))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation
    (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))).trans
      (tangentLinearEquivStd (Λ := Λ) f)

/-- The lifted dual-number tangent space identifies with the same actual tangent H¹. -/
def liftedTangentLinearEquivH1 [IsCurve k f] [Smooth f] :
    tangentSpaceArtinian Λ k
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  let := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
  exact (liftedTangentLinearEquivStd (Λ := Λ) f).trans
    (StandardCurveCotangentExt.tangentOneLinearEquiv f)

/-- The exact source endpoint module in the native scheme-morphism six-term sequence. -/
abbrev endpointTangentModule :=
  tangentModuleAt.{u, u, u}
    (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f))
    (FGModuleCat.of k (ULift.{u} k))

/-- The genuine native carrier comparison identifies the endpoint with lifted dual numbers. -/
def endpointTangentLinearEquivLifted :
    ↥(endpointTangentModule (Λ := Λ) f) ≃ₗ[k]
      tangentSpaceArtinian Λ k
        (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (schemeDeformation_cofibered (Over.mk f))) :=
  associatedTangentSpaceCarrierLinearEquiv
    (schemeDeformationBased (Λ := Λ) (Over.mk f))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation
    (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))

/-- The exact six-term endpoint maps to the original standard extension group. -/
def endpointTangentLinearEquivStd :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    ↥(endpointTangentModule (Λ := Λ) f) ≃ₗ[k]
      extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X) :=
  (endpointTangentLinearEquivLifted (Λ := Λ) f).trans
    (liftedTangentLinearEquivStd (Λ := Λ) f)

/-- The exact six-term endpoint identifies with actual tangent H¹. -/
def endpointTangentLinearEquivH1 [IsCurve k f] [Smooth f] :
    ↥(endpointTangentModule (Λ := Λ) f) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  let := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
  exact (endpointTangentLinearEquivStd (Λ := Λ) f).trans
    (StandardCurveCotangentExt.tangentOneLinearEquiv f)

/-- The endpoint H¹ comparison uses exactly this standard-model classifier. -/
theorem endpointTangentLinearEquivH1_apply [IsCurve k f] [Smooth f]
    (v : ↥(endpointTangentModule (Λ := Λ) f)) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    endpointTangentLinearEquivH1 (Λ := Λ) f v =
      StandardCurveCotangentExt.tangentOneLinearEquiv f
        (endpointTangentLinearEquivStd (Λ := Λ) f v) := rfl

/-- The lifted endpoint classifier commutes with the genuine rank-one coefficient map. -/
theorem endpointTangentLinearEquivStd_apply
    (v : ↥(endpointTangentModule (Λ := Λ) f)) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    endpointTangentLinearEquivStd (Λ := Λ) f v =
      schemeTangentExtRankOneLinearEquiv (Over.mk f)
        ((schemeTangentExtFunctor (Over.mk f)).map (fgModuleCatULiftSelfIso (k := k)).hom
          (liftedFamily
            (schemeDeformationBased (Λ := Λ) (Over.mk f))
            (isDeformationCategory_schemeDeformationCategoryProjection
              (Λ := Λ) (Over.mk f)).predeformation
            (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
            (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
            (FGModuleCat.of k (ULift.{u} k)) v)) := by
  unfold endpointTangentLinearEquivStd endpointTangentLinearEquivLifted
    liftedTangentLinearEquivStd tangentSpaceArtinianLinearEquivUnlifted
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [tangentLinearEquivStd_apply]
  change schemeTangentExtRankOneLinearEquiv (Over.mk f)
      (liftedFamily
        (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection
          (Λ := Λ) (Over.mk f)).predeformation
        (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
        (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
        (FGModuleCat.of k k)
        (((associatedTangentSpaceModuleStructureUnlifted
          (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (Λ := Λ) (Over.mk f)).predeformation
          (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))).functor.map
            (fgModuleCatULiftSelfIso (k := k)).hom) v)) = _
  exact congrArg (schemeTangentExtRankOneLinearEquiv (Over.mk f))
    (liftedFamily_natural
      (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection
        (Λ := Λ) (Over.mk f)).predeformation
      (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
      (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
      (fun g z => tangentExtClassAt_naturality (Over.mk f) g z)
      (fgModuleCatULiftSelfIso (k := k)).hom v)

/-- The original ULift class is the generic-coefficient native difference class,
pushed along the genuine rank-one coefficient isomorphism. -/
theorem endpointTangentLinearEquivStd_tangentClassAt
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)).Fiber
      (coordBase (FGModuleCat.of k (ULift.{u} k)))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    endpointTangentLinearEquivStd (Λ := Λ) f
        (tangentClassAt
          (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f))
          (FGModuleCat.of k (ULift.{u} k)) x) =
      schemeTangentExtRankOneLinearEquiv (Over.mk f)
        ((schemeTangentExtFunctor (Over.mk f)).map (fgModuleCatULiftSelfIso (k := k)).hom
          (fiberExtClassAt (Over.mk f) (FGModuleCat.of k (ULift.{u} k)) x)) := by
  rw [endpointTangentLinearEquivStd_apply]
  have h : liftedFamily
      (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection
        (Λ := Λ) (Over.mk f)).predeformation
      (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
      (schemeTangentExtFunctor (Over.mk f)) (tangentExtClassAt (Over.mk f))
      (FGModuleCat.of k (ULift.{u} k))
      (tangentClassAt
        (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f))
        (FGModuleCat.of k (ULift.{u} k)) x) =
        fiberExtClassAt (Over.mk f) (FGModuleCat.of k (ULift.{u} k)) x := by
    change tangentExtClassAt (Over.mk f) (FGModuleCat.of k (ULift.{u} k))
      (cast (liftCarrierEq
        (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection
          (Λ := Λ) (Over.mk f)).predeformation
        (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
        (FGModuleCat.of k (ULift.{u} k)))
        (cast (liftCarrierEq
          (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (Λ := Λ) (Over.mk f)).predeformation
          (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))
          (FGModuleCat.of k (ULift.{u} k))).symm
          (classOf (schemeDeformationBased (Λ := Λ) (Over.mk f))
            (schemeDeformation_cofibered (Over.mk f)) x))) = _
    rw [cast_symm_cancel]
    exact tangentExtClassAt_classOf (Over.mk f) _ x
  rw [h]

/-- The actual six-term endpoint H¹ value has the same proved ULift class formula. -/
theorem endpointTangentLinearEquivH1_tangentClassAt [IsCurve k f] [Smooth f]
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk f)).Fiber
      (coordBase (FGModuleCat.of k (ULift.{u} k)))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    endpointTangentLinearEquivH1 (Λ := Λ) f
        (tangentClassAt
          (schemeDeformationBased (Λ := Λ) (Over.mk f))
          (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f))
          (FGModuleCat.of k (ULift.{u} k)) x) =
      StandardCurveCotangentExt.tangentOneLinearEquiv f
        (schemeTangentExtRankOneLinearEquiv (Over.mk f)
          ((schemeTangentExtFunctor (Over.mk f)).map (fgModuleCatULiftSelfIso (k := k)).hom
            (fiberExtClassAt (Over.mk f) (FGModuleCat.of k (ULift.{u} k)) x))) :=
  congrArg (StandardCurveCotangentExt.tangentOneLinearEquiv f)
    (endpointTangentLinearEquivStd_tangentClassAt (Λ := Λ) f x)

end M9Native.StandardSchemeTangent
