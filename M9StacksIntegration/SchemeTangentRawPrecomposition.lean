module

public import M9StacksIntegration.StandardSchemeTangent
public import M9StacksIntegration.SchemeRawDifferenceClass

/-!
# Genuine raw extension annihilation at the original tangent endpoint

The original native ULift tangent classifier is the original raw
k-extension class, followed by its actual three coefficient maps:
the coordinate pulled-ideal isomorphism, the coefficient functor on the
ULift self-isomorphism, and the original rank-one coefficient isomorphism.
Annihilation by any actual derived arrow is therefore preserved.
No equality of independently constructed coefficient comparisons or
cotangent-image condition is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples
open AlgebraicGeometry.RingedSpaceThickening

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.SchemeTangentRawPrecomposition

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

/-- The literal three genuine native coefficient isomorphisms for the ULift endpoint. -/
def rankOneULiftCoefficientIso :
    SchemeDeformationCategory.pulledIdeal
      (coordBase (Λ := k) (FGModuleCat.of k (ULift.{u} k))) (Over.mk f) ≅
        InvertibleExtCancellation.unit X :=
  coordPulledIdealIso (Λ := k) (FGModuleCat.of k (ULift.{u} k)) (Over.mk f) ≪≫
    (coefficientSheafFunctor f).mapIso (fgModuleCatULiftSelfIso (k := k)) ≪≫
      coefficientSheafRankOneIso (Over.mk f)

/-- The original native rank-one linear comparison is actual coefficient postcomposition. -/
theorem rankOneLinearEquiv_apply_hom
    (xi : schemeTangentExtAt (Over.mk f) (FGModuleCat.of k k)) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    schemeTangentExtRankOneLinearEquiv (Over.mk f) xi =
      xi ≫ ((DerivedCategory.singleFunctor X.Modules 0).map
        (coefficientSheafRankOneIso (Over.mk f)).hom)⟦(1 : ℤ)⟧' := by
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    modulesLinear k (Over.mk f)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0
  let T := shiftFunctor
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (1 : ℤ)
  with_unfolding_all
    exact (Linear.homCongr_apply k (Iso.refl _)
      (T.mapIso (S.mapIso (coefficientSheafRankOneIso (Over.mk f)))) xi).trans
        (congrArg (fun z => z ≫ T.map (S.map (coefficientSheafRankOneIso (Over.mk f)).hom))
          (Category.id_comp xi))

/-- The exact original endpoint has the original raw class and literal actual coefficient maps. -/
theorem endpoint_class_postcompose
    (x : (schemeDeformationCategoryProjection (Λ := k) (k := k) (Over.mk f)).Fiber
      (coordBase (Λ := k) (FGModuleCat.of k (ULift.{u} k)))) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    StandardSchemeTangent.endpointTangentLinearEquivStd (Λ := k) f
        (tangentClassAt
          (schemeDeformationBased (Λ := k) (Over.mk f))
          (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
          (FGModuleCat.of k (ULift.{u} k)) x) =
      ((SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk f)
          (FGModuleCat.of k (ULift.{u} k)) x ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map
          (coordPulledIdealIso (Λ := k) (FGModuleCat.of k (ULift.{u} k)) (Over.mk f)).hom)⟦(1 : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map
          ((coefficientSheafFunctor f).map (fgModuleCatULiftSelfIso (k := k)).hom))⟦(1 : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map
          (coefficientSheafRankOneIso (Over.mk f)).hom)⟦(1 : ℤ)⟧' := by
  let V := FGModuleCat.of k (ULift.{u} k)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0
  let T := shiftFunctor
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (1 : ℤ)
  let a := T.map (S.map ((coefficientSheafFunctor f).map (fgModuleCatULiftSelfIso (k := k)).hom))
  let b := T.map (S.map (coefficientSheafRankOneIso (Over.mk f)).hom)
  have h0 := StandardSchemeTangent.endpointTangentLinearEquivStd_tangentClassAt (Λ := k) f x
  have h1 := rankOneLinearEquiv_apply_hom f
    ((schemeTangentExtFunctor (Over.mk f)).map (fgModuleCatULiftSelfIso (k := k)).hom
      (fiberExtClassAt (Over.mk f) V x))
  have h2 := schemeTangentExtFunctor_map_apply (Over.mk f)
    (fgModuleCatULiftSelfIso (k := k)).hom (fiberExtClassAt (Over.mk f) V x)
  have h3 := SchemeRawDifferenceClass.coefficient_rawFiberClass_hom (Λ := k) (Over.mk f) V x
  exact h0.trans (h1.trans
    ((congrArg (fun z => z ≫ b) h2).trans
      (congrArg (fun z => (z ≫ a) ≫ b) h3.symm)))

/-- Any actual derived precomposition annihilating the original raw class annihilates the endpoint. -/
theorem precomp_endpoint_eq_zero_of_raw_eq_zero
    (x : (schemeDeformationCategoryProjection (Λ := k) (k := k) (Over.mk f)).Fiber
      (coordBase (Λ := k) (FGModuleCat.of k (ULift.{u} k))))
    (T : DerivedCategory X.Modules) (q : T ⟶ StandardSmoothCotangent.nativeObject f)
    (hraw : q ≫ SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk f)
      (FGModuleCat.of k (ULift.{u} k)) x = 0) :
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    q ≫ StandardSchemeTangent.endpointTangentLinearEquivStd (Λ := k) f
      (tangentClassAt
        (schemeDeformationBased (Λ := k) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
        (FGModuleCat.of k (ULift.{u} k)) x) = 0 := by
  rw [endpoint_class_postcompose]
  simp only [← Category.assoc, hraw, Limits.zero_comp]


end M9Native.SchemeTangentRawPrecomposition
