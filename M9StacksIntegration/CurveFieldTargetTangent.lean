module

public import M9StacksIntegration.CurveFieldTargetComparison
public import M9StacksIntegration.StandardSchemeTangent
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Applications.TangentClassCoordinateMap
public import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicStackEssSurj

/-!
# Linear coordinates on the actual ground-field Curves tangent

The equivalence is induced by the genuine original three-stage functor.
Its value on every marked square-zero deformation is the literal native
tangent class of that functor's image. The inverse and the already-proved
standard scheme classifier identify this actual target with native H1.

The coefficient field k is retained. Only the genuine relative finite
type and quasi-compact properties of Spec k to Spec K are used; no map
to the integer spectrum is treated as finite type. Original Curves
algebraicity remains the explicit pending geometric producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local instance 100000] HasDerivedCategory.standard

universe u
namespace M9Native.CurveFieldTargetTangent

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ (curvesFiberedCategory B hZ).val)
  {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (iS : Spec (.of k) ⟶ Spec (.of K))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

open CurveFieldTargetComparison

local instance originalCurveProper : IsProper (Over.mk f).hom :=
  inferInstanceAs (IsProper f)

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

set_option maxHeartbeats 1600000 in
/-- The underlying comparison is literally original 0DZU, the original
small-model functor, and the inverse actual field-base comparison. -/
theorem basedComparison_functor :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    (basedComparison B hZ hK hAlg hk iS f).toFunctor =
      (schemeDeformationToCurves B hZ (Over.mk f) hk
          (IsCurve.topologicalKrullDim_eq_one (f := f)).le
          (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) ⋙
        (CurveFormalSmall.comparison B hZ hk f).hom.functor) ⋙
      (comparison B hZ hK hAlg hk iS f).inv.functor := rfl

/-- The original small-point category over the unchanged Artin k-base. -/
abbrev smallBased :=
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  BasedCategory.ofFunctor (CurveFormalSmall.predeformation B hZ hk f).projection

/-- Original 0DZU followed by the original small-model comparison. -/
def schemeToSmall : schemeDeformationBased (Λ := k) (Over.mk f) ⥤ᵇ smallBased B hZ hk f := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  let φ := schemeDeformationToCurvesBased B hZ (Over.mk f) hk
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
  let ψ : BasedCategory.ofFunctor (CurveFormalToCurves.pointPredeformation B hZ hk f).projection
      ⥤ᵇ smallBased B hZ hk f :=
    ⟨(CurveFormalSmall.comparison B hZ hk f).hom.functor,
      (CurveFormalSmall.comparison B hZ hk f).hom.w⟩
  exact BasedFunctor.comp φ ψ

/-- The actual ground-field comparison read towards the original small point. -/
def fieldToSmall :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection
      ⥤ᵇ smallBased B hZ hk f := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  exact ⟨(comparison B hZ hK hAlg hk iS f).hom.functor,
    (comparison B hZ hK hAlg hk iS f).hom.w⟩

set_option maxHeartbeats 1600000 in
/-- Projection of the actual field-stack image is canonically the
direct original 0DZU/small image, in the SAME marked Artinian fibre. -/
def projectedImageIso (A : ArtinianLocalAlgCat.{u,u,u} k k)
    (x : (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Fiber A) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    (fiberFunctor (fieldToSmall B hZ hK hAlg hk iS f) A).obj
        ((fiberFunctor (basedComparison B hZ hK hAlg hk iS f) A).obj x) ≅
      (fiberFunctor (schemeToSmall B hZ hk f) A).obj x := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  let E := comparison B hZ hK hAlg hk iS f
  let y := (schemeToSmall B hZ hk f).toFunctor.obj x.val
  let e := E.counitIso.app y
  have hy : (CurveFormalSmall.predeformation B hZ hk f).projection.obj y = A :=
    (BasedFunctor.w_obj (schemeToSmall B hZ hk f) x.val).trans x.property
  have he : (CurveFormalSmall.predeformation B hZ hk f).projection.IsHomLift (𝟙 A) e.hom := by
    have he₀ : (CurveFormalSmall.predeformation B hZ hk f).projection.IsHomLift
        (𝟙 ((CurveFormalSmall.predeformation B hZ hk f).projection.obj y)) e.hom :=
      E.isHomLift_counitIso_hom_app y
    exact (congrArg (fun U =>
      (CurveFormalSmall.predeformation B hZ hk f).projection.IsHomLift (𝟙 U) e.hom) hy).mp he₀
  exact Functor.fiberIsoOfLift (CurveFormalSmall.predeformation B hZ hk f).projection e he

omit [Smooth f] in
/-- The actual ground-field-stack point has the native deformation
structure, using only genuine relative point geometry. -/
theorem deformationStructure (hfinite : LocallyOfFiniteType iS) (hqc : QuasiCompact iS) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    IsDeformationCategory (predeformation B hZ hK hAlg hk iS f).projection := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  exact isDeformationCategory_predeformationCategory_of_isAlgebraicStack B (Spec (.of K)) hK
    (fieldStack B hZ hK hAlg) iS (fieldPoint B hZ hK hAlg hk iS f)
    (fieldPoint_lies_over B hZ hK hAlg hk iS f)
    (by simpa using hfinite) (by simpa using hqc)

variable (hfinite : LocallyOfFiniteType iS) (hqc : QuasiCompact iS)

/-- The actual composite induces a k-linear equivalence on every
native coefficient module. Fibre equivalence is proved, not assumed. -/
def tangentEquivalence (M : FGModuleCat.{u} k) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    ↥(tangentModuleAt.{u,u,u} (schemeDeformationBased (Λ := k) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f)) M) ≃ₗ[k]
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M) := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  let φ := basedComparison B hZ hK hAlg hk iS f
  letI : φ.toFunctor.IsEquivalence :=
    (schemeEquivalence B hZ hK hAlg hk iS f).isEquivalence_hom_functor
  let A := (squareZeroExtensionArtinian.{u,u,u} k k).obj M
  exact tangentLinearEquivOfFiberEquivalence.{u,u,u}
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
    (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) φ M
    (full_fiberFunctor φ A) (faithful_fiberFunctor φ A)
    (essSurj_fiberFunctor (schemeDeformation_cofibered (Over.mk f)) φ A)

/-- On a genuine marked deformation this is exactly the native tangent
class of the actual three-stage image, with the same square-zero base. -/
theorem tangentEquivalence_tangentClassAt (M : FGModuleCat.{u} k)
    (x : (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Fiber
      ((squareZeroExtensionArtinian.{u,u,u} k k).obj M)) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc M
      (tangentClassAt.{u,u,u} (schemeDeformationBased (Λ := k) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f)) M x) =
    tangentClassAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M
      ((fiberFunctor (basedComparison B hZ hK hAlg hk iS f)
        ((squareZeroExtensionArtinian.{u,u,u} k k).obj M)).obj x) :=
  tangentMapAt_tangentClassAt.{u,u,u}
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
    (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
    (basedComparison B hZ hK hAlg hk iS f) M x

omit [Smooth f] in
/-- Genuine projection to the original SMALL fibre reflects equality
of actual field tangent classes, with no small-point tangent module
or finite-type-to-integers assumption. -/
theorem fieldClass_eq_iff_projection_isomorphic (M : FGModuleCat.{u} k)
    (x y :
      letI := (predeformation B hZ hK hAlg hk iS f).category
      (predeformation B hZ hK hAlg hk iS f).projection.Fiber
        ((squareZeroExtensionArtinian.{u,u,u} k k).obj M)) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
        (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M x =
      tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
        (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M y ↔
    IsIsomorphic
      ((fiberFunctor (fieldToSmall B hZ hK hAlg hk iS f)
        ((squareZeroExtensionArtinian.{u,u,u} k k).obj M)).obj x)
      ((fiberFunctor (fieldToSmall B hZ hK hAlg hk iS f)
        ((squareZeroExtensionArtinian.{u,u,u} k k).obj M)).obj y) := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  let := (CurveFormalSmall.predeformation B hZ hk f).category
  let φ := fieldToSmall B hZ hK hAlg hk iS f
  let : φ.toFunctor.IsEquivalence := (comparison B hZ hK hAlg hk iS f).isEquivalence_hom_functor
  let A := (squareZeroExtensionArtinian.{u,u,u} k k).obj M
  let F := fiberFunctor φ A
  let : F.Full := full_fiberFunctor φ A
  let : F.Faithful := faithful_fiberFunctor φ A
  constructor
  · intro h
    obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M x y).mp h
    exact ⟨F.mapIso e⟩
  · rintro ⟨e⟩
    exact (tangentClassAt_eq_iff.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) M x y).mpr
      ⟨(Functor.FullyFaithful.ofFullyFaithful F).preimageIso e⟩

/-- The target tangent has coordinates in the actual original native
tangent-line H1 over the unchanged coefficient field. -/
def tangentLinearEquivH1 :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
      (FGModuleCat.of k (ULift.{u} k))) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 :=
  (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc
    (FGModuleCat.of k (ULift.{u} k))).symm.trans
      (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f)

/-- The H1 coordinate of an actual image is the original standard
classifier of the same original marked scheme deformation. -/
theorem tangentLinearEquivH1_image_class
    (x : (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Fiber
      ((squareZeroExtensionArtinian.{u,u,u} k k).obj (FGModuleCat.of k (ULift.{u} k)))) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
      (tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
        (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
        (FGModuleCat.of k (ULift.{u} k))
        ((fiberFunctor (basedComparison B hZ hK hAlg hk iS f)
          ((squareZeroExtensionArtinian.{u,u,u} k k).obj
            (FGModuleCat.of k (ULift.{u} k)))).obj x)) =
    StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f
      (tangentClassAt.{u,u,u} (schemeDeformationBased (Λ := k) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
        (FGModuleCat.of k (ULift.{u} k)) x) := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  rw [← tangentEquivalence_tangentClassAt B hZ hK hAlg hk iS f hfinite hqc]
  exact congrArg (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f)
    ((tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc
      (FGModuleCat.of k (ULift.{u} k))).symm_apply_apply _)

/-- The literal native standard extension-class formula is retained
after the actual field-stack target transport. -/
theorem tangentLinearEquivH1_image_class_standard
    (x : (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Fiber
      ((squareZeroExtensionArtinian.{u,u,u} k k).obj (FGModuleCat.of k (ULift.{u} k)))) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := StandardCurveCotangentExt.nativeExtModule f (InvertibleExtCancellation.unit X)
    tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
      (tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
        (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
        (FGModuleCat.of k (ULift.{u} k))
        ((fiberFunctor (basedComparison B hZ hK hAlg hk iS f)
          ((squareZeroExtensionArtinian.{u,u,u} k k).obj
            (FGModuleCat.of k (ULift.{u} k)))).obj x)) =
    StandardCurveCotangentExt.tangentOneLinearEquiv f
      (schemeTangentExtRankOneLinearEquiv (Over.mk f)
        ((schemeTangentExtFunctor (Over.mk f)).map (fgModuleCatULiftSelfIso (k := k)).hom
          (fiberExtClassAt (Over.mk f) (FGModuleCat.of k (ULift.{u} k)) x))) :=
  (tangentLinearEquivH1_image_class B hZ hK hAlg hk iS f hfinite hqc x).trans
    (StandardSchemeTangent.endpointTangentLinearEquivH1_tangentClassAt (Λ := k) f x)

/-- The actual coefficient isomorphism gives a genuine linear
equivalence from rank-one coordinates to the native ULift endpoint. -/
def coefficientLinearEquiv :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) (FGModuleCat.of k k)) ≃ₗ[k]
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
      (FGModuleCat.of k (ULift.{u} k))) := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  let T := BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection
  let hT := deformationStructure B hZ hK hAlg hk iS f hfinite hqc
  let e := fgModuleCatULiftSelfIso (k := k)
  refine
    { toLinearMap := tangentModuleMapAt.{u,u,u} T hT e.inv
      invFun := tangentModuleMapAt.{u,u,u} T hT e.hom
      left_inv := ?_
      right_inv := ?_ }
  · intro t
    exact (tangentModuleMapAt_comp.{u,u,u} T hT e.inv e.hom t).symm.trans
      ((congrArg (fun a => tangentModuleMapAt.{u,u,u} T hT a t) e.inv_hom_id).trans
        (tangentModuleMapAt_id.{u,u,u} T hT t))
  · intro t
    exact (tangentModuleMapAt_comp.{u,u,u} T hT e.hom e.inv t).symm.trans
      ((congrArg (fun a => tangentModuleMapAt.{u,u,u} T hT a t) e.hom_inv_id).trans
        (tangentModuleMapAt_id.{u,u,u} T hT t))

/-- Unlifted target coordinates map to H1 by the literal coefficient
map followed by the actual ULift endpoint classifier. -/
def unliftedTangentLinearEquivH1 :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
      (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) (FGModuleCat.of k k)) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 :=
  (coefficientLinearEquiv B hZ hK hAlg hk iS f hfinite hqc).trans
    (tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc)

set_option maxRecDepth 4096 in
/-- This is the actual native coordinate map used by the parameter
endpoint, rather than an assumed identification with a ULift carrier. -/
theorem unliftedTangentLinearEquivH1_apply
    (t :
      letI := (predeformation B hZ hK hAlg hk iS f).category
      ↥(tangentModuleAt.{u,u,u}
        (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
        (deformationStructure B hZ hK hAlg hk iS f hfinite hqc) (FGModuleCat.of k k))) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    unliftedTangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc t =
      tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
        (tangentModuleMapAt.{u,u,u}
          (BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection)
          (deformationStructure B hZ hK hAlg hk iS f hfinite hqc)
          (fgModuleCatULiftSelfIso (k := k)).inv t) := rfl

set_option maxRecDepth 4096 in
/-- The actual unlifted target H1 coordinates agree with the original
source coefficient map followed by the standard scheme classifier.
This is genuine coefficient naturality of the original comparison. -/
theorem unliftedTangentLinearEquivH1_comparison
    (v : ↥(tangentModuleAt.{u,u,u} (schemeDeformationBased (Λ := k) (Over.mk f))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
      (FGModuleCat.of k k))) :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    unliftedTangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
      (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k k) v) =
    StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f
      (tangentModuleMapAt.{u,u,u} (schemeDeformationBased (Λ := k) (Over.mk f))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
        (fgModuleCatULiftSelfIso (k := k)).inv v) := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  let F := schemeDeformationBased (Λ := k) (Over.mk f)
  let G := BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection
  let hF := isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f)
  let hG := deformationStructure B hZ hK hAlg hk iS f hfinite hqc
  let φ := basedComparison B hZ hK hAlg hk iS f
  let e := fgModuleCatULiftSelfIso (k := k)
  have hn :
      tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k (ULift.{u} k))
          (tangentModuleMapAt.{u,u,u} F hF e.inv v) =
        tangentModuleMapAt.{u,u,u} G hG e.inv
          (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k k) v) :=
    associatedTangentLiftFun_naturality.{u,u,u} F G hF.predeformation hG.predeformation
      (tangentConditionS2.{u,u,u} hF) (tangentConditionS2.{u,u,u} hG) φ e.inv v
  calc
    unliftedTangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
        (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k k) v) =
      tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
        (tangentModuleMapAt.{u,u,u} G hG e.inv
          (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k k) v)) :=
      unliftedTangentLinearEquivH1_apply B hZ hK hAlg hk iS f hfinite hqc _
    _ = tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc
        (tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc (FGModuleCat.of k (ULift.{u} k))
          (tangentModuleMapAt.{u,u,u} F hF e.inv v)) :=
      congrArg (tangentLinearEquivH1 B hZ hK hAlg hk iS f hfinite hqc) hn.symm
    _ = StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f
        (tangentModuleMapAt.{u,u,u} F hF e.inv v) :=
      congrArg (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) f)
        ((tangentEquivalence B hZ hK hAlg hk iS f hfinite hqc
          (FGModuleCat.of k (ULift.{u} k))).symm_apply_apply _)

end M9Native.CurveFieldTargetTangent
