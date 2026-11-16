module

public import M9StacksIntegration.SchemeMorphismSourceH1Map
public import M9StacksIntegration.NativeCotangentSourceRestriction
public import M9StacksIntegration.RawFamilyCotangentRestriction
public import M9StacksIntegration.SchemeRawCompatibleMorphism
public import M9StacksIntegration.SchemeTangentRawPrecomposition
public import M9StacksIntegration.ProjectiveLineNativeExtensionRigidity
public import M9StacksIntegration.GenusNineP1SourceKernel
public import M9StacksIntegration.SmoothCurveTangentCohomology

/-!
# Actual morphism-deformation source image for native projective-line covers

An actual deformation of the morphism gives its actual compatible raw
extensions. Native projective-line extension rigidity and the original
compatible conormal square force the actual source class to vanish after
the original direct cotangent arrow. Its proved normalization is the
literal differential, so the actual source-forgetting H1 image lies in
the literal derivative kernel. The checked genus-nine kernel bound then
applies to this genuine deformation image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Deformation Deformation.Examples
open AlgebraicGeometry.RingedSpaceThickening
open M9Native.PencilProjectiveLineGeometry M9Native.SchemeMorphismSourceH1

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] isCurve_projectiveSpaceOver_one M9Native.CurveP1NormalSections.line_smooth

universe u

namespace M9Native.SchemeMorphismP1SourceImage

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

section RawClasses

variable (g : X ⟶ Line k)
  (z : SchemeRawCompatibleMorphism.FamilyFiber (Λ := k)
    g (g ≫ toBase k) (toBase k) rfl (FGModuleCat.of k (ULift.{u} k)))

/-- The original raw source class of an actual morphism deformation
is annihilated by the actual original direct cotangent arrow. -/
theorem raw_source_class_restriction_zero :
    derivedPullbackNaiveCotangentMap g.toLRSHom.toShHom (toBase k).toLRSHom.toShHom ≫
      SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk (g ≫ toBase k))
        (FGModuleCat.of k (ULift.{u} k))
        (SchemeRawCompatibleMorphism.sourceFiber (Λ := k)
          g (g ≫ toBase k) (toBase k) rfl (FGModuleCat.of k (ULift.{u} k)) z) = 0 := by
  let V := FGModuleCat.of k (ULift.{u} k)
  have htarget : SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk (toBase k)) V
      (SchemeRawCompatibleMorphism.targetFiber (Λ := k)
        g (g ≫ toBase k) (toBase k) rfl V z) = 0 :=
    ProjectiveLineNativeExtensionRigidity.native_ext_one_eq_zero_of_coefficient_iso k
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := k) V) (Over.mk (toBase k)))
      (SchemeTangentRawPrecomposition.rankOneULiftCoefficientIso (toBase k)) _
  exact RawFamilyCotangentRestriction.raw_restriction_eq_zero k g (toBase k) V z htarget

/-- Genuine coefficient transport takes the same actual vanishing to
the exact original ULift source endpoint classifier. -/
theorem source_endpoint_class_restriction_zero :
    letI := StandardCurveCotangentExt.nativeExtModule (g ≫ toBase k)
      (InvertibleExtCancellation.unit X)
    derivedPullbackNaiveCotangentMap g.toLRSHom.toShHom (toBase k).toLRSHom.toShHom ≫
      StandardSchemeTangent.endpointTangentLinearEquivStd (Λ := k) (g ≫ toBase k)
        (tangentClassAt (schemeDeformationBased (Λ := k) (Over.mk (g ≫ toBase k)))
          (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k)
            (Over.mk (g ≫ toBase k))) (FGModuleCat.of k (ULift.{u} k))
          (SchemeRawCompatibleMorphism.sourceFiber (Λ := k)
            g (g ≫ toBase k) (toBase k) rfl (FGModuleCat.of k (ULift.{u} k)) z)) = 0 :=
  SchemeTangentRawPrecomposition.precomp_endpoint_eq_zero_of_raw_eq_zero
    (g ≫ toBase k)
    (SchemeRawCompatibleMorphism.sourceFiber (Λ := k)
      g (g ≫ toBase k) (toBase k) rfl (FGModuleCat.of k (ULift.{u} k)) z) _
    (derivedPullbackNaiveCotangentMap g.toLRSHom.toShHom (toBase k).toLRSHom.toShHom)
    (raw_source_class_restriction_zero g z)

end RawClasses

variable (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  (g : X ⟶ Line k) (hcomm : g ≫ toBase k = f)

/-- Actual source-forgetting tangent classes lie in the literal H1
kernel of the native dual differential. -/
theorem sourceForgettingH1_mem_sourceKernel
    (t : ↥(morphismTangentModule f (toBase k) g hcomm)) :
    sourceForgettingH1 f (toBase k) g hcomm t ∈
      CurveDerivativeSourceKernel.sourceKernel f (toBase k) g hcomm := by
  subst f
  let V := FGModuleCat.of k (ULift.{u} k)
  let B := BasedCategory.ofFunctor
    (schemeMorphismDeformationCategoryProjection (Λ := k) g (g ≫ toBase k) (toBase k) rfl)
  let hB := isDeformationCategory_schemeMorphismDeformationCategoryProjection (Λ := k)
    g (g ≫ toBase k) (toBase k) rfl
  obtain ⟨z, rfl⟩ := tangentClassAt_surjective B hB V t
  rw [sourceForgettingH1_apply]
  change StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) (g ≫ toBase k)
      (tangentMapAt hB
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk (g ≫ toBase k)))
        (schemeMorphismSourceBased g (g ≫ toBase k) (toBase k) rfl) V
        (tangentClassAt B hB V z)) ∈ _
  rw [tangentMapAt_tangentClassAt,
    ← SchemeRawCompatibleMorphism.sourceFiber_eq_fiberFunctor (Λ := k)]
  let := StandardCurveCotangentExt.nativeExtModule (g ≫ toBase k)
    (InvertibleExtCancellation.unit X)
  rw [StandardSchemeTangent.endpointTangentLinearEquivH1_apply]
  change cohomologyOverFieldMap k (g ≫ toBase k)
    (CurveDerivativeNormal.tangentMap (g ≫ toBase k) (toBase k) g rfl) 1
      (StandardCurveCotangentExt.tangentOneLinearEquiv (g ≫ toBase k)
        (StandardSchemeTangent.endpointTangentLinearEquivStd (Λ := k) (g ≫ toBase k)
          (tangentClassAt (schemeDeformationBased (Λ := k) (Over.mk (g ≫ toBase k)))
            (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k)
              (Over.mk (g ≫ toBase k))) V
            (SchemeRawCompatibleMorphism.sourceFiber (Λ := k)
              g (g ≫ toBase k) (toBase k) rfl V z)))) = 0
  exact (NativeCotangentSourceRestriction.restriction_eq_zero_iff (toBase k) g _).mp
    (source_endpoint_class_restriction_zero g z)

/-- The image inclusion concerns the actual original morphism tangent
space and actual original endpoint map. -/
theorem sourceForgettingH1_range_le_sourceKernel :
    LinearMap.range (sourceForgettingH1 f (toBase k) g hcomm) ≤
      CurveDerivativeSourceKernel.sourceKernel f (toBase k) g hcomm := by
  rintro a ⟨t, rfl⟩
  exact sourceForgettingH1_mem_sourceKernel f g hcomm t

variable [CharZero k] [IsProper f] (hg : genus f = 9)
  (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y)

include hg

/-- The genuine source deformation image has dimension at most13+2d. -/
theorem sourceForgettingH1_finrank_le :
    Module.finrank k (LinearMap.range (sourceForgettingH1 f (toBase k) g hcomm)) ≤
      13 + 2 * PencilDegreePullback.curveMapDegree f (toBase k) g hcomm hnc := by
  let : Module.Finite k (cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1) :=
    Module.finite_of_finrank_pos (by rw [SmoothCurveTangentCohomology.tangent_h1 f hg]; decide)
  exact (Submodule.finrank_mono
    (sourceForgettingH1_range_le_sourceKernel f g hcomm)).trans
      (GenusNineP1SourceKernel.sourceKernel_finrank_le f hg g hcomm hnc)

/-- For actual degree at most five the genuine original source
deformation image has dimension at most twenty-three. -/
theorem sourceForgettingH1_finrank_le_twenty_three
    (hd : PencilDegreePullback.curveMapDegree f (toBase k) g hcomm hnc ≤ 5) :
    Module.finrank k (LinearMap.range (sourceForgettingH1 f (toBase k) g hcomm)) ≤ 23 := by
  have h := sourceForgettingH1_finrank_le f g hcomm hg hnc
  omega

end M9Native.SchemeMorphismP1SourceImage
