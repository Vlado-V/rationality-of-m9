module

public import M9StacksIntegration.AllTestNativeFamilyMembership
public import M9StacksIntegration.AllTestNativeCurveNaturality
public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier
public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import M9StacksIntegration.ASClassifierGeometricLift

/-! Actual values of the chosen coarse map on EVERY original family over
native bounded bases, including nonschematic total spaces. All Cartesian
arrows retain their original field-base map. This constructs bounded data;
arbitrary original bases still require actual finite-stage descent and glue. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.BoundedOriginalFamilyCoarseValue
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeCurveNaturality
  M9StacksIntegration.AllTestNativeFamilyMembership
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestBoundedOriginalRecovery

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)

/-- The actual native image of the SAME original family, with intrinsic
genus membership derived from its original local geometry. -/
def moduliObject {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (moduliSmoothCurvesOfGenus B hZ g).val.obj :=
  ⟨nativeCurveFamily B hZ K hK (T := T) (g := g) F,
    nativeCurveFamily_membership B hZ K hK (T := T) (g := g) F⟩

/-- The actual original Cartesian arrow, retained in native genus objects. -/
def moduliArrow {U T : BigFppfOver B (Spec (.of K)) hK} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a))) :
    moduliObject B hZ K hK g G ⟶ moduliObject B hZ K hK g F :=
  ObjectProperty.homMk (nativeCartesianMap B hZ K hK a F G r hcart)

/-- The SAME original family's actual point of the chosen field source. -/
def sourceObject {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj := by
  refine ⟨T, (NativeSmoothGenusCoarseClassifier.integerComparison B hZ g hg).obj
    (moduliObject B hZ K hK g F), ?_⟩
  exact Functor.congr_obj
    (NativeSmoothGenusCoarseClassifier.integerComparison B hZ g hg).w
    (moduliObject B hZ K hK g F)

theorem sourceObject_base {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj
      (sourceObject B hZ K hK g hg F) = T := rfl

/-- Every actual original Cartesian arrow maps into the chosen field source,
with its actual original coefficient map rather than a chosen automorphism. -/
def sourceArrow {U T : BigFppfOver B (Spec (.of K)) hK} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a))) :
    sourceObject B hZ K hK g hg G ⟶ sourceObject B hZ K hK g hg F where
  base := a
  fib := (NativeSmoothGenusCoarseClassifier.integerComparison B hZ g hg).map
    (moduliArrow B hZ K hK g a F G r hcart)
  «over» := Functor.congr_hom
    (NativeSmoothGenusCoarseClassifier.integerComparison B hZ g hg).w
    (moduliArrow B hZ K hK g a F G r hcart)

theorem sourceArrow_isHomLift {U T : BigFppfOver B (Spec (.of K)) hK} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a))) :
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.IsHomLift
      a (sourceArrow B hZ K hK g hg a F G r hcart) :=
  IsHomLift.of_fac' _ a _ rfl rfl (by rfl)

/-- The literal value of the ACTUAL chosen coarse functor on this family. -/
def nativeValue {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj.obj (op T) :=
  elementOf (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
    (X := (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).obj
        (sourceObject B hZ K hK g hg F))
    (Functor.congr_obj (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).w
        (sourceObject B hZ K hK g hg F))

/-- Native coarse values commute with EVERY original Cartesian family arrow. -/
theorem nativeValue_naturality {U T : BigFppfOver B (Spec (.of K)) hK} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a))) :
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj.map a.op
      (nativeValue B hZ K hK g hg F) = nativeValue B hZ K hK g hg G := by
  let κ := ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
  let δ := sourceArrow B hZ K hK g hg a F G r hcart
  have : (BasedCategory.ofFunctor
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p).p.IsHomLift
      a δ := sourceArrow_isHomLift B hZ K hK g hg a F G r hcart
  have hκ := Functor.isHomLift_map_of_comp_eq κ.w a δ
  have h := elementOf_eq_map
    (Functor.congr_obj κ.w (sourceObject B hZ K hK g hg G))
    (Functor.congr_obj κ.w (sourceObject B hZ K hK g hg F)) a (κ.map δ) hκ
  exact h.symm

/-- The same actual chosen value, in the full-original presheaf over the
same original bounded base, using the proved actual restriction unit. -/
def originalValue {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    ((originalPresheafFunctor K B hK).obj
      (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)).obj
        (op ((boundedInclusion B K hK).obj T)) :=
  (originalNativeRestrictionSmallIso K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).property).inv.app (op T)
      (nativeValue B hZ K hK g hg F)

/-- Full-original values retain the same original Cartesian naturality. -/
theorem originalValue_naturality {U T : BigFppfOver B (Spec (.of K)) hK} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a))) :
    ((originalPresheafFunctor K B hK).obj
      (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)).map
        ((boundedInclusion B K hK).map a).op (originalValue B hZ K hK g hg F) =
      originalValue B hZ K hK g hg G := by
  let e := originalNativeRestrictionSmallIso K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).property
  have h := ConcreteCategory.congr_hom (e.inv.naturality a.op)
    (nativeValue B hZ K hK g hg F)
  exact h.symm.trans (congrArg (e.inv.app (op U))
    (nativeValue_naturality B hZ K hK g hg a F G r hcart))

end M9Native.BoundedOriginalFamilyCoarseValue
