module

public import M9StacksIntegration.BoundedOriginalFamilyCoarseValue

/-! The actual forward original-family source object recovers the same raw
native family through the genuine hom-shrink unit, with its full identity
base map. No projection comparison or classifier compatibility is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace M9Native.BoundedOriginalFamilyCoarseRecovery
open BoundedOriginalFamilyCoarseValue
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeFamilyMembership

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)
  {T : BigFppfOver B (Spec (.of K)) hK}
  (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)

/-- The actual projected source has exactly the original coefficient base. -/
theorem sourceObject_original_base :
    ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      (sourceObject B hZ K hK g hg F)).base = nativeBase B hZ K hK T :=
  Functor.congr_obj
    (NativeSmoothGenusCoarseClassifier.originalProjection_comp B hZ K hK g hg)
    (sourceObject B hZ K hK g hg F)

/-- The actual hom-shrink unit recovers the same full native family data. -/
def sourceObject_originalIso :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      (sourceObject B hZ K hK g hg F) ≅
      nativeCurveFamily B hZ K hK (T := T) (g := g) F :=
  ((curvesSmallEquivalenceOver B hZ).unitIso.app
    (nativeCurveFamily B hZ K hK (T := T) (g := g) F)).symm

/-- Its actual base map is precisely the equality transport derived above. -/
theorem sourceObject_originalIso_baseMap :
    (sourceObject_originalIso B hZ K hK g hg F).hom.baseMap =
      eqToHom (sourceObject_original_base B hZ K hK g hg F) := by
  let e := sourceObject_originalIso B hZ K hK g hg F
  let p := curvesProjectionOver B hZ
  have hl : p.IsHomLift (𝟙 (nativeBase B hZ K hK T)) e.hom :=
    (curvesSmallEquivalenceOver B hZ).isHomLift_unitIso_inv_app
      (nativeCurveFamily B hZ K hK (T := T) (g := g) F)
  let _ := hl
  simpa only [p, curvesProjectionOver, e, eqToHom_refl, Category.comp_id, Category.id_comp] using
    (IsHomLift.fac' p (𝟙 (nativeBase B hZ K hK T)) e.hom)

/-- The actual raw projected family has true genus membership, derived
from the same original family and the actual recovery arrow. -/
theorem sourceObject_original_membership :
    IsSmoothH0FamilyOfFibreGenus B hZ g
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
        (sourceObject B hZ K hK g hg F)) :=
  (intrinsic_isOpen B hZ g).prop_of_hom
    (sourceObject_originalIso B hZ K hK g hg F).hom
    (nativeCurveFamily_membership B hZ K hK (T := T) (g := g) F)

end M9Native.BoundedOriginalFamilyCoarseRecovery
