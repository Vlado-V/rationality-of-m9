module

public import M9StacksIntegration.AllTestNativeOriginalVarietyAtlas
public import M9StacksIntegration.AllTestNativeOriginalSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# The original variety-space property from genuine native geometry

Actual native separatedness, etale-local reducedness and finite type
give the original standalone variety property on all original test
schemes. No original variety, atlas-comparison or classifier premise
is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalVarietyGeometry
open AllTestNativeOriginalSpace AllTestNativeOriginalVarietyAtlas AllTestNativeOriginalSeparated
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Actual native separatedness, reducedness, local finite type and
quasi-compactness give the genuine full-original-site variety property. -/
theorem variety_of_native_locallyFiniteType
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (hs : Space.IsSeparatedOver B (Spec (.of K)) hK F)
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK F
      (fun X : Scheme.{u} => IsReduced X))
    (hf : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from F))
    (hc : Space.IsQuasiCompactSpace B (Spec (.of K)) hK F) :
    M9StandaloneDraft.VarietySpace K (originalSpaceOfNative K B hK F hF) :=
  ⟨originalSpace_diagonal_closed K B hK ⟨F, hF⟩ hs,
    originalSpace_etale_chart_reduced K B hK F hF hr,
    exists_original_finiteType_atlas K B hK F hF hf hc⟩

/-- A separated reduced finite-type native algebraic space constructs
an actual standalone variety over the SAME original field on ALL tests. -/
theorem variety_of_native
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (hs : Space.IsSeparatedOver B (Spec (.of K)) hK F)
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK F
      (fun X : Scheme.{u} => IsReduced X))
    (hf : Space.IsFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from F)) :
    M9StandaloneDraft.VarietySpace K (originalSpaceOfNative K B hK F hF) :=
  variety_of_native_locallyFiniteType K B hK F hF hs hr hf.1
    (Space.isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of K)) hK _ hf.2)

end M9StacksIntegration.AllTestNativeOriginalVarietyGeometry
