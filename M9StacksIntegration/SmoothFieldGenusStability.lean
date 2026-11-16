module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable

/-! Genuine stability of the TRUE original smooth field-genus category.
The original genus-g fibre witness at each field point is used directly.
No genus-rank, all-fibre comparison, algebraicity, or coarse premise occurs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.SmoothFieldGenusStability

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

local instance presheafHasPullbacks : HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Every actual smooth H0 family whose field fibres have genus g≥2 is
stable. The same original fibres provide its stability witnesses. -/
theorem isStableCurveFamily_of_smooth_fieldGenus {g : ℕ} (hg : 2 ≤ g)
    {F : CurveFamily B hZ} (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    IsStableCurveFamily B hZ F := by
  have hpre : IsPrestableCurveFamily B hZ F :=
    ⟨Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth B integerBase hZ
      hF.1.1.1 hF.1.1.2, hF.1.2⟩
  refine ⟨hpre, fun p => ?_⟩
  obtain ⟨V, v, q, hpb, hgv⟩ := hF.2 p
  let q₀ : schemeSpace V ⟶ F.total := ObjectProperty.homMk q
  have hsq : IsPullback q₀ (schemeSpaceMap v) F.toBase (schemeSpaceMap p.value) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb
  letI : Smooth ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    CurveFamily.smooth_of_isPullback_fieldValuedPoint hF.1.1.1 hsq
  letI : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    CurveFamily.isProper_of_isPullback_fieldValuedPoint hsq
  letI := irreducibleSpace_of_smooth_of_isIso_appTop p.carrier
    ((BigFppfOver.toScheme B integerBase hZ).map v)
    (CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint hF.1.2 hsq)
  letI : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over (Spec (.of p.carrier)) :=
    ⟨(BigFppfOver.toScheme B integerBase hZ).map v⟩
  have hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).obj V ↘
      Spec (.of p.carrier)) := ‹IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)›
  refine ⟨V, v, q, hpb, ?_, not_isRationalTail_of_irreducibleSpace p.carrier _,
    hproper, not_isRationalBridge_of_irreducibleSpace p.carrier _⟩
  exact hgv ▸ hg

end M9Native.SmoothFieldGenusStability
