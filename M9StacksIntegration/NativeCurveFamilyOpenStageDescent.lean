module

public import M9StacksIntegration.NativeCurveFamilyStageDescent
public import M9StacksIntegration.NativeCurveFamilyOpenStage

/-!
# Actual open-property descent to relative finite-type K-models

The actual unconditional native0D55 provider is source/object/trace verified.
This new integration source needs its own ordinary direct and fresh checks.

The actual unconditional family descent is followed by the actual eventual
open-property theorem. Thus the descended family, and not merely its base,
has the given genuinely open property. Relative K-stages belong to EVERY
native site containing Spec K. No absolute finite-type assertion over Z,
no backwards transport along a family arrow, and no site-equivalence or
limit-preservation premise is inserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeCurveFamilyOpenStageDescent
universe u

/-- Actual0D55 plus actual openness constructs a stage family WITH the
property, retaining the actual limit base map. -/
theorem exists_hom_to_stage_with_property
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ BigAffineFppf B integerBase hZ} (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c))
    (G : CurveFamily B hZ)
    (hG : G.base = (BigAffineFppf.inclusion B integerBase hZ).obj c.pt)
    (hPG : P G) :
    ∃ (i : I) (Gi : CurveFamily B hZ)
      (hGi : Gi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
      (δ : G ⟶ Gi), P Gi ∧ δ.baseMap = eqToHom hG ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i) ≫ eqToHom hGi.symm := by
  obtain ⟨i, Gi, hGi, δ, hδ⟩ :=
    NativeCurveFamilyStageDescent.exists_hom_to_stage_of_isLimit c hc G hG
  obtain ⟨j, a, H, hH, χ, η, hPH, hχ, _, _⟩ :=
    NativeCurveFamilyOpenStage.exists_property_at_later_stage B hZ hP
      (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) hc
      (fun i => (D.obj i).property) G hG hPG i Gi hGi δ hδ
  exact ⟨j, H, hH, χ, hPH, hχ⟩

/-- A true open-property family over Spec A has a true relative K-model
WITH that property whose base belongs to EVERY SpecK-containing site. -/
theorem exists_hom_to_relative_small_base_with_property
    (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
    (B₀ B₁ : BigFppfSite.{u}) (hK₀ : B₀.Contains (Spec (.of K)))
    (hK₁ : B₁.Contains (Spec (.of K))) (hA₁ : B₁.Contains (Spec (.of A)))
    (hZ₁ : B₁.Contains integerBase) (k : B₁.obj hK₁ ⟶ B₁.obj hZ₁)
    {P : ObjectProperty (CurveFamily B₁ hZ₁)} (hP : IsOpenCurvesLocus B₁ hZ₁ P)
    (G : CurveFamily B₁ hZ₁)
    (hG : G.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj
      (NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁).pt)
    (hPG : P G) :
    ∃ (i : (Finset A)ᵒᵖ) (Gi : CurveFamily B₁ hZ₁)
      (hGi : Gi.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj
        ((NativeRelativeAffineRebase.diagramOver K A B₁ hK₁ integerBase hZ₁ k).obj i))
      (δ : G ⟶ Gi), P Gi ∧
      δ.baseMap = eqToHom hG ≫ (BigAffineFppf.inclusion B₁ integerBase hZ₁).map
        ((NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁).π.app i) ≫
          eqToHom hGi.symm ∧
      B₀.Contains ((BigFppfOver.toScheme B₁ integerBase hZ₁).obj Gi.base) := by
  obtain ⟨i, Gi, hGi, δ, hPGi, hδ⟩ := exists_hom_to_stage_with_property hP
    (NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁)
    (NativeRelativeAffineRebase.isLimit_toScheme_coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁)
    G hG hPG
  refine ⟨i, Gi, hGi, δ, hPGi, hδ, ?_⟩
  rw [hGi]
  exact NativeRelativeAffineModels.contains_stage K A B₀ hK₀ i.unop

end M9StacksIntegration.NativeCurveFamilyOpenStageDescent
