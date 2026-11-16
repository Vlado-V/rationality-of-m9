module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import M9StacksIntegration.NativeRelativeAffineRebase

/-!
# ACTUAL family descent to relative finite-type K-models

The actual native unconditional0D55 provider is now source/object/trace
verified. This NEW integration source is not a checked result until its own
ordinary direct and fresh kernel checks pass.

The first proof is the literal pinned native CurveFamilyLimitDescent proof,
using the actual PUBLIC unconditional0D55 theorem instead of its historical
private alias. The concrete relative K-model corollary proves the descended
BASE belongs to every site containing Spec K. It makes no assertion that the
stage is of finite type over Z or that a smooth-genus condition automatically
descends backward along a family arrow.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeCurveFamilyStageDescent
universe u

/-- Actual unconditional family descent from the actual native Stacks0D55
provider, with no limit-preservation or family-classifier premise. -/
theorem exists_hom_to_stage_of_isLimit
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ BigAffineFppf B integerBase hZ} (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c))
    (G : CurveFamily B hZ)
    (hG : G.base = (BigAffineFppf.inclusion B integerBase hZ).obj c.pt) :
    ∃ (i : I) (Gi : CurveFamily B hZ)
      (hGi : Gi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
      (δ : G ⟶ Gi), δ.baseMap = eqToHom hG ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i) ≫ eqToHom hGi.symm := by
  have hlim := isLimitPreserving_curvesFiberedCategory_unconditional B hZ
  let : (curvesFiberedCategory B hZ).val.p.IsFibered :=
    (curvesFiberedCategory B hZ).2.isFibered
  have := hlim I D c hc
  obtain ⟨i, ⟨Gi, hGi⟩, δ, hδ⟩ := Deformation.Artin.descentObj_of_essSurj
    (curvesFiberedCategory B hZ).val.p (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
    ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) ⟨G, hG⟩
  have hδ' : (curvesProjectionOver B hZ).IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) δ := hδ
  exact ⟨i, Gi, hGi, δ, IsHomLift.fac' (curvesProjectionOver B hZ)
    ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) δ⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An actual native family over Spec A descends to an actual relative
finite-type K-model BASE lying in every Spec-K-containing site. This retains
the actual underlying K-algebra maps and the actual native family arrow. -/
theorem exists_hom_to_relative_small_base
    (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
    (B₀ B₁ : BigFppfSite.{u}) (hK₀ : B₀.Contains (Spec (.of K)))
    (hK₁ : B₁.Contains (Spec (.of K))) (hA₁ : B₁.Contains (Spec (.of A)))
    (hZ₁ : B₁.Contains integerBase) (k : B₁.obj hK₁ ⟶ B₁.obj hZ₁)
    (G : CurveFamily B₁ hZ₁)
    (hG : G.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj
      (NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁).pt) :
    ∃ (i : (Finset A)ᵒᵖ) (Gi : CurveFamily B₁ hZ₁)
      (hGi : Gi.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj
        ((NativeRelativeAffineRebase.diagramOver K A B₁ hK₁ integerBase hZ₁ k).obj i))
      (δ : G ⟶ Gi),
      δ.baseMap = eqToHom hG ≫ (BigAffineFppf.inclusion B₁ integerBase hZ₁).map
        ((NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁).π.app i) ≫
          eqToHom hGi.symm ∧
      B₀.Contains ((BigFppfOver.toScheme B₁ integerBase hZ₁).obj Gi.base) := by
  obtain ⟨i, Gi, hGi, δ, hδ⟩ := exists_hom_to_stage_of_isLimit
    (NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁)
    (NativeRelativeAffineRebase.isLimit_toScheme_coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁)
    G hG
  refine ⟨i, Gi, hGi, δ, hδ, ?_⟩
  rw [hGi]
  exact NativeRelativeAffineModels.contains_stage K A B₀ hK₀ i.unop

end M9StacksIntegration.NativeCurveFamilyStageDescent
