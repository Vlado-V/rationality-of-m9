module

public import M9StacksIntegration.FiberedCommonStageRefinement
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingOfCharts

/-! Actual native curve-family choices admit a common later-stage source.
The genuine unconditional Stacks0D55 theorem supplies fullness. No limit
preservation, common refinement, arrow descent, or comparison isomorphism
is a public input. Both original limit arrows and all original cone and
transition maps are retained literally in the conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] Functor.Fiber

namespace M9Native.NativeCurveFamilyCommonStageRefinement

universe u

/-- Fullness in actual native0D55 gives one actual later curve family
factoring BOTH specified family choices over the actual affine limit. -/
theorem exists_common_stage_of_isLimit
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ BigAffineFppf B integerBase hZ} (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B integerBase hZ).mapCone c))
    (G : CurveFamily B hZ)
    (hG : G.base = (BigAffineFppf.inclusion B integerBase hZ).obj c.pt)
    (i j : I) (Gi Gj : CurveFamily B hZ)
    (hGi : Gi.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i))
    (hGj : Gj.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj j))
    (δ : G ⟶ Gi) (ε : G ⟶ Gj)
    (hδ : δ.baseMap = eqToHom hG ≫
      (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i) ≫ eqToHom hGi.symm)
    (hε : ε.baseMap = eqToHom hG ≫
      (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app j) ≫ eqToHom hGj.symm) :
    ∃ (k : I) (a : k ⟶ i) (b : k ⟶ j) (H : CurveFamily B hZ)
      (hH : H.base = (BigAffineFppf.inclusion B integerBase hZ).obj (D.obj k))
      (χ : G ⟶ H) (η : H ⟶ Gi) (θ : H ⟶ Gj),
      χ.baseMap = eqToHom hG ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (c.π.app k) ≫ eqToHom hH.symm ∧
      η.baseMap = eqToHom hH ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (D.map a) ≫ eqToHom hGi.symm ∧
      θ.baseMap = eqToHom hH ≫
        (BigAffineFppf.inclusion B integerBase hZ).map (D.map b) ≫ eqToHom hGj.symm ∧
      χ ≫ η = δ ∧ χ ≫ θ = ε := by
  let p := (curvesFiberedCategory B hZ).val.p
  let _ : p.IsFibered := (curvesFiberedCategory B hZ).property.isFibered
  have hlim := isLimitPreserving_curvesFiberedCategory_unconditional B hZ
  have := hlim I D c hc
  have hHom : Deformation.Artin.DescentHom p
      (D ⋙ BigAffineFppf.inclusion B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).mapCone c) :=
    Deformation.Artin.descentHom_of_full p (curvesFiberedCategory B hZ).property _ _
  have hδlift : p.IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) δ :=
    IsHomLift.of_fac' p _ δ hG hGi hδ
  have hεlift : p.IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app j)) ε :=
    IsHomLift.of_fac' p _ ε hG hGj hε
  obtain ⟨k, a, b, H, χ, η, θ, hχ, hη, hθ, hχη, hχθ⟩ :=
    FiberedCommonStageRefinement.exists_common_stage p
      (curvesFiberedCategory B hZ).property _ _ hHom
      ⟨G, hG⟩ i j ⟨Gi, hGi⟩ ⟨Gj, hGj⟩ δ ε hδlift hεlift
  let _ : p.IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app k)) χ := hχ
  let _ : p.IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (D.map a)) η := hη
  let _ : p.IsHomLift
      ((BigAffineFppf.inclusion B integerBase hZ).map (D.map b)) θ := hθ
  refine ⟨k, a, b, H.1, H.2, χ, η, θ, ?_, ?_, ?_, hχη, hχθ⟩
  · exact IsHomLift.fac' p _ χ
  · exact IsHomLift.fac' p _ η
  · exact IsHomLift.fac' p _ θ

end M9Native.NativeCurveFamilyCommonStageRefinement
