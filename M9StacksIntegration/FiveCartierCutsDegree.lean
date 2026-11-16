module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper

/-!
# Euler degree after five actual Cartier hyperplane cuts

The successive schemes are the literal divisor subschemes. Native
intersection restriction (0BEU) and the native curve Euler comparison
(0BEY) identify the final curve-line degree with the original sixfold
ample degree. No numerical degree, cycle equality or genus is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.FiveCartierCutsDegree

open CategoryTheory AlgebraicGeometry
open Stacks.Divisors

/-- Five genuine Cartier hyperplane cuts retain the original ample degree
as the Euler-defined degree on the final curve. The dimension bound is
also derived, rather than supplied. -/
theorem degree_after_five_cartier_cuts
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 6) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hample : Scheme.Modules.IsAmple X L)
    (D₁ : X.IdealSheafData) [IsEffectiveCartierDivisor D₁]
    (D₂ : D₁.subscheme.IdealSheafData) [IsEffectiveCartierDivisor D₂]
    (D₃ : D₂.subscheme.IdealSheafData) [IsEffectiveCartierDivisor D₃]
    (D₄ : D₃.subscheme.IdealSheafData) [IsEffectiveCartierDivisor D₄]
    (D₅ : D₄.subscheme.IdealSheafData) [IsEffectiveCartierDivisor D₅]
    (e₁ : (Scheme.Modules.pullback (𝟙 X)).obj L ≅ (invertibleSheaf D₁ : X.Modules))
    (e₂ : (Scheme.Modules.pullback (D₁.subschemeι ≫ 𝟙 X)).obj L ≅
      (invertibleSheaf D₂ : D₁.subscheme.Modules))
    (e₃ : (Scheme.Modules.pullback (D₂.subschemeι ≫ D₁.subschemeι ≫ 𝟙 X)).obj L ≅
      (invertibleSheaf D₃ : D₂.subscheme.Modules))
    (e₄ : (Scheme.Modules.pullback
      (D₃.subschemeι ≫ D₂.subschemeι ≫ D₁.subschemeι ≫ 𝟙 X)).obj L ≅
      (invertibleSheaf D₄ : D₃.subscheme.Modules))
    (e₅ : (Scheme.Modules.pullback
      (D₄.subschemeι ≫ D₃.subschemeι ≫ D₂.subschemeι ≫ D₁.subschemeι ≫ 𝟙 X)).obj L ≅
      (invertibleSheaf D₅ : D₄.subscheme.Modules)) :
    let i : D₅.subscheme ⟶ X :=
      D₅.subschemeι ≫ D₄.subschemeι ≫ D₃.subschemeι ≫ D₂.subschemeι ≫ D₁.subschemeι ≫ 𝟙 X
    ∃ hcurve : topologicalKrullDim D₅.subscheme ≤ 1,
      invertibleCurveDegree k (i ≫ f) hcurve ((Scheme.Modules.pullback i).obj L) =
        degreeWithRespectTo k f (𝟙 X) 6 hdim L hample := by
  let i₀ : X ⟶ X := 𝟙 X
  let i₁ : D₁.subscheme ⟶ X := D₁.subschemeι ≫ i₀
  let i₂ : D₂.subscheme ⟶ X := D₂.subschemeι ≫ i₁
  let i₃ : D₃.subscheme ⟶ X := D₃.subschemeι ≫ i₂
  let i₄ : D₄.subscheme ⟶ X := D₄.subschemeι ≫ i₃
  let i₅ : D₅.subscheme ⟶ X := D₅.subschemeι ≫ i₄
  have h₁ := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    k f i₀ 5 hdim.le D₁
  have h₂ := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    k f i₁ 4 h₁ D₂
  have h₃ := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    k f i₂ 3 h₂ D₃
  have h₄ := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    k f i₃ 2 h₃ D₄
  have h₅ := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    k f i₄ 1 h₄ D₅
  have a₁ := intersectionNumber_eq_of_isEffectiveCartierDivisor
    k f i₀ 5 hdim.le (fun _ : Fin 6 => L) D₁ h₁ e₁
  have a₂ := intersectionNumber_eq_of_isEffectiveCartierDivisor
    k f i₁ 4 h₁ (fun _ : Fin 5 => L) D₂ h₂ e₂
  have a₃ := intersectionNumber_eq_of_isEffectiveCartierDivisor
    k f i₂ 3 h₂ (fun _ : Fin 4 => L) D₃ h₃ e₃
  have a₄ := intersectionNumber_eq_of_isEffectiveCartierDivisor
    k f i₃ 2 h₃ (fun _ : Fin 3 => L) D₄ h₄ e₄
  have a₅ := intersectionNumber_eq_of_isEffectiveCartierDivisor
    k f i₄ 1 h₄ (fun _ : Fin 2 => L) D₅ h₅ e₅
  have a₆ := intersectionNumber_one_eq_invertibleCurveDegree k f i₅ h₅ L
  refine ⟨h₅, ?_⟩
  change invertibleCurveDegree k (i₅ ≫ f) h₅ ((Scheme.Modules.pullback i₅).obj L) =
    intersectionNumber k f (𝟙 X) 6 hdim.le (fun _ : Fin 6 => L)
  exact (a₁.trans (a₂.trans (a₃.trans (a₄.trans (a₅.trans a₆))))).symm

end M9Native.FiveCartierCutsDegree
