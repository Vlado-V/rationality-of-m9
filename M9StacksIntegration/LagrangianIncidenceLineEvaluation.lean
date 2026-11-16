module

public import M9StacksIntegration.LagrangianLinearSectionLineCharts
public import M9StacksIntegration.LineFramePullback
public import M9StacksIntegration.LagrangianIncidenceFieldPoints

/-!
# The actual incidence equation after a line frame

Only the determinant line is framed.  The actual universal rank-five
quotient remains arbitrary; in particular it is not supplied with a global
free frame.  The formula holds on arbitrary test schemes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianIncidenceLineEvaluation

open LinearIncidenceTensorCoordinates LagrangianMatrixChart
open LagrangianLinearSections LagrangianLinearSectionEquations
open LagrangianLinearSectionLineCharts FiniteFreeBasisPullback

/-- A native line frame trivializes its tensor with an arbitrary pulled
module, without choosing a frame for that module. -/
def tensorLineIso {T X : Scheme.{u}} (f : T ⟶ X) (A B : X.Modules)
    (e : (Scheme.Modules.pullback f).obj A ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules)) :
    (Scheme.Modules.pullback f).obj (tensorObj X A B) ≅
      (Scheme.Modules.pullback f).obj B :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso T.sheaf.obj T.ringCatSheaf.property
      e (Iso.refl _) ≪≫ unitTensorIso T ((Scheme.Modules.pullback f).obj B)

theorem tensorLineIso_apply {T X : Scheme.{u}} (f : T ⟶ X) (A B : X.Modules)
    (e : (Scheme.Modules.pullback f).obj A ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    (tensorLineIso f A B e).hom.app ⊤
      (pullbackGlobalSections f (tensorObj X A B) (tensorTop X A B s t)) =
        unitCoordinate T (e.hom.app ⊤ (pullbackGlobalSections f A s)) •
          pullbackGlobalSections f B t := by
  refine (congrArg (fun z => (unitTensorIso T ((Scheme.Modules.pullback f).obj B)).hom.app ⊤
      ((Stacks.SheafOfModules.Invertible.tensorProductIso T.sheaf.obj T.ringCatSheaf.property
        e (Iso.refl _)).hom.val.app (op ⊤) z))
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B s t)).trans ?_
  refine (congrArg (fun z =>
      (unitTensorIso T ((Scheme.Modules.pullback f).obj B)).hom.app ⊤ z)
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt T.sheaf.obj T.ringCatSheaf.property
      (op ⊤) _ _ _ _ e (Iso.refl _) (pullbackGlobalSections f A s)
      (pullbackGlobalSections f B t))).trans ?_
  exact unitTensor_apply T ((Scheme.Modules.pullback f).obj B) _ _

/-- The literal section of the native free module with the specified
coefficients. -/
def coefficientVector (T : Scheme.{u}) (c : Fin 14 → Γ(T, ⊤)) :
    Γ(freeOn T 14, ⊤) :=
  ∑ i : Fin 14, c i • freeBasisSection T 14 i

variable (K : Type u) [Field K]

/-- The framed original tensor equation is precisely the original
quotient evaluated on the original coefficient vector. -/
theorem equationSection_evaluation {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules)) :
    (tensorLineIso f (lineBundle K) (quotientFive K) e).hom.app ⊤
      (pullbackGlobalSections f (equationBundle K) (equationSection K)) =
        Scheme.Modules.Hom.app (X := T)
          (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map ⊤
          (coefficientVector T (lineCoefficients K f e)) := by
  simp only [equationSection, coefficientVector, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorSection_eq_tensorTop, tensorLineIso_apply, Scheme.Modules.Hom.app_smul]
  exact congrArg (fun t : Γ((Scheme.Modules.pullback f).obj (quotientFive K), ⊤) =>
    lineCoefficients K f e i • t) (pullbackPresentation_basis f (ambientQuotient K) i).symm

theorem equation_zero_iff_evaluation_zero {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules)) :
    pullbackGlobalSections f (equationBundle K) (equationSection K) = 0 ↔
      Scheme.Modules.Hom.app (X := T)
        (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map ⊤
        (coefficientVector T (lineCoefficients K f e)) = 0 := by
  rw [← equationSection_evaluation K f e]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((tensorLineIso f (lineBundle K) (quotientFive K) e).hom.app ⊤)).injective).symm

/-- The original scheme-theoretic factorization criterion, retaining the
arbitrary actual universal quotient. -/
theorem factorsThrough_iff_evaluation_zero {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules)) :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      Scheme.Modules.Hom.app (X := T)
        (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map ⊤
        (coefficientVector T (lineCoefficients K f e)) = 0 :=
  (factorsThrough_iff_equation_zero K f).trans (equation_zero_iff_evaluation_zero K f e)

end M9Native.LagrangianIncidenceLineEvaluation

end
