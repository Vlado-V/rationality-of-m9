module

public import M9StacksIntegration.TensorFreeFrames
public import M9StacksIntegration.LagrangianLinearSectionEquations

/-! Global matrix rows of the original universal incidence equation.
Only the actual quotient bundle is framed. The determinant line remains
the original pulled bundle, with no line trivialization or coordinate
comparison premise. All test schemes, including nonreduced ones, occur. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.LagrangianLinearSections M9Native.LagrangianLinearSectionEquations
open M9Native.LinearIncidenceTensorCoordinates M9Native.LagrangianMatrixChart
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianIncidenceRows

variable (K : Type u) [Field K] {T : Scheme.{u}} (f : T ⟶ ambient K)
    (d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5)
    (q : freeOn T 14 ⟶ freeOn T 5)
    (hq : (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map ≫ d.hom = q)

def rowSections (j : Fin 5) :
    Γ((Scheme.Modules.pullback f).obj (lineBundle K), ⊤) :=
  ∑ i : Fin 14, Stacks.FreeSheafMatrix.toMatrix q j i •
    pullbackGlobalSections f (lineBundle K) (lineSection K i)

include hq in
theorem equationSection_rows :
    (TensorFreeFrames.pullbackFrameIso (ambient K) (lineBundle K) (quotientFive K) 5 f d).hom.app ⊤
      (pullbackGlobalSections f (equationBundle K) (equationSection K)) =
    TensorFreeCoordinates.rowTensor T ((Scheme.Modules.pullback f).obj (lineBundle K)) 5 q
      (fun i => pullbackGlobalSections f (lineBundle K) (lineSection K i)) := by
  simp only [equationSection, map_sum, TensorFreeCoordinates.rowTensor]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorSection_eq_tensorTop, TensorFreeFrames.pullbackFrameIso_tensorTop,
    quotientSection_pullback K f d q hq]

include d hq in
/-- Global vanishing of the actual original rank-five tensor equation is
the simultaneous vanishing of the actual five original line sections. -/
theorem equationSection_zero_iff_rows :
    pullbackGlobalSections f (equationBundle K) (equationSection K) = 0 ↔
      ∀ j : Fin 5, rowSections K f q j = 0 := by
  change _ ↔ ∀ j : Fin 5, (∑ i : Fin 14, Stacks.FreeSheafMatrix.toMatrix q j i •
    pullbackGlobalSections f (lineBundle K) (lineSection K i)) = 0
  rw [← TensorFreeCoordinates.rowTensor_zero_iff T
    ((Scheme.Modules.pullback f).obj (lineBundle K)) 5 q]
  rw [← equationSection_rows K f d q hq]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((TensorFreeFrames.pullbackFrameIso (ambient K) (lineBundle K) (quotientFive K) 5 f d).hom.app ⊤)).injective).symm

include d hq in
theorem factorsThrough_iff_rows :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      ∀ j : Fin 5, rowSections K f q j = 0 :=
  (factorsThrough_iff_equation_zero K f).trans (equationSection_zero_iff_rows K f d q hq)

end M9Native.LagrangianIncidenceRows
