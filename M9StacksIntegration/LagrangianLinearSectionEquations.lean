module

public import M9StacksIntegration.LagrangianLinearSectionQuotientCharts
public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import M9StacksIntegration.FiniteFreeBasisPullback

/-! Literal native coefficient equations for the original universal rank-five
tensor section, retaining the actual quotient and determinant-line triangles. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.LagrangianLinearSectionEquations
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LinearIncidenceTensorCoordinates M9Native.FiniteFreeBasisPullback
open AlgebraicGeometry.Grassmannian
variable (K : Type u) [Field K]

theorem tensorSection_eq_tensorTop (s : Γ(lineBundle K,⊤)) (t : Γ(quotientFive K,⊤)) :
    tensorSection K s t=tensorTop (ambient K) (lineBundle K) (quotientFive K) s t := by
  exact (Stacks.SheafOfModules.pairingApp_tensorSectionPairing
    (O:=(ambient K).sheaf) (lineBundle K) (quotientFive K) (op ⊤) s t).trans (Eq.refl _)

theorem quotientSection_pullback {T : Scheme.{u}} (f : T ⟶ ambient K)
    (d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5)
    (q : freeOn T 14 ⟶ freeOn T 5)
    (hq : (pullbackPresentation f (ambientQuotient K)).map ≫ d.hom=q) (i : Fin 14) :
    d.hom.app ⊤ (pullbackGlobalSections f (quotientFive K) (quotientSection K i))=
      q.app ⊤ (freeBasisSection T 14 i) := by
  have h := pullbackPresentation_basis f (ambientQuotient K) i
  have he := congrArg (fun φ => Scheme.Modules.Hom.app (X:=T) φ ⊤ (freeBasisSection T 14 i)) hq
  exact (congrArg (d.hom.app ⊤) h).symm.trans he

def lineCoefficients {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules)) : Fin 14 → Γ(T,⊤) := fun i =>
  unitCoordinate T (e.hom.app ⊤ (pullbackGlobalSections f (lineBundle K) (lineSection K i)))

/-- Under the actual bundle isomorphisms, the actual universal section has the
literal normalized matrix-times-Plucker-coordinate value. -/
theorem equationSection_coordinates {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5)
    (q : freeOn T 14 ⟶ freeOn T 5)
    (hq : (pullbackPresentation f (ambientQuotient K)).map ≫ d.hom=q) :
    freeSectionCoordinates T 5
      ((pullbackTensorTrivialization f (lineBundle K) (quotientFive K) 5 e d).hom.app ⊤
        (pullbackGlobalSections f (equationBundle K) (equationSection K)))=
      (Stacks.FreeSheafMatrix.toMatrix q).mulVec (lineCoefficients K f e) := by
  simp only [equationSection,map_sum]
  funext j
  change (∑ i : Fin 14,freeSectionCoordinates T 5
    ((pullbackTensorTrivialization f (lineBundle K) (quotientFive K) 5 e d).hom.app ⊤
      (pullbackGlobalSections f (equationBundle K)
        (tensorSection K (lineSection K i) (quotientSection K i))))) j=_
  simp only [Finset.sum_apply,Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun v : Γ(freeOn T 5,⊤) => freeSectionCoordinates T 5 v j)
    (pullbackTensorTrivialization_apply f (lineBundle K) (quotientFive K) 5 e d
      (lineSection K i) (quotientSection K i))
  rw [← tensorSection_eq_tensorTop] at h
  simp only [map_smul,Pi.smul_apply,smul_eq_mul] at h
  rw [h,quotientSection_pullback K f d q hq]
  change lineCoefficients K f e i *
    freeSectionCoordinates T 5 (q.app ⊤ (freeBasisSection T 14 i)) j=_
  have hc : freeSectionCoordinates T 5 (q.app ⊤ (freeBasisSection T 14 i)) j=
      Stacks.FreeSheafMatrix.toMatrix q j i := freeCoordinates_map_basis q j i
  exact (congrArg (fun z => lineCoefficients K f e i*z) hc).trans (mul_comm _ _)

/-- Actual section vanishing is exactly vanishing of the actual matrix coefficient vector. -/
theorem equation_zero_iff_matrix_zero {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5)
    (q : freeOn T 14 ⟶ freeOn T 5)
    (hq : (pullbackPresentation f (ambientQuotient K)).map ≫ d.hom=q) :
    pullbackGlobalSections f (equationBundle K) (equationSection K)=0 ↔
      (Stacks.FreeSheafMatrix.toMatrix q).mulVec (lineCoefficients K f e)=0 := by
  have he := equationSection_coordinates K f e d q hq
  constructor
  · intro hs
    rw [← he,hs,map_zero,map_zero]
  · intro hm
    have hv := he.trans hm
    have hz := (freeSectionCoordinates T 5).injective (hv.trans (map_zero _).symm)
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((pullbackTensorTrivialization f (lineBundle K) (quotientFive K) 5 e d).hom.app ⊤)).injective).mp hz

/-- The original universal family factorization is detected by the literal coefficient equations. -/
theorem factorsThrough_iff_matrix_zero {T : Scheme.{u}} (f : T ⟶ ambient K)
    (e : (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5)
    (q : freeOn T 14 ⟶ freeOn T 5)
    (hq : (pullbackPresentation f (ambientQuotient K)).map ≫ d.hom=q) :
    (∃ g : T ⟶ family K,g ≫ inclusion K=f) ↔
      (Stacks.FreeSheafMatrix.toMatrix q).mulVec (lineCoefficients K f e)=0 :=
  (factorsThrough_iff_equation_zero K f).trans (equation_zero_iff_matrix_zero K f e d q hq)

end M9Native.LagrangianLinearSectionEquations
end
