module

public import M9StacksIntegration.LagrangianHyperplaneEvaluation
public import M9StacksIntegration.LagrangianConstantSymplectic
public import M9StacksIntegration.UnitSectionEpimorphism
public import M9StacksIntegration.SymplecticFunctionalCoordinates

/-! A nonzero original six-vector gives the actual split epimorphic
symplectic functional. Its constant right inverse is constructed from
the original nondegenerate pairing, rather than supplied as a premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianHyperplaneEpimorphism

open LagrangianMatrixChart LagrangianUniversalSections LagrangianHyperplaneEvaluation

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

theorem omegaMap_constant_pairing (v w : Fin 6 → k) :
    (omegaMap k f v).app ⊤ (constantVector k f w) =
      ExteriorEvaluation.baseRingMap k f (LagrangianRing.omega k v w) := by
  change (SymplecticQuotientEvaluation.omegaFunctional (constantVector k f v)).app ⊤
    (constantVector k f w) = _
  rw [SymplecticFunctionalCoordinates.omegaFunctional_top_pairing]
  exact LagrangianConstantSymplectic.constantVector_pairing k f v w

theorem exists_constant_rightInverse (v : Fin 6 → k) (hv : v ≠ 0) :
    ∃ w : Fin 6 → k, Scheme.Modules.unitHomEquivTop (freeOn X 6) (constantVector k f w) ≫
      omegaMap k f v = 𝟙 _ := by
  obtain ⟨w,hw⟩ := LagrangianConstantSymplectic.exists_constant_pairing_one k f v hv
  refine ⟨w,UnitSectionEpimorphism.section_rightInverse (omegaMap k f v)
    (constantVector k f w) ?_⟩
  change (SymplecticQuotientEvaluation.omegaFunctional (constantVector k f v)).app ⊤
    (constantVector k f w) = (1 : Γ(X,⊤))
  rw [SymplecticFunctionalCoordinates.omegaFunctional_top_pairing]
  exact hw

theorem omegaMap_epi (v : Fin 6 → k) (hv : v ≠ 0) : Epi (omegaMap k f v) := by
  obtain ⟨w,hw⟩ := exists_constant_rightInverse k f v hv
  exact epi_of_epi_fac hw

end M9Native.LagrangianHyperplaneEpimorphism
end
