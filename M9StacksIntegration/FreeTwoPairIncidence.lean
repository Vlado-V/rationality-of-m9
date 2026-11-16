module

public import M9StacksIntegration.FreeTwoProjectiveCharts
public import M9StacksIntegration.TensorFreeCoordinates
public import M9StacksIntegration.SectionZeroSubbundle

/-! The actual free-two coefficient incidence, in the original
sheaf-graded projective bundle. The target comes FIRST and the true
tautological line comes second. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.FreeTwoPairIncidence
open LagrangianMatrixChart LinearIncidenceTensorCoordinates FreeTwoProjectiveCharts

variable (X : Scheme.{u}) (F : X.Modules)

abbrev pulledTarget := (Scheme.Modules.pullback (projectiveBundleProjection X)).obj F
abbrev equationBundle :=
  tensorObj (projectiveBundleSpace X) (pulledTarget X F) (tautologicalLine X)

def equationSection (s : Fin 2 → Γ(F,⊤)) : Γ(equationBundle X F,⊤) :=
  ∑ i : Fin 2, tensorTop (projectiveBundleSpace X) (pulledTarget X F) (tautologicalLine X)
    (pullbackGlobalSections (projectiveBundleProjection X) F (s i)) (tautCoordinate X i)

def ideal (s : Fin 2 → Γ(F,⊤)) : (projectiveBundleSpace X).IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal (projectiveBundleSpace X)
    (equationBundle X F) (equationSection X F s)

abbrev space (s : Fin 2 → Γ(F,⊤)) := (ideal X F s).subscheme
abbrev inclusion (s : Fin 2 → Γ(F,⊤)) : space X F s ⟶ projectiveBundleSpace X :=
  (ideal X F s).subschemeι
def toBase (s : Fin 2 → Γ(F,⊤)) : space X F s ⟶ X :=
  inclusion X F s ≫ projectiveBundleProjection X

instance tautologicalLine_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tautologicalLine X) 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (projectiveBundleSpace X) (tautologicalLine X)
    (Stacks.Chow.isInvertible_bundleTwist (freeOn X 2))

instance equationBundle_rank (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle X F) r := by
  letI := isFiniteLocallyFreeOfRank_pullback (projectiveBundleProjection X) F r
  letI := tautologicalLine_rank X
  have h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle X F) (r * 1) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
      (projectiveBundleSpace X) (pulledTarget X F) (tautologicalLine X) r 1
  exact (Nat.mul_one r) ▸ h

theorem factors_iff (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    (s : Fin 2 → Γ(F,⊤)) {T : Scheme.{u}} (f : T ⟶ projectiveBundleSpace X) :
    (∃ a : T ⟶ space X F s, a ≫ inclusion X F s=f) ↔
      pullbackGlobalSections f (equationBundle X F) (equationSection X F s)=0 :=
  (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (equationBundle X F) r (equationSection X F s) f).symm

end M9Native.FreeTwoPairIncidence
