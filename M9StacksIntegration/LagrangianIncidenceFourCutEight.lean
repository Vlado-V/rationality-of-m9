module

public import M9StacksIntegration.LagrangianIncidenceFourCutClass
public import M9StacksIntegration.LagrangianMixedDegreeEight

/-! The actual full finite four-cut on the original independent-plane
incidence has length eight. All class, compatibility and numerical
degree data are derived from their genuine producers. Only actual
independence and finiteness of the full scheme occur as geometric
inputs; the original-curve comparison supplies the latter separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.LagrangianIncidenceFourCutEight
open LagrangianIncidenceFourCutBase LagrangianIncidenceFourCapPush
open LagrangianIncidenceFourCutClass
variable (K : Type u) [Field K] [CharZero K]

theorem finrank_fourCut_eq_eight (w : Fin 2 → (Fin 6 → K))
    (hw : LinearIndependent K w) (N : Matrix (Fin 5) (Fin 14) K)
    [IsFinite (fourInclusion K w N ≫ structuralMap K w)] :
    letI : Algebra K Γ(fourCut K w N, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (fourInclusion K w N ≫ structuralMap K w).appTop).hom.toAlgebra
    (Module.finrank K Γ(fourCut K w N, ⊤) : ℤ) = 8 := by
  exact (finrank_fourCut_eq_mixedDegree K w hw N).trans
    (LagrangianMixedDegreeEight.mixedDegree_eq_eight K)

theorem finrank_fourCut_eq_eight_nat (w : Fin 2 → (Fin 6 → K))
    (hw : LinearIndependent K w) (N : Matrix (Fin 5) (Fin 14) K)
    [IsFinite (fourInclusion K w N ≫ structuralMap K w)] :
    letI : Algebra K Γ(fourCut K w N, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (fourInclusion K w N ≫ structuralMap K w).appTop).hom.toAlgebra
    Module.finrank K Γ(fourCut K w N, ⊤) = 8 := by
  exact_mod_cast finrank_fourCut_eq_eight K w hw N

end M9Native.LagrangianIncidenceFourCutEight
