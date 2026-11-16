module

public import M9StacksIntegration.LagrangianUniversalTriples

/-! Actual tuple evaluation in an original complete six-section basis.
The three-column map is the literal structural coefficient matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.MukaiTupleEvaluationCoordinates

open MukaiEvaluationMatrix LagrangianUniversalTriples LagrangianUniversalSections
open LagrangianMatrixChart

variable (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))

/-- Every original vector is evaluated by its actual constant free
section in the original complete cohomology basis. -/
theorem evaluation_constantVector (v : Fin 6 → K) :
    (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation K f E b) ⊤) (constantVector K f v) =
      ExteriorEvaluation.h0SectionsSemilinear K f E (b.equivFun.symm v) := by
  change (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation K f E b) ⊤)
    (∑ j : Fin 6, ExteriorEvaluation.baseRingMap K f (v j) • freeBasisSection X 6 j) = _
  simp only [map_sum, Scheme.Modules.Hom.app_smul, evaluation_basisSection]
  have hs : (∑ j : Fin 6, v j • b j) = b.equivFun.symm v := by
    have h := b.sum_repr (b.equivFun.symm v)
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using h
  have h := congrArg (ExteriorEvaluation.h0SectionsSemilinear K f E) hs
  simpa only [map_sum, map_smulₛₗ] using h

/-- Evaluation of an arbitrary actual triple is precomposition of the
original complete evaluation by its original coefficient columns. -/
theorem evaluation_eq_sourceMap (s : Fin 3 → (Fin 6 → K)) :
    MukaiSemiIrreducible.evaluation K f E (fun i => b.equivFun.symm (s i)) =
      LagrangianUniversalTriples.sourceMap K f s ≫ MukaiSemiIrreducible.evaluation K f E b := by
  apply freeHom_ext_top
  intro j
  change (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation K f E (fun i => b.equivFun.symm (s i))) ⊤)
    (freeBasisSection X 3 j) =
    (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation K f E b) ⊤)
      ((LagrangianUniversalTriples.sourceMap K f s).app ⊤ (freeBasisSection X 3 j))
  rw [evaluation_basisSection, sourceMap_basis, evaluation_constantVector]

end M9Native.MukaiTupleEvaluationCoordinates
