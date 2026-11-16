module

public import M9StacksIntegration.LagrangianUniversalSections
public import M9StacksIntegration.MukaiEvaluationMatrix

/-!
# Actual evaluation of triples in the original six-dimensional quotient system

The original six-space need not be identified with complete H0, and its
map to H0 need not be assumed injective. Every original triple defines
the actual constant free-sheaf map followed by the actual restricted
universal quotient. The equality with native H0 evaluation is proved on
the original free generators.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianUniversalTriples

open LagrangianMatrixChart LagrangianUniversalSections

variable {X : Scheme.{u}} (k : Type u) [Field k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)

/-- The literal original three columns in the original constant six-space. -/
def columnMatrix (s : Fin 3 → (Fin 6 → k)) : Matrix (Fin 6) (Fin 3) k :=
  Matrix.of fun i j => s j i

/-- Their actual constant free-sheaf map, with the original structural coefficients. -/
def sourceMap (s : Fin 3 → (Fin 6 → k)) : freeOn X 3 ⟶ freeOn X 6 :=
  Stacks.FreeSheafMatrix.ofMatrix ((columnMatrix k s).map (ExteriorEvaluation.baseRingMap k f))

/-- Each original generator has precisely its actual original constant-vector value. -/
theorem sourceMap_basis (s : Fin 3 → (Fin 6 → k)) (j : Fin 3) :
    (sourceMap k f s).app ⊤ (freeBasisSection X 3 j) = constantVector k f (s j) := by
  rw [SplitMatrixGrassmannianNaturality.freeMap_column_eq_sum]
  simp only [sourceMap, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    columnMatrix, Matrix.map_apply, Matrix.of_apply, constantVector]

/-- The literal native H0 evaluation of the original triple; no complete-system premise. -/
def evaluation (s : Fin 3 → (Fin 6 → k)) : freeOn X 3 ⟶ bundle k l :=
  MukaiSemiIrreducible.evaluation k f (bundle k l)
    (fun i => sectionMap k f l (s i))

/-- Its generator values are exactly the original quotient evaluated on the original vectors. -/
theorem evaluation_basis (s : Fin 3 → (Fin 6 → k)) (j : Fin 3) :
    (evaluation k f l s).app ⊤ (freeBasisSection X 3 j) =
      (quotientMap k l).app ⊤ (constantVector k f (s j)) :=
  (MukaiEvaluationMatrix.evaluation_basisSection k f (bundle k l)
    (fun i => sectionMap k f l (s i)) j).trans
      (sectionMap_constantVector k f l (s j))

/-- The original universal quotient, rather than a chosen H0 basis,
defines exactly this native triple evaluation morphism. -/
theorem evaluation_eq_sourceMap_quotient (s : Fin 3 → (Fin 6 → k)) :
    evaluation k f l s = sourceMap k f s ≫ quotientMap k l := by
  apply MukaiEvaluationMatrix.freeHom_ext_top
  intro j
  change (evaluation k f l s).app ⊤ (freeBasisSection X 3 j) =
    (quotientMap k l).app ⊤ ((sourceMap k f s).app ⊤ (freeBasisSection X 3 j))
  rw [sourceMap_basis]
  exact evaluation_basis k f l s j

end M9Native.LagrangianUniversalTriples
