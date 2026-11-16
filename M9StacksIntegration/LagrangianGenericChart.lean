module

public import M9StacksIntegration.LagrangianIntegral

/-!
# Every actual LG generic point lies in the original matrix chart

Integrality of the actual LG and nonemptiness of its actual affine-six
big cell place every generic point in that original chart. This is the
generic-point scope of the genuine top-Chern zero-section theorem.
No transitivity of an ambient Grassmannian action or codimension
assumption is used to move its regular-sequence calculation to a point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart

variable (K : Type u) [Field K]

theorem genericPoint_mem_bigCell (xi : genericPoints (space K)) :
    xi.val ∈ Set.range (bigCell K) := by
  have hxi : IsGenericPoint xi.val (Set.univ : Set (space K)) := by
    change closure {xi.val} = Set.univ
    have h := xi.property
    change closure {xi.val} ∈ irreducibleComponents (space K) at h
    rw [irreducibleComponents_eq_singleton] at h
    exact Set.mem_singleton_iff.mp h
  apply (hxi.mem_open_set_iff (bigCell K).isOpenEmbedding.isOpen_range).mpr
  let z := genericPoint (Spec (.of (MvPolynomial (Fin 6) K)))
  exact ⟨bigCell K z, Set.mem_univ _, ⟨z, rfl⟩⟩

theorem genericPoint_bigCell_factor (xi : genericPoints (space K)) :
    ∃ z : Spec (.of (MvPolynomial (Fin 6) K)), bigCell K z = xi.val :=
  genericPoint_mem_bigCell K xi

/-- The image of every actual LG generic point is in the original
ambient affine-nine matrix chart, with the original cartesian maps. -/
theorem genericPoint_matrixChart_factor (xi : genericPoints (space K)) :
    ∃ a : Spec (.of (MatrixRing K)), matrixChart K a = inclusion K xi.val := by
  obtain ⟨z, hz⟩ := genericPoint_bigCell_factor K xi
  let y : lagrangianChart K := (lagrangianChartIsoPolynomialSix K).inv z
  refine ⟨pullback.fst (matrixChart K) (inclusion K) y, ?_⟩
  have hcart := congrArg
    (fun f : lagrangianChart K ⟶ grassmannian K => f y)
    (pullback.condition (f := matrixChart K) (g := inclusion K))
  change matrixChart K (pullback.fst (matrixChart K) (inclusion K) y) =
    inclusion K (pullback.snd (matrixChart K) (inclusion K) y) at hcart
  rw [hcart]
  exact congrArg (inclusion K) hz

end M9Native.LagrangianDegree
