module

public import M9StacksIntegration.LagrangianTailLinearSpace
public import M9StacksIntegration.LagrangianProjectiveLinearForms

/-! Literal original tail rows lie in the actual tail constraint space,
and the original ordered tail list is precisely their `List.ofFn`. -/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
universe u
namespace M9Native.LagrangianTailLinearForms
open LagrangianProjectiveIntersection LagrangianProjectiveLinearForms LagrangianTailLinearSpace

theorem drop_ofFn_tail {α : Type u} (f : Fin 5 → α) (i : ℕ) (hi : i ≤ 5) :
    (List.ofFn f).drop i = List.ofFn (fun j : Fin (5 - i) => f (tailEmbedding i hi j)) := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    congr 1

theorem row_mem_constraints (K : Type u) [Field K]
    (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) (j : Fin (5 - i)) :
    rowForms K M.mulVecLin (tailEmbedding i hi j) ∈ constraints K M i hi := by
  refine ⟨(Pi.basisFun K (Fin (5 - i))).dualBasis j, ?_⟩
  apply LinearMap.ext
  intro w
  simp only [rowForms, LinearMap.dualMap_apply, Module.Basis.dualBasis_apply]
  change (tailMatrix K M i hi).mulVecLin w j = M.mulVecLin w (tailEmbedding i hi j)
  rfl

end M9Native.LagrangianTailLinearForms
