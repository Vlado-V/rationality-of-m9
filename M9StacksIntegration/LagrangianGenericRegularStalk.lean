module

public import M9StacksIntegration.LagrangianStalkTransport
public import M9StacksIntegration.LagrangianGenericChart

/-!
# The actual length-three regular stalk condition on the actual LG

The original actual matrix-chart square, its actual quotient-scheme
isomorphism and its actual three regular equations give exactly three
regular generators of the original inclusion's native stalk kernel at
each actual generic point. The generic point lies in the original big
cell by integrality. No expected codimension or top-Chern identity is
assumed in this condition for the genuine zero-section theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart

variable (K : Type u) [Field K]

/-- The actual chart isomorphism retains its original ambient quotient
inclusion, rather than merely identifying both charts with affine six. -/
def symmetryChartIso : lagrangianChart K ≅ symmetryScheme K :=
  ((ideal K).comapIso (matrixChart K)).symm ≪≫
    eqToIso (congrArg (fun I : (Spec (.of (MatrixRing K))).IdealSheafData => I.subscheme)
      (lagrangianIdeal_comap_eq_symmetryKer K)) ≪≫
    (asIso (symmetryInclusion K).toImage).symm

@[reassoc] theorem symmetryChartIso_hom_inclusion :
    (symmetryChartIso K).hom ≫ symmetryInclusion K =
      pullback.fst (matrixChart K) (inclusion K) := by
  simp only [symmetryChartIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [asIso_toImage_inv_imageι]
  change ((ideal K).comapIso (matrixChart K)).inv ≫
      (eqToIso (congrArg (fun I : (Spec (.of (MatrixRing K))).IdealSheafData => I.subscheme)
        (lagrangianIdeal_comap_eq_symmetryKer K))).hom ≫
      ((symmetryInclusion K).ker).subschemeι = _
  rw [eqToIso_subscheme_ι ((ideal K).comap (matrixChart K))
      ((symmetryInclusion K).ker) (lagrangianIdeal_comap_eq_symmetryKer K),
    Scheme.IdealSheafData.comapIso_inv_subschemeι]

theorem lagrangianChart_stalk_regular_three (y : lagrangianChart K) :
    RegularStalkKernel (pullback.fst (matrixChart K) (inclusion K)) y 3 := by
  have h : RegularStalkKernel (symmetryInclusion K) ((symmetryChartIso K).hom y) 3 :=
    symmetryInclusion_stalk_regular_three K ((symmetryChartIso K).hom y)
  have h' := (regularStalkKernel_source_open_iff (symmetryChartIso K).hom
    (symmetryInclusion K) y 3).mpr h
  rw [symmetryChartIso_hom_inclusion] at h'
  exact h'

/-- This is the literal native stalk-kernel condition, with the exact
length three, at every actual generic point of the actual LG scheme. -/
theorem generic_stalk_regular_three (xi : genericPoints (space K)) :
    ∃ rs : List ((grassmannian K).presheaf.stalk (inclusion K xi.val)),
      rs.length = 3 ∧ IsRegular ((grassmannian K).presheaf.stalk (inclusion K xi.val)) rs ∧
        Ideal.ofList rs = RingHom.ker ((inclusion K).stalkMap xi.val).hom := by
  rcases xi with ⟨xi, hxi⟩
  obtain ⟨z, hz⟩ := genericPoint_bigCell_factor K ⟨xi, hxi⟩
  change bigCell K z = xi at hz
  subst xi
  let y : lagrangianChart K := (lagrangianChartIsoPolynomialSix K).inv z
  have h := regularStalkKernel_of_open_square (lagrangianChartMap K) (inclusion K)
    (pullback.fst (matrixChart K) (inclusion K)) (matrixChart K)
      (pullback.condition (f := matrixChart K) (g := inclusion K)).symm y 3
      (lagrangianChart_stalk_regular_three K y)
  exact h

end M9Native.LagrangianDegree
