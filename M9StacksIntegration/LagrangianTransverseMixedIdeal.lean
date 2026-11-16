module
public import M9StacksIntegration.LagrangianPolynomialLinearRows
public import M9StacksIntegration.ClosedSectionCutIdeal
public import M9StacksIntegration.LagrangianOrderedFibre
public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianPluckerClosed

/-! The ORIGINAL five ordered linear cuts inside the ORIGINAL LG image.
Their ambient kernel is the sum of the original LG kernel and the five
actual polynomial row ideals. No defining-ideal hypothesis is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
universe u

namespace M9Native.LagrangianTransverseMixedIdeal
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianSymmetricPlucker
open LagrangianProjectiveLinearForms LagrangianPolynomialPluckerFrame
open LagrangianPolynomialLinearRows LagrangianTransverseRestriction

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)

def rowAmbientIdeal := ⨆ j : Fin 5,
  MixedQuadraticTrisecant.degreeIdeal K 13 1 (rowPolynomial K M j)

def rowOnLGIdeal : (space K).IdealSheafData := ⨆ j : Fin 5,
  zeroScheme (space K) (determinantLine K) (sectionLinear K (rowForms K M.mulVecLin j))

/-- The literal ordered cut has exactly the original row-zero ideal. -/
theorem inclusion_kernel : (inclusion K M).ker = rowOnLGIdeal K M := by
  let i := inclusion K M
  let J := rowOnLGIdeal K M
  have hself : IteratedLineSectionCuts.FactorsThrough i (LagrangianPrimitiveSystem.sectionCut K M) :=
    ⟨𝟙 _, Category.id_comp _⟩
  have hz := (LagrangianOrderedFibre.sectionCut_factorsThrough_iff_rows K M i).mp hself
  have hJ : J ≤ i.ker := by
    apply iSup_le
    intro j
    obtain ⟨g,hg⟩ :=
      (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (space K)
        (determinantLine K) (sectionLinear K (rowForms K M.mulVecLin j)) i).mp (hz j)
    have h := Scheme.Hom.le_ker_comp g
      (zeroScheme (space K) (determinantLine K) (sectionLinear K (rowForms K M.mulVecLin j))).subschemeι
    rw [hg, Scheme.IdealSheafData.ker_subschemeι] at h
    exact h
  have hvan (j : Fin 5) : pullbackGlobalSections J.subschemeι (determinantLine K)
      (sectionLinear K (rowForms K M.mulVecLin j)) = 0 := by
    have hj : zeroScheme (space K) (determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) ≤ J := by
      exact le_iSup (fun a : Fin 5 => zeroScheme (space K) (determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin a))) j
    exact (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (space K)
      (determinantLine K) (sectionLinear K (rowForms K M.mulVecLin j)) J.subschemeι).mpr
      ⟨Scheme.IdealSheafData.inclusion hj, Scheme.IdealSheafData.inclusion_subschemeι hj⟩
  obtain ⟨g,hg⟩ :=
    (LagrangianOrderedFibre.sectionCut_factorsThrough_iff_rows K M J.subschemeι).mpr hvan
  apply le_antisymm _ hJ
  have h := Scheme.Hom.le_ker_comp g i
  rw [hg, Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

/-- Pulling the ambient polynomial row equations gives exactly the
original row-zero ideals, including on nonreduced schemes. -/
theorem rowAmbientIdeal_comap :
    (rowAmbientIdeal K M).comap (polynomialPlucker K) = rowOnLGIdeal K M := by
  apply le_antisymm
  · apply (Scheme.IdealSheafData.le_map_iff_comap_le).mp
    apply iSup_le
    intro j
    exact (Scheme.IdealSheafData.le_map_iff_comap_le).mpr
      ((rowIdeal_comap K M j).le.trans
        (le_iSup (fun a : Fin 5 => zeroScheme (space K) (determinantLine K)
          (sectionLinear K (rowForms K M.mulVecLin a))) j))
  · apply iSup_le
    intro j
    rw [← rowIdeal_comap K M j]
    exact Scheme.IdealSheafData.comap_mono (polynomialPlucker K)
      (le_iSup (fun a : Fin 5 =>
        MixedQuadraticTrisecant.degreeIdeal K 13 1 (rowPolynomial K M a)) j)

/-- The actual original transverse curve's full polynomial ambient ideal.
The original LG ideal remains visible; it is not replaced by an assumed
quadric description. -/
theorem polynomial_inclusion_kernel :
    (inclusion K M ≫ polynomialPlucker K).ker =
      rowAmbientIdeal K M ⊔ (polynomialPlucker K).ker := by
  letI : IsClosedImmersion (inclusion K M) := IteratedLineSectionCuts.simultaneousCut_closed _ _
  letI : IsClosedImmersion (LagrangianPlucker.primitivePlucker K) :=
    LagrangianPluckerClosed.primitivePlucker_isClosedImmersion K
  letI : IsClosedImmersion (polynomialPlucker K) := by
    dsimp only [polynomialPlucker]
    infer_instance
  exact ClosedSectionCutIdeal.composite_kernel_of_comap (polynomialPlucker K)
    (inclusion K M) (rowAmbientIdeal K M)
    ((inclusion_kernel K M).trans (rowAmbientIdeal_comap K M).symm)

end M9Native.LagrangianTransverseMixedIdeal
