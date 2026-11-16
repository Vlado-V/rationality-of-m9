module

public import M9StacksIntegration.IntegralRestrictionPrefixes
public import M9StacksIntegration.LagrangianPrimitiveSystem

/-! The exact original section-list prefix convention feeds the
literal integral-cut ladder. Geometry remains geometry; no kernel or
linear-normality conclusion is placed in its input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianIntegralPrefixData

open LagrangianPrimitiveSystem IteratedLineSectionCuts

variable (K : Type u) [Field K]

theorem map_take_sections (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) :
    ((List.ofFn M).take i).map (system K).sectionOf = (sectionList K M).take i := by
  rw [List.map_take,coefficientSectionList_eq]

theorem integralPrefixes_of_data (M : Matrix (Fin 5) (Fin 14) K)
    (hI : ∀ (i : ℕ) (_hi : i ≤ 5),
      IsIntegral (simultaneousCut (LagrangianPluckerQuotient.determinantLine K)
        ((sectionList K M).take i)).left)
    (hN : ∀ (i : ℕ) (hi : i < 5),
      pullbackGlobalSections
        (simultaneousCut (LagrangianPluckerQuotient.determinantLine K)
          ((sectionList K M).take i)).hom
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i,hi⟩)) ≠ 0) :
    IntegralPrefixes K M := by
  apply IntegralRestrictionPrefixes.integralSteps_of_simultaneous_prefixes (system K) (List.ofFn M)
  · intro i hi
    have hi5 : i < 5 := by simpa only [List.length_ofFn] using hi
    change IsIntegral (simultaneousCut (LagrangianPluckerQuotient.determinantLine K)
      (((List.ofFn M).take i).map (system K).sectionOf)).left
    rw [map_take_sections]
    exact hI i hi5.le
  · intro i hi
    have hi5 : i < 5 := by simpa only [List.length_ofFn] using hi
    change pullbackGlobalSections
      (simultaneousCut (system K).L (((List.ofFn M).take i).map (system K).sectionOf)).hom
      (system K).L ((system K).sectionOf (List.ofFn M)[i]) ≠ 0
    rw [map_take_sections,List.getElem_ofFn,system_section]
    exact hN i hi5

end M9Native.LagrangianIntegralPrefixData
end
