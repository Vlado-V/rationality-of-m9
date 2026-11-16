module

public import M9StacksIntegration.LagrangianSymmetricPlucker
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeNonvanishingLocus

/-! The actual original Plucker point and the support of the actual
original determinant zero scheme. The selected preimage-open argument
is a thin replay of the pinned native GeneratingSectionsPointValue
proof, without its unrelated collinearity and rational-point imports.
Pinned source and Apache-2.0 provenance are retained in the audit. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.NonvanishingOpen
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

universe u

namespace M9Native.LagrangianPrimitivePointVanishing

open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianProjectiveIntersection LagrangianSymmetricPlucker

variable (K : Type u) [Field K] [CharZero K]
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

theorem preimage_basicOpen (v : Forms K) :
    canonicalPlucker K ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (grading K (Forms K))
        (SymmetricAlgebra.ι K (Forms K) v) =
      nonvanishingOpen (space K) (determinantLine K) (sectionLinear K v) := by
  refine ((classifies_classifyingPair K (Forms K) (determinantLine K)
    (sectionLinear K) (sectionLinear_generates K)).1 (degreeOneElement K (Forms K) v)).trans ?_
  change nonvanishingOpen (space K) (Stacks.TensorPowers.natTensorPow (determinantLine K) 1)
    ((veroneseOfLinearMap K (Forms K) (determinantLine K) (sectionLinear K)).pow
      (degreeOneElement K (Forms K) v).2 1) = _
  rw [pow_degreeOneElement,nonvanishingOpen_twistOneSection]

theorem mem_pointSubmodule_iff_not_mem_nonvanishingOpen (x : space K) (v : Forms K) :
    v ∈ pointSubmodule K (Forms K) ((canonicalPlucker K).base x) ↔
      x ∉ nonvanishingOpen (space K) (determinantLine K) (sectionLinear K v) := by
  rw [mem_pointSubmodule_iff]
  have hp : (x ∈ canonicalPlucker K ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (grading K (Forms K))
        (SymmetricAlgebra.ι K (Forms K) v)) ↔
      SymmetricAlgebra.ι K (Forms K) v ∉
        ((canonicalPlucker K).base x).asHomogeneousIdeal := Iff.rfl
  rw [preimage_basicOpen] at hp
  simpa only [not_not] using (not_congr hp).symm

/-- At every actual point, the primitive linear form belongs to its
actual projective point submodule precisely on the support of its
original determinant-section zero scheme. -/
theorem mem_pointSubmodule_iff_mem_support_zeroScheme (x : space K) (v : Forms K) :
    v ∈ pointSubmodule K (Forms K) ((canonicalPlucker K).base x) ↔
      x ∈ (zeroScheme (space K) (determinantLine K) (sectionLinear K v)).supportSet := by
  let : SheafOfModules.IsInvertible (space K).sheaf.obj (space K).ringCatSheaf.property
      (determinantLine K) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ (determinantLine_invertible K)
  have hn := mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme
    (determinantLine K) (sectionLinear K v) x
  change (x ∈ nonvanishingOpen (space K) (determinantLine K) (sectionLinear K v)) ↔
    x ∉ (zeroScheme (space K) (determinantLine K) (sectionLinear K v)).supportSet at hn
  rw [mem_pointSubmodule_iff_not_mem_nonvanishingOpen]
  simpa only [not_not] using not_congr hn

end M9Native.LagrangianPrimitivePointVanishing
end
