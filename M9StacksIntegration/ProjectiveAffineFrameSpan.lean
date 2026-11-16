module
public import M9StacksIntegration.ProjectiveLinearSystemFactor
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit
namespace M9Native.ProjectiveLinearSystemFactor
open LagrangianMatrixChart LagrangianPluckerQuotient LagrangianSectionGeneration
/-- On an actual affine scheme, generating functions generate the
actual global unit ideal. -/
theorem affine_span_range_of_unit_generates {T : Scheme.{u}} [IsAffine T] {r : ℕ}
    [Stacks.Ample.IsInvertibleModule T (ProjectiveSectionFunctions.UnitLine T)]
    (s : Fin r → Γ(T, ⊤))
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks
      (show Fin r → Γ(ProjectiveSectionFunctions.UnitLine T, ⊤) from s)) :
    Ideal.span (Set.range s) = ⊤ := by
  let L : T.Modules := ProjectiveSectionFunctions.UnitLine T
  let φ := sectionMap T L (show Fin r → Γ(L, ⊤) from s)
  let : Epi φ := LagrangianPluckerGeneration.sectionMap_epi_of_generatesStalks
    (X := T) (Q := L) (show Fin r → Γ(L, ⊤) from s) hs
  let hfree := AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank T r
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeOn T r) := hfree.isFiniteLocallyFree
  let : (freeOn T r).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  let hunit := SheafOfModules.isFiniteLocallyFreeOfRank_unit T
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} L := hunit.isFiniteLocallyFree
  let : L.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  have hsurj := surjective_sectionsLinearMap_of_epi φ
  obtain ⟨v,hv⟩ := hsurj (1 : Γ(T, ⊤))
  have hc := (sectionMap_top_apply T L (show Fin r → Γ(L, ⊤) from s) v).symm.trans hv
  change (∑ j : Fin r, freeSectionCoordinates T r v j * s j) = 1 at hc
  rw [Ideal.eq_top_iff_one]
  rw [← hc]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

end M9Native.ProjectiveLinearSystemFactor
