module

public import M9StacksIntegration.SpecFieldStalkSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-! On an actual field spectrum, epimorphisms of native module sheaves
are surjective on the original field-linear global sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.SpecFieldEpimorphism

open SpecFieldStalkSections

variable (K : Type u) [Field K]

theorem sections_surjective {M N : (Spec (.of K)).Modules} (φ : M ⟶ N) [Epi φ] :
    Function.Surjective (moduleSpecΓFunctor.map φ).hom := by
  intro y
  have hφ := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := (Spec (.of K)).ringCatSheaf) φ).mp inferInstance (point K)
  obtain ⟨s, hs⟩ := hφ (sectionsStalkEquiv K N y)
  refine ⟨(sectionsStalkEquiv K M).symm s, ?_⟩
  apply (sectionsStalkEquiv K N).injective
  have hn := AlgebraicGeometry.SheafOfModules.stalkMap_germ
    (Spec (.of K)).ringCatSheaf (point K) φ ⊤ (by trivial)
      ((sectionsStalkEquiv K M).symm s)
  calc
    _ = (AlgebraicGeometry.SheafOfModules.stalkMap (Spec (.of K)).ringCatSheaf
        (point K) φ).hom
        (sectionsStalkEquiv K M ((sectionsStalkEquiv K M).symm s)) := hn.symm
    _ = (AlgebraicGeometry.SheafOfModules.stalkMap (Spec (.of K)).ringCatSheaf
        (point K) φ).hom s := congrArg _ ((sectionsStalkEquiv K M).apply_symm_apply s)
    _ = _ := hs

end M9Native.SpecFieldEpimorphism
