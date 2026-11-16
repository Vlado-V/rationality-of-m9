module

public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import M9StacksIntegration.IntegralRestrictionLadder

/-! Transport of the actual original primitive restriction kernel
through an actual scheme isomorphism.  Pullback-zero detection is proved
from the actual inverse and identity pullback, not supplied as an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.LagrangianRestrictionIso

theorem pullback_iso_zero_iff {X Y : Scheme.{u}} (e : X ≅ Y)
    (L : Y.Modules) (s : Γ(L,⊤)) :
    pullbackGlobalSections e.hom L s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    have hc : pullbackGlobalSections (e.inv ≫ e.hom) L s = 0 :=
      (IteratedLineSectionCuts.pullback_comp_zero_iff L e.inv e.hom s).mpr (by
        rw [hs,map_zero])
    rw [e.inv_hom_id] at hc
    have hi := IntegralRestrictionLadder.pullbackId_section L s
    rw [hc,map_zero] at hi
    exact hi.symm
  · intro hs
    rw [hs,map_zero]

theorem pullback_over_iso_zero_iff {X Y Z : Scheme.{u}} (e : X ≅ Y)
    (lX : X ⟶ Z) (lY : Y ⟶ Z) (he : e.hom ≫ lY = lX)
    (L : Z.Modules) (s : Γ(L,⊤)) :
    pullbackGlobalSections lX L s = 0 ↔ pullbackGlobalSections lY L s = 0 := by
  rw [← he,IteratedLineSectionCuts.pullback_comp_zero_iff]
  exact pullback_iso_zero_iff e ((Scheme.Modules.pullback lY).obj L)
    (pullbackGlobalSections lY L s)

theorem primitiveRestriction_kernel_iso {X Y : Scheme.{u}} (k : Type u) [Field k]
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    (lX : X ⟶ LagrangianGrassmannian.space k) (lY : Y ⟶ LagrangianGrassmannian.space k)
    (hX : lX ≫ LagrangianGrassmannian.projection k = fX)
    (hY : lY ≫ LagrangianGrassmannian.projection k = fY)
    (e : X ≅ Y) (he : e.hom ≫ lY = lX) :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction k fX lX) =
      LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction k fY lY) := by
  ext v
  rw [LinearMap.mem_ker,LinearMap.mem_ker,
    LagrangianPrimitiveRestriction.primitiveRestriction_ker_iff k fX lX hX,
    LagrangianPrimitiveRestriction.primitiveRestriction_ker_iff k fY lY hY]
  exact pullback_over_iso_zero_iff e lX lY he (LagrangianPluckerQuotient.determinantLine k)
    (LagrangianHyperplaneCoordinates.determinantSection k v)

end M9Native.LagrangianRestrictionIso
end
