module

public import M9StacksIntegration.LagrangianSectionGeneration

/-! A genuine global preimage of the unit gives a split epimorphism
onto the structure module. This is the actual sheaf statement, without
an assumed epimorphy or a pointwise surjectivity replacement. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.UnitSectionEpimorphism

open LagrangianAffineDeterminant LagrangianSectionGeneration

variable {X : Scheme.{u}} {F : X.Modules}
  (p : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (t : Γ(F,⊤)) (ht : p.app ⊤ t = (1 : Γ(X,⊤)))

include ht

theorem section_rightInverse : Scheme.Modules.unitHomEquivTop F t ≫ p = 𝟙 _ := by
  apply unitHom_ext_top_one
  change p.app ⊤ ((Scheme.Modules.unitHomEquivTop F t).app ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤))
  rw [unitHom_top_one,ht]

theorem epi_of_unit_preimage : Epi p :=
  epi_of_epi_fac (section_rightInverse p t ht)

end M9Native.UnitSectionEpimorphism
end
