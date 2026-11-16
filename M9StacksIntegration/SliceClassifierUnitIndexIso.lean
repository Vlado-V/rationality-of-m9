module

public import M9StacksIntegration.PresheafValuedClassifierReflection

/-! The value of an actually precomposed classifier over the identity is
vertically isomorphic to its value at the literal original slice arrow.
The comparison comes from the genuine isomorphism in `Over`, rather than
an equality of object presentations or a supplied compatibility. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.SliceClassifierUnitIndexIso

universe u v uD vD
variable {C : Type u} [Category.{v} C] {U T : C}

/-- The literal identity slice index after postcomposition is genuinely
isomorphic to the specified original arrow. -/
def indexIso (a : T ⟶ U) :
    (Over.map a).obj (Functor.FiberedMor.unit T) ≅ Over.mk a :=
  Over.isoMk (Iso.refl T) (by simp)

variable {D : BasedCategory.{vD, uD} C}
  (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ D) (a : T ⟶ U)

/-- The actual classifier image of the original slice-index isomorphism. -/
def valueIso :
    (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A).obj
        (Functor.FiberedMor.unit T) ≅ A.obj (Over.mk a) :=
  A.toFunctor.mapIso (indexIso a)

/-- Both values are compared over the identity of the SAME test object. -/
theorem valueIso_hom_lift :
    D.p.IsHomLift (𝟙 T) (valueIso A a).hom := by
  have : (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift (𝟙 T) (indexIso a).hom :=
    IsHomLift.map (Over.forget U) (indexIso a).hom
  exact BasedFunctor.preserves_isHomLift A (𝟙 T) (indexIso a).hom

end M9Native.SliceClassifierUnitIndexIso
