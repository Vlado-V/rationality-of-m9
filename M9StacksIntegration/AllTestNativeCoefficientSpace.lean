module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import M9StacksIntegration.AllTestPointedRelocalizeFull

/-!
# Genuine inverse coefficient-base algebraic space

An actual native algebraic space over S' with an actual map to represented
S constructs an actual algebraic space over S. Its lower-shriek image is
isomorphic to the ORIGINAL native space and the isomorphism retains the
ORIGINAL supplied map to S. This is the proved native smaller-base
presheaf/slice equivalence, with genuine algebraicity reflection, rather
than an arbitrary field identification or assumed inverse factory.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeCoefficientSpace
universe u
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- The actual inverse coefficient-base space of an actual pointed space. -/
def coefficientSpace (X : AlgebraicSpaces B S' hS')
    (p : X.obj ⟶ yoneda.obj (Over.mk k)) : AlgebraicSpaces B S hS :=
  ⟨(smallerBasePresheafEquivalence B S S' hS hS' k).inverse.obj (Over.mk p),
    isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S S' hS hS' k
      (Over.mk p) X.property⟩

/-- Relocalizing the inverse factory recovers the SAME actual native space. -/
def coefficientRelocalizeIso (X : AlgebraicSpaces B S' hS')
    (p : X.obj ⟶ yoneda.obj (Over.mk k)) :
    (OverShriek.relocalizePresheafFunctor k).obj
        (coefficientSpace B S S' hS hS' k X p).obj ≅ X.obj :=
  ((smallerBasePresheafForgetIso B S S' hS hS' k).app
    (coefficientSpace B S S' hS hS' k X p).obj).symm ≪≫
    (Over.forget (yoneda.obj (Over.mk k))).mapIso
      ((smallerBasePresheafEquivalence B S S' hS hS' k).counitIso.app (Over.mk p))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse factory recovers the ORIGINAL supplied coefficient map,
not merely an isomorphic unpointed native presheaf. -/
theorem coefficientRelocalizeIso_toYoneda (X : AlgebraicSpaces B S' hS')
    (p : X.obj ⟶ yoneda.obj (Over.mk k)) :
    (coefficientRelocalizeIso B S S' hS hS' k X p).hom ≫ p =
      OverShriek.relocalizeToYoneda k (coefficientSpace B S S' hS hS' k X p).obj := by
  let E := smallerBasePresheafEquivalence B S S' hS hS' k
  let H := (coefficientSpace B S S' hS hS' k X p).obj
  let e := (smallerBasePresheafForgetIso B S S' hS hS' k).app H
  let c := E.counitIso.app (Over.mk p)
  change (e.inv ≫ c.hom.left) ≫ p = OverShriek.relocalizeToYoneda k H
  have hc : c.hom.left ≫ p = (E.functor.obj H).hom := Over.w c.hom
  have he : e.hom ≫ OverShriek.relocalizeToYoneda k H = (E.functor.obj H).hom :=
    AllTestPointedRelocalizeFull.forgetIso_hom_toYoneda B S S' hS hS' k H
  calc
    (e.inv ≫ c.hom.left) ≫ p = e.inv ≫ (c.hom.left ≫ p) := Category.assoc _ _ _
    _ = e.inv ≫ (E.functor.obj H).hom := congrArg (fun m => e.inv ≫ m) hc
    _ = e.inv ≫ (e.hom ≫ OverShriek.relocalizeToYoneda k H) :=
      congrArg (fun m => e.inv ≫ m) he.symm
    _ = OverShriek.relocalizeToYoneda k H := Iso.inv_hom_id_assoc e _

end M9StacksIntegration.AllTestNativeCoefficientSpace
