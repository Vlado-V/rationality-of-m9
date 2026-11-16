module

public import M9StacksIntegration.CurriedHomSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom

/-!
# The actual curried Hom bundle is the native sheaf-Hom

The monoidal internal Hom used for the actual incidence section is
canonically the native sheaf of local module morphisms. The isomorphism
comes from uniqueness of the actual tensor right adjoint; it is not a
comparison supplied as data.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.HomBundleComparison

@[instance_reducible] local instance moduleMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

@[instance_reducible] local instance moduleClosed (X : Scheme.{u}) :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosedSheafTensor X.sheaf

/-- The actual monoidal internal Hom is the actual native sheaf-Hom. -/
def homBundleIsoSheafHom {X : Scheme.{u}} (E F : X.Modules) :
    CurriedHomSection.homBundle E F ≅
      Stacks.SheafOfModules.sheafHom X.sheaf.obj X.ringCatSheaf.property E F :=
  Stacks.SheafOfModules.InternalHom.ihomIsoInternalHom X.sheaf E F

end M9Native.HomBundleComparison
