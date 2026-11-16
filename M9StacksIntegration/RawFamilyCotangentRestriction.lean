module

public import M9StacksIntegration.SchemeRawCompatibleMorphism
public import M9StacksIntegration.CompatibleMorphismClassNecessity

/-! The original direct cotangent restriction equation for the actual
raw extensions of a native scheme-morphism coordinate family. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Deformation Deformation.Examples RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening
open M9Native.SchemeRawCompatibleMorphism

attribute [local instance 5000] _root_.SheafOfModules.instAbelian
attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.RawFamilyCotangentRestriction

/-- Translate the checked necessary equation through equalities of the
actual underlying extensions, before specializing their presentation data. -/
theorem restriction_eq_zero_of_extension_equalities
    {Y X S : RingedSpace.{u,u}} {f : Y ⟶ S} {g : X ⟶ Y}
    {F : SheafOfModules.{u} (structureSheafRing Y)}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
    (c : F ⟶ (modulePushforward g).obj G) (h : CompatibleMorphism P Q c)
    (P₀ : AlgebraSquareZeroExtension f F) (Q₀ : AlgebraSquareZeroExtension (g ≫ f) G)
    (hP : P.toAlgebraSquareZeroExtension = P₀) (hQ : Q.toAlgebraSquareZeroExtension = Q₀)
    (hP₀ : P₀.toPresented.extClass = 0) :
    derivedPullbackNaiveCotangentMap g f ≫ Q₀.toPresented.extClass = 0 := by
  have hP' := (congrArg (fun e : AlgebraSquareZeroExtension f F =>
    e.toPresented.extClass) hP).trans hP₀
  have hn := CompatibleMorphismClassNecessity.restrict_extClass_eq_zero
    (g := g) (f := f) (P := P) (Q := Q) (c := c) h hP'
  have he := congrArg (fun e : AlgebraSquareZeroExtension (g ≫ f) G =>
    derivedPullbackNaiveCotangentMap g f ≫ e.toPresented.extClass) hQ
  exact he.symm.trans hn

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (g : X ⟶ Y)
  (pY : Y ⟶ Spec (.of k)) (V : FGModuleCat.{u} k)
  (z : FamilyFiber (Λ := k) g (g ≫ pY) pY rfl V)

/-- A zero actual raw target class forces zero restriction of the actual
raw source class along the original native direct cotangent arrow. -/
theorem raw_restriction_eq_zero
    (htarget : SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk pY) V
      (targetFiber g (g ≫ pY) pY rfl V z) = 0) :
    derivedPullbackNaiveCotangentMap g.toLRSHom.toShHom pY.toLRSHom.toShHom ≫
      SchemeRawDifferenceClass.rawFiberClass (Λ := k) (Over.mk (g ≫ pY)) V
        (sourceFiber g (g ≫ pY) pY rfl V z) = 0 := by
  exact restriction_eq_zero_of_extension_equalities
    (g := g.toLRSHom.toShHom) (f := pY.toLRSHom.toShHom)
    (literalTargetExtension g pY V z) (literalSourceExtension g pY V z)
    (literalCoefficientMap g pY V z) (compatibleLiteral g pY V z)
    (SchemeRawDifferenceClass.rawFiberExtension (Over.mk pY) V
      (targetFiber g (g ≫ pY) pY rfl V z))
    (SchemeRawDifferenceClass.rawFiberExtension (Over.mk (g ≫ pY)) V
      (sourceFiber g (g ≫ pY) pY rfl V z))
    (literalTargetExtension_toAlgebra g pY V z) (literalSourceExtension_toAlgebra g pY V z)
    htarget

end M9Native.RawFamilyCotangentRestriction
