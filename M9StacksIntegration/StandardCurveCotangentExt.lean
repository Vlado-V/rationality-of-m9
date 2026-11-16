module

public import M9StacksIntegration.StandardSmoothCotangent
public import M9StacksIntegration.DualExtNaturality
public import M9StacksIntegration.CurveTangentLineGeometry
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The original standard-model curve extension class as actual tangent H1

The source is the literal native ringed-space extension-class group used
by the geometric difference-class and compatible-morphism constructions.
Actual standard-model smooth normalization and model-independent Yoneda
Ext give a scalar-compatible map to actual tangent H1. The final step is
the evaluation-natural dual comparison, with no inverse-tensor choice.
The separate locally-small scheme tangent classifier is preserved.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.RingedSpaceThickening

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.StandardCurveCotangentExt

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

/-- The original field action on the actual native standard extension group. -/
@[instance_reducible]
def nativeExtModule (G : X.Modules) :
    Module k (extOneNaiveCotangent f.toLRSHom.toShHom G) := by
  let := modulesLinearOverField k f
  exact inferInstanceAs (Module k
    (StandardSmoothCotangent.nativeObject f ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧))

/-- Actual original standard-model extension classes become ordinary
Yoneda Ext of the original sheaf of differentials, linearly over k. -/
def ordinaryExtOneLinearEquiv [Smooth f] (G : X.Modules) :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f G
    extOneNaiveCotangent f.toLRSHom.toShHom G ≃ₗ[k]
      Ext.{u} (Scheme.Hom.relativeDifferentials f) G 1 := by
  let := modulesLinearOverField k f
  let := nativeExtModule f G
  exact (Linear.homCongr k (StandardSmoothCotangent.differentialsIso f) (Iso.refl _)).trans
    (Ext.homLinearEquiv (R := k)).symm

/-- The class map is literal precomposition with the genuine normalized
standard smooth comparison, followed by the original Ext hom bijection. -/
theorem ordinaryExtOneLinearEquiv_hom [Smooth f] (G : X.Modules)
    (ξ : extOneNaiveCotangent f.toLRSHom.toShHom G) :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f G
    (ordinaryExtOneLinearEquiv f G ξ).hom =
      (StandardSmoothCotangent.differentialsIso f).inv ≫ ξ := by
  let := modulesLinearOverField k f
  let := nativeExtModule f G
  change (Ext.homLinearEquiv (R := k)
      (X := Scheme.Hom.relativeDifferentials f) (Y := G) (n := 1))
    ((Ext.homLinearEquiv (R := k)
      (X := Scheme.Hom.relativeDifferentials f) (Y := G) (n := 1)).symm
      (((StandardSmoothCotangent.differentialsIso f).inv ≫ ξ) ≫ 𝟙 _)) =
        (StandardSmoothCotangent.differentialsIso f).inv ≫ ξ
  rw [LinearEquiv.apply_symm_apply]
  exact Category.comp_id _

/-- The exact original standard geometric class group identifies with
actual native tangent H1, preserving the field action and dual-map normalization. -/
def tangentOneLinearEquiv [IsCurve k f] [Smooth f] :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f (InvertibleExtCancellation.unit X)
    extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  let := modulesLinearOverField k f
  let := nativeExtModule f (InvertibleExtCancellation.unit X)
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact (ordinaryExtOneLinearEquiv f (InvertibleExtCancellation.unit X)).trans
    (DualExtNaturality.dualExtOneCohomologyLinearEquiv f (Scheme.Hom.relativeDifferentials f))

/-- The actual H1 value has precisely the evaluation-natural original Yoneda value. -/
theorem tangentOneLinearEquiv_apply [IsCurve k f] [Smooth f]
    (ξ : extOneNaiveCotangent f.toLRSHom.toShHom (InvertibleExtCancellation.unit X)) :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f (InvertibleExtCancellation.unit X)
    letI := CurveTangentLineGeometry.differentials_isInvertible f
    tangentOneLinearEquiv f ξ =
      DualExtNaturality.dualExtOneCohomologyLinearEquiv f (Scheme.Hom.relativeDifferentials f)
        (ordinaryExtOneLinearEquiv f (InvertibleExtCancellation.unit X) ξ) := rfl

end M9Native.StandardCurveCotangentExt
