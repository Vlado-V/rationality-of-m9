module

public import M9StacksIntegration.SmoothNaiveCotangent
public import M9StacksIntegration.CurveExtLinear
public import M9StacksIntegration.CurveTangentLineGeometry
public import M9StacksIntegration.NativeHomScalars
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Original smooth cotangent Ext and actual tangent cohomology

The source is the original native `Scheme.naiveCotangentExt`, in its
locally small derived-category model. The smooth comparison is normalized
by the native `H⁰(NL) ≅ Ω`; Mathlib's model-independent Ext comparison
retains the original scalar action. Actual invertible tensor cancellation
then identifies deformation Ext with the actual tangent cohomology.
-/

attribute [local instance 10000] SheafOfModules.hasDerivedCategory
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open M9Native.InvertibleExtCancellation

universe u

namespace M9Native.SmoothCotangentExt

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

/-- The actual base-scalar action on the original derived Ext group. -/
@[instance_reducible]
def nativeExtModule (G : X.Modules) (i : ℤ) :
    Module k (Scheme.naiveCotangentExt f G i) := by
  let := modulesLinearOverField k f
  exact inferInstanceAs (Module k
    (SmoothNaiveCotangent.derivedObject f ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦i⟧))

/-- The literal native cotangent Ext equals ordinary Ext of the literal
sheaf of differentials, with the original base-field scalars. -/
def ordinaryExtLinearEquiv [Smooth f] (G : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f G (n : ℤ)
    Scheme.naiveCotangentExt f G (n : ℤ) ≃ₗ[k]
      Ext.{u} (Scheme.Hom.relativeDifferentials f) G n := by
  let := modulesLinearOverField k f
  let := nativeExtModule f G (n : ℤ)
  exact (Linear.homCongr k (SmoothNaiveCotangent.differentialsIso f) (Iso.refl _)).trans
    (Ext.homLinearEquiv (R := k)).symm

/-- The comparison acts by precomposition with the actual normalized
smooth comparison, without a chosen replacement Ext group. -/
theorem ordinaryExtLinearEquiv_hom [Smooth f] (G : X.Modules) (n : ℕ)
    (ξ : Scheme.naiveCotangentExt f G (n : ℤ)) :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f G (n : ℤ)
    (ordinaryExtLinearEquiv f G n ξ).hom =
      (SmoothNaiveCotangent.differentialsIso f).inv ≫ ξ := by
  let := modulesLinearOverField k f
  let := nativeExtModule f G (n : ℤ)
  change (Ext.homLinearEquiv (R := k)
      (X := Scheme.Hom.relativeDifferentials f) (Y := G) (n := n))
    ((Ext.homLinearEquiv (R := k)
      (X := Scheme.Hom.relativeDifferentials f) (Y := G) (n := n)).symm
        (((SmoothNaiveCotangent.differentialsIso f).inv ≫ ξ) ≫ 𝟙 _)) =
          (SmoothNaiveCotangent.differentialsIso f).inv ≫ ξ
  rw [LinearEquiv.apply_symm_apply]
  exact Category.comp_id ((SmoothNaiveCotangent.differentialsIso f).inv ≫ ξ)

/-- The inverse cotangent line is the actual tangent line, by the native
evaluation pairing and uniqueness of a tensor inverse. -/
def tangentTwistIso [IsCurve k f] [Smooth f] :
    letI := CurveTangentLineGeometry.differentials_isInvertible f
    Scheme.Modules.tensorObj (unit X)
      (Scheme.Modules.tensorInverse (Scheme.Hom.relativeDifferentials f)) ≅
        CurveTangentLineGeometry.tangentLine f := by
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      X.ringCatSheaf.property _ ≪≫
    Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
      X.ringCatSheaf.property (Scheme.Hom.relativeDifferentials f) _
      (inverseTensorUnitIso (Scheme.Hom.relativeDifferentials f))

/-- The original infinitesimal-automorphism Ext group is actual tangent
zeroth cohomology, linearly for the native deformation scalar action. -/
def tangentZeroLinearEquiv [IsCurve k f] [Smooth f] :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f (unit X) 0
    Scheme.naiveCotangentExt f (unit X) 0 ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 0 := by
  let := modulesLinearOverField k f
  let := nativeExtModule f (unit X) 0
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact (ordinaryExtLinearEquiv f (unit X) 0).trans
    ((Ext.linearEquiv₀ (R := k)).trans
      (M9StacksIntegration.InvertibleHomCancellation.homDualLinearEquivCohomologyZero
        f (Scheme.Hom.relativeDifferentials f)))

/-- The original infinitesimal-deformation Ext group is actual tangent
first cohomology, retaining the canonical base-field scalars. -/
def tangentOneLinearEquiv [IsCurve k f] [Smooth f] :
    letI := modulesLinearOverField k f
    letI := nativeExtModule f (unit X) 1
    Scheme.naiveCotangentExt f (unit X) 1 ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  let := modulesLinearOverField k f
  let := nativeExtModule f (unit X) 1
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact (ordinaryExtLinearEquiv f (unit X) 1).trans
    ((CurveExtLinear.invertibleExtOneCohomologyLinearEquiv f
      (Scheme.Hom.relativeDifferentials f) (unit X)).trans
        (cohomologyOverFieldIso k f (tangentTwistIso f) 1).toLinearEquiv)

/-- All original cotangent Ext groups have the actual cohomological
inverse-twist interpretation. No coherence assumption is required. -/
def twistedCohomologyAddEquiv [IsCurve k f] [Smooth f] (G : X.Modules) (n : ℕ) :
    letI := CurveTangentLineGeometry.differentials_isInvertible f
    Scheme.naiveCotangentExt f G (n : ℤ) ≃+
      cohomologyOverField k f
        (Scheme.Modules.tensorObj G
          (Scheme.Modules.tensorInverse (Scheme.Hom.relativeDifferentials f))) n := by
  let := modulesLinearOverField k f
  let := nativeExtModule f G (n : ℤ)
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact (ordinaryExtLinearEquiv f G n).toAddEquiv.trans
    (invertibleExtCohomologyAddEquiv k f (Scheme.Hom.relativeDifferentials f) G n)

/-- Actual obstruction Ext vanishes above degree one on a proper smooth
curve, for every coefficient sheaf. -/
theorem ext_eq_zero_of_one_lt [IsCurve k f] [Smooth f] [IsProper f]
    (G : X.Modules) (n : ℕ) (hn : 1 < n)
    (ξ : Scheme.naiveCotangentExt f G (n : ℤ)) : ξ = 0 := by
  let := CurveTangentLineGeometry.differentials_isInvertible f
  let e := twistedCohomologyAddEquiv f G n
  have hzero := isZero_cohomologyOverField_of_topologicalKrullDim_le k f
    (Scheme.Modules.tensorObj G
      (Scheme.Modules.tensorInverse (Scheme.Hom.relativeDifferentials f)))
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le hn
  let := ModuleCat.subsingleton_of_isZero hzero
  apply e.injective
  exact Subsingleton.elim _ _

/-- In particular the original degree-two obstruction space is zero. -/
theorem ext_two_eq_zero [IsCurve k f] [Smooth f] [IsProper f]
    (G : X.Modules) (ξ : Scheme.naiveCotangentExt f G 2) : ξ = 0 :=
  ext_eq_zero_of_one_lt f G 2 (by omega) ξ

end M9Native.SmoothCotangentExt
