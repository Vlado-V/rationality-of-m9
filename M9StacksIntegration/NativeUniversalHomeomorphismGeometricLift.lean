module

public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism

/-!
# Same-field geometric lifting for an actual universal homeomorphism

This is the injection-only proof of
`AlgebraicGeometry.Stack.exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace`
from `StacksFrontier/AlgebraicGeometry/Stacks/KeelMoriEtaleLocal/GeometricPoints.lean`,
lines 64–77, at Stacks commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`
(Apache-2.0). It avoids the unrelated surjectivity and cartesian-square imports.

The spectrum of the same algebraically closed field is an actual object of
the chosen site. No claim for a field outside that site is made here.
-/

set_option autoImplicit false

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace M9Native.NativeUniversalHomeomorphismGeometricLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
  {N : AlgebraicSpaces B S hS}

/-- Equality of the actual algebraic-space image objects gives an arrow over
the identity of the same algebraically closed field's spectrum. -/
theorem exists_isHomLift_id
    (F : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS N.obj N.property)
    (hF : Stack.UniversalHomeomorphism B S hS F)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (x₁ x₂ : 𝒴.val.val.obj)
    (h₁ : 𝒴.val.val.p.obj x₁ = V) (h₂ : 𝒴.val.val.p.obj x₂ = V)
    (h : F.hom.hom.obj x₁ = F.hom.hom.obj x₂) :
    ∃ α : x₁ ⟶ x₂, 𝒴.val.val.p.IsHomLift (𝟙 V) α := by
  have hl := (Stack.universallyInjective_iff_liftsTwoArrowsAtGeometricPoints B S hS F).1
    (Stack.universallyInjective_of_universalHomeomorphism B S hS hF)
  have hlift : (Stack.fibredCategory B S hS N.obj).val.p.IsHomLift (𝟙 V) (eqToHom h) :=
    IsHomLift.eqToHom_domain_lift_id h ((Functor.congr_obj F.hom.hom.w x₁).trans h₁)
  obtain ⟨α, hα, -⟩ := hl k V hV x₁ x₂ h₁ h₂ (eqToHom h) hlift
  exact ⟨α, hα⟩

end M9Native.NativeUniversalHomeomorphismGeometricLift
