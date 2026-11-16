module

public import M9StacksIntegration.AlgebraicSpaceValuedClassifierReflection
public import M9StacksIntegration.PresheafClassifierInjectivity

/-! Equality of genuine algebraic-space maps determines the actual
postcomposed classifier functors and every object they name. No equality
or isomorphism in the original source category is asserted. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.AlgebraicSpaceClassifierObjectEquality

universe u uD vD
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {D : Type uD} [Category.{vD} D] {p : D ⥤ BigFppfOver B S hS}
  {M : AlgebraicSpaces B S hS}
  (κ : BasedCategory.ofFunctor p ⥤ᵇ
    AlgebraicSpaceValuedClassifierReflection.target B S hS M)
  {U : BigFppfOver B S hS}
  {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}

/-- Equal ACTUAL algebraic-space maps give equal classifier functors
AFTER κ. There is no injectivity or equality claim for the source F,G. -/
theorem postcomposed_functor_eq_of_nativeMap_eq
    (h : AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ F =
      AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ G) :
    (BasedFunctor.comp F κ).toFunctor = (BasedFunctor.comp G κ).toFunctor :=
  PresheafClassifierInjectivity.functor_eq_of_representingMap_eq
    (congrArg (fun f : schemeSpace U ⟶ M => f.hom) h)

/-- The genuine map comparison is exact in both directions. -/
theorem nativeMap_eq_iff_postcomposed_functor_eq :
    AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ F =
        AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ G ↔
      (BasedFunctor.comp F κ).toFunctor = (BasedFunctor.comp G κ).toFunctor := by
  refine ⟨postcomposed_functor_eq_of_nativeMap_eq B S hS κ, ?_⟩
  intro h
  apply ObjectProperty.hom_ext
  exact PresheafClassifierInjectivity.representingMap_eq_iff_functor_eq.mpr h

/-- Equality holds literally at EVERY native slice object, in the actual
category of elements of the real algebraic space. -/
theorem object_eq_of_nativeMap_eq
    (h : AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ F =
      AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ G) (t : Over U) :
    κ.toFunctor.obj (F.toFunctor.obj t) = κ.toFunctor.obj (G.toFunctor.obj t) :=
  Functor.congr_obj (postcomposed_functor_eq_of_nativeMap_eq B S hS κ h) t

/-- In particular the actual unit values of the classifiers agree. -/
theorem unit_eq_of_nativeMap_eq
    (h : AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ F =
      AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ G) :
    κ.toFunctor.obj (F.toFunctor.obj (Functor.FiberedMor.unit U)) =
      κ.toFunctor.obj (G.toFunctor.obj (Functor.FiberedMor.unit U)) :=
  object_eq_of_nativeMap_eq B S hS κ h (Functor.FiberedMor.unit U)

end M9Native.AlgebraicSpaceClassifierObjectEquality
