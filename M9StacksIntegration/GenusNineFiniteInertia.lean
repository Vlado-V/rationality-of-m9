module

public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite

/-!
A separated quasi-DM algebraic stack has finite inertia. The inertia projection
is compared with the actual base change of its diagonal, using the native
relative-inertia equivalence. This proof does not require curve algebraicity
or a coarse-space existence hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarse

universe u w

section Inertia

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every relative property of the absolute diagonal passes to the inertia
projection. This is the diagonal base-change proof of Stacks 034H/045C, followed
by transport across its actual equivalence of categories. -/
theorem relativeProperty_inertiaProjection_of_diagonal
    (X : Stack.AlgebraicStacks.{u, w} B S hS)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hΔ : Stack.RelativeProperty B S hS P
      (Stack.diagonal.{u, u, u + 1} B S hS X.val)) :
    Stack.RelativeProperty B S hS P
      (Stack.inertiaProjectionAlgebraicStacks B S hS X).hom := by
  have hG : X.val.val.p ⋙ 𝟭 (BigFppfOver B S hS) = X.val.val.p := Functor.comp_id _
  set Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (Stack.diagonal.{u, u, u + 1} B S hS X.val)
    (Stack.diagonal.{u, u, u + 1} B S hS X.val)
  have h₁ : Stack.RelativeProperty B S hS P Q.fst := by
    intro U z hz F hF he
    refine hΔ U (z ⋙ (Stack.diagonal.{u, u, u + 1} B S hS X.val).hom.toFunctor)
      (by rw [Functor.assoc, (Stack.diagonal.{u, u, u + 1} B S hS X.val).hom.w, hz])
      F hF ?_
    obtain ⟨e⟩ := he
    obtain ⟨E⟩ := Stack.nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS
      X.val (CatFiberedInGroupoids.product X.val X.val) X.val
      (Stack.diagonal.{u, u, u + 1} B S hS X.val)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) Q
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      U z hz
    exact ⟨E.symm.trans e⟩
  let a : (Stack.inertia B S hS X.val).val ⥤ᵇ Q.pt.val :=
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
  have : Functor.IsEquivalence a.toFunctor :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
      (TwoFibreProductOver.toRelativeInertia hG)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
      (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor
  have : Functor.IsEquivalence (BasedFunctor.id X.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 X.val.val.obj))
  exact Stack.relativeProperty_of_equivalences B S hS P
    (Stack.inertiaProjectionAlgebraicStacks B S hS X).hom.hom Q.fst.hom a
    (BasedFunctor.id X.val.val) (Iso.refl _) h₁

/-- A separated quasi-DM algebraic stack has finite inertia: the diagonal is
proper and locally quasi-finite, and inertia is its base change. -/
theorem finite_inertia_of_separated_quasiDM
    (X : Stack.AlgebraicStacks.{u, w} B S hS)
    (hsep : Stack.AlgebraicStacks.IsSeparated B S hS
      (Stack.structureMorphism B S hS X))
    (hqdm : Stack.IsQuasiDMOver B S hS X) :
    Stack.AlgebraicStacks.IsFinite B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS X) := by
  have hΔp : Stack.RelativeProperty B S hS (Space.properProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) :=
    (Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B S hS X
      (Space.properProperty B S hS)).2 hsep
  have hΔq : Stack.RelativeProperty B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) :=
    (Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B S hS X
      (Space.locallyQuasiFiniteProperty B S hS)).2 hqdm
  have hIp := relativeProperty_inertiaProjection_of_diagonal B S hS X _ hΔp
  have hIq := relativeProperty_inertiaProjection_of_diagonal B S hS X _ hΔq
  refine ⟨Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
    B S hS X.val X.property, ?_⟩
  intro U y hy F hF he
  exact Space.isFinite_of_isProper_of_isLocallyQuasiFinite B S hS
    (ObjectProperty.FullSubcategory.property _) (ObjectProperty.FullSubcategory.property _)
    _ (hIp U y hy F hF he) (hIq U y hy F hF he)

end Inertia

end M9StacksIntegration.GenusNineCoarse
