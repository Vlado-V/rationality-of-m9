module

public import M9StacksIntegration.GenusNineFiniteDiagonal
public import M9StacksIntegration.FiniteDiagonalSchemePullback
public import M9StacksIntegration.SchemeStackPullbackPoints

/-!
# Actual genus-nine cover-family pullbacks

This is the full native fibre product of an actual source scheme classifier
and an actual target scheme classifier into the chosen smooth genus-nine
stack. The finite diagonal comes from the checked source constructor.
The universal represented point gives actual projections and a vertical
family-comparison arrow, with coverage for every object of the original site.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.CoverFamilyStackPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

local instance siteProducts : HasBinaryProducts (BigFppfOver B (Spec (.of K)) hK) :=
  Stack.hasBinaryProducts_bigFppfOver B (Spec (.of K)) hK

/-- The exact original source stack of the chosen field-base M9 coarse space. -/
abbrev sourceStack :=
  M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)

variable (Y V : BigFppfOver B (Spec (.of K)) hK)
  (a : Stack.schemeStack.{u, u + 1} B (Spec (.of K)) hK Y ⟶
    sourceStack B hZ K hK)
  (b : Stack.schemeStack.{u, u + 1} B (Spec (.of K)) hK V ⟶
    sourceStack B hZ K hK)

/-- The actual native fibre-product category, with both original classifiers. -/
abbrev pairCategory := TwoFibreProductOver (Over.forget Y) (Over.forget V)
  (sourceStack B hZ K hK).val.val.p a.hom.hom.toFunctor b.hom.hom.toFunctor

/-- Its actual projection to the original field site. -/
abbrev pairProjection := FiniteDiagonalSchemePullback.pairProjection
  B (Spec (.of K)) hK (sourceStack B hZ K hK) Y V a b

/-- An actual scheme representing the entire cover-family fibre product,
finite over the product of the two original parameter schemes. -/
theorem exists_scheme :
    ∃ (P : BigFppfOver B (Spec (.of K)) hK) (q : P ⟶ Y ⨯ V),
      IsFinite ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (Over.forget P) (pairProjection B hZ K hK Y V a b)) :=
  FiniteDiagonalSchemePullback.exists_scheme B (Spec (.of K)) hK
    (sourceStack B hZ K hK) Y V a b (GenusNineFiniteDiagonal.actual B hZ K hK)

variable {P : BigFppfOver B (Spec (.of K)) hK}

abbrev PointData := SchemeStackPullbackPoints.PointData B (Spec (.of K)) hK
  (sourceStack B hZ K hK) Y V a b (P := P)
abbrev pointObject := SchemeStackPullbackPoints.pointObject B (Spec (.of K)) hK
  (sourceStack B hZ K hK) Y V a b (P := P)
abbrev exists_pointData := SchemeStackPullbackPoints.exists_pointData B (Spec (.of K)) hK
  (sourceStack B hZ K hK) Y V a b (P := P)
abbrev covers_native_point := SchemeStackPullbackPoints.covers_native_point B (Spec (.of K)) hK
  (sourceStack B hZ K hK) Y V a b (P := P)

end M9Native.CoverFamilyStackPullback
