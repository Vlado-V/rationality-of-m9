module

public import M9StacksIntegration.CurveFieldClassifierComposition
public import M9StacksIntegration.CurveAtlasTangentH1
public import M9StacksIntegration.ParameterP1SourceImage

/-!
# Genuine low-degree covers obstruct a smooth curve-family classifier

At an original closed genus-nine cover point, actual smooth lifting makes
the SAME original family H1 map onto a space of dimension24. The proved
native source-forgetting image theorem bounds that SAME map by23. Thus
the original classifier is not smooth. The parameter-pullback corollary
uses the actual derived classifier composition, with no image-rank,
Kodaira--Spencer or family-comparison premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] M9Native.ParameterTangentH1.residueTangentModule

universe u
namespace M9Native.CurveCoverSmoothClassifierObstruction

open ParameterTangentDeformation

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K)) [LocallyOfFiniteType s]

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

variable (x : T)
  [IsCurve (IsLocalRing.ResidueField (T.presheaf.stalk x)) (fibre p x).hom]

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

set_option maxRecDepth 1024 in
/-- The original smooth classifier is impossible at a genuine closed
genus-nine constant-P1 cover point of native function-field degree<=5. -/
theorem not_isSmooth_classifier
    (h : X ⟶ ConstantProjectiveLineFibre.target K s)
    (hh : h ≫ ConstantProjectiveLineFibre.projection K s = p)
    (hx : IsClosed ({x} : Set T)) (hg : genus (fibre p x).hom = 9)
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left,
        (ParameterP1SourceImage.originalPointMap K s p h hh x).base c = y)
    (hd : ParameterP1SourceImage.pointDegree K s p h hh x hnc ≤ 5) :
    ¬ Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (CurveClassifierPullback.originalFamily B hZ hX hT p) s) := by
  intro hsm
  have : IsCurve κ (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom :=
    inferInstanceAs (IsCurve κ (fibre p x).hom)
  have : Smooth (fibre p x).hom :=
    inferInstanceAs (Smooth (pullback.snd p (T.fromSpecResidueField x)))
  have : IsProper (fibre p x).hom :=
    inferInstanceAs (IsProper (pullback.snd p (T.fromSpecResidueField x)))
  have hk : B.Contains (Spec (.of κ)) := B.residueField_spec_contains hT x
  have : IsAlgClosed κ := ParameterClosedResidueField.isAlgClosed K s x hx
  have honto := CurveAtlasTangentH1.tangentH1_surjective_of_closed
    B hZ hK hAlg hX hT p s x hk hx hsm
  have hbound := ParameterP1SourceImage.tangentH1_finrank_le_twenty_three
    K s p h hh x hx hg hnc hd
  rw [LinearMap.range_eq_top.mpr honto, finrank_top,
    SmoothCurveTangentCohomology.tangent_h1 (fibre p x).hom hg] at hbound
  omega

/-- A genuine arrow from the original cover family to an actual smooth
curve atlas cannot have a smooth original parameter map. The target
family may have an algebraic-space total space. -/
theorem not_smooth_parameterMap
    (R : CurveFamily B hZ) (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    (β : CurveClassifierPullback.originalFamily B hZ hX hT p ⟶ R)
    (hβ : B.inclusion.map β.baseMap.left ≫ sR = s)
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg R sR))
    (h : X ⟶ ConstantProjectiveLineFibre.target K s)
    (hh : h ≫ ConstantProjectiveLineFibre.projection K s = p)
    (hx : IsClosed ({x} : Set T)) (hg : genus (fibre p x).hom = 9)
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left,
        (ParameterP1SourceImage.originalPointMap K s p h hh x).base c = y)
    (hd : ParameterP1SourceImage.pointDegree K s p h hh x hnc ≤ 5) :
    ¬ Smooth (B.inclusion.map β.baseMap.left) := by
  intro hf
  apply not_isSmooth_classifier B hZ K hK hAlg hX hT p s x h hh hx hg hnc hd
  exact CurveFieldClassifierComposition.source_classifier_isSmooth B hZ hK hAlg
    (Q := CurveClassifierPullback.originalFamily B hZ hX hT p) (R := R) s sR
    β hβ hf hR

end M9Native.CurveCoverSmoothClassifierObstruction
