module

public import M9StacksIntegration.LineSectionPrefixStalkRegularity
public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.LagrangianPluckerQuotient
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# A common regular point of the actual Lagrangian hyperplane prefixes

For any five original determinant-line sections with an actual smooth
integral one-dimensional final cut, choose a genuine closed point on that
curve. The ambient local ring has dimension six and the final local ring has
dimension one. The proved ordered-equation comparison makes every literal
prefix stalk regular at the image of this same point. No prefix regularity,
line frame, stalk identification, or prescribed point is an assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
namespace M9Native.LagrangianPrefixRegularPoint
open IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]

local instance determinantLine_invertible :
    SheafOfModules.IsInvertible (LagrangianGrassmannian.space K).sheaf.obj
      (LagrangianGrassmannian.space K).ringCatSheaf.property
      (LagrangianPluckerQuotient.determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (LagrangianPluckerQuotient.determinantLine_invertible K)

theorem exists_common_regular_point
    (ss : List Γ(LagrangianPluckerQuotient.determinantLine K, ⊤)) (hlen : ss.length = 5)
    [IsIntegral (simultaneousCut (LagrangianPluckerQuotient.determinantLine K) ss).left]
    [SmoothOfRelativeDimension 1
      ((simultaneousCut (LagrangianPluckerQuotient.determinantLine K) ss).hom ≫
        LagrangianGrassmannian.projection K)] :
    ∃ z : (simultaneousCut (LagrangianPluckerQuotient.determinantLine K) ss).left,
      IsClosed ({z} : Set (simultaneousCut (LagrangianPluckerQuotient.determinantLine K) ss).left) ∧
      ∀ i ≤ 5,
        IsRegularLocalRing
          ((simultaneousCut (LagrangianPluckerQuotient.determinantLine K) (ss.take i)).left.presheaf.stalk
            (LineSectionPrefixes.prefixHom (LagrangianPluckerQuotient.determinantLine K) ss i z)) := by
  let L := LagrangianPluckerQuotient.determinantLine K
  let C := simultaneousCut L ss
  let f := C.hom ≫ LagrangianGrassmannian.projection K
  have : SmoothOfRelativeDimension 1 f := inferInstance
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨w⟩ := (inferInstance : Nonempty C.left)
  obtain ⟨z, hzc, _⟩ := exists_specializes_closedPoint C.left w
  have hzclosed : IsClosed ({z} : Set C.left) := hzc
  have hxclosed : IsClosed ({C.hom z} : Set (LagrangianGrassmannian.space K)) := by
    simpa only [Set.image_singleton] using C.hom.isClosedEmbedding.isClosedMap _ hzclosed
  have hCdim : topologicalKrullDim C.left = (1 : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  have hRdim : ringKrullDim
      ((LagrangianGrassmannian.space K).presheaf.stalk (C.hom z)) = (6 : WithBot ℕ∞) := by
    rw [← Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
      (Stacks.Chow.fieldChowSituation K) (fun _ _ => rfl)
      (LagrangianGrassmannian.projection K) (𝟙 _) (C.hom z) hxclosed]
    exact LagrangianIntegral.space_dimension K
  have hZdim : ringKrullDim (C.left.presheaf.stalk z) = (1 : WithBot ℕ∞) := by
    rw [← Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
      (Stacks.Chow.fieldChowSituation K) (fun _ _ => rfl) f (𝟙 _) z hzclosed]
    exact hCdim
  have hR : IsRegularLocalRing ((LagrangianGrassmannian.space K).presheaf.stalk (C.hom z)) :=
    (isRegular_of_smooth_over_field (LagrangianGrassmannian.projection K)).isRegularLocalRing_stalk
      (C.hom z)
  have hZ : IsRegularLocalRing (C.left.presheaf.stalk z) :=
    (isRegular_of_smooth_over_field f).isRegularLocalRing_stalk z
  have hcodim : ringKrullDim (C.left.presheaf.stalk z) + ss.length =
      ringKrullDim ((LagrangianGrassmannian.space K).presheaf.stalk (C.hom z)) := by
    rw [hZdim, hRdim, hlen]
    norm_num
  refine ⟨z, hzclosed, fun i hi => ?_⟩
  exact (LineSectionPrefixStalkRegularity.regular_at_final_point_unframed L ss z
    hR hZ hcodim i (by omega)).1

end M9Native.LagrangianPrefixRegularPoint
