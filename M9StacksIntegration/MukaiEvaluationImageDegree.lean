module

public import M9StacksIntegration.MukaiThreeSectionDeterminant
public import M9StacksIntegration.MukaiNetFromNoSeven
public import M9StacksIntegration.MukaiRankTwoExteriorDegree
public import M9StacksIntegration.CurveDivisorSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional

/-!
# Actual degree bounds for the original generated image and saturation

Three genuine determinant sections force degree at least eight for
the original rank-two image. The independent bound on the actual
saturation comes from native H0 exactness: middle dimension six and
kernel dimension at most three give three quotient sections; that
line's degree is at least eight. Degree additivity then bounds the
rank-two saturation by eight. No identification of image and
saturation is assumed in either bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiEvaluationImageDegree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Native H0 exactness supplies three actual quotient sections. -/
theorem three_le_h0_quotient
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ 0)]
    (h6 : Module.finrank k (cohomologyOverField k f S.X₂ 0) = 6)
    (h3 : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 3) :
    3 ≤ Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  obtain ⟨_,hinj,hex,_,_⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let i := (cohomologyOverFieldMap k f S.f 0).hom
  let q := (cohomologyOverFieldMap k f S.g 0).hom
  have hi : Function.Injective i := hinj
  have he : Function.Exact i q := hex 0
  have hd := q.finrank_range_add_finrank_ker
  rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi] at hd
  have hr := Submodule.finrank_le (LinearMap.range q)
  omega

variable [IsAlgClosed k] [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (hn : ¬ Nonempty (LinearSeries k f hdim 7 2))

include hn

/-- The original monic rank-two image with three sections has degree
at least eight, deriving its determinant section bound first. -/
theorem eight_le_degree_of_three_sections_and_mono
    (F E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (j : F ⟶ E) [Mono j]
    (h3 : 3 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hpair : ∀ s : Fin 2 → cohomologyOverField k f E 0,
      LinearIndependent k s →
        ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) ≠ 0) :
    (8 : ℤ) ≤ curveDegree k f hdim F 2 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower F 2) := MukaiTwistBounds.exterior_two_isInvertible F
  let : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f _
  have hdet := MukaiThreeSectionDeterminant.three_le_h0_exterior_two_of_mono k f F E j h3 hpair
  have hd := MukaiNetFromNoSeven.eight_le_degree_of_three_sections f hdim hn
    (Scheme.Modules.exteriorPower F 2) hdet
  have heq := MukaiTwistBounds.degree_exterior_two f F
  change invertibleCurveDegree k f hdim (Scheme.Modules.exteriorPower F 2) =
    curveDegree k f hdim F 2 at heq
  simpa only [heq] using hd

/-- The independent degree bound on the actual rank-two saturation
comes from its actual line quotient and native H0 exactness. -/
theorem degree_le_eight_of_line_quotient
    (F E ξ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [FiniteDimensional k (cohomologyOverField k f F 0)]
    [FiniteDimensional k (cohomologyOverField k f E 0)]
    (u : F ⟶ E) (v : E ⟶ ξ) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact)
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (h3 : Module.finrank k (cohomologyOverField k f F 0) ≤ 3)
    (hdegree : curveDegree k f hdim E 3 = 16) :
    curveDegree k f hdim F 2 ≤ 8 := by
  let : FiniteDimensional k (cohomologyOverField k f ξ 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f ξ
  have hξ := three_le_h0_quotient k f (ShortComplex.mk u v w) hS h6 h3
  have hξdegree := MukaiNetFromNoSeven.eight_le_degree_of_three_sections f hdim hn ξ hξ
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ξ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  have hd := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk u v w) hS 2 3 1
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim ξ] at hd
  change curveDegree k f hdim E 3 = curveDegree k f hdim F 2 +
    invertibleCurveDegree k f hdim ξ at hd
  rw [hdegree] at hd
  omega

end M9Native.MukaiEvaluationImageDegree
