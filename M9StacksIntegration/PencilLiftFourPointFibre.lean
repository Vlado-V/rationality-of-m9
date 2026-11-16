module

public import M9StacksIntegration.PencilFourPointFibre
public import M9StacksIntegration.LagrangianNoTrigonal

/-!
# Retaining the actual original-pencil section comparison on its four-point fibre

The moving map, original basis, and comparison into the ORIGINAL pencil
line are constructed together. The absence of a lower pencil derives
exact degree four, then actual finite-flat rank four and the complete
rational étale fibre. The original section pinning is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.PencilProjectiveLineGeometry M9Native.PencilDegreePullback
open Stacks.LinearSeriesMorphism Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned

universe u

namespace M9Native.PencilLiftFourPointFibre

open PencilFourPointFibre PencilBasepointRemoval
attribute [local instance] isCurve_projectiveSpaceOver_one

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [IsProper f] [IsCurve K f] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1)

/-- No map, point, fibre, tuple, rank, or generating-basis premise is
supplied. The comparison still has its original line and both section pins. -/
theorem exists_fourPointFibre_with_original_section_pins
    (A : LinearSeries K f hdim 4 1)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1)) :
    ∃ D : FourPointFibre K f, ∃ b : Module.Basis (Fin 2) K A.V,
      ∃ α : (Scheme.Modules.pullback
        (D.map ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K)))).obj
          (twistingSheafAtUniverse.{u} 1) ⟶ A.L,
        ∀ i, α.app ⊤ (pullbackCoordSection
          (D.map ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K))) i) =
            seriesSections A b i := by
  classical
  obtain ⟨b⟩ := nonempty_basis A
  obtain ⟨p,hp,α,hαiso,hα,hnc,hd,hfinite⟩ :=
    PencilProjectiveLineBridge.exists_map_with_movingLine f hdim A b
  let αA := α ≫ movingInclusion f hdim A b
  have hpin (i : Fin 2) : αA.app ⊤ (pullbackCoordSection
      (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K))) i) =
        seriesSections A b i := by
    change (movingInclusion f hdim A b).app ⊤
      (α.app ⊤ (pullbackCoordSection
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K))) i)) = _
    rw [hα i,movingInclusion_sections]
  have hlow : ¬ curveMapDegree f (toBase K) p hp hnc ≤ 3 := by
    intro h
    exact hno3 (PencilProjectiveLineBridge.nonempty_pencil_of_hasMapDegreeLE
      f hdim 3 ⟨p,hp,hnc,h⟩)
  have hdegree : curveMapDegree f (toBase K) p hp hnc = 4 := by omega
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 1
  let : Smooth (toBase K) := smooth_of_iso_projectiveLine (toBase K) c.iso c.toBase
  let : IsNormal (Line K) := isNormal_of_isRegular _
    (isRegular_of_smooth_over_field (toBase K))
  have hr := CurveMapFiniteFlatDegree.finiteLocallyFreeOfRank_curveMapDegree
    f (toBase K) p hp hnc
  let hr4 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p 4 := hdegree ▸ hr
  let := hr4
  obtain ⟨q,hq,he,hcard⟩ :=
    CurveEtaleRationalFibre.exists_fibre_card K f (toBase K) p hp hnc 4
  let S := {a : Spec (.of K) ⟶ pullback p q // a ≫ pullback.snd p q = 𝟙 _}
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card S = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  exact ⟨⟨p,hp,hnc,hdegree,hr4,q,hq,he,(Fintype.equivFinOfCardEq hc).symm⟩,b,αA,hpin⟩

open LagrangianTransverseRestriction

/-- The actual original-LG no-degree-three theorem supplies the entire
lower-degree obstruction. Only the original degree-four pencil remains. -/
theorem exists_original_lagrangian_fibre_with_section_pins
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1)
    (A : LinearSeries K (curveProjection K M) hdim 4 1) :
    ∃ D : FourPointFibre K (curveProjection K M), ∃ b : Module.Basis (Fin 2) K A.V,
      ∃ α : (Scheme.Modules.pullback
        (D.map ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K)))).obj
          (twistingSheafAtUniverse.{u} 1) ⟶ A.L,
        ∀ i, α.app ⊤ (pullbackCoordSection
          (D.map ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K))) i) =
            seriesSections A b i := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  exact exists_fourPointFibre_with_original_section_pins (curveProjection K M) hdim A
    (LagrangianNoTrigonal.no_g1_three_at_dimension K M hM hdim)

end M9Native.PencilLiftFourPointFibre
