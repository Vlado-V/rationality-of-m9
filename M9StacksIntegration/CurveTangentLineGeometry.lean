module

public import M9StacksIntegration.MukaiDualDegree
public import M9StacksIntegration.PencilDegreePullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank

/-!
# The actual tangent lines of a smooth curve and a curve morphism

These are the literal duals of the original native relative-differential
sheaves, including the dual of the actual pulled-back cotangent sheaf.
Smooth relative dimension one derives their line ranks. Actual native
evaluation derives dual degree, and native pullback degree uses the
original function-field degree. No canonical/differentials identification
or supplied cotangent degree is used.

The rank calculation is the small scheme-only argument of pinned
StacksFrontier `F6Rank136.SmoothIsNodal`, restricted to smooth curves.
Pinned package sources are unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.CurveTangentLineGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The actual native tangent sheaf, defined as the dual of differentials. -/
abbrev tangentLine (f : X ⟶ Spec (.of k)) : X.Modules :=
  dualSheaf (Scheme.Hom.relativeDifferentials f)

/-- The actual dual of the pulled-back cotangent line, before a dual/pullback adapter. -/
abbrev pulledTangentLine (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) : X.Modules :=
  dualSheaf ((Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY))

/-- Smoothness of the original curve derives rank one for its native differentials. -/
theorem differentials_rank_one (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials f) 1 := by
  let := smoothOfRelativeDimension_one_of_isCurve k f
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  obtain ⟨hft, hfree, -⟩ :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae
      (Scheme.Hom.relativeDifferentials f)).out 4 5 rfl rfl).mp hflf
  have _ := hft
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq _ 1 fun x => ?_
  rw [Scheme.Modules.fiberRank_eq_finrank_stalk
    (Scheme.Hom.relativeDifferentials f) x (hfree x)]
  have hdim := finrank_stalk_relativeDifferentials_eq_fiberDimensionAt f x
  rw [fiberDimensionAt_eq_of_smoothOfRelativeDimension f 1 x] at hdim
  exact_mod_cast hdim

/-- Native differentials on the actual smooth curve are invertible. -/
theorem differentials_isInvertible (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials f) :=
  (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X _).mpr (differentials_rank_one f)

/-- The original actual tangent sheaf is invertible. -/
theorem tangent_isInvertible (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tangentLine f) := by
  have h := isFiniteLocallyFreeOfRank_dualSheaf (Scheme.Hom.relativeDifferentials f)
    1 (differentials_rank_one f)
  exact (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X _).mpr h

/-- The actual dual pulled-back cotangent sheaf is invertible. -/
theorem pulledTangent_isInvertible (pY : Y ⟶ Spec (.of k))
    [IsCurve k pY] [Smooth pY] (g : X ⟶ Y) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (pulledTangentLine pY g) := by
  let := differentials_rank_one pY
  have hp := isFiniteLocallyFreeOfRank_pullback g (Scheme.Hom.relativeDifferentials pY) 1
  have hd := isFiniteLocallyFreeOfRank_dualSheaf _ 1 hp
  exact (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X _).mpr hd

/-- Genuine finite-locally-free dual base change identifies the target
with the actual pullback of the original tangent line. -/
def pulledTangentIso (pY : Y ⟶ Spec (.of k)) [IsCurve k pY] [Smooth pY]
    (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).obj (tangentLine pY) ≅ pulledTangentLine pY g := by
  let := differentials_rank_one pY
  exact @asIso _ _ _ _ (Stacks.Chow.pullbackDualMap g (Scheme.Hom.relativeDifferentials pY))
    (Stacks.Chow.pullbackDualMap_isIso g (Scheme.Hom.relativeDifferentials pY)
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1))

/-- The comparison uses the actual canonical native dual-base-change arrow. -/
@[simp] theorem pulledTangentIso_hom (pY : Y ⟶ Spec (.of k))
    [IsCurve k pY] [Smooth pY] (g : X ⟶ Y) :
    (pulledTangentIso pY g).hom =
      Stacks.Chow.pullbackDualMap g (Scheme.Hom.relativeDifferentials pY) := rfl

/-- Actual tangent degree is minus the original differential degree. -/
theorem tangent_degree (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] :
    letI := differentials_rank_one f
    letI := tangent_isInvertible f
    invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (tangentLine f) =
        -curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
          (Scheme.Hom.relativeDifferentials f) 1 := by
  let := differentials_rank_one f
  let := tangent_isInvertible f
  let hdim := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hd := MukaiDualDegree.curveDegree_dual_line k f hdim
    (Scheme.Hom.relativeDifferentials f) (differentials_rank_one f)
  rw [invertibleCurveDegree_eq_curveDegree_one]
  exact hd

/-- Actual dual pullback degree uses the original native map degree. -/
theorem pulledTangent_degree (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [Smooth pY] [IsProper pX] [IsProper pY]
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    letI := differentials_rank_one pY
    letI := pulledTangent_isInvertible pY g
    invertibleCurveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
      (pulledTangentLine pY g) =
        -(PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ) *
          curveDegree k pY (IsCurve.topologicalKrullDim_eq_one (f := pY)).le
            (Scheme.Hom.relativeDifferentials pY) 1 := by
  let := differentials_rank_one pY
  let := pulledTangent_isInvertible pY g
  let hp := isFiniteLocallyFreeOfRank_pullback g (Scheme.Hom.relativeDifferentials pY) 1
  let hdim := (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
  have hd := MukaiDualDegree.curveDegree_dual_line k pX hdim
    ((Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY)) hp
  have hpb := curveDegree_pullback_eq_degreeOver_mul k pX pY g hg hnc
    (Scheme.Hom.relativeDifferentials pY) 1
  rw [invertibleCurveDegree_eq_curveDegree_one]
  rw [hd, hpb]
  exact (neg_mul _ _).symm

end M9Native.CurveTangentLineGeometry
