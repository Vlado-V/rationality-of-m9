module

public import M9StacksIntegration.MukaiCanonicalSelfDualObstruction

/-!
# Actual line-cube obstruction for the canonical genus-nine determinant

A cubic with values in the inverse determinant, restricted to an actual
line and nonzero on every fiber, would identify its tensor cube with that
inverse determinant. Native tensor and dual degrees then give
`3 deg(L) = -16`. This file proves that actual arithmetic obstruction; it
does not assert that an arbitrary conormal line has such a cubic.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant M9Native.MukaiCanonicalExteriorCohomology
open M9Native.MukaiTwistedSelfDualObstruction

universe u

namespace M9Native.MukaiCanonicalCubicObstruction

variable {X : Scheme.{u}}

def cubeLine (L : X.Modules) : X.Modules := tensor (tensor L L) L

theorem cubeLine_rank (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cubeLine L) 1 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor L L) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X L L 1 1
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X (tensor L L) L 1 1

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)

theorem curveDegree_cubeLine (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := cubeLine_rank L
    curveDegree k f hdim (cubeLine L) 1 = 3 * invertibleCurveDegree k f hdim L := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor L L) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X L L 1 1
  let := cubeLine_rank L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor (tensor L L) L) 1 :=
    cubeLine_rank L
  have h₁ := MukaiDualDegree.curveDegree_tensor k f hdim L L 1 1
  have h₂ := MukaiDualDegree.curveDegree_tensor k f hdim (tensor L L) L 1 1
  have hL := invertibleCurveDegree_eq_curveDegree_one k f hdim L
  simp only [Nat.cast_one, one_mul] at h₁ h₂
  change curveDegree k f hdim (tensor (tensor L L) L) 1 = _
  linarith

theorem no_cubeLine_iso_inverse_degreeSixteen (L D : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D]
    (hdegree : curveDegree k f hdim D 1 = 16) (e : cubeLine L ≅ dualSheaf D) : False := by
  let := cubeLine_rank L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf D) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf D 1 inferInstance
  have hi := curveDegree_eq_of_iso k f hdim 1 e
  have hc := curveDegree_cubeLine k f hdim L
  have hd := MukaiDualDegree.curveDegree_dual_line k f hdim D inferInstance
  rw [hdegree] at hd
  omega

theorem not_fieldFiberIsomorphisms_inverse_degreeSixteen (L D : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D]
    (hdegree : curveDegree k f hdim D 1 = 16) (a : cubeLine L ⟶ dualSheaf D) :
    ¬ FieldFiberIsomorphisms a := by
  intro ha
  have hM := cubeLine_rank L
  have hN := isFiniteLocallyFreeOfRank_dualSheaf D 1
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 1)
  exact no_cubeLine_iso_inverse_degreeSixteen k f hdim L D hdegree
    (@asIso _ _ _ _ a (isIso_of_fieldFiberIsomorphisms a 1 hM hN ha))

include hdim in
theorem no_canonical_cubeLine_iso (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : genus f = 9) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (e : cubeLine L ≅ dualSheaf (exteriorCube E)) : False := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (exteriorCube E) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (exteriorCube E) :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
      X (exteriorCube E)).mpr inferInstance
  apply no_cubeLine_iso_inverse_degreeSixteen k f hdim L (exteriorCube E) _ e
  exact (curveDegree_eq_curveDegree_exteriorPower_of_isProper k f hdim 3 E).symm.trans
    (canonical_curveDegree_genus_nine k f hdim E d hg)

end M9Native.MukaiCanonicalCubicObstruction
