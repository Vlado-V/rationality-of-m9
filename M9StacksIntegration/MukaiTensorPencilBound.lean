module

public import M9StacksIntegration.MukaiTensorPencilSequence
public import M9StacksIntegration.MukaiTensorSerreDimension
public import M9StacksIntegration.MukaiResidualDualSpanTwistBound

/-!
# The actual tensor-pencil H0 bound after endpoint identification

The original tensor short exact sequence, the proved divisor twist
bound, its computed Euler difference, and native Serre duality give
H0(Q_alpha tensor Q_beta)≤10. The structural endpoint isomorphism is
constructed separately from the genuine rank-two wedge pairing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections M9Native.CurveDivisorSections

universe u

namespace M9Native.MukaiTensorSectionBound

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

theorem tensor_h0_le_ten_of_rightEndpointIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f beta 0))
    (hA : Epi (netEvaluation alpha (completeNetSections f alpha bA)))
    (hB : Epi (netEvaluation beta (completeNetSections f beta bB)))
    (hres : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8)
    (hb : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le beta = 8)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (bP : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D beta) 0))
    (hP : Epi (MukaiPencilQuotient.pencilEvaluation (twistDown D beta)
      (MukaiPencilQuotient.completePencilSections f D beta bP)))
    (eR : MukaiTensorLineCancellation.rightEndpoint D
        (dualSpan alpha (completeNetSections f alpha bA)) beta ≅
      (MukaiHomExact.homFunctor (MukaiTensorLineCancellation.twist D
        (dualSpan alpha (completeNetSections f alpha bA)))).obj
          (Stacks.Duality.dualizingSheafOverField f)) :
    Module.finrank k (cohomologyOverField k f
      (tensor (dualSpan alpha (completeNetSections f alpha bA))
        (dualSpan beta (completeNetSections f beta bB))) 0) ≤ 10 := by
  let Q := dualSpan alpha (completeNetSections f alpha bA)
  let B := dualSpan beta (completeNetSections f beta bB)
  let C := MukaiTensorLineCancellation.twist D Q
  let S := MukaiTensorPencilSequence.tensorSequence f D beta bP bB hP hB Q
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank alpha (completeNetSections f alpha bA) hA
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2 :=
    dualSpan_rank beta (completeNetSections f beta bB) hB
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.divisorSheaf D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
    (Stacks.Divisors.divisorSheaf D)
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (twistDown D beta)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ 2 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (tensor (Stacks.Divisors.divisorSheaf D) Q) 2
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X _ _ 1 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ 4 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor B Q) 4
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X _ _ 2 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 2 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor (twistDown D beta) Q) 2
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X _ _ 1 2
  letI : S.X₁.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₁ 2
  letI : S.X₂.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₂ 4
  letI : S.X₃.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₃ 2
  letI := finiteDimensional_cohomologyOverField_of_isProper k f S.X₁ 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f S.X₂ 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f S.X₃ 0
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  letI : C.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f C 2
  let eL := MukaiTensorPencilSequence.leftEndpointIso f D beta bP bB hP hB Q
  let eM := MukaiTensorPencilSequence.middleEndpointIso f D beta bP bB hP hB Q
  let eRight := MukaiTensorPencilSequence.rightEndpointIso f D beta bP bB hP hB Q
  have hL0 := (cohomologyOverFieldIso k f eL 0).toLinearEquiv.finrank_eq
  have hL1 := (cohomologyOverFieldIso k f eL 1).toLinearEquiv.finrank_eq
  have hSerre := rightEndpoint_finrank_eq_h1 f
    (IsCurve.topologicalKrullDim_eq_one f).le C S.X₃ (eRight ≪≫ eR)
  have h3 := MukaiResidualLineBounds.completeDualSpan_twist_h0_le_three f
    hg hnp alpha beta bA hA hres ha hb D hlen
  have hEuler := MukaiResidualLineBounds.completeDualSpan_twist_h0_sub_h1_eq_neg_four f
    hg alpha bA hA ha D hlen
  change Module.finrank k (cohomologyOverField k f C 0) ≤ 3 at h3
  change (Module.finrank k (cohomologyOverField k f C 0) : ℤ) -
    Module.finrank k (cohomologyOverField k f C 1) = -4 at hEuler
  rw [← hL0, ← hL1] at hEuler
  have hS := MukaiTensorPencilSequence.tensorSequence_shortExact f D beta bP bB hP hB Q
  have hbnd := MukaiBundleUniqueness.tensor_H0_le_ten_of_twist_H0_le_three k f hS
    (hSerre.trans hL1.symm) hEuler (hL0.le.trans h3)
  have hM := (cohomologyOverFieldIso k f eM 0).toLinearEquiv.finrank_eq
  change Module.finrank k (cohomologyOverField k f (tensor Q B) 0) ≤ 10
  rw [← hM]
  exact hbnd

end M9Native.MukaiTensorSectionBound
