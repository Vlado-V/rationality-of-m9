module

public import M9StacksIntegration.MukaiTensorPencilBound
public import M9StacksIntegration.MukaiWedgeSelfDual
public import M9StacksIntegration.MukaiPencilGeometry
public import M9StacksIntegration.MukaiLemmaFiveOne

/-!
# The actual tensor cohomology bound for complete residual nets

The native rank-two wedge isomorphism and the actual Cartier line
cancellations construct the Serre endpoint in the literal tensor of
the original pencil sequence. The geometric pencil factory supplies
the divisor and both actual evaluation epimorphisms. Thus no divisor,
section bound, self-duality, or generation premise is left in the
complete-net theorem.
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

/-- The literal right endpoint is the genuine Serre-dual sheaf, by the
perfect rank-two wedge pairing and the actual residual tensor iso. -/
def completeDualSpan_rightEndpointIso
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (hA : Epi (netEvaluation alpha (completeNetSections f alpha bA)))
    (hres : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    MukaiTensorLineCancellation.rightEndpoint D
        (dualSpan alpha (completeNetSections f alpha bA)) beta ≅
      (MukaiHomExact.homFunctor (MukaiTensorLineCancellation.twist D
        (dualSpan alpha (completeNetSections f alpha bA)))).obj
          (Stacks.Duality.dualizingSheafOverField f) := by
  let Q := dualSpan alpha (completeNetSections f alpha bA)
  let C := MukaiTensorLineCancellation.twist D Q
  let N := MukaiTensorLineCancellation.coefficient D beta
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank alpha (completeNetSections f alpha bA) hA
  let hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  let hdet : MukaiCupAlternating.exteriorSquare Q ≅ alpha :=
    MukaiDualSpanDeterminant.dualSpanTopExteriorIso alpha
      (completeNetSections f alpha bA) hA
  exact (MukaiTensorLineCancellation.coefficientTwistIso D Q beta).symm ≪≫
    MukaiWedgeSelfDual.tensorWedgeHomIso C N (Stacks.Duality.dualizingSheafOverField f)
      hC (MukaiTensorLineCancellation.coefficientDeterminantIso D Q alpha beta
        (Stacks.Duality.dualizingSheafOverField f) hdet hres)

/-- The full bound with the original complete evaluation maps and an
actual length-two Cartier divisor; the endpoint duality is proved. -/
theorem tensor_h0_le_ten_for_pencil
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
      (MukaiPencilQuotient.completePencilSections f D beta bP))) :
    Module.finrank k (cohomologyOverField k f
      (tensor (dualSpan alpha (completeNetSections f alpha bA))
        (dualSpan beta (completeNetSections f beta bB))) 0) ≤ 10 := by
  exact tensor_h0_le_ten_of_rightEndpointIso f hg hnp alpha beta bA bB hA hB
    hres ha hb D hlen bP hP (completeDualSpan_rightEndpointIso f alpha beta bA hA hres D)

/-- Genuine degree-eight residual nets on a non-pentagonal genus-nine
curve satisfy the bound for their literal original complete dual spans.
All auxiliary Cartier and generation data are constructed internally. -/
theorem tensor_h0_le_ten_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ealpha Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ealpha.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ebeta.L 0))
    (hres : tensor Ealpha.L Ebeta.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    Module.finrank k (cohomologyOverField k f
      (tensor (dualSpan Ealpha.L (completeNetSections f Ealpha.L bA))
        (dualSpan Ebeta.L (completeNetSections f Ebeta.L bB))) 0) ≤ 10 := by
  letI := Ealpha.isInvertible
  letI := Ebeta.isInvertible
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hA := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 Ealpha bA
  obtain ⟨D, hD, _hDdim, hlen, bP, _hPdegree, _hPcount, hP, hB⟩ :=
    MukaiPencilGeometry.exists_completePencilData f
      (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ebeta bB
  letI := hD
  exact tensor_h0_le_ten_for_pencil f hg hnp Ealpha.L Ebeta.L bA bB hA hB hres
    Ealpha.degree_eq Ebeta.degree_eq D hlen bP hP

/-- The same theorem stated directly for the original line bundles
and complete bases. The actual nets and generation are constructed. -/
theorem tensor_h0_le_ten_of_degrees
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f beta 0))
    (hres : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8)
    (hb : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le beta = 8) :
    Module.finrank k (cohomologyOverField k f
      (tensor (dualSpan alpha (completeNetSections f alpha bA))
        (dualSpan beta (completeNetSections f beta bB))) 0) ≤ 10 := by
  let Ealpha : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2 :=
    { L := alpha
      isInvertible := inferInstance
      degree_eq := ha
      V := ⊤
      finrank_eq := by simpa using Module.finrank_eq_card_basis bA }
  let Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2 :=
    { L := beta
      isInvertible := inferInstance
      degree_eq := hb
      V := ⊤
      finrank_eq := by simpa using Module.finrank_eq_card_basis bB }
  exact tensor_h0_le_ten_complete_nets f hg hnp Ealpha Ebeta bA bB hres

/-- The same actual tensor bound with complete bases constructed from
the original native degree-eight nets. No basis-existence premise is
needed in this interface. -/
theorem tensor_h0_le_ten
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ealpha Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (hres : tensor Ealpha.L Ebeta.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    let bA := MukaiLemmaFiveOne.completeNetBasis f (IsCurve.topologicalKrullDim_eq_one f).le
      hg hnp Ealpha
    let bB := MukaiLemmaFiveOne.completeNetBasis f (IsCurve.topologicalKrullDim_eq_one f).le
      hg hnp Ebeta
    Module.finrank k (cohomologyOverField k f
      (tensor (dualSpan Ealpha.L (completeNetSections f Ealpha.L bA))
        (dualSpan Ebeta.L (completeNetSections f Ebeta.L bB))) 0) ≤ 10 := by
  exact tensor_h0_le_ten_complete_nets f hg hnp Ealpha Ebeta
    (MukaiLemmaFiveOne.completeNetBasis f (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ealpha)
    (MukaiLemmaFiveOne.completeNetBasis f (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ebeta)
    hres

end M9Native.MukaiTensorSectionBound
