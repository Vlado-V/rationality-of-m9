module

public import M9StacksIntegration.MukaiPrimitiveCanonicalDiagram
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials
public import M9StacksIntegration.LagrangianCurveConormal
public import M9StacksIntegration.LagrangianCanonicalDeterminant
public import M9StacksIntegration.LagrangianFiveEquationDeterminant
public import M9StacksIntegration.LagrangianFiveSectionModel
public import M9StacksIntegration.LagrangianCurveAdjunction

/-!
# The genuine determinant lines of the Mukai curve conormal map

The original canonical evaluation diagram identifies the pulled quotient
determinant with the actual curve cotangent line. The actual conormal
short exact sequence, the proved ambient cotangent determinant, and
native integer-power cancellation then identify its determinant with
the minus-fifth power of that same original pulled line. The literal
five-equation dual has the same determinant by its genuine free model.

No determinant identification or normal-map isomorphism is supplied as
an input. Closedness of the original map is an independent geometric
input to this reusable comparison, proved on the actual forward path.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianConormalDeterminantPullback
open M9Native.SymmetricSquareIntegerTensorPower
universe u

namespace M9Native.MukaiCurveConormalDeterminant

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

/-- The actual short exact sequence and quotient-line identification determine
the first determinant line by genuine invertible tensor cancellation. -/
def sourceIsoOfDeterminants {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r : ℕ) (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (a : ℤ) (eQ : S.X₃ ≅ L)
    (eM : topExterior S.X₂ (r + 1) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1)) :
    topExterior S.X₁ r ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a := by
  let eS : tensor (topExterior S.X₁ r) S.X₃ ≅ topExterior S.X₂ (r + 1) :=
    tensorIso (Iso.refl _) (Scheme.Modules.exteriorPowerOneIsoSelf S.X₃).symm ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso S.f S.g S.zero hS r 0
  let e : tensor L (topExterior S.X₁ r) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1) :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
        L (topExterior S.X₁ r) ≪≫
      tensorIso (Iso.refl _) eQ.symm ≪≫ eS ≪≫ eM
  let j : tensor L
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1) :=
    tensorIso
      (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L).symm
      (Iso.refl _) ≪≫ integerMultiplication L 1 a ≪≫
        Stacks.SheafOfModules.Invertible.tensorPowerReindex X.presheaf X.ringCatSheaf.2 L
          (add_comm 1 a)
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L
  letI : T.IsEquivalence :=
    Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L
  exact T.preimageIso (e ≪≫ j.symm)

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K]
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
  (b : Module.Basis (Fin 6) K (H0 K f E)) (d : EvaluationDiagram K f E b)
  [IsClosedImmersion d.map]
  (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)

/-- The actual original pulled determinant line. -/
abbrev curveLine : X.Modules := (Scheme.Modules.pullback d.map).obj (determinantLine K)

omit [CharZero K] [IsCurve K f] [Smooth f] [IsProper f]
  [SheafOfModules.IsFiniteLocallyFreeOfRank E 3] [IsClosedImmersion d.map] in
/-- Its invertibility is derived from the actual universal rank-three quotient. -/
theorem curveLine_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (curveLine K f E b d) := by
  let := LagrangianCanonicalDeterminant.determinantLine_isInvertible K
  exact pulledLine_isInvertible d.map (determinantLine K)

/-- The original canonical evaluation diagram gives the genuine
cotangent comparison, with the actual structural triangle retained. -/
def differentialsIsoCurveLine :
    Scheme.Hom.relativeDifferentials (d.map ≫ projection K) ≅ curveLine K f E b d :=
  eqToIso (congrArg Scheme.Hom.relativeDifferentials d.over_base) ≪≫
    (SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso f).symm ≪≫
      (d.canonicalIso K f E c).symm

omit [CharZero K] [IsProper f]
  [SheafOfModules.IsFiniteLocallyFreeOfRank E 3] [IsClosedImmersion d.map] in
/-- Smoothness and dimension one belong to the original source curve. -/
theorem map_smoothOfRelativeDimension_one :
    SmoothOfRelativeDimension 1 (d.map ≫ projection K) := by
  rw [d.over_base]
  exact smoothOfRelativeDimension_one_of_isCurve K f

/-- The actual native conormal determinant is minus five in the
original pulled determinant line, derived from the true exact sequence. -/
def conormalDeterminantIso :
    letI := curveLine_isInvertible K f E b d
    topExterior (LagrangianCurveConormal.sequence K d.map).X₁ 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (curveLine K f E b d) (-5) := by
  letI := map_smoothOfRelativeDimension_one K f E b d
  letI := curveLine_isInvertible K f E b d
  letI := LagrangianCanonicalDeterminant.determinantLine_isInvertible K
  letI := LagrangianCurveConormal.sequence_rank K d.map
  letI := LagrangianCurveConormal.quotient_rank K d.map
  exact sourceIsoOfDeterminants (LagrangianCurveConormal.sequence K d.map)
    (LagrangianCurveConormal.sequence_shortExact K d.map) 5 (curveLine K f E b d) (-5)
    (differentialsIsoCurveLine K f E b d c)
    (topExteriorPullbackOfIntegerIso d.map
      (Scheme.Hom.relativeDifferentials (projection K)) 6 (determinantLine K) (-4)
      (LagrangianCanonicalDeterminant.cotangentDeterminantIso K))

/-- The genuine literal original equation-dual determinant has the same
minus-five normalization, without a supplied free-model comparison. -/
def equationDualDeterminantIso :
    letI := curveLine_isInvertible K f E b d
    topExterior ((Scheme.Modules.pullback d.map).obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (LagrangianFiveSectionModel.equationBundle K))) 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (curveLine K f E b d) (-5) := by
  letI := LagrangianCanonicalDeterminant.determinantLine_isInvertible K
  exact LagrangianFiveEquationDeterminant.pulledFiveEquationDualTopIso d.map (determinantLine K)

/-- The determinant lines of the actual row-to-conormal map are
isomorphic by proved geometry, independently of whether that map vanishes. -/
def determinantLineComparison :
    topExterior ((Scheme.Modules.pullback d.map).obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (LagrangianFiveSectionModel.equationBundle K))) 5 ≅
      topExterior (LagrangianCurveConormal.sequence K d.map).X₁ 5 :=
  equationDualDeterminantIso K f E b d ≪≫ (conormalDeterminantIso K f E b d c).symm

end M9Native.MukaiCurveConormalDeterminant
