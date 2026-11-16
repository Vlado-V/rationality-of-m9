module

public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation
public import M9StacksIntegration.MukaiConormalContraction
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf

/-!
# The actual primitive-Plücker conormal bundle model

The object here is the actual native conormal sheaf of the proved native
primitive Plücker closed immersion. Its determinant twist and actual
curve pullback retain that original ideal-sheaf construction. The
pullback comparison uses the original evaluation quotient's determinant
isomorphism. No rank-seven, first-jet-kernel, symmetric-square quotient,
or nondegeneracy statement is supplied as a defining field or hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open M9Native.MukaiHomCoefficient

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiConormalBundle

variable (K : Type u) [Field K] [CharZero K]

/-- Native `I/I²` of the ACTUAL primitive-Plücker closed immersion. -/
abbrev conormal : (LagrangianGrassmannian.space K).Modules :=
  Stacks.Conormal.conormalSheaf (LagrangianPluckerLinear.primitivePlucker K)

instance conormal_quasicoherent : (conormal K).IsQuasicoherent := inferInstance

/-- The actual determinant twist `N* ⊗ det Q`; its comparison with the
first-jet kernel is a theorem still to be constructed, not a definition. -/
abbrev twistedConormal : (LagrangianGrassmannian.space K).Modules :=
  tensor (conormal K) (LagrangianPluckerQuotient.determinantLine K)

variable {X : Scheme.{u}} (g : X ⟶ LagrangianGrassmannian.space K)

abbrev curveConormal : X.Modules := (Scheme.Modules.pullback g).obj (conormal K)

abbrev curveTwistedConormal : X.Modules :=
  (Scheme.Modules.pullback g).obj (twistedConormal K)

/-- The actual pullback of the actual determinant-twisted conormal sheaf. -/
def curveTwistedConormalIso :
    curveTwistedConormal K g ≅
      tensor (curveConormal K g)
        ((Scheme.Modules.pullback g).obj (LagrangianPluckerQuotient.determinantLine K)) :=
  Stacks.RingedSpace.pullbackTensorIsoApp g.toLRSHom.toShHom
    (conormal K) (LagrangianPluckerQuotient.determinantLine K)

variable (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))

/-- The determinant in the curve twist is the actual determinant of E,
transported by the original evaluation-quotient triangle. -/
def evaluationTwistedConormalIso
    (d : MukaiPrimitiveCanonicalEvaluation.EvaluationDiagram K f E b) :
    curveTwistedConormal K d.map ≅
      tensor (curveConormal K d.map) (Scheme.Modules.exteriorPower E (3 : ℤ)) :=
  curveTwistedConormalIso K d.map ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
      (curveConormal K d.map)).mapIso (d.determinantIso K f E)

end M9Native.MukaiConormalBundle
