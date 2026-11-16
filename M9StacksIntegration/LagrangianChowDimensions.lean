module

public import M9StacksIntegration.LagrangianAmbientDimension
public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.LagrangianRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension

/-! The actual dimension-nine and dimension-six hypotheses in the
genuine native field Chow situation, derived from the original schemes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.Chow

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

instance grassmannianProjection_locallyOfFiniteType :
    LocallyOfFiniteType (grassmannianProjection K) := by
  change LocallyOfFiniteType (AlgebraicGeometry.Grassmannian.schemeOver.over 3 6 (base K)).hom
  infer_instance

instance lagrangianProjection_locallyOfFiniteType :
    LocallyOfFiniteType (inclusion K ≫ grassmannianProjection K) :=
  inferInstanceAs (LocallyOfFiniteType (projection K))

theorem ambient_delta_dimension :
    schemeDeltaDimension (fieldChowSituation K) (grassmannianProjection K) = (9 : EInt) := by
  letI : IsIntegral (grassmannian K) :=
    inferInstanceAs (IsIntegral (M9Native.GrassmannianCharts.space K 3 6))
  exact schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (grassmannianProjection K) (ambient_dimension K)

theorem lagrangian_delta_dimension :
    schemeDeltaDimension (fieldChowSituation K) (inclusion K ≫ grassmannianProjection K) =
      (6 : EInt) := by
  change schemeDeltaDimension (fieldChowSituation K) (projection K) = (6 : EInt)
  exact schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (projection K) (M9Native.LagrangianIntegral.space_dimension K)

end M9Native.LagrangianDegree
