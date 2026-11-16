module

public import M9StacksIntegration.LagrangianGenusNine
public import M9StacksIntegration.LagrangianTransverseGoodOpen
public import M9StacksIntegration.LagrangianTransverseCanonical

/-! The actual genus and complete canonical system of every integral
smooth transverse five-row section. The genuine good-family comparison
and the proved actual LG degree supply genus nine; neither genus nor a
canonical-line comparison is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianTransverseGenusNine
open LagrangianTransverseRestriction

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The actual original ordered section has native genus nine. -/
theorem genus_eq_nine (hM : Function.Surjective M.mulVec) :
    genus (curveProjection K M) = 9 :=
  (LagrangianTransverseGoodOpen.genus_eq_fibreGenus K M hM).trans
    (LagrangianGenusNine.family_genus_eq_nine K)

/-- The original fourteen primitive sections give the full native
canonical section space on this actual ordered section. -/
theorem canonicalRestriction_surjective (hM : Function.Surjective M.mulVec) :
    Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K
      (curveProjection K M) (inclusion K M)
      (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM)) :=
  LagrangianTransverseRestriction.canonicalRestriction_surjective K M hM
    (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM) (genus_eq_nine K M hM)

/-- The actual canonical H0 target has dimension nine. -/
theorem canonicalH0_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (cohomologyOverField K (curveProjection K M)
      (Stacks.Duality.dualizingSheafOverField (curveProjection K M)) 0) = 9 := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (curveProjection K M).appTop) :=
    isIso_globalSections_of_isAlgClosed K (curveProjection K M)
  exact (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
    (curveProjection K M)
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le).trans
      (genus_eq_nine K M hM)

end M9Native.LagrangianTransverseGenusNine
