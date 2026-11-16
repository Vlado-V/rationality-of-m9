module

public import M9StacksIntegration.SmoothFieldGenusStability
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesGenusDecomposition

/-! The exact original cohomological genus predicate used by the actual coarse
constructor. Stability follows from the genuine field-genus/rank theorem.
No curve-algebraicity or coarse-space premise is supplied. -/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarse

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A smooth H0 family with actual R¹ rank g≥2 is stable of that genus. -/
theorem stable_of_smooth_cohomological_genus {g : ℕ} (hg : 2 ≤ g)
    {F : CurveFamily B hZ}
    (hF : IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) :
    IsStableCurveFamilyOfGenus B hZ g F := by
  have hfg : IsSmoothH0FamilyOfFibreGenus B hZ g F :=
    ⟨hF.1, (F.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hF.1.2)
      g).mpr hF.2⟩
  exact ⟨M9Native.SmoothFieldGenusStability.isStableCurveFamily_of_smooth_fieldGenus
    B hZ hg hfg, hF.2⟩

/-- The actual cohomological and smooth/stable predicates agree on every
original family, with its original base and coefficient structure retained. -/
theorem smooth_cohomological_genus_iff_smooth_stable {g : ℕ} (hg : 2 ≤ g)
    (F : CurveFamily B hZ) :
    (IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) ↔
      (IsSmoothFamily B hZ F ∧ IsStableCurveFamilyOfGenus B hZ g F) := by
  constructor
  · intro hF
    exact ⟨hF.1.1.1, stable_of_smooth_cohomological_genus B hZ hg hF⟩
  · rintro ⟨hsm, hst⟩
    exact isSmoothH0Family_and_hasGenus_of_isStableCurveFamilyOfGenus B hZ hsm hst

end M9StacksIntegration.GenusNineCoarse
