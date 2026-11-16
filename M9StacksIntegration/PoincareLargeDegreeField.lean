module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField

/-!
# Large-degree fibre cohomology using the checked field-vanishing provider

Ordinary field base change gives the actual unit H0 rank, and the
native Riemann--Roch identity gives H0 after native H1 vanishing.
This avoids the broader symmetric-power import of the separate native
LargeDegreeVanishingFieldExtension wrapper. The module, curve, degree
and cartesian field extension in these statements are actual ones.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.PoincareChern.LargeDegreeField

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
  (g : Y ⟶ X) (π : Y ⟶ Spec (.of K)) [IsProper π]
  (hsq : IsPullback g π f (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include hsq

/-- The original proper integral curve's actual unit H0 remains
one-dimensional over every actual extension field. -/
theorem unitH0_rank_one_baseChange :
    Module.finrank K (cohomologyOverField K π (SheafOfModules.unit Y.ringCatSheaf) 0) = 1 := by
  calc
    _ = Module.finrank K (cohomologyOverField K π
        ((Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf)) 0) :=
      (finrank_cohomologyOverField_eq_of_iso K π (Scheme.Modules.pullbackUnitIso g) 0).symm
    _ = Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :=
      finrank_cohomologyOverField_baseChange_field k K g π f hsq
        (SheafOfModules.unit X.ringCatSheaf) 0
    _ = 1 := by
      rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f]
      exact finrank_globalSections_eq_one k f

variable [IsCurve K π] [GeometricallyIntegral π] (L : Y.Modules)
  (hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)

/-- Native arbitrary-field H1 vanishing plus native Riemann--Roch,
with actual genus and actual unit rank transported from the original curve. -/
theorem h0_h1_of_largeDegree
    (hdeg : 2 * (genus f : ℤ) - 1 ≤ @invertibleCurveDegree K _ Y π _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := π)).le L hL) :
    IsZero (cohomologyOverField K π L 1) ∧
      (Module.finrank K (cohomologyOverField K π L 0) : ℤ) =
        @invertibleCurveDegree K _ Y π _
          (IsCurve.topologicalKrullDim_eq_one (k := K) (f := π)).le L hL + 1 - genus f := by
  have hg : genus π = genus f := genus_baseChange k K g π f hsq
  have h1 := isZero_cohomologyOverField_one_of_geometricallyIntegral K π L hL
    (by rw [hg]; exact hdeg)
  have hz : Module.finrank K (cohomologyOverField K π L 1) = 0 := by
    haveI := ModuleCat.subsingleton_of_isZero h1
    exact Module.finrank_zero_of_subsingleton
  have h0 := finrank_cohomologyOverField_zero_sub_one_eq K π
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := π)).le L hL
  have hu := unitH0_rank_one_baseChange k K f g π hsq
  refine ⟨h1,?_⟩
  simpa only [hz,Nat.cast_zero,sub_zero,hu,Nat.cast_one,hg] using h0

/-- The ranks needed for all nine actual moving-graph stages and
for the actual degree-eighteen Picard twist. -/
theorem genusNine_h0_h1 (hg : genus f = 9) (r : ℕ) (hr : 9 ≤ r)
    (hd : @invertibleCurveDegree K _ Y π _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := π)).le L hL = (r : ℤ) + 8) :
    IsZero (cohomologyOverField K π L 1) ∧
      Module.finrank K (cohomologyOverField K π L 0) = r := by
  obtain ⟨h1,h0⟩ := h0_h1_of_largeDegree k K f g π hsq L hL
    (by rw [hg,hd]; omega)
  refine ⟨h1,?_⟩
  rw [hd,hg] at h0
  exact_mod_cast (by omega : (Module.finrank K (cohomologyOverField K π L 0) : ℤ) = (r : ℤ))

end M9Native.PoincareChern.LargeDegreeField
