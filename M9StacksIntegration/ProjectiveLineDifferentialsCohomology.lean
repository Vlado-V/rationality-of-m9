module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.EulerCharBiproduct.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions

/-!
# The actual cotangent cohomology of the native projective line

The original Euler sequence and the native computation of the twists give
`H⁰(Ω)=0` and `H¹(Ω)=k`. This uses the actual relative differentials and the
actual structure morphism of `Proj k[T₀,T₁]`; no comparison with a dualizing
sheaf or supplied cotangent-degree formula is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.ProjectiveSpace.Cohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.ProjectiveLineDifferentialsCohomology

variable (k : Type u) [Field k]

abbrev cotangent : (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1)

def eulerSequence : ShortComplex (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  ShortComplex.mk (eulerFirstArrow k 1) (eulerSurjection k 1)
    (eulerFirstArrow_comp_eulerSurjection k 1)

theorem eulerSequence_shortExact : (eulerSequence k).ShortExact :=
  shortExact_eulerSequence k 1

/-- All cohomology of the literal `O(-1)` vanishes. -/
theorem twistMinusOne_cohomology_isZero (n : ℕ) :
    IsZero (cohomologyOverField k (projToSpecCoeff k 1)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k 1) (-1)) n) := by
  apply (cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 1 _ n).isZero_iff.mpr
  change IsZero (twistCohomology k 1 (-1) n)
  rcases n with _ | n
  · exact isZero_twistCohomology_zero_of_neg k (by norm_num)
  · rcases n with _ | n
    · exact isZero_twistCohomology_one_of_neg_one_le k le_rfl
    · exact isZero_twistCohomology_of_two_le k (-1) (by omega)

/-- The actual middle term of the Euler sequence is acyclic. -/
theorem eulerMiddle_cohomology_isZero (n : ℕ) :
    IsZero (cohomologyOverField k (projToSpecCoeff k 1)
      (eulerSequence k).X₂ n) := by
  exact isZero_cohomologyOverField_biproduct k (projToSpecCoeff k 1)
    (twistMinusOneFamily k 1) n fun _ => twistMinusOne_cohomology_isZero k n

theorem unit_cohomology_finrank (n : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
      (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k 1)).ringCatSheaf) n) =
      if n = 0 then 1 else 0 := by
  have ht : Module.finrank k (twistCohomology k 1 0 n) = if n = 0 then 1 else 0 := by
    rcases n with _ | n
    · simpa using (twistCohomologyZeroIsoCoeff k 1).toLinearEquiv.finrank_eq
    · have hz : IsZero (twistCohomology k 1 0 (n + 1)) := by
        rcases n with _ | n
        · exact isZero_twistCohomology_one_of_neg_one_le k (by norm_num)
        · exact isZero_twistCohomology_of_two_le k 0 (by omega)
      have := ModuleCat.subsingleton_of_isZero hz
      have hfin : Module.finrank k (twistCohomology k 1 0 (n + 1)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simpa using hfin
  exact (cohomologyOverFieldIso k (projToSpecCoeff k 1)
    (twistingSheafZeroIsoUnit (polyGrading k 1)) n).toLinearEquiv.finrank_eq.symm.trans
      ((cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 1 _ n).toLinearEquiv.finrank_eq.trans ht)

theorem cotangent_H0_isZero :
    IsZero (cohomologyOverField k (projToSpecCoeff k 1) (cotangent k) 0) := by
  obtain ⟨d, hi, -, -, -⟩ := exists_cohomologyOverField_longExactSequence
    k (projToSpecCoeff k 1) (eulerSequence_shortExact k)
  let := ModuleCat.subsingleton_of_isZero (eulerMiddle_cohomology_isZero k 0)
  have : Subsingleton (cohomologyOverField k (projToSpecCoeff k 1) (cotangent k) 0) :=
    ⟨fun a b => hi (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr this

/-- The connecting map of the actual Euler sequence identifies each positive
cotangent cohomology group with the preceding structure-sheaf cohomology. -/
def cotangentSuccEquivUnit (n : ℕ) :
    cohomologyOverField k (projToSpecCoeff k 1) (cotangent k) (n + 1) ≃ₗ[k]
      cohomologyOverField k (projToSpecCoeff k 1)
        (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k 1)).ringCatSheaf) n := by
  let hex := exists_cohomologyOverField_longExactSequence
    k (projToSpecCoeff k 1) (eulerSequence_shortExact k)
  let d := hex.choose
  have hbc := hex.choose_spec.2.2.1
  have hca := hex.choose_spec.2.2.2
  let := ModuleCat.subsingleton_of_isZero (eulerMiddle_cohomology_isZero k n)
  let := ModuleCat.subsingleton_of_isZero (eulerMiddle_cohomology_isZero k (n + 1))
  have hgzero : (cohomologyOverFieldMap k (projToSpecCoeff k 1) (eulerSequence k).g n).hom = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp only [hx, map_zero]
  exact (LinearEquiv.ofBijective (d n).hom
    ⟨(LinearMap.injective_iff_eq_zero_of_exact (hbc n)).mpr hgzero,
      (LinearMap.surjective_iff_eq_zero_of_exact (hca n)).mpr (by ext; exact Subsingleton.elim _ _)⟩).symm

/-- The original native cotangent sheaf has exactly the expected cohomology dimensions. -/
theorem cotangent_cohomology_finrank (n : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1) (cotangent k) n) =
      if n = 1 then 1 else 0 := by
  rcases n with _ | n
  · have := ModuleCat.subsingleton_of_isZero (cotangent_H0_isZero k)
    simp only [Nat.zero_ne_one, ↓reduceIte]
    exact Module.finrank_zero_of_subsingleton
  · rw [(cotangentSuccEquivUnit k n).finrank_eq, unit_cohomology_finrank]
    simp

theorem cotangent_alternating_finrank :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1) (cotangent k) n) : ℤ)) =
      -1 := by
  simp_rw [cotangent_cohomology_finrank]
  rw [finsum_eq_single _ 1 (fun n hn => by simp [hn])]
  norm_num

theorem unit_alternating_finrank :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
        (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k 1)).ringCatSheaf) n) : ℤ)) = 1 := by
  simp_rw [unit_cohomology_finrank]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
  norm_num

end M9Native.ProjectiveLineDifferentialsCohomology
