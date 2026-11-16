module

public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection
public import M9StacksIntegration.MukaiCanonicalBundleFromNet
public import M9StacksIntegration.MukaiEvaluationChoices
public import M9StacksIntegration.MukaiEvaluationMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The complete original six-section basis on an actual cut

The actual original six-space injects into H0 by the proved primitive
restriction rank nine. The actual canonical-bundle property supplies H0
dimension six, so the original quotient sections themselves are a complete
basis. Their evaluation is the literal original quotient, and their
standard bivector vanishes by the actual isotropic quotient relation.

The canonical-bundle property remains a genuine intermediate geometric
input; no section-space comparison or normalized basis is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

universe u
namespace M9Native.LagrangianOriginalSixBasis

open LagrangianTransverseRestriction LagrangianUniversalSections
open MukaiCanonicalBundleFromNet MukaiLagrangianMap

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
  (hM : Function.Surjective M.mulVec)

local instance curveSmooth : Smooth (curveProjection K M) :=
  SmoothOfRelativeDimension.smooth 1 _

include hM in
/-- The original constant six-space injects by the actual original
primitive-restriction image rank nine, without a completeness input. -/
theorem sectionMap_injective :
    Function.Injective (sectionMap K (curveProjection K M) (inclusion K M)) := by
  apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
    K (curveProjection K M) (inclusion K M) rfl
  rw [LagrangianTransverseRestriction.primitiveRestriction_range_finrank K M hM]
  norm_num

variable (hQ : IsCanonicalGeneratedSemi (curveProjection K M) (bundle K (inclusion K M)))

include hM hQ in
/-- Completeness follows from original injection and the actual
canonical property, rather than an assumed H0-preserving coordinate map. -/
theorem sectionMap_bijective :
    Function.Bijective (sectionMap K (curveProjection K M) (inclusion K M)) := by
  let : Module.Finite K (cohomologyOverField K (curveProjection K M)
      (bundle K (inclusion K M)) 0) := Module.finite_of_finrank_pos (by rw [hQ.2.1]; decide)
  have hd : finrank K (Fin 6 → K) =
      finrank K (cohomologyOverField K (curveProjection K M) (bundle K (inclusion K M)) 0) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hQ.2.1.symm
  exact ⟨sectionMap_injective K M hM,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (sectionMap_injective K M hM)⟩

/-- The actual original quotient six-space is the full H0 space. -/
def sectionEquiv : (Fin 6 → K) ≃ₗ[K]
    cohomologyOverField K (curveProjection K M) (bundle K (inclusion K M)) 0 :=
  LinearEquiv.ofBijective (sectionMap K (curveProjection K M) (inclusion K M))
    (sectionMap_bijective K M hM hQ)

/-- This basis consists of the six original quotient sections. -/
def originalBasis : Basis (Fin 6) K
    (cohomologyOverField K (curveProjection K M) (bundle K (inclusion K M)) 0) :=
  (Pi.basisFun K (Fin 6)).map (sectionEquiv K M hM hQ)

/-- Each basis vector is the actual original quotient H0 section. -/
theorem originalBasis_apply (j : Fin 6) :
    originalBasis K M hM hQ j = sectionH0 K (curveProjection K M) (inclusion K M) j := by
  change sectionMap K (curveProjection K M) (inclusion K M) ((Pi.basisFun K (Fin 6)) j) = _
  simpa only [Pi.basisFun_apply] using
    sectionMap_basis K (curveProjection K M) (inclusion K M) j

/-- The full evaluation in this derived basis is the literal original
quotient map; no evaluation compatibility is an additional hypothesis. -/
theorem evaluation_originalBasis :
    MukaiSemiIrreducible.evaluation K (curveProjection K M) (bundle K (inclusion K M))
      (originalBasis K M hM hQ) = quotientMap K (inclusion K M) := by
  apply MukaiEvaluationMatrix.freeHom_ext_top
  intro j
  rw [MukaiEvaluationMatrix.evaluation_basisSection, originalBasis_apply]
  change (cohomologyOverFieldZeroLinearIso K (curveProjection K M) (bundle K (inclusion K M))).hom
    ((cohomologyOverFieldZeroLinearIso K (curveProjection K M) (bundle K (inclusion K M))).inv
      (quotientSection K (inclusion K M) j)) = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- The actual standard bivector vanishes in exterior evaluation of
the derived complete basis, by the original LG quotient isotropy. -/
theorem basisSigma_lambda_eq_zero :
    ExteriorEvaluation.lambda K (curveProjection K M) (bundle K (inclusion K M)) 2
      (basisSigma K (curveProjection K M) (bundle K (inclusion K M))
        (originalBasis K M hM hQ)) = 0 := by
  have h := LagrangianQuotientExteriorEvaluation.lambda_two_sigma_eq_zero
    K (curveProjection K M) (quotientMap K (inclusion K M))
    (LagrangianUniversalSectionInjection.universal_quotient_annihilates K (inclusion K M))
  change ExteriorEvaluation.lambda K (curveProjection K M) (bundle K (inclusion K M)) 2
    (exteriorPower.map 2 (sectionMap K (curveProjection K M) (inclusion K M))
      (LagrangianField.sigma K)) = 0 at h
  have hv (i : Fin 3) :
      (fun a : Fin 2 => sectionMap K (curveProjection K M) (inclusion K M)
        (![Pi.single (i.castAdd 3) 1, Pi.single (Fin.natAdd 3 i) 1] a)) =
      ![sectionH0 K (curveProjection K M) (inclusion K M) (i.castAdd 3),
        sectionH0 K (curveProjection K M) (inclusion K M) (Fin.natAdd 3 i)] := by
    funext a
    fin_cases a
    · change sectionMap K (curveProjection K M) (inclusion K M) (Pi.single (i.castAdd 3) 1) = _
      exact sectionMap_basis K (curveProjection K M) (inclusion K M) (i.castAdd 3)
    · change sectionMap K (curveProjection K M) (inclusion K M) (Pi.single (Fin.natAdd 3 i) 1) = _
      exact sectionMap_basis K (curveProjection K M) (inclusion K M) (Fin.natAdd 3 i)
  simpa only [LagrangianField.sigma, LagrangianField.e, LagrangianField.f,
    LagrangianField.eIndex, LagrangianField.fIndex, LagrangianField.basisVector,
    map_sum, exteriorPower.map_apply_ιMulti, Function.comp_def, basisSigma,
    originalBasis_apply, sectionMap_basis, hv] using h

end M9Native.LagrangianOriginalSixBasis
