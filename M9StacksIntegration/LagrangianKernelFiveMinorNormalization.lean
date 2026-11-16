module

public import M9StacksIntegration.LagrangianKernelFiveSections
public import M9StacksIntegration.LagrangianCommonKernelQuadric

/-!
# The five derived sections are the literal original ordered minors

The finite-coordinate extraction is identified with the actual exterior
coefficient functionals. Its coefficient vectors are therefore the actual
ordered wedges, through the genuine coefficient-duality equivalence.
Applying native exterior evaluation proves the global-section equality;
no frame or coordinate-normalization equality is supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelFiveMinorNormalization

open LagrangianField LagrangianMatrixChart LagrangianCommonKernelQuadric
open LagrangianKernelPrimitiveSections LagrangianQuotientExteriorEvaluation
open LagrangianKernelFiveSections LagrangianDeterminantSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

/-- Original ordered q11,q12,q22,p00,b columns, including their cyclic signs. -/
def fiveMinor : Fin 5 → (Fin 3 ↪ Fin 6) :=
  ![⟨![1,5,3], by decide⟩, ⟨![1,3,4], by decide⟩, ⟨![2,3,4], by decide⟩,
    ⟨![3,1,2], by decide⟩, ⟨![3,4,5], by decide⟩]

variable (k : Type u) [Field k]

theorem extraction_coefficient (i : Fin 20) (a : Fin 5) :
    fiveExtraction k (projectionColumn k i) a =
      coordinate3 k (fiveMinor a) (thirdBasis20 k i) := by
  let M : Matrix (Fin 3) (Fin 6) k := fun r => basisVector k (LagrangianRing.triple i r)
  have hw : rowPlucker k M = thirdBasis20 k i := by
    rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply]
    change exteriorPower.ιMulti k 3 ![M 0, M 1, M 2] = _
    congr 1
    funext r
    fin_cases r <;> rfl
  have hc : rowFourteen k M = projectionColumn k i := by
    rw [rowFourteen, hw]
    funext j
    simp only [projectionColumn, projectionMatrix, LinearMap.toMatrix_apply, Basis.equivFun_apply]
  have hex : fiveExtraction k (projectionColumn k i) = fiveCoordinates k M := by
    rw [← hc]
    change LagrangianCommonKernelSpan.extraction k
      ((coordinateBasis14 k).equivFun.symm
        ((coordinateBasis14 k).equivFun (coordinateProjection k (rowPlucker k M)))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact (fiveCoordinates_eq_original k M).symm
  rw [hex, ← hw, coordinate3_rowPlucker]
  fin_cases a <;> rfl

/-- The actual coefficient vector of one of the five extraction functionals. -/
def fiveCoefficientVector (a : Fin 5) : Third k :=
  ∑ i : Fin 20, fiveExtraction k (projectionColumn k i) a • thirdBasis20 k i

theorem fiveCoefficientVector_eq_wedge (a : Fin 5) :
    fiveCoefficientVector k a =
      exteriorPower.ιMulti k 3 (fun r => basisVector k (fiveMinor a r)) := by
  let w := (MukaiPrimitiveDuality.coefficientDuality k).symm (coordinate3 k (fiveMinor a))
  have hc (i : Fin 20) : (thirdBasis20 k).repr w i =
      fiveExtraction k (projectionColumn k i) a := by
    have h := (thirdBasis20 k).toDual_apply_left w i
    change MukaiPrimitiveDuality.coefficientDuality k w (thirdBasis20 k i) =
      (thirdBasis20 k).repr w i at h
    rw [show MukaiPrimitiveDuality.coefficientDuality k w = coordinate3 k (fiveMinor a)
      from (MukaiPrimitiveDuality.coefficientDuality k).apply_symm_apply _] at h
    exact h.symm.trans (extraction_coefficient k i a).symm
  have h : fiveCoefficientVector k a = w := by
    simpa only [fiveCoefficientVector, hc] using (thirdBasis20 k).sum_repr w
  exact h.trans (MukaiPrimitiveDuality.coefficientSharp_coordinate k (fiveMinor a))

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {Q : X.Modules} (q : freeOn X 6 ⟶ Q)

/-- The original quotient exterior evaluation on any ordered coordinate wedge. -/
theorem lambda_orderedMinor (c : Fin 3 ↪ Fin 6) :
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom
      (lambda k f q 3 (exteriorPower.ιMulti k 3 (fun r => basisVector k (c r)))) =
        minorSection X q c := by
  rw [lambda_ιMulti]
  refine (ExteriorEvaluation.lambda_ιMulti k f Q 3
    (fun r => originalSectionMap k f q (basisVector k (c r)))).trans ?_
  have hv : (fun r : Fin 3 => ExteriorEvaluation.h0SectionsSemilinear k f Q
      (originalSectionMap k f q (basisVector k (c r)))) =
      (fun r => q.app ⊤ (freeBasisSection X 6 (c r))) := by
    funext r
    change (cohomologyOverFieldZeroLinearIso k f Q).hom
      (originalSectionMap k f q (basisVector k (c r))) = _
    rw [originalSectionMap_basis]
    exact originalSection_sections k f q _
  rw [hv]
  exact (minorSection_eq_wedge X q c).symm

theorem fiveValues_eq_lambda (a : Fin 5) :
    fiveValues k (minorH0 k f q) a =
      lambda k f q 3 (exteriorPower.ιMulti k 3 (fun r => basisVector k (fiveMinor a r))) := by
  have hs : lambda k f q 3 (fiveCoefficientVector k a) = fiveValues k (minorH0 k f q) a := by
    unfold fiveCoefficientVector fiveValues
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    exact congrArg (fun z => fiveExtraction k (projectionColumn k i) a • z)
      (lambda_thirdBasis_eq_minorH0 k f q i)
  exact hs.symm.trans (congrArg (lambda k f q 3) (fiveCoefficientVector_eq_wedge k a))

/-- Exact original five-minor normalization, proved for any actual quotient map. -/
theorem fiveSections_eq_orderedMinor (a : Fin 5) :
    fiveSections k f q a = minorSection X q (fiveMinor a) := by
  exact (congrArg (fun s => (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower Q 3)).hom s) (fiveValues_eq_lambda k f q a)).trans
      (lambda_orderedMinor k f q (fiveMinor a))

end M9Native.LagrangianKernelFiveMinorNormalization
