module

public import M9StacksIntegration.LagrangianFiveCutTransport
public import M9StacksIntegration.FiniteFreeBasisPullback
public import M9StacksIntegration.LagrangianQuotientConstantTransport
public import M9StacksIntegration.Sp6VectorTransitivity

/-!
# Original quotient and first-section transport on the actual five cuts

The genuine original cut isomorphism is combined with the actual
quotient representing functor. Its target bundle isomorphism retains
the literal quotient map and sends the actual pulled first section to
the original quotient section of the genuine first symplectic column.
Every nonzero original vector is such a column by proved transitivity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module
open scoped BigOperators
universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianFiveCutQuotientTransport

open AlgebraicGeometry.Grassmannian
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open LagrangianSymplecticAction LagrangianSigmaInvariance LagrangianFreeMatrixPullback
open LagrangianUniversalSections LagrangianFiveCutTransport
open LagrangianStandardSectionZeroModel

variable (K : Type u) [Field K] [CharZero K]

/-- The first vector of the literal symplectic matrix implementing the
original transpose-convention LG action. -/
abbrev firstVector (g : Matrix.symplecticGroup (Fin 3) K) : Fin 6 → K :=
  (LagrangianTransitivity.matrixSix K (transposeSymplectic K g)).col 0

/-- Constant source transport retains the original structural field coefficients. -/
theorem constantFreeIso_first {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (h : Matrix.symplecticGroup (Fin 3) K) :
    (constantFreeIso K f h).hom.app ⊤ (freeBasisSection X 6 0) =
      constantVector K f ((LagrangianTransitivity.matrixSix K h).col 0) := by
  have hc := end_column_eq_sum X (constantFreeIso K f h).hom (0 : Fin 6)
  change (constantFreeIso K f h).hom.app ⊤ (freeBasisSection X 6 0) =
    ∑ j : Fin 6, Stacks.FreeSheafMatrix.toMatrix (constantFreeIso K f h).hom j 0 •
      freeBasisSection X 6 j at hc
  rw [hc]
  simp only [constantFreeIso_matrix, constantMatrix, Matrix.map_apply,
    LagrangianQuotientConstantTransport.scalarMap_eq_baseRingMap,
    LagrangianUniversalSections.constantVector, Matrix.col_apply]

/-- Every nonzero original six-vector is a genuine first column; there
is no symplectic-normalizer premise. -/
theorem exists_firstVector_eq (v : Fin 6 → K) (hv : v ≠ 0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K, firstVector K g = v := by
  obtain ⟨h,hh⟩ := Sp6VectorTransitivity.exists_matrixSix_send_e0 K v hv
  have ht : transposeSymplectic K (transposeSymplectic K h) = h := by
    apply Subtype.ext
    exact Matrix.transpose_transpose _
  refine ⟨transposeSymplectic K h, ?_⟩
  simpa only [firstVector, ht, Matrix.mulVec_single_one, Matrix.col_apply] using hh

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (g : Matrix.symplecticGroup (Fin 3) K)

/-- Actual quotient composition and the actual LG action construct the
target bundle isomorphism together with its original quotient triangle. -/
theorem exists_quotientIso :
    ∃ a : (Scheme.Modules.pullback (cutIso K M hM g).hom).obj
          (bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))) ≅
        bundle K (toLG K M hM),
      (pullbackPresentation (cutIso K M hM g).hom
        (quotient K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))).map ≫
          a.hom =
        (constantFreeIso K (toLG K M hM ≫ projection K) (transposeSymplectic K g)).hom ≫
          quotientMap K (toLG K M hM) := by
  have hc : (pullbackPresentation (cutIso K M hM g).hom
      (quotient K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))).Isomorphic
        (quotient K (toLG K M hM ≫ (actionIso K g).hom)) := by
    simpa only [cutIso_hom_toLG] using
      LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
        (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))
        (cutIso K M hM g).hom (quotientOnLG K)
  obtain ⟨a₀,h₀⟩ := hc
  obtain ⟨a₁,h₁⟩ := LagrangianCotangentActionQuotient.pulled_action_isomorphic
    K (toLG K M hM) (transposeSymplectic K g)
  refine ⟨a₀ ≪≫ a₁, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, h₀]
  simpa only [actionIso] using h₁

/-- The target comparison is chosen only from the proved true quotient triangle. -/
def targetIso : (Scheme.Modules.pullback (cutIso K M hM g).hom).obj
      (bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))) ≅
    bundle K (toLG K M hM) :=
  Classical.choose (exists_quotientIso K M hM g)

@[reassoc] theorem targetIso_triangle :
    (pullbackPresentation (cutIso K M hM g).hom
      (quotient K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))).map ≫
        (targetIso K M hM g).hom =
      (constantFreeIso K (toLG K M hM ≫ projection K) (transposeSymplectic K g)).hom ≫
        quotientMap K (toLG K M hM) :=
  Classical.choose_spec (exists_quotientIso K M hM g)

/-- The actual pulled standard quotient section is exactly the actual
original section of the genuine first symplectic column. -/
theorem targetIso_firstSection :
    (targetIso K M hM g).hom.app ⊤
      (pullbackGlobalSections (cutIso K M hM g).hom
        (bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))
        (curveSection K (transformedMatrix K M g) (transformed_surjective K M hM g))) =
      (quotientMap K (toLG K M hM)).app ⊤
        (constantVector K (curveProjection K M hM) (firstVector K g)) := by
  have hb := FiniteFreeBasisPullback.pullbackPresentation_basis (cutIso K M hM g).hom
    (quotient K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))) 0
  change Scheme.Modules.Hom.app (X := curve K M hM)
      (pullbackPresentation (cutIso K M hM g).hom
        (quotient K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))).map ⊤
        (freeBasisSection (curve K M hM) 6 0) =
      pullbackGlobalSections (cutIso K M hM g).hom
        (bundle K (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))
        (curveSection K (transformedMatrix K M g) (transformed_surjective K M hM g)) at hb
  have ht := congrArg
    (fun a : freeOn (curve K M hM) 6 ⟶ bundle K (toLG K M hM) =>
      a.app ⊤ (freeBasisSection (curve K M hM) 6 0)) (targetIso_triangle K M hM g)
  have hv := (constantFreeIso_first K (toLG K M hM ≫ projection K)
    (transposeSymplectic K g)).trans
      (congrArg (fun f => constantVector K f (firstVector K g))
        (LagrangianOrderedFibre.geometricFibre_over K M hM))
  calc
    _ = (targetIso K M hM g).hom.app ⊤
        (Scheme.Modules.Hom.app (X := curve K M hM)
          (pullbackPresentation (cutIso K M hM g).hom
          (quotient K (toLG K (transformedMatrix K M g)
            (transformed_surjective K M hM g)))).map ⊤
          (freeBasisSection (curve K M hM) 6 0)) :=
      congrArg ((targetIso K M hM g).hom.app ⊤) hb.symm
    _ = (quotientMap K (toLG K M hM)).app ⊤
        ((constantFreeIso K (toLG K M hM ≫ projection K)
          (transposeSymplectic K g)).hom.app ⊤ (freeBasisSection (curve K M hM) 6 0)) := ht
    _ = _ := congrArg ((quotientMap K (toLG K M hM)).app ⊤) hv

end M9Native.LagrangianFiveCutQuotientTransport
