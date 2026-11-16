module

public import M9StacksIntegration.LagrangianTripleDeterminantSection
public import M9StacksIntegration.LagrangianAffineDeterminant
public import M9StacksIntegration.FreeSheafMatrixFiberRank

/-!
# The original primitive hyperplane is the actual local triple determinant

Every actual rank-three quotient frame induces a genuine frame of the
original determinant line. In this frame, the original primitive
hyperplane of an original triple is the determinant of its actual
original evaluation matrix. All H0, exterior, and pullback comparisons
are proved; no local determinant normalization is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianTripleDeterminantCoordinates

open LagrangianMatrixChart LagrangianDeterminantSections
open LagrangianUniversalSections LagrangianUniversalTriples LagrangianTripleDeterminantSection

variable {X : Scheme.{u}}

/-- Actual top-wedge coordinates of any triple of actual free-sheaf sections. -/
theorem free_wedge_coordinates (v : Fin 3 → Γ(freeOn X 3,⊤)) :
    freeDeterminantCoordinates X
      (ExteriorEvaluation.sectionComparison (freeOn X 3) 3 ⊤
        (exteriorPower.ιMulti Γ(X,⊤) 3 v)) =
      (Matrix.of (fun i j => freeSectionCoordinates X 3 (v j) i)).det := by
  change topEquiv Γ(X,⊤) ((freeExteriorSectionsEquiv X 3 3).symm _) = _
  rw [freeExteriorSectionsEquiv_symm_comparison, topEquiv_apply,
    topCoordinate_ιMulti, Module.Basis.det_apply]
  rfl

/-- Actual top-wedge coordinates of every actual free-sheaf evaluation matrix. -/
theorem evaluation_wedge_coordinates (a : freeOn X 3 ⟶ freeOn X 3) :
    freeDeterminantCoordinates X
      (ExteriorEvaluation.sectionComparison (freeOn X 3) 3 ⊤
        (exteriorPower.ιMulti Γ(X,⊤) 3
          (fun j => a.app ⊤ (freeBasisSection X 3 j)))) =
      (Stacks.FreeSheafMatrix.toMatrix a).det := by
  rw [free_wedge_coordinates]
  congr 1
  ext i j
  exact freeCoordinates_map_basis a i j

variable (k : Type u) [Field k] [CharZero k] (f : X ⟶ Spec (.of k))
  (l : X ⟶ LagrangianGrassmannian.space k)

/-- Original actual determinant value in an actual quotient frame. -/
theorem framed_determinantValue_coordinates (e : bundle k l ≅ freeOn X 3)
    (s : Fin 3 → (Fin 6 → k)) :
    freeDeterminantCoordinates X
      ((Scheme.Modules.exteriorPowerMap e.hom (3 : ℤ)).app ⊤
        ((cohomologyOverFieldZeroLinearIso k f
          (Scheme.Modules.exteriorPower (bundle k l) 3)).hom
          (determinantValue k f l s))) =
      (Stacks.FreeSheafMatrix.toMatrix (evaluation k f l s ≫ e.hom)).det := by
  refine (congrArg (fun z : Γ(Scheme.Modules.exteriorPower (bundle k l) 3,⊤) =>
    freeDeterminantCoordinates X ((Scheme.Modules.exteriorPowerMap e.hom (3 : ℤ)).app ⊤ z))
    (ExteriorEvaluation.lambda_ιMulti k f (bundle k l) 3
      (fun i => sectionMap k f l (s i)))).trans ?_
  refine (congrArg (freeDeterminantCoordinates X)
    (ExteriorEvaluation.sectionComparison_map_ιMulti e.hom 3 ⊤
      (fun i => ExteriorEvaluation.h0SectionsSemilinear k f (bundle k l)
        (sectionMap k f l (s i))))).trans ?_
  have hv : (fun j : Fin 3 => e.hom.app ⊤
      (ExteriorEvaluation.h0SectionsSemilinear k f (bundle k l) (sectionMap k f l (s j)))) =
      (fun j => (evaluation k f l s ≫ e.hom).app ⊤ (freeBasisSection X 3 j)) := by
    funext j
    exact congrArg (e.hom.app ⊤)
      (MukaiEvaluationMatrix.evaluation_basisSection k f (bundle k l)
        (fun i => sectionMap k f l (s i)) j).symm
  rw [hv]
  exact evaluation_wedge_coordinates _

/-- The original native H0 comparison retains restriction of the original ambient hyperplane. -/
theorem determinantValue_sections_eq_pullback
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k)) :
    (cohomologyOverFieldZeroLinearIso k f
      (Scheme.Modules.exteriorPower (bundle k l) 3)).hom (determinantValue k f l s) =
      (determinantIso k l).hom.app ⊤
        (pullbackGlobalSections l (LagrangianPluckerQuotient.determinantLine k)
          (LagrangianHyperplaneCoordinates.determinantSection k
            (PrimitiveDecomposableNonzero.coefficients k s))) := by
  rw [determinantValue_eq_restriction k f l hl,
    cohomologyIso_hom_eq_map]
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f (determinantIso k l).hom
    (LagrangianPrimitiveRestriction.primitiveRestriction k f l
      (PrimitiveDecomposableNonzero.coefficients k s))).trans
      (congrArg ((determinantIso k l).hom.app ⊤)
        (LagrangianPrimitiveRestriction.primitiveRestriction_sections_eq_pullback k f l hl _))

/-- Actual primitive hyperplane restriction has the literal determinant in every actual quotient frame. -/
theorem framed_hyperplane_coordinates
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (e : bundle k l ≅ freeOn X 3) (s : Fin 3 → (Fin 6 → k)) :
    freeDeterminantCoordinates X
      ((Scheme.Modules.exteriorPowerMap e.hom (3 : ℤ)).app ⊤
        ((determinantIso k l).hom.app ⊤
          (pullbackGlobalSections l (LagrangianPluckerQuotient.determinantLine k)
            (LagrangianHyperplaneCoordinates.determinantSection k
              (PrimitiveDecomposableNonzero.coefficients k s))))) =
      (Stacks.FreeSheafMatrix.toMatrix (evaluation k f l s ≫ e.hom)).det := by
  rw [← determinantValue_sections_eq_pullback k f l hl]
  exact framed_determinantValue_coordinates k f l e s

/-- The actual affine quotient frame induces an actual frame of the original determinant line. -/
def framedLineIso [IsAffine X] (e : bundle k l ≅ freeOn X 3) :
    LagrangianPrimitiveRestriction.restrictedLine k l ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  determinantIso k l ≪≫ (Scheme.Modules.exteriorPowerFunctor X (3 : ℤ)).mapIso e ≪≫
    LagrangianAffineDeterminant.affineDeterminantIso X

/-- In that derived genuine line frame, the actual original hyperplane is the literal triple determinant. -/
theorem framedLineIso_hyperplane [IsAffine X]
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (e : bundle k l ≅ freeOn X 3) (s : Fin 3 → (Fin 6 → k)) :
    (framedLineIso k l e).hom.app ⊤
      (pullbackGlobalSections l (LagrangianPluckerQuotient.determinantLine k)
        (LagrangianHyperplaneCoordinates.determinantSection k
          (PrimitiveDecomposableNonzero.coefficients k s))) =
      (Stacks.FreeSheafMatrix.toMatrix (evaluation k f l s ≫ e.hom)).det := by
  change (LagrangianAffineDeterminant.affineDeterminantIso X).hom.app ⊤
    ((Scheme.Modules.exteriorPowerMap e.hom (3 : ℤ)).app ⊤
      ((determinantIso k l).hom.app ⊤ _)) = _
  rw [LagrangianAffineDeterminant.affineDeterminantIso_coordinate]
  exact framed_hyperplane_coordinates k f l hl e s

end M9Native.LagrangianTripleDeterminantCoordinates
