module

public import M9StacksIntegration.LagrangianBigCellMatrixEntries
public import M9StacksIntegration.LagrangianActualGraphIsomorphism
public import M9StacksIntegration.LagrangianIsotropicRestriction
public import M9StacksIntegration.LagrangianCotangentSections

/-! The genuine intrinsic cotangent map of the original native big-cell quotient is invertible. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianBigCellIntrinsic

open LagrangianGrassmannian LagrangianMatrixChart LagrangianBigCellQuotient
open LagrangianPluckerQuotient LagrangianChartCotangent LagrangianIsotropicRestriction
open LagrangianIsotropicDual LagrangianCotangentMap LagrangianAffineGraphCotangent
open LagrangianNativeGraphCotangent LagrangianPolynomialDifferentials
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

/-- The original universal quotient pulled to the actual big cell and
expressed in its original native quotient frame. -/
def normalizedQuotient : freeOn (chart K) 6 ⟶ freeOn (chart K) 3 :=
  (pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫ (bigCellQuotientIso K).hom

/-- Its exterior-isotropy is derived from the actual universal LG
quotient and the actual pullback, not imposed on a graph model. -/
theorem normalizedQuotient_annihilates : AnnihilatesSigma (chart K) (normalizedQuotient K) :=
  annihilatesSigma_postcomp _ (bigCellQuotientIso K).hom
    (pulledQuotient_annihilates (bigCell K) (quotientOnLG K).map
      (LagrangianSymplecticAction.lagrangianUniversal_annihilates K))

theorem normalizedQuotient_first (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix (normalizedQuotient K) i (j.castAdd 3)=
      if i=j then 1 else 0 := bigCellQuotient_first K i j

/-- The matrix coefficients on actual sections retain the literal
native polynomial graph coordinates. -/
theorem sectionMatrix_entry (i j : Fin 3) :
    (sectionMatrix K).val i j=
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 6) K))).inv
        (MvPolynomial.X (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) := rfl

theorem normalizedQuotient_last (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix (normalizedQuotient K) i (Fin.natAdd 3 j)=
      (sectionMatrix K).val i j :=
  (bigCellQuotient_last K i j).trans (sectionMatrix_entry K i j).symm

/-- The actual intrinsic cotangent sheaf morphism for the original
normalized big-cell quotient is invertible, with all graph data proved. -/
instance normalizedCotangentMap_isIso :
    IsIso (cotangentMap (X := chart K) (S := Spec (.of K))
      (Q := freeOn (chart K) 3) (chartProjection K)
        (normalizedQuotient K) (normalizedQuotient_annihilates K)) :=
  LagrangianActualGraphIsomorphism.actualGraph_cotangentMap_isIso K
    (normalizedQuotient K) (normalizedQuotient_annihilates K)
      (normalizedQuotient_first K) (normalizedQuotient_last K)

end M9Native.LagrangianBigCellIntrinsic
