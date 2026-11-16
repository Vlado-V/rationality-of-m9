module

public import M9StacksIntegration.LagrangianPluckerTrivialization

/-! The actual quotient frame on the original native LG big cell. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace M9Native.LagrangianBigCellQuotient

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerTrivialization AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

/-- The original big cell's actual map to the original nine-entry matrix chart. -/
def bigCellMatrixMap : Spec (.of (MvPolynomial (Fin 6) K)) ⟶ Spec (.of (MatrixRing K)) :=
  (lagrangianChartIsoPolynomialSix K).inv ≫ pullback.fst (matrixChart K) (inclusion K)

@[reassoc] theorem bigCellMatrixMap_fac :
    bigCellMatrixMap K ≫ matrixChart K=bigCell K ≫ inclusion K := by
  change ((lagrangianChartIsoPolynomialSix K).inv ≫ pullback.fst _ _) ≫ matrixChart K=
    ((lagrangianChartIsoPolynomialSix K).inv ≫ pullback.snd _ _) ≫ inclusion K
  rw [Category.assoc,Category.assoc,pullback.condition]

/-- The corresponding original integral Grassmannian chart point. -/
def bigCellIntegralPoint : Spec (.of (MvPolynomial (Fin 6) K)) ⟶
    Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) firstPivot) (ULift.{u} ℤ))) :=
  bigCellMatrixMap K ≫ integralChartPoint K

theorem bigCellIntegralPoint_fac :
    (bigCell K ≫ inclusion K) ≫ pullback.snd _ _=
      bigCellIntegralPoint K ≫ chart 3 6 firstPivot := by
  rw [← bigCellMatrixMap_fac,Category.assoc,matrixChart_toIntegral,← Category.assoc]
  rfl

/-- A genuine quotient frame of the actual pulled-back universal bundle,
with its original quotient map retained. -/
def bigCellQuotientIso :
    (pullbackPresentation (bigCell K) (quotientOnLG K)).target ≅
      freeOn (Spec (.of (MvPolynomial (Fin 6) K))) 3 :=
  chartQuotientIso K (bigCell K) firstPivot (bigCellIntegralPoint K) (bigCellIntegralPoint_fac K)

theorem bigCellQuotientIso_triangle :
    (pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫ (bigCellQuotientIso K).hom=
      chartQuotientMap 3 6 firstPivot (bigCellIntegralPoint K) :=
  chartQuotientIso_triangle K (bigCell K) firstPivot (bigCellIntegralPoint K)
    (bigCellIntegralPoint_fac K)

/-- The chosen native six-coordinate isomorphism retains the original
closed matrix-chart inclusion. -/
@[reassoc] theorem matrixZeroSchemeIsoPolynomialSix_inclusion :
    (matrixZeroSchemeIsoPolynomialSix K).hom ≫ (symmetrySchemeIsoPolynomialSix K).inv ≫
      symmetryInclusion K=(matrixZeroIdeal K).subschemeι := by
  simp only [matrixZeroSchemeIsoPolynomialSix,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [Iso.hom_inv_id_assoc,asIso_toImage_inv_imageι,
    eqToIso_subscheme_ι (matrixZeroIdeal K) ((symmetryInclusion K).ker)
      (matrixZeroIdeal_eq_symmetryKer K)]

@[reassoc] theorem lagrangianChartIsoPolynomialSix_inclusion :
    (lagrangianChartIsoPolynomialSix K).hom ≫ (symmetrySchemeIsoPolynomialSix K).inv ≫
      symmetryInclusion K=pullback.fst (matrixChart K) (inclusion K) := by
  simp only [lagrangianChartIsoPolynomialSix,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    matrixZeroSchemeIsoPolynomialSix_inclusion]
  rw [eqToIso_subscheme_ι
      ((LagrangianGrassmannian.ideal K).comap (matrixChart K)) (matrixZeroIdeal K)
      (lagrangianIdeal_comap_matrixChart K),Scheme.IdealSheafData.comapIso_inv_subschemeι]

theorem bigCellMatrixMap_eq : bigCellMatrixMap K=
    (symmetrySchemeIsoPolynomialSix K).inv ≫ symmetryInclusion K := by
  rw [bigCellMatrixMap,← lagrangianChartIsoPolynomialSix_inclusion]
  exact Iso.inv_hom_id_assoc _ _

/-- The literal polynomial map from the nine matrix entries to the
original chosen six native variables. -/
def matrixToSix : MatrixRing K →+* MvPolynomial (Fin 6) K :=
  (quotientPolynomialSixEquiv K).toRingHom.comp (Ideal.Quotient.mk (symmetryIdeal K))

theorem bigCellMatrixMap_eq_spec :
    bigCellMatrixMap K=Spec.map (CommRingCat.ofHom (matrixToSix K)) := by
  rw [bigCellMatrixMap_eq]
  change Spec.map (CommRingCat.ofHom (quotientPolynomialSixEquiv K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (symmetryIdeal K)))=_
  rw [← Spec.map_comp]
  rfl

@[simp] theorem matrixToSix_X (i j : Fin 3) :
    matrixToSix K (MvPolynomial.X (ULift.up.{u} (i,j)))=
      MvPolynomial.X (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j)))) := by
  change MvPolynomial.rename symmetricEntryEquivFinSix
    (quotientToSymmetric K (Ideal.Quotient.mk (symmetryIdeal K)
      (MvPolynomial.X (ULift.up.{u} (i,j)))))=_
  rw [quotientToSymmetric_mk,symmetrize_X,MvPolynomial.rename_X]

/-- The actual original matrix entries on the actual big cell are the
actual native polynomial coordinates, with the frozen variable numbering. -/
theorem bigCellMatrixMap_matrixEntry (i j : Fin 3) :
    (bigCellMatrixMap K).appTop (matrixEntry K (i,j))=
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 6) K))).inv
        (MvPolynomial.X (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) := by
  rw [bigCellMatrixMap_eq_spec]
  change (Spec.map (CommRingCat.ofHom (matrixToSix K))).appTop
    ((Scheme.ΓSpecIso (.of (MatrixRing K))).inv (MvPolynomial.X (ULift.up.{u} (i,j))))=_
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
  change (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 6) K))).inv
    (matrixToSix K (MvPolynomial.X (ULift.up.{u} (i,j))))=_
  rw [matrixToSix_X]

/-- The original big-cell quotient matrix, rather than an abstract
rank-three frame: its first three columns are literally the identity. -/
theorem bigCellQuotient_first (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix
      ((pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫
        (bigCellQuotientIso K).hom) i (j.castAdd 3)=if i=j then 1 else 0 := by
  rw [bigCellQuotientIso_triangle,toMatrix_chartQuotientMap]
  exact chartMatrix_apply_self firstPivot _ i j

end M9Native.LagrangianBigCellQuotient
