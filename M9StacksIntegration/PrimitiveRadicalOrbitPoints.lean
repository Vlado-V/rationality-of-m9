module

public import M9StacksIntegration.PrimitiveRadicalOrbitFamily
public import M9StacksIntegration.PrimitiveRadicalKernelPair
public import M9StacksIntegration.GrassmannianFieldKernels
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality

/-! Literal field-point matrices of the genuine native radical orbit family. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Module
open scoped Classical TensorProduct Matrix

namespace M9Native.PrimitiveRadicalOrbitPoints
open PrimitiveRadicalOrbitFamily PrimitiveRhoFiberChart PrimitiveRhoFiberNondegenerate
open PrimitiveExtensionFieldBridge

variable (K : Type) [CommRing K] [Algebra ℂ K]

abbrev Point := coordinateRing →ₐ[ℂ] K

def leftPoint (y : Point K) : gaussRing →ₐ[ℂ] K :=
  y.comp Algebra.TensorProduct.includeLeft

def rightPoint (y : Point K) : nondegenerateRing →ₐ[ℂ] K :=
  y.comp Algebra.TensorProduct.includeRight

def gaussAt (y : Point K) : Matrix.symplecticGroup (Fin 3) K :=
  LagrangianTransitivity.mapSymplectic gaussRing (leftPoint K y).toRingHom (PrimitiveGaussFamily.family ℂ)

def graphAt (y : Point K) : Matrix (Fin 12) (Fin 4) K := localizedGraph.map (rightPoint K y)

omit [Algebra ℂ K] in
theorem headMatrix_natural {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (headMatrix R).map f = headMatrix S := by
  ext i j
  simp only [headMatrix,LinearMap.toMatrix'_apply,LinearMap.funLeft_apply,Pi.single_apply,Matrix.map_apply]
  split_ifs <;> simp

theorem localizedGraph_head : headMatrix nondegenerateRing * localizedGraph = 1 := by
  have hP : headMatrix parameterRing * parameterGraph = 1 := graphMatrix_head _ _ _ _
  have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) parameterRing => M.map localizationMap.toRingHom) hP
  simp only [Matrix.map_mul,headMatrix_natural,Matrix.map_one _ (map_zero _) (map_one _)] at hm
  exact hm

theorem graphAt_head (y : Point K) : headMatrix K * graphAt K y = 1 := by
  have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) nondegenerateRing => M.map (rightPoint K y).toRingHom)
    localizedGraph_head
  simp only [Matrix.map_mul,headMatrix_natural,Matrix.map_one _ (map_zero _) (map_one _)] at hm
  exact hm

def primitiveAt (y : Point K) : Matrix (Fin 14) (Fin 14) K :=
  PrimitiveRingCoordinates.primitiveMatrix K (algebraMap ℂ K) (gaussAt K y)

def primitiveInverseAt (y : Point K) : Matrix (Fin 14) (Fin 14) K :=
  PrimitiveRingCoordinates.primitiveMatrix K (algebraMap ℂ K) ((gaussAt K y)⁻¹)

theorem primitiveAt_inverse (y : Point K) : primitiveInverseAt K y * primitiveAt K y = 1 := by
  rw [primitiveAt,primitiveInverseAt,← PrimitiveRingCoordinates.primitiveMatrix_mul,
    inv_mul_cancel,PrimitiveRingCoordinates.primitiveMatrix_one]

def quotientAt (y : Point K) : Matrix (Fin 5) (Fin 14) K :=
  quotientMatrix K (graphAt K y) * primitiveInverseAt K y

def sectionAt (y : Point K) : Matrix (Fin 14) (Fin 5) K :=
  primitiveAt K y * quotientSection K

theorem quotientAt_sectionAt (y : Point K) : quotientAt K y * sectionAt K y = 1 := by
  rw [quotientAt,sectionAt,Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (quotientSection K),primitiveAt_inverse,Matrix.one_mul,
    quotientMatrix_section K _ (graphAt_head K y)]

theorem quotientAt_surjective (y : Point K) : Function.Surjective (Matrix.mulVec (quotientAt K y)) :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨sectionAt K y,quotientAt_sectionAt K y⟩

/-- The actual Spec K-valued point of the frozen native family. -/
def nativePoint (y : Point K) : Spec (.of K) ⟶ GrassmannianCharts.space ℂ 9 14 :=
  Spec.map (CommRingCat.ofHom y.toRingHom) ≫ PrimitiveRadicalOrbitFamily.map

@[reassoc] theorem nativePoint_projection (y : Point K) :
    nativePoint K y ≫ GrassmannianCharts.projection ℂ 9 14 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) := by
  rw [nativePoint,Category.assoc,PrimitiveRadicalOrbitFamily.map_projection,projection,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact y.comp_algebraMap

section MatrixNaturality
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

theorem sumFrame_map (f : R →ₐ[ℂ] S) (P : Matrix (Fin 12) (Fin 4) R) :
    (sumFrame R P).map f = sumFrame S (P.map f) := by
  have hρ : (rhoColumn.map (algebraMap ℂ R)).map f = rhoColumn.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes (rhoColumn i j)
  have hL : (liftMatrix.map (algebraMap ℂ R)).map f = liftMatrix.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes (liftMatrix i j)
  simp only [sumFrame,Matrix.fromCols_map,Matrix.map_mul,hρ,hL]

theorem frame_map (f : R →ₐ[ℂ] S) (P : Matrix (Fin 12) (Fin 4) R) :
    (frame R P).map f = frame S (P.map f) := by
  ext i j
  exact congrFun (congrFun (sumFrame_map f P) i) ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm j)

theorem quotientMatrix_map (f : R →ₐ[ℂ] S) (P : Matrix (Fin 12) (Fin 4) R) :
    (quotientMatrix R P).map f = quotientMatrix S (P.map f) := by
  have hJ : (pairingMatrix.map (algebraMap ℂ R)).map f = pairingMatrix.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes (pairingMatrix i j)
  have hT (M : Matrix (Fin 14) (Fin 5) R) : M.transpose.map f = (M.map f).transpose := rfl
  simp only [quotientMatrix,Matrix.map_mul,hT,frame_map,hJ]

theorem sumRetraction_map (f : R →ₐ[ℂ] S) : (sumRetraction R).map f = sumRetraction S := by
  ext i j
  exact f.commutes ((Matrix.fromRows rhoRow (headMatrix ℂ * retractionMatrix)) i j)

theorem frameRetraction_map (f : R →ₐ[ℂ] S) :
    (frameRetraction R).map f = frameRetraction S := by
  ext i j
  exact congrFun (congrFun (sumRetraction_map f) ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm i)) j

theorem quotientSection_map (f : R →ₐ[ℂ] S) :
    (quotientSection R).map f = quotientSection S := by
  have hJ : ((pairingIsomorphism⁻¹).val.map (algebraMap ℂ R)).map f =
      (pairingIsomorphism⁻¹).val.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes ((pairingIsomorphism⁻¹).val i j)
  have hT (M : Matrix (Fin 5) (Fin 14) R) : M.transpose.map f = (M.map f).transpose := rfl
  simp only [quotientSection,Matrix.map_mul,hT,frameRetraction_map,hJ]

end MatrixNaturality

abbrev graphRing := PrimitiveRhoFiberNondegenerate.parameterRing

def graphQuotientRaw : Matrix (Fin 5) (Fin 14) graphRing := quotientMatrix graphRing parameterGraph
def graphSectionRaw : Matrix (Fin 14) (Fin 5) graphRing := quotientSection graphRing

theorem graphRawSplit : graphQuotientRaw * graphSectionRaw = 1 :=
  quotientMatrix_section _ _ (graphMatrix_head _ _ _ _)

def graphGlobalMap : graphRing →ₐ[ℂ] Γ(PrimitiveRhoFiberChart.domain,⊤) where
  __ := (Scheme.ΓSpecIso (.of graphRing)).inv.hom
  commutes' _ := rfl

theorem graphGlobalGraph : parameterGraph.map graphGlobalMap = PrimitiveRhoFiberChart.universalGraph := by
  change parameterGraph.map graphGlobalMap.toRingHom = _
  rw [parameterGraph,graphMatrix_map]
  rfl

theorem graphGlobalQuotient : graphQuotientRaw.map graphGlobalMap =
    quotientMatrix Γ(PrimitiveRhoFiberChart.domain,⊤) PrimitiveRhoFiberChart.universalGraph := by
  rw [graphQuotientRaw,quotientMatrix_map,graphGlobalGraph]

/-- The frozen original rho-family classifier is the genuine split ring-matrix classifier. -/
theorem graphMap_matrix_class : SplitMatrixGrassmannianNaturality.pointClass 9 14 ℂ
    PrimitiveRhoFiberChart.map =
      ⟦SplitMatrixGrassmannianNaturality.ringPresentation 9 14 graphQuotientRaw graphSectionRaw graphRawSplit⟧ := by
  change (AlgebraicGeometry.Grassmannian.functorData 9 14).objEquiv PrimitiveRhoFiberChart.domain
    ((AlgebraicGeometry.Grassmannian.schemeRepresentableBy 9 14).homEquiv
      (PrimitiveRhoFiberChart.map ≫ GrassmannianCharts.toIntegral ℂ 9 14)) = _
  rw [PrimitiveRhoFiberChart.map_class]
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _,?_⟩
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [SplitMatrixGrassmannianNaturality.ringPresentation_matrix]
  change Stacks.FreeSheafMatrix.toMatrix PrimitiveRhoFiberChart.sheafQuotient =
    graphQuotientRaw.map (Scheme.ΓSpecIso (.of graphRing)).inv.hom
  rw [PrimitiveRhoFiberChart.sheafQuotient,Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
  exact graphGlobalQuotient.symm

def universalPoint : Point coordinateRing := AlgHom.id ℂ coordinateRing

def fiberQuotientRaw : Matrix (Fin 5) (Fin 14) coordinateRing :=
  quotientMatrix coordinateRing (graphAt coordinateRing universalPoint)

def fiberSectionRaw : Matrix (Fin 14) (Fin 5) coordinateRing := quotientSection coordinateRing

theorem fiberRawSplit : fiberQuotientRaw * fiberSectionRaw = 1 :=
  quotientMatrix_section _ _ (graphAt_head _ _)

def graphRingPoint : graphRing →ₐ[ℂ] coordinateRing :=
  Algebra.TensorProduct.includeRight.comp localizationMap

theorem graphRingPoint_graph : parameterGraph.map graphRingPoint = graphAt coordinateRing universalPoint := by
  ext i j
  rfl

theorem fiberParameter_eq : PrimitiveRadicalOrbitFamily.fiberParameter.left =
    Spec.map (CommRingCat.ofHom graphRingPoint.toRingHom) ≫ PrimitiveRhoFiberChart.map := by
  change (PrimitiveRadicalOrbitFamily.fiberProjection ≫ PrimitiveRhoFiberNondegenerate.map) = _
  rw [PrimitiveRhoFiberNondegenerate.map,PrimitiveRadicalOrbitFamily.fiberProjection,
    PrimitiveRhoFiberNondegenerate.inclusion,← Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp]
  rfl

theorem fiberParameter_matrix_class : PrimitiveGrassmannianAction.pointClass
    PrimitiveRadicalOrbitFamily.fiberParameter.left =
      ⟦SplitMatrixGrassmannianNaturality.ringPresentation 9 14 fiberQuotientRaw fiberSectionRaw fiberRawSplit⟧ := by
  rw [fiberParameter_eq]
  have h := SplitMatrixGrassmannianNaturality.spec_class_comp_of_matrix_class
    (R := graphRing) (S := coordinateRing) 9 14 ℂ graphRingPoint.toRingHom PrimitiveRhoFiberChart.map
    graphQuotientRaw graphSectionRaw graphRawSplit graphMap_matrix_class
  have hQ : graphQuotientRaw.map graphRingPoint.toRingHom = fiberQuotientRaw := by
    change (quotientMatrix graphRing parameterGraph).map graphRingPoint = _
    rw [quotientMatrix_map (R := graphRing) (S := coordinateRing) graphRingPoint parameterGraph,
      graphRingPoint_graph]
    rfl
  refine h.trans (Quotient.sound (.rel _ _ ⟨Iso.refl _,?_⟩))
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [SplitMatrixGrassmannianNaturality.ringPresentation_matrix,
    SplitMatrixGrassmannianNaturality.ringPresentation_matrix,hQ]

/-- The actual universal symplectic point is the coefficient-mapped original Gauss matrix. -/
theorem groupParameter_matrix :
    Sp6GroupScheme.pointsMulEquiv PrimitiveRadicalOrbitFamily.base sourceOver groupParameter =
      Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom
        (gaussAt coordinateRing universalPoint) := by
  rw [groupParameter,Sp6GroupScheme.pointsMulEquiv_natural,
    PrimitiveGaussGroupScheme.pointsMulEquiv_gaussFamily]
  apply Subtype.ext
  ext i j
  change (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : gaussRing →ₐ[ℂ] coordinateRing).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of gaussRing)).inv ((PrimitiveGaussFamily.family ℂ).val i j)) =
    (Scheme.ΓSpecIso (.of coordinateRing)).inv
      ((Algebra.TensorProduct.includeLeft : gaussRing →ₐ[ℂ] coordinateRing)
        ((PrimitiveGaussFamily.family ℂ).val i j))
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
  rfl

theorem sourceScalarMap : PrimitiveFamilyFreeAction.scalarMap sourceOver =
    (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom.comp (algebraMap ℂ coordinateRing) := by
  ext c
  change (Spec.map (CommRingCat.ofHom (algebraMap ℂ coordinateRing))).appTop
      ((Scheme.ΓSpecIso (.of ℂ)).inv c) =
    (Scheme.ΓSpecIso (.of coordinateRing)).inv (algebraMap ℂ coordinateRing c)
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
  rfl

theorem sourcePrimitive_global (g : Matrix.symplecticGroup (Fin 3) coordinateRing) :
    PrimitiveFamilyFreeAction.familyMatrix sourceOver
      (Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom g) =
      (PrimitiveRingCoordinates.primitiveMatrix coordinateRing (algebraMap ℂ coordinateRing) g).map
        (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom := by
  have hg : Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom g =
      LagrangianTransitivity.mapSymplectic coordinateRing
        (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom g := by apply Subtype.ext; rfl
  rw [PrimitiveFamilyFreeAction.familyMatrix,sourceScalarMap,hg]
  exact PrimitiveRingCoordinates.primitiveMatrix_map _ _ _ g

def universalQuotientRaw : Matrix (Fin 5) (Fin 14) coordinateRing := quotientAt coordinateRing universalPoint
def universalSectionRaw : Matrix (Fin 14) (Fin 5) coordinateRing := sectionAt coordinateRing universalPoint

theorem universalRawSplit : universalQuotientRaw * universalSectionRaw = 1 :=
  quotientAt_sectionAt _ _

/-- The genuine native orbit-family class has the literal acted universal quotient matrix. -/
theorem family_matrix_class : PrimitiveGrassmannianAction.pointClass PrimitiveRadicalOrbitFamily.map =
    ⟦SplitMatrixGrassmannianNaturality.ringPresentation 9 14
      universalQuotientRaw universalSectionRaw universalRawSplit⟧ := by
  rw [PrimitiveRadicalOrbitFamily.map_pointClass,fiberParameter_matrix_class,groupParameter_matrix]
  change (⟦PrimitiveFamilyFreeAction.transform sourceOver
    (Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom
      (gaussAt coordinateRing universalPoint))
    (SplitMatrixGrassmannianNaturality.ringPresentation 9 14
      fiberQuotientRaw fiberSectionRaw fiberRawSplit)⟧ : AlgebraicGeometry.Grassmannian.Points source 9 14) = _
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _,?_⟩
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  dsimp only [PrimitiveFamilyFreeAction.transform,SplitMatrixGrassmannianNaturality.ringPresentation,
    SplitMatrixGrassmannian.presentation,SplitMatrixGrassmannian.quotientMap]
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    PrimitiveFamilyFreeAction.freeIso_matrix,Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
  have hg : (Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom
        (gaussAt coordinateRing universalPoint))⁻¹ =
      Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom
        ((gaussAt coordinateRing universalPoint)⁻¹) := (map_inv _ _).symm
  rw [hg,sourcePrimitive_global]
  change fiberQuotientRaw.map (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom *
      (primitiveInverseAt coordinateRing universalPoint).map (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom =
    (fiberQuotientRaw * primitiveInverseAt coordinateRing universalPoint).map
      (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom
  exact (Matrix.map_mul (L := fiberQuotientRaw)
    (M := primitiveInverseAt coordinateRing universalPoint)
    (f := (Scheme.ΓSpecIso (.of coordinateRing)).inv.hom)).symm

theorem universalGauss_map (y : Point K) :
    Sp6GroupScheme.mapMatrix y.toRingHom (gaussAt coordinateRing universalPoint) = gaussAt K y := by
  apply Subtype.ext
  ext i j
  rfl

theorem universalGraph_map (y : Point K) :
    (graphAt coordinateRing universalPoint).map y = graphAt K y := by
  ext i j
  rfl

theorem universalPrimitiveInverse_map (y : Point K) :
    (primitiveInverseAt coordinateRing universalPoint).map y = primitiveInverseAt K y := by
  have hg : LagrangianTransitivity.mapSymplectic coordinateRing y.toRingHom
      ((gaussAt coordinateRing universalPoint)⁻¹) = (gaussAt K y)⁻¹ := by
    change Sp6GroupScheme.mapMatrix y.toRingHom ((gaussAt coordinateRing universalPoint)⁻¹) = _
    rw [map_inv,universalGauss_map]
  have h := PrimitiveRingCoordinates.primitiveMatrix_map coordinateRing (algebraMap ℂ coordinateRing)
    y.toRingHom ((gaussAt coordinateRing universalPoint)⁻¹)
  have hc : y.toRingHom.comp (algebraMap ℂ coordinateRing) = algebraMap ℂ K := by
    ext c
    exact y.commutes c
  change PrimitiveRingCoordinates.primitiveMatrix K (y.toRingHom.comp (algebraMap ℂ coordinateRing))
      (LagrangianTransitivity.mapSymplectic coordinateRing y.toRingHom
        ((gaussAt coordinateRing universalPoint)⁻¹)) =
    (PrimitiveRingCoordinates.primitiveMatrix coordinateRing (algebraMap ℂ coordinateRing)
      ((gaussAt coordinateRing universalPoint)⁻¹)).map y.toRingHom at h
  rw [hc,hg] at h
  exact h.symm

theorem universalQuotient_map (y : Point K) :
    universalQuotientRaw.map y = quotientAt K y := by
  have hQ := quotientMatrix_map (R := coordinateRing) (S := K) y
    (graphAt coordinateRing universalPoint)
  rw [universalGraph_map] at hQ
  change (fiberQuotientRaw * primitiveInverseAt coordinateRing universalPoint).map y =
    quotientMatrix K (graphAt K y) * primitiveInverseAt K y
  exact Matrix.map_mul.trans (congrArg₂ (fun A B => A * B) hQ (universalPrimitiveInverse_map K y))

section FieldPresentation
variable (L : Type) [Field L] [Algebra ℂ L]

/-- The actual native family at every field point has the literal acted field-matrix quotient. -/
theorem nativePoint_class (y : Point L) :
    SplitMatrixGrassmannianNaturality.pointClass 9 14 ℂ (nativePoint L y) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 L (quotientAt L y) (quotientAt_surjective L y)⟧ := by
  have h := SplitMatrixGrassmannianNaturality.spec_class_comp_fieldPresentation
    (R := coordinateRing) (L := L) 9 14 ℂ y.toRingHom PrimitiveRadicalOrbitFamily.map
    universalQuotientRaw universalSectionRaw universalRawSplit family_matrix_class
  have hQ : universalQuotientRaw.map y.toRingHom = quotientAt L y := universalQuotient_map L y
  refine h.trans (Quotient.sound (.rel _ _ ⟨Iso.refl _,?_⟩))
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [SplitMatrixGrassmannian.fieldPresentation_matrix,SplitMatrixGrassmannian.fieldPresentation_matrix,hQ]

end FieldPresentation

end M9Native.PrimitiveRadicalOrbitPoints
