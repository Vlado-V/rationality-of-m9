module

public import M9StacksIntegration.PrimitiveRadicalOrbitParameterRecovery
public import M9StacksIntegration.PrimitiveRadicalOrbitKernelPoints
public import M9StacksIntegration.PrimitiveGaussFieldRatios
public import M9StacksIntegration.PrimitiveCoordinateRadical
public import M9StacksIntegration.QuotientRadicalFieldRatios
public import M9StacksIntegration.GrassmannianFieldChartCoordinates

/-! The actual source fraction field is algebraic over the literal coordinates of its
native Grassmannian image. Both the thirteen orbit parameters and the thirty-two graph
parameters are recovered; no expected fibre or transversality hypothesis is supplied. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory Matrix Module

namespace M9Native.PrimitiveRadicalOrbitFieldRecovery

open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitPoints
open PrimitiveRadicalOrbitParameterRecovery PrimitiveRadicalOrbitKernelPoints
open PrimitiveRhoFiberChart PrimitiveExtensionFieldBridge MatrixChartFieldRecovery
open PrimitiveGaussFieldRatios PrimitiveRadicalOrbitFieldGeneration

abbrev L := FractionRing coordinateRing

local instance extensionCharZero : CharZero L := charZero_extension L
local instance primitiveGroup : AddCommGroup (M9.ExteriorPrimitive.Primitive L) :=
  { (M9.ExteriorPrimitive.Primitive L).addCommGroup with
    toAddCommMonoid := (M9.ExteriorPrimitive.Primitive L).addCommMonoid }

theorem orbitAt_coordinates : orbitAt (leftPoint L genericPoint) =
    fieldCoordinates L (M9.PrimitiveStabilizer.primitiveLinear L
      (originalGroupAt L genericPoint) (M9.PrimitiveStabilizer.rho L)) := by
  have hm := primitiveAt_map L genericPoint
  have hρ : (leftPoint L genericPoint).toRingHom ∘
      (algebraMap ℂ gaussRing ∘ PrimitiveGaussOrbitVector.rhoCoordinates) =
        algebraMap ℂ L ∘ PrimitiveGaussOrbitVector.rhoCoordinates := by
    funext i
    exact (leftPoint L genericPoint).commutes _
  funext i
  change (leftPoint L genericPoint).toRingHom
    ((PrimitiveRingCoordinates.primitiveMatrix gaussRing (algebraMap ℂ gaussRing)
      (PrimitiveGaussFamily.family ℂ) *ᵥ
        (algebraMap ℂ gaussRing ∘ PrimitiveGaussOrbitVector.rhoCoordinates)) i) = _
  rw [RingHom.map_mulVec,hρ]
  change ((PrimitiveRingCoordinates.primitiveMatrix gaussRing (algebraMap ℂ gaussRing)
    (PrimitiveGaussFamily.family ℂ)).map (leftPoint L genericPoint).toRingHom *ᵥ
      (algebraMap ℂ L ∘ PrimitiveGaussOrbitVector.rhoCoordinates)) i = _
  rw [← hm]
  change (PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L)
    (gaussAt L genericPoint) *ᵥ
      (fun j => algebraMap ℂ L
        (M9.PrimitiveRadicalScheme.primitiveCoordinates (M9.PrimitiveStabilizer.rho ℂ) j))) i = _
  rw [← fieldCoordinates_rho L,primitiveMatrix_fieldCoordinates]
  rfl

variable (ι : Fin 5 ↪ Fin 14)
  (φ : GrassmannianFieldChartCoordinates.Polynomial (B := ℂ) 9 14 ι →ₐ[ℂ] L)

abbrev chartMatrix := GrassmannianFieldChartCoordinates.matrix 9 14 ι φ
abbrev chartField := IntermediateField.adjoin ℂ (Set.range fun a => φ (MvPolynomial.X a))

/-- Algebraic recovery from an actual chart presentation of the original generic family. -/
theorem source_isAlgebraic
    (hpoint : GrassmannianFieldChartCoordinates.point 9 14 ι φ = nativePoint L genericPoint) :
    Algebra.IsAlgebraic (chartField ι φ) L := by
  let F := chartField ι φ
  let N := chartMatrix ι φ
  have hNP : N.submatrix id ι = 1 := GrassmannianFieldChartCoordinates.matrix_pivots 9 14 ι φ
  have hNF : EntriesIn F.toSubfield N :=
    GrassmannianFieldChartCoordinates.matrix_entriesIn 9 14 ι F.toSubfield φ
      (fun a => IntermediateField.subset_adjoin ℂ _ ⟨a,rfl⟩)
  have hK : LinearMap.ker N.mulVecLin = LinearMap.ker (quotientAt L genericPoint).mulVecLin := by
    apply (GrassmannianFieldKernels.points_eq_iff_kernel_eq (k := 9) (n := 14) (K := L)
      (GrassmannianFieldChartCoordinates.point 9 14 ι φ) (nativePoint L genericPoint)
      N (quotientAt L genericPoint)
      (GrassmannianFieldChartCoordinates.matrix_surjective 9 14 ι φ)
      (quotientAt_surjective L genericPoint)
      (GrassmannianFieldChartCoordinates.point_class 9 14 ι φ)
      (nativePoint_class L genericPoint)
      (by rw [GrassmannianFieldChartCoordinates.point_projection,nativePoint_projection])).mp
    exact hpoint
  have hRad : M9.RadicalFiber.radical (PrimitiveCoordinateRadical.coordinateForm L)
      (LinearMap.ker N.mulVecLin) = Submodule.span L {orbitAt (leftPoint L genericPoint)} := by
    rw [orbitAt_coordinates]
    apply PrimitiveCoordinateRadical.coordinate_radical_span L N
    rw [hK]
    exact kernelAt_radical L genericPoint
  let J := pairingMatrix.map (algebraMap ℂ L)
  have hJ : IsUnit J.det := by
    have h := (isUnit_iff_ne_zero.mpr pairingMatrix_det_ne_zero).map (algebraMap ℂ L)
    simpa only [RingHom.map_det,RingHom.mapMatrix_apply] using h
  have hJF : EntriesIn F.toSubfield J := fun i j => F.algebraMap_mem _
  have hNS : N * (MatrixKernelChartNormalization.pivotSection (K := L) ι :
      Matrix (Fin 14) (Fin 5) L) = 1 := by
    rw [MatrixKernelChartNormalization.mul_section,hNP]
  have hRatio : ∀ j : Fin 13, leftPoint L genericPoint
      (PrimitiveGaussCoordinates.sourceCoordinate ℂ j) ∈ F := by
    have hr := QuotientRadicalFieldRatios.radical_ratios_mem F.toSubfield J hJ
      (PrimitiveCoordinateRadical.coordinateForm_isAlt L) N
      (MatrixKernelChartNormalization.pivotSection (K := L) ι) hNS hJF hNF
      (orbitAt (leftPoint L genericPoint)) (inverseCoordinates (R := L) 0)
      (fun j => inverseCoordinates (R := L) j.succ) hRad
      (fun i => F.algebraMap_mem _) (fun j i => F.algebraMap_mem _)
      (normalAt_zero_ne_zero (leftPoint L genericPoint))
    intro j
    have h := hr j
    change normalAt (leftPoint L genericPoint) j.succ /
      normalAt (leftPoint L genericPoint) 0 ∈ F at h
    rwa [normalAt_ratio] at h
  have hσ : ∀ j, parameterFieldEmbedding (PrimitiveGaussCoordinates.coordinate ℂ j) ∈ F := by
    intro j
    have h := parameterFieldEmbedding_toRational (PrimitiveGaussCoordinates.sourceCoordinate ℂ j)
    rw [PrimitiveGaussCoordinates.toRational_sourceCoordinate] at h
    rw [h]
    exact hRatio j
  let E := algebraicClosure F L
  have hFE (x : L) (hx : x ∈ F) : x ∈ E := E.algebraMap_mem (⟨x,hx⟩ : F)
  have hCE (c : ℂ) : algebraMap ℂ L c ∈ E := hFE _ (F.algebraMap_mem c)
  have hGauss : ∀ r : gaussRing, leftPoint L genericPoint r ∈ E := by
    intro r
    change coordinateFractionMap (gaussInclusion r) ∈ E
    rw [← parameterFieldEmbedding_toRational]
    exact mem_algebraicClosure_iff.mpr
      (PrimitiveGaussFieldExtension.mapped_parameter_isAlgebraic parameterFieldEmbedding F hσ _)
  have hNE : EntriesIn E.toSubfield N := fun i j => hFE _ (hNF i j)
  have hME : EntriesIn E.toSubfield (primitiveAt L genericPoint) :=
    primitiveAt_entriesIn L E.toSubfield genericPoint hGauss
  have hSE : EntriesIn E.toSubfield (quotientSection L) := by
    rw [← quotientSection_map (IsScalarTower.toAlgHom ℂ ℂ L)]
    exact fun i j => hCE _
  obtain ⟨hP,hN⟩ := MatrixKernelChartNormalization.normalize_of_same_kernel
    (quotientAt L genericPoint) N (sectionAt L genericPoint) (quotientAt_sectionAt L genericPoint)
    ι hNP (fun v hv => hK.le hv)
  have hNM : N * primitiveAt L genericPoint =
      ((quotientAt L genericPoint).submatrix id ι)⁻¹ * quotientMatrix L (graphAt L genericPoint) := by
    rw [hN,quotientAt,Matrix.mul_assoc,Matrix.mul_assoc,
      primitiveAt_inverse,Matrix.mul_one]
  have hNMS : N * primitiveAt L genericPoint * quotientSection L =
      ((quotientAt L genericPoint).submatrix id ι)⁻¹ := by
    rw [hNM,Matrix.mul_assoc,quotientMatrix_section L _ (graphAt_head L genericPoint),Matrix.mul_one]
  have hRec : (N * primitiveAt L genericPoint * quotientSection L)⁻¹ *
      (N * primitiveAt L genericPoint) = quotientMatrix L (graphAt L genericPoint) := by
    cases ((Matrix.isUnit_iff_isUnit_det _).mpr hP).nonempty_invertible
    rw [hNMS,hNM,Matrix.inv_inv_of_invertible,← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hP,Matrix.one_mul]
  have hQ : EntriesIn E.toSubfield (quotientMatrix L (graphAt L genericPoint)) := by
    rw [← hRec]
    exact (((hNE.mul E.toSubfield hME).mul E.toSubfield hSE).inv E.toSubfield).mul
      E.toSubfield (hNE.mul E.toSubfield hME)
  have hGraph : EntriesIn E.toSubfield (graphAt L genericPoint) :=
    PrimitiveRhoGraphRecovery.entriesIn_graph L E.toSubfield hCE _ hQ
  have hall := all_mem_of_gauss_graph E.toSubfield hCE hGauss hGraph
  exact ⟨fun x => mem_algebraicClosure_iff.mp (hall x)⟩

end M9Native.PrimitiveRadicalOrbitFieldRecovery
