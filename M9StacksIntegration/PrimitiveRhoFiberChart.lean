module

public import M9StacksIntegration.PrimitiveRadicalNativeScheme
public import M9StacksIntegration.GraphGrassmannianChart
public import M9.PrimitiveRadicalReducedAction
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# The actual rho-fiber as a native algebraic family

The constants in the family come from the actual primitive wedge pairing,
rho, the original mixed-section splitting, and the fixed Q-plus-Q-dual
coordinates. No rational homogeneous-space section is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct Matrix

namespace M9Native.PrimitiveRhoFiberChart
open Module M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveBlockCoordinates
open M9.PrimitiveRadicalScheme M9.GraphBundleDescent

local instance primitiveGroup : AddCommGroup (Primitive ℂ) :=
  { (Primitive ℂ).addCommGroup with toAddCommMonoid := (Primitive ℂ).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp ℂ) :=
  { (Perp ℂ).addCommGroup with toAddCommMonoid := (Perp ℂ).addCommMonoid }

/-- The original reduced mixed coordinates in the same twelve-coordinate
order used by the checked actual graph chart. -/
def mixedCoordinates : Mixed ℂ ≃ₗ[ℂ] (Fin 12 → ℂ) :=
  ((M9.PrimitiveTwistedReduced.mixedDualEquiv ℂ).trans
    ((symmetricSplit ℂ).prodCongr (dualSymmetricSplit ℂ))).trans
      M9Native.GraphGrassmannianChart.ambientCoordinates

def mixedCoordinateProjection : Primitive ℂ →ₗ[ℂ] (Fin 12 → ℂ) :=
  mixedCoordinates.toLinearMap.comp (mixedProjection ℂ)

/-- The actual mixed-section lift into the original primitive exterior kernel. -/
def mixedCoordinateLift : (Fin 12 → ℂ) →ₗ[ℂ] Primitive ℂ :=
  (Perp ℂ).subtype.comp ((mixedSection ℂ).comp mixedCoordinates.symm.toLinearMap)

theorem mixedProjection_lift (z : Fin 12 → ℂ) :
    mixedCoordinateProjection (mixedCoordinateLift z) = z := by
  change mixedCoordinates (perpProjection ℂ (mixedSection ℂ (mixedCoordinates.symm z))) = z
  rw [perpProjection_mixedSection,LinearEquiv.apply_symm_apply]

theorem mixedProjection_lift_comp : mixedCoordinateProjection.comp mixedCoordinateLift = LinearMap.id := by
  apply LinearMap.ext
  exact mixedProjection_lift

def rhoCoefficient : Primitive ℂ →ₗ[ℂ] ℂ :=
  (aCoordinate ℂ).comp (Primitive ℂ).subtype

theorem rhoCoefficient_lift (z : Fin 12 → ℂ) : rhoCoefficient (mixedCoordinateLift z) = 0 := by
  change aCoordinate ℂ (primitiveEquiv ℂ
    (0,(mixedCoordinates.symm z).1,(mixedCoordinates.symm z).2,0)).val = 0
  rw [primitiveEquiv_val,aCoordinate_embedding]

theorem rhoCoefficient_rho : rhoCoefficient (rho ℂ) = 1 := by
  simp [rhoCoefficient,rho]

theorem mixedProjection_rho : mixedCoordinateProjection (rho ℂ) = 0 := by
  change mixedCoordinates (mixedProjection ℂ (rho ℂ)) = 0
  rw [← primitiveEquiv_rhoCoordinates,mixedProjection_primitiveEquiv]
  change mixedCoordinates 0 = 0
  exact map_zero mixedCoordinates

theorem mixedLift_mem_perp (z : Fin 12 → ℂ) : mixedCoordinateLift z ∈ Perp ℂ :=
  (mixedSection ℂ (mixedCoordinates.symm z)).property

def coordinateLift : (Fin 12 → ℂ) →ₗ[ℂ] (Fin 14 → ℂ) :=
  primitiveCoordinates.toLinearMap.comp mixedCoordinateLift

def coordinateRetraction : (Fin 14 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ) :=
  mixedCoordinateProjection.comp primitiveCoordinates.symm.toLinearMap

def coordinateRhoCoefficient : (Fin 14 → ℂ) →ₗ[ℂ] ℂ :=
  rhoCoefficient.comp primitiveCoordinates.symm.toLinearMap

def coordinateRho : Fin 14 → ℂ := primitiveCoordinates (rho ℂ)

theorem coordinateRetraction_lift : coordinateRetraction.comp coordinateLift = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change mixedCoordinateProjection (primitiveCoordinates.symm (primitiveCoordinates (mixedCoordinateLift z))) = z
  rw [LinearEquiv.symm_apply_apply,mixedProjection_lift]

theorem coordinateCoefficient_lift : coordinateRhoCoefficient.comp coordinateLift = 0 := by
  apply LinearMap.ext
  intro z
  change rhoCoefficient (primitiveCoordinates.symm (primitiveCoordinates (mixedCoordinateLift z))) = 0
  rw [LinearEquiv.symm_apply_apply,rhoCoefficient_lift]

theorem coordinateRetraction_rho : coordinateRetraction coordinateRho = 0 := by
  change mixedCoordinateProjection (primitiveCoordinates.symm (primitiveCoordinates (rho ℂ))) = 0
  rw [LinearEquiv.symm_apply_apply,mixedProjection_rho]

theorem coordinateCoefficient_rho : coordinateRhoCoefficient coordinateRho = 1 := by
  change rhoCoefficient (primitiveCoordinates.symm (primitiveCoordinates (rho ℂ))) = 1
  rw [LinearEquiv.symm_apply_apply,rhoCoefficient_rho]

/-- The original primitive wedge form in the fixed fourteen-coordinate basis. -/
def coordinatePairing : LinearMap.BilinForm ℂ (Fin 14 → ℂ) :=
  (primitivePairing ℂ).compl₁₂ primitiveCoordinates.symm.toLinearMap
    primitiveCoordinates.symm.toLinearMap

theorem coordinatePairing_nondegenerate : coordinatePairing.Nondegenerate := by
  constructor
  · intro v hv
    apply primitiveCoordinates.symm.injective
    rw [map_zero]
    apply (primitivePairing_nondegenerate ℂ).1
    intro w
    have h := hv (primitiveCoordinates w)
    simpa only [coordinatePairing,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  · intro v hv
    apply primitiveCoordinates.symm.injective
    rw [map_zero]
    apply (primitivePairing_nondegenerate ℂ).2
    intro w
    have h := hv (primitiveCoordinates w)
    simpa only [coordinatePairing,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h

def pairingMatrix : Matrix (Fin 14) (Fin 14) ℂ := coordinatePairing.toMatrix'

theorem pairingMatrix_det_ne_zero : pairingMatrix.det ≠ 0 := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
  simpa only [pairingMatrix,Matrix.toBilin'_toMatrix'] using coordinatePairing_nondegenerate

/-- The actual wedge pairing is invertible before any parameter specialization. -/
def pairingIsomorphism : Matrix.GeneralLinearGroup (Fin 14) ℂ :=
  Matrix.GeneralLinearGroup.mk'' pairingMatrix (isUnit_iff_ne_zero.mpr pairingMatrix_det_ne_zero)

def liftMatrix : Matrix (Fin 14) (Fin 12) ℂ := coordinateLift.toMatrix'
def retractionMatrix : Matrix (Fin 12) (Fin 14) ℂ := coordinateRetraction.toMatrix'
def rhoColumn : Matrix (Fin 14) (Fin 1) ℂ := fun i _ => coordinateRho i
def rhoRow : Matrix (Fin 1) (Fin 14) ℂ :=
  (LinearMap.pi (fun _ : Fin 1 => coordinateRhoCoefficient)).toMatrix'

def headMatrix (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 12) R :=
  (LinearMap.funLeft R R GraphGrassmannianChart.head).toMatrix'

theorem retractionMatrix_liftMatrix : retractionMatrix * liftMatrix = 1 := by
  rw [retractionMatrix,liftMatrix,← LinearMap.toMatrix'_comp,
    coordinateRetraction_lift,LinearMap.toMatrix'_id]

theorem rhoRow_liftMatrix : rhoRow * liftMatrix = 0 := by
  rw [rhoRow,liftMatrix,← LinearMap.toMatrix'_comp]
  have h : (LinearMap.pi (fun _ : Fin 1 => coordinateRhoCoefficient)).comp coordinateLift = 0 := by
    apply LinearMap.ext
    intro z
    funext i
    exact LinearMap.congr_fun coordinateCoefficient_lift z
  rw [h,map_zero]

theorem retractionMatrix_rhoColumn : retractionMatrix * rhoColumn = 0 := by
  ext i j
  change (retractionMatrix *ᵥ coordinateRho) i = 0
  change (Matrix.toLin' retractionMatrix coordinateRho) i = 0
  rw [retractionMatrix,Matrix.toLin'_toMatrix',coordinateRetraction_rho]
  rfl

theorem rhoRow_rhoColumn : rhoRow * rhoColumn = 1 := by
  ext i j
  change (rhoRow *ᵥ coordinateRho) i = _
  change (Matrix.toLin' rhoRow coordinateRho) i = _
  rw [rhoRow,Matrix.toLin'_toMatrix']
  simpa only [LinearMap.pi_apply,coordinateCoefficient_rho,Matrix.one_apply] using
    (show (1 : ℂ) = if i = j then 1 else 0 by simp [Subsingleton.elim i j])

section ArbitraryCoefficientRing
variable (R : Type*) [CommRing R] [Algebra ℂ R]

theorem headMatrix_map : (headMatrix ℂ).map (algebraMap ℂ R) = headMatrix R := by
  ext i j
  simp only [headMatrix,LinearMap.toMatrix'_apply,LinearMap.funLeft_apply,
    Pi.single_apply,Matrix.map_apply]
  split_ifs <;> simp

/-- A constant retraction onto rho and the first four mixed coordinates. -/
def sumRetraction : Matrix (Fin 1 ⊕ Fin 4) (Fin 14) R :=
  (Matrix.fromRows rhoRow (headMatrix ℂ * retractionMatrix)).map (algebraMap ℂ R)

/-- Adjoin the actual rho vector to the actual mixed lift of the four-plane. -/
def sumFrame (P : Matrix (Fin 12) (Fin 4) R) : Matrix (Fin 14) (Fin 1 ⊕ Fin 4) R :=
  Matrix.fromCols (rhoColumn.map (algebraMap ℂ R))
    (liftMatrix.map (algebraMap ℂ R) * P)

theorem sumRetraction_frame (P : Matrix (Fin 12) (Fin 4) R)
    (hP : headMatrix R * P = 1) : sumRetraction R * sumFrame R P = 1 := by
  have h00 : rhoRow.map (algebraMap ℂ R) * rhoColumn.map (algebraMap ℂ R) = 1 := by
    rw [← Matrix.map_mul,rhoRow_rhoColumn,Matrix.map_one] <;> simp
  have h01 : rhoRow.map (algebraMap ℂ R) * liftMatrix.map (algebraMap ℂ R) = 0 := by
    rw [← Matrix.map_mul,rhoRow_liftMatrix,Matrix.map_zero]; simp
  have h10 : retractionMatrix.map (algebraMap ℂ R) * rhoColumn.map (algebraMap ℂ R) = 0 := by
    rw [← Matrix.map_mul,retractionMatrix_rhoColumn,Matrix.map_zero]; simp
  have h11 : retractionMatrix.map (algebraMap ℂ R) * liftMatrix.map (algebraMap ℂ R) = 1 := by
    rw [← Matrix.map_mul,retractionMatrix_liftMatrix,Matrix.map_one] <;> simp
  rw [sumRetraction,sumFrame,Matrix.fromRows_map,Matrix.map_mul,headMatrix_map,
    Matrix.fromRows_mul_fromCols,h00,← Matrix.mul_assoc,h01,Matrix.zero_mul,
    Matrix.mul_assoc,h10,Matrix.mul_zero,Matrix.mul_assoc,← Matrix.mul_assoc _ _ P,h11,
    Matrix.one_mul,hP]
  exact Matrix.fromBlocks_one

def frame (P : Matrix (Fin 12) (Fin 4) R) : Matrix (Fin 14) (Fin 5) R :=
  (sumFrame R P).submatrix id (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm

def frameRetraction : Matrix (Fin 5) (Fin 14) R :=
  (sumRetraction R).submatrix (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm id

theorem frameRetraction_frame (P : Matrix (Fin 12) (Fin 4) R)
    (hP : headMatrix R * P = 1) : frameRetraction R * frame R P = 1 := by
  change (sumRetraction R).submatrix (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm (Equiv.refl (Fin 14)) *
    (sumFrame R P).submatrix (Equiv.refl (Fin 14)) (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm = 1
  rw [Matrix.submatrix_mul_equiv,sumRetraction_frame R P hP,Matrix.submatrix_one_equiv]

/-- The actual perpendicular quotient, in the original primitive coordinates. -/
def quotientMatrix (P : Matrix (Fin 12) (Fin 4) R) : Matrix (Fin 5) (Fin 14) R :=
  (frame R P).transpose * pairingMatrix.map (algebraMap ℂ R)

/-- The section uses the actual inverse primitive wedge pairing. -/
def quotientSection : Matrix (Fin 14) (Fin 5) R :=
  ((pairingIsomorphism⁻¹).val.map (algebraMap ℂ R)) * (frameRetraction R).transpose

theorem quotientMatrix_section (P : Matrix (Fin 12) (Fin 4) R)
    (hP : headMatrix R * P = 1) : quotientMatrix R P * quotientSection R = 1 := by
  have hJ : pairingMatrix.map (algebraMap ℂ R) *
      ((pairingIsomorphism⁻¹).val.map (algebraMap ℂ R)) = 1 := by
    rw [← Matrix.map_mul]
    change (((pairingIsomorphism * pairingIsomorphism⁻¹).val).map (algebraMap ℂ R)) = 1
    rw [mul_inv_cancel,Units.val_one,Matrix.map_one] <;> simp
  rw [quotientMatrix,quotientSection,Matrix.mul_assoc,← Matrix.mul_assoc _ _ (frameRetraction R).transpose,
    hJ,Matrix.one_mul,← Matrix.transpose_mul,frameRetraction_frame R P hP,Matrix.transpose_one]

end ArbitraryCoefficientRing

section ActualGraphFamily
variable (R : Type*) [CommRing R]

def graphMatrix (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    Matrix (Fin 12) (Fin 4) R :=
  (GraphGrassmannianChart.ambientCoordinates.toLinearMap.comp
    (graphFamilyEmbedding R A B X)).toMatrix'

theorem graphMatrix_head (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    headMatrix R * graphMatrix R A B X = 1 := by
  rw [headMatrix,graphMatrix,← LinearMap.toMatrix'_comp]
  have h : (LinearMap.funLeft R R GraphGrassmannianChart.head).comp
      (GraphGrassmannianChart.ambientCoordinates.toLinearMap.comp
        (graphFamilyEmbedding R A B X)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext i
    change GraphGrassmannianChart.ambientCoordinates (graphFamilyEmbedding R A B X x)
      (GraphGrassmannianChart.head i) = x i
    rw [GraphGrassmannianChart.ambientCoordinates_head,graphFamilyEmbedding_apply]
  rw [h,LinearMap.toMatrix'_id]

theorem graphMatrix_mulVec (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R)
    (x : Fin 4 → R) : graphMatrix R A B X *ᵥ x =
      GraphGrassmannianChart.ambientCoordinates (graphFamilyEmbedding R A B X x) := by
  change Matrix.toLin' (graphMatrix R A B X) x = _
  rw [graphMatrix,Matrix.toLin'_toMatrix']
  rfl

end ActualGraphFamily

/-- The same actual relative-isomorphism chart already bound to native Gr4(12). -/
abbrev domain := GraphGrassmannianChart.domain ℂ

instance globalComplexAlgebra : Algebra ℂ Γ(domain,⊤) :=
  ((Scheme.ΓSpecIso (.of (IsomChartRing ℂ))).inv.hom.comp
    (algebraMap ℂ (IsomChartRing ℂ))).toAlgebra

/-- The original graph columns, now as actual global functions. -/
def universalGraph : Matrix (Fin 12) (Fin 4) Γ(domain,⊤) :=
  graphMatrix Γ(domain,⊤) (GraphGrassmannianChart.globalBase ℂ 0)
    (GraphGrassmannianChart.globalBase ℂ 1) (GraphGrassmannianChart.globalIsomorphism ℂ)

theorem universalGraph_head : headMatrix Γ(domain,⊤) * universalGraph = 1 :=
  graphMatrix_head _ _ _ _

def sheafQuotient : Stacks.FreeSheafMatrix.F domain 14 ⟶ Stacks.FreeSheafMatrix.F domain 5 :=
  Stacks.FreeSheafMatrix.ofMatrix (quotientMatrix Γ(domain,⊤) universalGraph)

def sheafSection : Stacks.FreeSheafMatrix.F domain 5 ⟶ Stacks.FreeSheafMatrix.F domain 14 :=
  Stacks.FreeSheafMatrix.ofMatrix (quotientSection Γ(domain,⊤))

theorem sheafSection_quotient : sheafSection ≫ sheafQuotient = 𝟙 _ := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp]
  simp only [sheafSection,sheafQuotient,Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    Stacks.FreeSheafMatrix.toMatrix_id,quotientMatrix_section _ _ universalGraph_head]

theorem sheafQuotient_epi : Epi sheafQuotient := by
  have : Epi (sheafSection ≫ sheafQuotient) := by rw [sheafSection_quotient]; infer_instance
  exact epi_of_epi sheafSection sheafQuotient

/-- A genuine rank-nine native Grassmannian quotient, split by the actual pairing inverse. -/
def presentation : AlgebraicGeometry.Grassmannian.QuotientPresentation domain 9 14 where
  target := Stacks.FreeSheafMatrix.F domain 5
  map := sheafQuotient
  map_epi := sheafQuotient_epi
  finiteLocallyFree := AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank domain 5

/-- The actual classifying morphism of the perpendicular-to-rho-plus-graph family. -/
def integralMap : domain ⟶ AlgebraicGeometry.Grassmannian.scheme 9 14 :=
  (AlgebraicGeometry.Grassmannian.schemeRepresentableBy 9 14).homEquiv.symm
    (((AlgebraicGeometry.Grassmannian.functorData 9 14).objEquiv domain).symm ⟦presentation⟧)

theorem integralMap_class :
    (AlgebraicGeometry.Grassmannian.functorData 9 14).objEquiv domain
      ((AlgebraicGeometry.Grassmannian.schemeRepresentableBy 9 14).homEquiv integralMap) =
      ⟦presentation⟧ := by simp only [integralMap,Equiv.apply_symm_apply]

def map : domain ⟶ GrassmannianCharts.space ℂ 9 14 :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap ℂ (IsomChartRing ℂ))))
    integralMap (terminal.hom_ext _ _)

@[reassoc] theorem map_projection : map ≫ GrassmannianCharts.projection ℂ 9 14 =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (IsomChartRing ℂ))) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem map_toIntegral : map ≫ GrassmannianCharts.toIntegral ℂ 9 14 = integralMap :=
  pullback.lift_snd _ _ _

theorem map_class :
    (AlgebraicGeometry.Grassmannian.functorData 9 14).objEquiv domain
      ((AlgebraicGeometry.Grassmannian.schemeRepresentableBy 9 14).homEquiv
        (map ≫ GrassmannianCharts.toIntegral ℂ 9 14)) = ⟦presentation⟧ := by
  rw [map_toIntegral,integralMap_class]

theorem sheafQuotient_matrix : Stacks.FreeSheafMatrix.toMatrix sheafQuotient =
    (frame Γ(domain,⊤) universalGraph).transpose *
      pairingMatrix.map (algebraMap ℂ Γ(domain,⊤)) := by
  rw [sheafQuotient,Stacks.FreeSheafMatrix.toMatrix_ofMatrix,quotientMatrix]

/-- The actual primitive vectors defining the five perpendicular equations. -/
def primitiveColumn (P : Matrix (Fin 12) (Fin 4) ℂ) : (Fin 1 ⊕ Fin 4) → Primitive ℂ :=
  Sum.elim (fun _ => rho ℂ) (fun a => mixedCoordinateLift (fun i => P i a))

theorem primitiveColumn_coordinates (P : Matrix (Fin 12) (Fin 4) ℂ)
    (j : Fin 1 ⊕ Fin 4) : primitiveCoordinates (primitiveColumn P j) =
      fun i => sumFrame ℂ P i j := by
  rcases j with j | a
  · rfl
  · change coordinateLift (fun i => P i a) =
      fun i => ((liftMatrix.map (algebraMap ℂ ℂ)) * P) i a
    simp only [Algebra.algebraMap_self]
    exact (LinearMap.toMatrix'_mulVec coordinateLift (fun i => P i a)).symm

/-- The quotient rows are literally the original primitive wedge-pairing equations. -/
theorem quotientMatrix_row (P : Matrix (Fin 12) (Fin 4) ℂ)
    (j : Fin 1 ⊕ Fin 4) (v : Primitive ℂ) :
    (quotientMatrix ℂ P *ᵥ primitiveCoordinates v) (finSumFinEquiv j) =
      primitivePairing ℂ (primitiveColumn P j) v := by
  have hc : (fun i => frame ℂ P i (finSumFinEquiv j)) =
      primitiveCoordinates (primitiveColumn P j) := by
    rw [primitiveColumn_coordinates]
    funext i
    simp only [frame,Matrix.submatrix_apply,id_eq,Equiv.symm_apply_apply]
  have hJ : pairingMatrix.map (algebraMap ℂ ℂ) = pairingMatrix := by ext i k; simp
  rw [quotientMatrix,hJ,← Matrix.mulVec_mulVec]
  change (fun i => frame ℂ P i (finSumFinEquiv j)) ⬝ᵥ
    (pairingMatrix *ᵥ primitiveCoordinates v) = _
  rw [hc,← Matrix.toBilin'_apply',pairingMatrix,Matrix.toBilin'_toMatrix']
  simp only [coordinatePairing,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- Exact actual primitive membership, retaining rho and every original lifted graph column. -/
theorem quotientMatrix_kernel_iff (P : Matrix (Fin 12) (Fin 4) ℂ) (v : Primitive ℂ) :
    Matrix.toLin' (quotientMatrix ℂ P) (primitiveCoordinates v) = 0 ↔
      primitivePairing ℂ (rho ℂ) v = 0 ∧
        ∀ a : Fin 4, primitivePairing ℂ (mixedCoordinateLift (fun i => P i a)) v = 0 := by
  constructor
  · intro h
    constructor
    · have hh := congrFun h ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5) (.inl (0 : Fin 1)))
      simpa only [Matrix.toLin'_apply,quotientMatrix_row,primitiveColumn,Sum.elim_inl,Pi.zero_apply]
        using hh
    · intro a
      have hh := congrFun h (finSumFinEquiv (.inr a))
      simpa only [Matrix.toLin'_apply,quotientMatrix_row,primitiveColumn,Sum.elim_inr,Pi.zero_apply]
        using hh
  · rintro ⟨hρ,hP⟩
    funext j
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).surjective j
    change (quotientMatrix ℂ P *ᵥ primitiveCoordinates v) (finSumFinEquiv j) = 0
    rw [quotientMatrix_row]
    rcases j with j | a
    · exact hρ
    · exact hP a

theorem pairingMatrix_apply (i j : Fin 14) : pairingMatrix i j =
    primitivePairing ℂ (primitiveCoordinates.symm (Pi.single i 1))
      (primitiveCoordinates.symm (Pi.single j 1)) := rfl

/-- The kernel of the genuine perpendicular quotient equals the actual orthogonal submodule. -/
theorem matrix_kernel_orthogonal {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (J : Matrix n n R) (H : Matrix n m R) :
    (Matrix.toLin' (H.transpose * J)).ker = J.toBilin'.orthogonal (Matrix.toLin' H).range := by
  have hp (x : m → R) (v : n → R) : J.toBilin' (H *ᵥ x) v =
      x ⬝ᵥ ((H.transpose * J) *ᵥ v) := by
    rw [Matrix.toBilin'_apply',dotProduct_comm,
      ← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
  ext v
  rw [LinearMap.mem_ker,LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h w hw
    obtain ⟨x,rfl⟩ := hw
    change J.toBilin' (H *ᵥ x) v = 0
    rw [hp]
    change x ⬝ᵥ Matrix.toLin' (H.transpose * J) v = 0
    rw [h,dotProduct_zero]
  · intro h
    funext j
    have hv := h (Matrix.toLin' H (Pi.single j 1)) ⟨Pi.single j 1,rfl⟩
    change J.toBilin' (H *ᵥ Pi.single j 1) v = 0 at hv
    rw [hp,single_one_dotProduct] at hv
    exact hv

section ActualScalarExtension
variable (R : Type*) [CommRing R] [Algebra ℂ R]

/-- The genuine base change of the actual primitive exterior wedge form. -/
def scalarExtendedPairing : LinearMap.BilinForm R (R ⊗[ℂ] Primitive ℂ) :=
  (primitivePairing ℂ).baseChange R

theorem scalarExtendedCoordinates_symm_single (i : Fin 14) :
    (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).symm (Pi.single i 1) =
      1 ⊗ₜ[ℂ] primitiveCoordinates.symm (Pi.single i 1) := by
  apply (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rw [PrimitiveRadicalNativeScheme.scalarExtendedCoordinates_tmul,
    LinearEquiv.apply_symm_apply]
  by_cases h : j = i <;> simp [h]

theorem scalarExtendedPairing_single (i j : Fin 14) :
    scalarExtendedPairing R
        ((PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).symm (Pi.single i 1))
        ((PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).symm (Pi.single j 1)) =
      algebraMap ℂ R (pairingMatrix i j) := by
  rw [scalarExtendedCoordinates_symm_single,scalarExtendedCoordinates_symm_single]
  change (primitivePairing ℂ).baseChange R
    (1 ⊗ₜ[ℂ] primitiveCoordinates.symm (Pi.single i 1))
    (1 ⊗ₜ[ℂ] primitiveCoordinates.symm (Pi.single j 1)) = _
  rw [LinearMap.BilinForm.baseChange_tmul,pairingMatrix_apply]
  simp only [Algebra.smul_def,mul_one]

/-- Exact coordinate identification of the actual tensor wedge form over every C-algebra. -/
theorem scalarExtendedPairing_coordinates (u v : R ⊗[ℂ] Primitive ℂ) :
    scalarExtendedPairing R u v =
      (pairingMatrix.map (algebraMap ℂ R)).toBilin'
        (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R u)
        (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R v) := by
  let e := PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R
  have hm : LinearMap.BilinForm.toMatrix' ((scalarExtendedPairing R).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap) =
      pairingMatrix.map (algebraMap ℂ R) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix'_apply,LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe]
    exact scalarExtendedPairing_single R i j
  have hb := congrArg Matrix.toBilin' hm
  rw [Matrix.toBilin'_toMatrix'] at hb
  have hv := congrArg (fun B : LinearMap.BilinForm R (Fin 14 → R) => B (e u) (e v)) hb
  simpa only [LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hv

/-- The actual five-frame in the scalar-extended primitive exterior kernel. -/
def scalarExtendedFrame (P : Matrix (Fin 12) (Fin 4) R) :
    (Fin 5 → R) →ₗ[R] (R ⊗[ℂ] Primitive ℂ) :=
  (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).symm.toLinearMap.comp
    (Matrix.toLin' (frame R P))

theorem scalarExtendedFrame_coordinates (P : Matrix (Fin 12) (Fin 4) R) (x : Fin 5 → R) :
    PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R (scalarExtendedFrame R P x) =
      frame R P *ᵥ x := by
  simp only [scalarExtendedFrame,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,Matrix.toLin'_apply]

/-- The classified native quotient has exactly the actual scalar-extended perpendicular kernel. -/
theorem kernel_scalarExtendedFrame (P : Matrix (Fin 12) (Fin 4) R) :
    (Matrix.toLin' (quotientMatrix R P)).ker.map
        (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates R).symm.toLinearMap =
      (scalarExtendedPairing R).orthogonal (scalarExtendedFrame R P).range := by
  ext v
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm]
  rw [quotientMatrix,matrix_kernel_orthogonal]
  constructor
  · intro h w hw
    obtain ⟨x,rfl⟩ := hw
    rw [scalarExtendedPairing_coordinates,scalarExtendedFrame_coordinates]
    exact h _ ⟨x,rfl⟩
  · intro h w hw
    obtain ⟨x,rfl⟩ := hw
    have hv := h (scalarExtendedFrame R P x) ⟨x,rfl⟩
    rw [scalarExtendedPairing_coordinates,scalarExtendedFrame_coordinates] at hv
    exact hv

/-- The original primitive exterior module is retained by the actual universal quotient. -/
theorem universal_kernel_scalarExtendedFrame :
    (Matrix.toLin' (Stacks.FreeSheafMatrix.toMatrix sheafQuotient)).ker.map
        (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates Γ(domain,⊤)).symm.toLinearMap =
      (scalarExtendedPairing Γ(domain,⊤)).orthogonal
        (scalarExtendedFrame Γ(domain,⊤) universalGraph).range := by
  rw [sheafQuotient,Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
  exact kernel_scalarExtendedFrame _ _

end ActualScalarExtension

end M9Native.PrimitiveRhoFiberChart
