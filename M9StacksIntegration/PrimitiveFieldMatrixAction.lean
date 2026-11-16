module

public import M9StacksIntegration.PrimitiveOriginalExtensionAction
public import M9StacksIntegration.PrimitiveRadicalOrbitKernelPoints

@[expose] public section

/-! Literal split field-matrix quotients under the genuine native Sp6 action.
The final equality follows from original primitive-kernel transport, rather
than an assumed native classifying-map or action equality. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open MonoidalCategory CartesianMonoidalCategory
open scoped Classical Matrix CategoryTheory.MonObj

namespace M9Native.PrimitiveFieldMatrixAction
open M9.ExteriorPrimitive M9.PrimitiveStabilizer
open PrimitiveGrassmannianAction PrimitiveUniversalExtensionPoints
open PrimitiveOriginalExtensionAction PrimitiveExtensionFieldBridge

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

def coordinateMatrix (g : Sp6 K) : Matrix (Fin 14) (Fin 14) K :=
  PrimitiveRingCoordinates.primitiveMatrix K (algebraMap ℂ K) (fromOriginal K g)

theorem coordinateMatrix_coordinates (g : Sp6 K) (v : Primitive K) :
    coordinateMatrix K g *ᵥ fieldCoordinates K v =
      fieldCoordinates K (primitiveLinear K g v) :=
  PrimitiveOriginalExtensionAction.primitiveMatrix_fieldCoordinates g v

theorem coordinateMatrix_inv_mul (g : Sp6 K) :
    coordinateMatrix K g⁻¹ * coordinateMatrix K g = 1 := by
  rw [coordinateMatrix,coordinateMatrix,← PrimitiveRingCoordinates.primitiveMatrix_mul,
    ← map_mul,inv_mul_cancel,map_one,PrimitiveRingCoordinates.primitiveMatrix_one]

theorem coordinateMatrix_mul_inv (g : Sp6 K) :
    coordinateMatrix K g * coordinateMatrix K g⁻¹ = 1 := by
  rw [coordinateMatrix,coordinateMatrix,← PrimitiveRingCoordinates.primitiveMatrix_mul,
    ← map_mul,mul_inv_cancel,map_one,PrimitiveRingCoordinates.primitiveMatrix_one]

def groupMatrix (g : Sp6 K) : Matrix.symplecticGroup (Fin 3) Γ((overField K).left,⊤) :=
  Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of K)).inv.hom (fromOriginal K g)

theorem global_familyMatrix (g : Sp6 K) :
    PrimitiveFamilyFreeAction.familyMatrix (overField K) (groupMatrix K g) =
      (coordinateMatrix K g).map (Scheme.ΓSpecIso (.of K)).inv.hom := by
  have h := nativeGroupPoint_familyMatrix g
  rw [pointsMulEquiv_nativeGroupPoint] at h
  ext i j
  apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of K)).hom _ = (Scheme.ΓSpecIso (.of K)).hom
    ((Scheme.ΓSpecIso (.of K)).inv (coordinateMatrix K g i j))
  rw [Iso.inv_hom_id_apply]
  exact congrFun (congrFun h i) j

theorem acted_surjective (g : Sp6 K) (Q : Matrix (Fin 5) (Fin 14) K)
    (hQ : Function.Surjective Q.mulVec) :
    Function.Surjective (Q * coordinateMatrix K g⁻¹).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨coordinateMatrix K g * SplitMatrixGrassmannian.fieldRightInverse 9 14 K Q hQ,?_⟩
  calc
    Q * coordinateMatrix K g⁻¹ *
        (coordinateMatrix K g * SplitMatrixGrassmannian.fieldRightInverse 9 14 K Q hQ) =
      Q * (coordinateMatrix K g⁻¹ * coordinateMatrix K g) *
        SplitMatrixGrassmannian.fieldRightInverse 9 14 K Q hQ := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [coordinateMatrix_inv_mul,Matrix.mul_one]
      exact SplitMatrixGrassmannian.fieldRightInverse_spec 9 14 K Q hQ

/-- A genuine native quotient-class computation, retaining the actual inverse. -/
theorem transform_fieldPresentation (g : Sp6 K) (Q : Matrix (Fin 5) (Fin 14) K)
    (hQ : Function.Surjective Q.mulVec) :
    PrimitiveFamilyFreeAction.transformPoints (overField K) (groupMatrix K g)
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K Q hQ⟧ =
        ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K (Q * coordinateMatrix K g⁻¹)
          (acted_surjective K g Q hQ)⟧ := by
  change (⟦PrimitiveFamilyFreeAction.transform (overField K) (groupMatrix K g)
    (SplitMatrixGrassmannian.fieldPresentation 9 14 K Q hQ)⟧ :
      AlgebraicGeometry.Grassmannian.Points (Spec (.of K)) 9 14) = _
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _,?_⟩
  dsimp only [PrimitiveFamilyFreeAction.transform]
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,PrimitiveFamilyFreeAction.freeIso_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix,SplitMatrixGrassmannian.fieldPresentation_matrix]
  have hg : (groupMatrix K g)⁻¹ = groupMatrix K g⁻¹ := by
    simp only [groupMatrix,map_inv]
  rw [hg,global_familyMatrix,Matrix.map_mul]

def overPoint (p : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) :
    overField K ⟶ overSpace := Over.homMk p hp

def actPoint (g : Sp6 K) (p : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) :
    Spec (.of K) ⟶ space :=
  (lift (nativeGroupPoint g) (overPoint K p hp) ≫ nativeAction.act).left

@[reassoc] theorem actPoint_projection (g : Sp6 K) (p : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) :
    actPoint K g p hp ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) :=
  (lift (nativeGroupPoint g) (overPoint K p hp) ≫ nativeAction.act).w

theorem actPoint_class (g : Sp6 K) (p : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))
    (Q : Matrix (Fin 5) (Fin 14) K) (hQ : Function.Surjective Q.mulVec)
    (hc : pointClass p = ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K Q hQ⟧) :
    pointClass (actPoint K g p hp) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K (Q * coordinateMatrix K g⁻¹)
        (acted_surjective K g Q hQ)⟧ := by
  rw [actPoint,PrimitiveOriginalExtensionAction.action_pointClass]
  change PrimitiveFamilyFreeAction.transformPoints (overField K) (groupMatrix K g)
    (pointClass p) = _
  rw [hc]
  exact transform_fieldPresentation K g Q hQ

/-- Literal matrix inverse-precomposition transports the actual original
primitive kernel by the original primitive linear equivalence. -/
theorem actedKernel_original (g : Sp6 K) (Q : Matrix (Fin 5) (Fin 14) K) :
    (Matrix.toLin' (Q * coordinateMatrix K g⁻¹)).ker.map (fieldCoordinates K).symm.toLinearMap =
      ((Matrix.toLin' Q).ker.map (fieldCoordinates K).symm.toLinearMap).map
        (primitiveLinear K g).toLinearMap := by
  ext v
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm,LinearMap.mem_ker,Matrix.toLin'_apply]
  rw [Submodule.mem_map_equiv,Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm,LinearMap.mem_ker,Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec,coordinateMatrix_coordinates,
    PrimitiveRadicalOrbitKernelPoints.primitiveLinear_inv]

/-- Equality of literal original primitive kernels proves the actual native
scheme-point action equality. No classifying-map comparison is assumed. -/
theorem actPoint_eq_of_original_kernel_transport (g : Sp6 K)
    (p q : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))
    (hq : q ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))
    (Q Q' : Matrix (Fin 5) (Fin 14) K)
    (hQ : Function.Surjective Q.mulVec) (hQ' : Function.Surjective Q'.mulVec)
    (hc : pointClass p = ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K Q hQ⟧)
    (hc' : pointClass q = ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K Q' hQ'⟧)
    (hk : (Matrix.toLin' Q').ker.map (fieldCoordinates K).symm.toLinearMap =
      ((Matrix.toLin' Q).ker.map (fieldCoordinates K).symm.toLinearMap).map
        (primitiveLinear K g).toLinearMap) :
    actPoint K g p hp = q := by
  have hb : actPoint K g p hp ≫ projection = q ≫ projection := by
    rw [actPoint_projection,hq]
  apply (GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 9) (n := 14)
    (actPoint K g p hp) q (Q * coordinateMatrix K g⁻¹) Q'
    (acted_surjective K g Q hQ) hQ' (actPoint_class K g p hp Q hQ hc) hc' hb).mpr
  apply Submodule.map_injective_of_injective
    (f := (fieldCoordinates K).symm.toLinearMap) (fieldCoordinates K).symm.injective
  change (Matrix.toLin' (Q * coordinateMatrix K g⁻¹)).ker.map
      (fieldCoordinates K).symm.toLinearMap =
    (Matrix.toLin' Q').ker.map (fieldCoordinates K).symm.toLinearMap
  rw [actedKernel_original]
  exact hk.symm

end M9Native.PrimitiveFieldMatrixAction
