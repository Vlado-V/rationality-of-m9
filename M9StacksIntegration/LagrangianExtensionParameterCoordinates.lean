module

public import M9StacksIntegration.LagrangianParameterCoordinates
public import M9StacksIntegration.GrassmannianFieldBaseChange
public import M9StacksIntegration.LagrangianParameterFieldMatrixAction

@[expose] public section

/-! Original native parameter points over every extension of the actual
complex base. The raw field matrix is classified by the genuine base-change
map, then by the inverse of the frozen complex coordinate automorphism.
Its actual quotient matrix is M*C^{-1}, including its structural map. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix

namespace M9Native.LagrangianExtensionParameterCoordinates

open LagrangianParameterLinearAction

variable (L : Type) [Field L] [Algebra ℂ L]

theorem scalarMap_spec :
    scalarMap ℂ (Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) =
      (Scheme.ΓSpecIso (.of L)).inv.hom.comp (algebraMap ℂ L) := by
  ext c
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ Γ(Spec (.of L), ⊤) => f.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ L))).symm

theorem constantProduct_surjective (U : Matrix.GeneralLinearGroup (Fin 14) ℂ)
    (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    Function.Surjective (M * U.val.map (algebraMap ℂ L)).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨(U⁻¹).val.map (algebraMap ℂ L) *
    SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM, ?_⟩
  calc
    M * U.val.map (algebraMap ℂ L) * ((U⁻¹).val.map (algebraMap ℂ L) *
        SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM) =
      M * (U.val.map (algebraMap ℂ L) * (U⁻¹).val.map (algebraMap ℂ L)) *
        SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      exact SplitMatrixGrassmannian.fieldRightInverse_spec 9 14 L M hM

/-- Constant complex matrices act on the actual extension-field quotient
through their literal scalar images, with no action-identification input. -/
theorem transform_fieldPresentation (U : Matrix.GeneralLinearGroup (Fin 14) ℂ)
    (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    transformPoints ℂ (Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) U
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 L M hM⟧ =
        ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 L
          (M * U.val.map (algebraMap ℂ L)) (constantProduct_surjective L U M hM)⟧ := by
  change (⟦transform ℂ (Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) U
    (SplitMatrixGrassmannian.fieldPresentation 9 14 L M hM)⟧ :
      AlgebraicGeometry.Grassmannian.Points (Spec (.of L)) 9 14) = _
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _, ?_⟩
  dsimp only [transform]
  simp only [Iso.refl_hom, Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, constantFreeIso_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix]
  change M.map (Scheme.ΓSpecIso (.of L)).inv.hom *
      U.val.map (scalarMap ℂ (Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))) =
    (M * U.val.map (algebraMap ℂ L)).map (Scheme.ΓSpecIso (.of L)).inv.hom
  rw [scalarMap_spec L, Matrix.map_mul]
  rfl

def rawPoint (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    Spec (.of L) ⟶ GrassmannianCharts.space ℂ 9 14 :=
  SplitMatrixGrassmannian.fieldPoint 9 14 L M hM ≫
    GrassmannianFieldBaseChange.map (algebraMap ℂ L) 9 14

@[reassoc] theorem rawPoint_projection (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) :
    rawPoint L M hM ≫ GrassmannianCharts.projection ℂ 9 14 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  dsimp only [rawPoint]
  rw [Category.assoc, GrassmannianFieldBaseChange.map_projection,
    ← Category.assoc, SplitMatrixGrassmannian.fieldPoint_projection, Category.id_comp]

theorem rawPoint_class (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) :
    pointClass ℂ (rawPoint L M hM) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 L M hM⟧ := by
  change (AlgebraicGeometry.Grassmannian.functorData 9 14).objEquiv (Spec (.of L))
    ((AlgebraicGeometry.Grassmannian.schemeRepresentableBy 9 14).homEquiv
      ((SplitMatrixGrassmannian.fieldPoint 9 14 L M hM ≫
        GrassmannianFieldBaseChange.map (algebraMap ℂ L) 9 14) ≫
          GrassmannianCharts.toIntegral ℂ 9 14)) = _
  rw [Category.assoc, GrassmannianFieldBaseChange.map_toIntegral]
  exact SplitMatrixGrassmannian.fieldPoint_class 9 14 L M hM

def originalMatrix (M : Matrix (Fin 5) (Fin 14) L) : Matrix (Fin 5) (Fin 14) L :=
  M * PrimitiveRingCoordinates.inverseChangeMatrix.map (algebraMap ℂ L)

theorem originalMatrix_surjective (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) : Function.Surjective (originalMatrix L M).mulVec :=
  constantProduct_surjective L LagrangianParameterCoordinates.coordinateUnit⁻¹ M hM

def originalPoint (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    Spec (.of L) ⟶ GrassmannianCharts.space ℂ 9 14 :=
  rawPoint L M hM ≫ LagrangianParameterCoordinates.coordinateChange.inv

@[reassoc] theorem originalPoint_projection (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) :
    originalPoint L M hM ≫ GrassmannianCharts.projection ℂ 9 14 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  change (rawPoint L M hM ≫ action ℂ LagrangianParameterCoordinates.coordinateUnit⁻¹) ≫
    GrassmannianCharts.projection ℂ 9 14 = _
  rw [Category.assoc, action_projection, rawPoint_projection L]

/-- The actual original quotient class, over the unchanged complex base,
is M*C_L^{-1}. This is proved on native quotient presentations. -/
theorem originalPoint_class (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) :
    pointClass ℂ (originalPoint L M hM) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 L (originalMatrix L M)
        (originalMatrix_surjective L M hM)⟧ := by
  change pointClass ℂ
    (rawPoint L M hM ≫ action ℂ LagrangianParameterCoordinates.coordinateUnit⁻¹) = _
  rw [pointClass_action ℂ, rawPoint_projection L, rawPoint_class L]
  exact transform_fieldPresentation L LagrangianParameterCoordinates.coordinateUnit⁻¹ M hM

@[reassoc] theorem originalPoint_coordinateChange (M : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) :
    originalPoint L M hM ≫ LagrangianParameterCoordinates.coordinateChange.hom =
      rawPoint L M hM := by
  dsimp only [originalPoint]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem originalPoint_eq_of_rowSpan_eq (M N : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (h : LagrangianParameterFieldMatrixAction.rowSpan L M =
      LagrangianParameterFieldMatrixAction.rowSpan L N) :
    originalPoint L M hM = originalPoint L N hN := by
  exact congrArg (fun p : Spec (.of L) ⟶ GrassmannianCharts.space L 9 14 =>
    (p ≫ GrassmannianFieldBaseChange.map (algebraMap ℂ L) 9 14) ≫
      LagrangianParameterCoordinates.coordinateChange.inv)
    (LagrangianParameterFieldMatrixAction.fieldPoint_eq_of_rowSpan_eq L M N hM hN h)

end M9Native.LagrangianExtensionParameterCoordinates
