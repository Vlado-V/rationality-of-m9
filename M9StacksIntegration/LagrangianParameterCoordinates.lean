module

public import M9StacksIntegration.LagrangianParameterLinearAction
public import M9StacksIntegration.PrimitiveConstantFieldAction
public import M9StacksIntegration.LagrangianLinearSectionQuotientCharts
public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
public import StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

@[expose] public section

/-! The exact raw/original primitive coordinate change on the SAME actual
LG linear-section parameter. The conjugacy is proved on original quotient
presentations over every test scheme, with the frozen Sp6 action retained.
No family or moduli-classifier invariance is supplied as a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix

namespace M9Native.LagrangianParameterCoordinates

open AlgebraicGeometry.Grassmannian
open LagrangianMatrixChart

abbrev Sp6 := Matrix.symplecticGroup (Fin 3) ℂ
abbrev GL14 := Matrix.GeneralLinearGroup (Fin 14) ℂ

/-- The actual raw primitive exterior matrix and its actual inverse. -/
def rawUnit (g : Sp6) : GL14 where
  val := PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g
  inv := PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g⁻¹
  val_inv := by
    rw [← PrimitiveRingMatrices.matrix14_mul, mul_inv_cancel, PrimitiveRingMatrices.matrix14_one]
  inv_val := by
    rw [← PrimitiveRingMatrices.matrix14_mul, inv_mul_cancel, PrimitiveRingMatrices.matrix14_one]

/-- The frozen original radical-coordinate primitive matrix. -/
def originalUnit (g : Sp6) : GL14 where
  val := PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g
  inv := PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g⁻¹
  val_inv := by
    rw [← PrimitiveRingCoordinates.primitiveMatrix_mul, mul_inv_cancel,
      PrimitiveRingCoordinates.primitiveMatrix_one]
  inv_val := by
    rw [← PrimitiveRingCoordinates.primitiveMatrix_mul, inv_mul_cancel,
      PrimitiveRingCoordinates.primitiveMatrix_one]

/-- The literal proved field-coordinate change C, with its proved inverse. -/
def coordinateUnit : GL14 where
  val := PrimitiveRingCoordinates.changeMatrix
  inv := PrimitiveRingCoordinates.inverseChangeMatrix
  val_inv := PrimitiveRingCoordinates.changeMatrix_inverse
  inv_val := PrimitiveRingCoordinates.inverse_changeMatrix

theorem originalUnit_mul_coordinate (g : Sp6) :
    originalUnit g * coordinateUnit = coordinateUnit * rawUnit g := by
  apply Units.ext
  change PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g *
      PrimitiveRingCoordinates.changeMatrix =
    PrimitiveRingCoordinates.changeMatrix * PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g
  rw [PrimitiveRingCoordinates.primitiveMatrix]
  change (PrimitiveRingCoordinates.changeMatrix *
      PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g *
      PrimitiveRingCoordinates.inverseChangeMatrix) * PrimitiveRingCoordinates.changeMatrix =
    PrimitiveRingCoordinates.changeMatrix * PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g
  rw [Matrix.mul_assoc, Matrix.mul_assoc, PrimitiveRingCoordinates.inverse_changeMatrix,
    Matrix.mul_one]

/-- Parameter quotients precompose with C, so their raw kernel is C⁻¹W. -/
def coordinateChange : LagrangianLinearSections.parameter ℂ ≅
    LagrangianLinearSections.parameter ℂ :=
  LagrangianParameterLinearAction.rightAutomorphism ℂ coordinateUnit

@[reassoc] theorem coordinateChange_projection :
    coordinateChange.hom ≫ LagrangianLinearSections.parameterProjection ℂ =
      LagrangianLinearSections.parameterProjection ℂ :=
  LagrangianParameterLinearAction.action_projection ℂ coordinateUnit

/-- The raw primitive kernel action is inverse quotient precomposition. -/
def rawAction (g : Sp6) : LagrangianLinearSections.parameter ℂ ⟶
    LagrangianLinearSections.parameter ℂ :=
  LagrangianParameterLinearAction.action ℂ (rawUnit g⁻¹)

@[reassoc] theorem rawAction_projection (g : Sp6) :
    rawAction g ≫ LagrangianLinearSections.parameterProjection ℂ =
      LagrangianLinearSections.parameterProjection ℂ :=
  LagrangianParameterLinearAction.action_projection ℂ (rawUnit g⁻¹)

theorem native_freeIso_eq (T : Over PrimitiveFamilyFreeAction.base) (g : Sp6) :
    (PrimitiveFamilyFreeAction.freeIso T
      (Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T) g)).hom =
      (LagrangianParameterLinearAction.constantFreeIso ℂ T.hom (originalUnit g)).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [PrimitiveFamilyFreeAction.freeIso_matrix,
    LagrangianParameterLinearAction.constantFreeIso_matrix]
  change PrimitiveRingCoordinates.primitiveMatrix Γ(T.left,⊤)
      (PrimitiveFamilyFreeAction.scalarMap T)
      (Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T) g) =
    (PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g).map
      (LagrangianParameterLinearAction.scalarMap ℂ T.hom)
  have hs : LagrangianParameterLinearAction.scalarMap ℂ T.hom =
      PrimitiveFamilyFreeAction.scalarMap T := rfl
  rw [hs]
  have hm : Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T) g =
      LagrangianTransitivity.mapSymplectic ℂ (PrimitiveFamilyFreeAction.scalarMap T) g := by
    apply Subtype.ext
    rfl
  rw [hm]
  simpa only [RingHom.comp_id] using PrimitiveRingCoordinates.primitiveMatrix_map
    ℂ (RingHom.id ℂ) (PrimitiveFamilyFreeAction.scalarMap T) g

/-- The original native quotient action is the same literal GL14
precomposition in its original coordinates, over every test scheme. -/
theorem native_transformPoints_eq (T : Over PrimitiveFamilyFreeAction.base) (g : Sp6)
    (x : Points T.left 9 14) :
    PrimitiveFamilyFreeAction.transformPoints T
      (Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T) g) x =
    LagrangianParameterLinearAction.transformPoints ℂ T.hom (originalUnit g⁻¹) x := by
  refine Quotient.inductionOn x fun q => ?_
  refine Quotient.sound (.rel _ _ ⟨Iso.refl _, ?_⟩)
  change ((PrimitiveFamilyFreeAction.freeIso T
      ((Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T) g)⁻¹)).hom ≫ q.map) ≫
      𝟙 _ =
    (LagrangianParameterLinearAction.constantFreeIso ℂ T.hom (originalUnit g⁻¹)).hom ≫ q.map
  rw [Category.comp_id,
    ← map_inv (Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap T)) g,
    native_freeIso_eq]

/-- This is equality of the actual scheme morphisms, not an action-identification premise. -/
theorem schemeMap_eq_linear (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    PrimitiveConstantFieldAction.schemeMap h =
      LagrangianParameterLinearAction.action ℂ (originalUnit (PrimitiveRingFieldBridge.fromOriginal h)⁻¹) := by
  apply LagrangianParameterLinearAction.hom_ext ℂ
  · rw [PrimitiveConstantFieldAction.schemeMap_projection,
      LagrangianParameterLinearAction.action_projection]
  · have hn := PrimitiveConstantFieldAction.schemeMap_pointClass
      PrimitiveGrassmannianAction.overSpace (𝟙 _) h
    calc
      LagrangianParameterLinearAction.pointClass ℂ (PrimitiveConstantFieldAction.schemeMap h) =
          PrimitiveGrassmannianAction.pointClass (PrimitiveConstantFieldAction.schemeMap h) := rfl
      _ = PrimitiveFamilyFreeAction.transformPoints PrimitiveGrassmannianAction.overSpace
          (Sp6GroupScheme.mapMatrix (PrimitiveFamilyFreeAction.scalarMap
            PrimitiveGrassmannianAction.overSpace) (PrimitiveRingFieldBridge.fromOriginal h))
          (PrimitiveGrassmannianAction.pointClass (𝟙 _)) := by
            simpa only [Over.id_left, Category.id_comp] using hn
      _ = LagrangianParameterLinearAction.transformPoints ℂ
          (LagrangianParameterLinearAction.projection ℂ)
          (originalUnit (PrimitiveRingFieldBridge.fromOriginal h)⁻¹)
          (LagrangianParameterLinearAction.pointClass ℂ (𝟙 _)) :=
        native_transformPoints_eq PrimitiveGrassmannianAction.overSpace
          (PrimitiveRingFieldBridge.fromOriginal h) _
      _ = _ := (LagrangianParameterLinearAction.action_class ℂ
        (originalUnit (PrimitiveRingFieldBridge.fromOriginal h)⁻¹)).symm

/-- The real parameter coordinate change conjugates the frozen original
Sp6 action to the raw action used by the original universal equations. -/
theorem schemeMap_coordinateChange (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    PrimitiveConstantFieldAction.schemeMap h ≫ coordinateChange.hom =
      coordinateChange.hom ≫ rawAction (PrimitiveRingFieldBridge.fromOriginal h) := by
  change PrimitiveConstantFieldAction.schemeMap h ≫
      LagrangianParameterLinearAction.action ℂ coordinateUnit =
    LagrangianParameterLinearAction.action ℂ coordinateUnit ≫
      LagrangianParameterLinearAction.action ℂ (rawUnit (PrimitiveRingFieldBridge.fromOriginal h)⁻¹)
  rw [schemeMap_eq_linear, LagrangianParameterLinearAction.action_mul,
    LagrangianParameterLinearAction.action_mul, originalUnit_mul_coordinate]

/-- The literal original universal quotient is retained through C, with
its actual target isomorphism and precomposition triangle. -/
theorem coordinateChange_pullback_isomorphic {T : Scheme}
    (p : T ⟶ LagrangianLinearSections.parameter ℂ) :
    (pullbackPresentation (p ≫ coordinateChange.hom)
      (LagrangianLinearSections.parameterQuotient ℂ)).Isomorphic
    (LagrangianParameterLinearAction.transform ℂ
      (p ≫ LagrangianLinearSections.parameterProjection ℂ) coordinateUnit
      (pullbackPresentation p (LagrangianLinearSections.parameterQuotient ℂ))) := by
  apply LagrangianGrassmannian.presentation_isomorphic_of_class_eq
  change (⟦pullbackPresentation (p ≫ coordinateChange.hom)
      (LagrangianLinearSections.parameterQuotient ℂ)⟧ : Points T 9 14) =
    LagrangianParameterLinearAction.transformPoints ℂ
      (p ≫ LagrangianLinearSections.parameterProjection ℂ) coordinateUnit
      (⟦pullbackPresentation p (LagrangianLinearSections.parameterQuotient ℂ)⟧ : Points T 9 14)
  rw [LagrangianLinearSectionQuotientCharts.pullback_parameter_class,
    LagrangianLinearSectionQuotientCharts.pullback_parameter_class]
  exact LagrangianParameterLinearAction.pointClass_action ℂ p coordinateUnit

end M9Native.LagrangianParameterCoordinates
