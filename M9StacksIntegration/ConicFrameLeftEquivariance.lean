module

public import M9StacksIntegration.GrassmannianLinearAction
public import M9StacksIntegration.ConicFrameMap
public import M9StacksIntegration.ConicFrameBaseChange
public import M9StacksIntegration.PrimitiveFreeMatrixPullback
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Literal symmetric-square equivariance of the actual native conic-frame
classifying morphism. These are equalities of genuine scheme maps over every
test scheme, together with actual pullback of their free quotient presentations. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped BigOperators

universe u

namespace M9Native.ConicFrameLeftEquivariance

open AlgebraicGeometry.Grassmannian
open LagrangianMatrixChart LagrangianGrassmannian LagrangianFreeMatrixPullback
open SectionZeroIdealFactorization ConicFrame

section Polynomial
variable {R : Type*} [CommRing R]

/-- Multiplication of frames is read in the actual polynomial quotient matrix. -/
theorem quotientMatrix_mul (A F : Mat3 R) :
    quotientMatrix (A * F) = quotientMatrix F * congruence A.adjugate := by
  rw [quotientMatrix, Matrix.adjugate_mul_distrib, congruence_mul, ← Matrix.mul_assoc]
  rfl

theorem adjugate_sl_inverse (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R).val.adjugate = g.val := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_adjugate']
  simp only [g.prop, one_pow, one_smul]

theorem quotientMatrix_sl_inverse (g : Matrix.SpecialLinearGroup (Fin 3) R) (F : Mat3 R) :
    quotientMatrix (g⁻¹.val * F) = quotientMatrix F * congruence g.val := by
  rw [quotientMatrix_mul, adjugate_sl_inverse]

/-- The actual six-dimensional symmetric-square matrix representation. -/
def symmetricSquare : Matrix.SpecialLinearGroup (Fin 3) R →* Matrix.GeneralLinearGroup (Fin 6) R where
  toFun g := congruenceUnit g.val (by rw [g.prop]; exact isUnit_one)
  map_one' := by apply Units.ext; exact congruence_one
  map_mul' g h := by apply Units.ext; exact congruence_mul g.val h.val

@[simp] theorem symmetricSquare_val (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (symmetricSquare g).val = congruence g.val := rfl

end Polynomial

/-- Pullback of an arbitrary rectangular free-sheaf matrix through the actual
canonical free-bundle identifications. -/
def pulledFreeMap {X Y : Scheme.{u}} (f : Y ⟶ X) (n m : ℕ)
    (a : freeOn X n ⟶ freeOn X m) : freeOn Y n ⟶ freeOn Y m :=
  (pullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackFreeIso f m).hom

theorem freeMap_column (X : Scheme.{u}) (n m : ℕ)
    (a : freeOn X n ⟶ freeOn X m) (j : Fin n) :
    a.app ⊤ (freeBasisSection X n j) =
      ∑ i : Fin m, Stacks.FreeSheafMatrix.toMatrix a i j • freeBasisSection X m i := by
  have hc (i : Fin m) : freeSectionCoordinates X m (a.app ⊤ (freeBasisSection X n j)) i =
      Stacks.FreeSheafMatrix.toMatrix a i j := freeCoordinates_map_basis a i j
  have h := eq_sum_coordinates_basis X m (a.app ⊤ (freeBasisSection X n j))
  simpa only [hc] using h

theorem pulledFreeMap_column {X Y : Scheme.{u}} (f : Y ⟶ X) (n m : ℕ)
    (a : freeOn X n ⟶ freeOn X m) (j : Fin n) :
    (pulledFreeMap f n m a).app ⊤ (freeBasisSection Y n j) =
      ∑ i : Fin m, f.appTop (Stacks.FreeSheafMatrix.toMatrix a i j) • freeBasisSection Y m i := by
  change (pullbackFreeIso f m).hom.app ⊤
    (((Scheme.Modules.pullback f).map a).app ⊤
      ((pullbackFreeIso f n).inv.app ⊤ (freeBasisSection Y n j))) = _
  rw [PrimitiveFreeMatrixPullback.inverse_freeBasisSection_pullback,
    pullback_map_app_pullbackGlobalSections, freeMap_column]
  simp only [map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, PrimitiveFreeMatrixPullback.freeBasisSection_pullback]

theorem pulledFreeMap_matrix {X Y : Scheme.{u}} (f : Y ⟶ X) (n m : ℕ)
    (a : freeOn X n ⟶ freeOn X m) :
    Stacks.FreeSheafMatrix.toMatrix (pulledFreeMap f n m a) =
      (Stacks.FreeSheafMatrix.toMatrix a).map f.appTop.hom := by
  ext i j
  rw [← freeCoordinates_map_basis (pulledFreeMap f n m a) i j]
  change freeSectionCoordinates Y m ((pulledFreeMap f n m a).app ⊤ (freeBasisSection Y n j)) i = _
  rw [pulledFreeMap_column]
  simp only [map_sum, _root_.map_smul, Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis]
  simp

/-- Actual conic-frame quotient presentations commute with arbitrary pullback. -/
theorem presentation_pullback {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Mat3 Γ(S, ⊤)) (hF : IsUnit F.det)
    (hF' : IsUnit (F.map f.appTop.hom).det) :
    (pullbackPresentation f (presentation S F hF)).Isomorphic
      (presentation T (F.map f.appTop.hom) hF') := by
  refine ⟨pullbackFreeIso f 2, ?_⟩
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  change Stacks.FreeSheafMatrix.toMatrix (pulledFreeMap f 6 2 (sheafQuotient S F)) =
    Stacks.FreeSheafMatrix.toMatrix (sheafQuotient T (F.map f.appTop.hom))
  rw [pulledFreeMap_matrix]
  simp only [sheafQuotient, Stacks.FreeSheafMatrix.toMatrix_ofMatrix, quotientMatrix_map]

variable (K : Type u) [Field K]

theorem pointClass_map {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    GrassmannianLinearAction.pointClass K (ConicFrame.map T K b F hF) =
      ⟦presentation T F hF⟧ := by
  rw [GrassmannianLinearAction.pointClass, map_toIntegral, integralMap_class]

/-- Native scheme-level naturality; the two quotient bundles are canonically
isomorphic by the actual free-bundle pullback comparison. -/
theorem map_natural {S T : Scheme.{u}} (f : T ⟶ S) (b : S ⟶ Spec (.of K))
    (F : Mat3 Γ(S, ⊤)) (hF : IsUnit F.det)
    (hF' : IsUnit (F.map f.appTop.hom).det) :
    f ≫ ConicFrame.map S K b F hF =
      ConicFrame.map T K (f ≫ b) (F.map f.appTop.hom) hF' := by
  apply GrassmannianLinearAction.hom_ext K
  · simp only [Category.assoc, map_projection]
  · rw [GrassmannianLinearAction.pointClass_comp, pointClass_map, pointClass_map]
    exact Quotient.sound (.rel _ _ (presentation_pullback f F hF hF'))

def constantSL {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix.SpecialLinearGroup (Fin 3) Γ(T, ⊤) :=
  Matrix.SpecialLinearGroup.map (GrassmannianLinearAction.scalarMap K b) g

theorem constantSL_val {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (constantSL K b g).val = g.val.map (GrassmannianLinearAction.scalarMap K b) := rfl

/-- The literal inverse frame substitution over an arbitrary test scheme. -/
def inverseFrame {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (F : Mat3 Γ(T, ⊤)) : Mat3 Γ(T, ⊤) :=
  (constantSL K b g)⁻¹.val * F

theorem inverseFrame_det_unit {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    IsUnit (inverseFrame K b g F).det := by
  rw [inverseFrame, Matrix.det_mul, ((constantSL K b g)⁻¹).prop, one_mul]
  exact hF

theorem presentation_inverseFrame {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    (presentation T (inverseFrame K b g F) (inverseFrame_det_unit K b g F hF)).Isomorphic
      (GrassmannianLinearAction.transform K b (symmetricSquare g) (presentation T F hF)) := by
  refine ⟨Iso.refl _, ?_⟩
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  change Stacks.FreeSheafMatrix.toMatrix (sheafQuotient T (inverseFrame K b g F) ≫ 𝟙 _) =
    Stacks.FreeSheafMatrix.toMatrix
      ((GrassmannianLinearAction.constantFreeIso K b (symmetricSquare g)).hom ≫ sheafQuotient T F)
  rw [Category.comp_id, Stacks.FreeSheafMatrix.toMatrix_comp,
    GrassmannianLinearAction.constantFreeIso_matrix]
  simp only [sheafQuotient, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    inverseFrame, quotientMatrix_sl_inverse, GrassmannianLinearAction.constantMatrix,
    symmetricSquare_val, congruence_map, constantSL_val]

/-- Genuine conic pullback equivariance for the canonical constant SL₃ action.
On four-planes the native map sends S to g⁻¹S; on fields its pullback is the
original inverse frame substitution. -/
theorem map_inverseFrame {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    ConicFrame.map T K b (inverseFrame K b g F) (inverseFrame_det_unit K b g F hF) =
      ConicFrame.map T K b F hF ≫ GrassmannianLinearAction.action K (symmetricSquare g) := by
  apply GrassmannianLinearAction.hom_ext K
  · rw [Category.assoc, GrassmannianLinearAction.action_projection, map_projection, map_projection]
  · rw [GrassmannianLinearAction.pointClass_action, map_projection, pointClass_map, pointClass_map]
    exact Quotient.sound (.rel _ _ (presentation_inverseFrame K b g F hF))

end M9Native.ConicFrameLeftEquivariance
