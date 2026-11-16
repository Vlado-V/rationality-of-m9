module

public import M9StacksIntegration.LagrangianPolynomialPluckerFrame
public import M9StacksIntegration.LagrangianPrimitiveSectionCovariance

/-! The original LG-to-polynomial-P13 triangle for the actual symplectic
action. The matrix is the literal primitive matrix of the transpose,
with the row convention of the native graded substitution. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.LagrangianPolynomialPluckerEquivariance

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerGeneration LagrangianPluckerEpimorphism LagrangianDeterminantSections
open LagrangianPrimitiveSectionCovariance LagrangianSymplecticAction
open LagrangianPolynomialPluckerFrame ProjectiveSectionFunctions
open Stacks.ProjectiveSpaceChartRatio PrimitiveRingMatrices LagrangianSigmaInvariance

variable (K : Type u) [Field K] [CharZero K]

abbrev polynomialPlucker := LagrangianPolynomialPluckerFrame.polynomialPlucker K

/-- Invertibility is derived from the actual exterior/primitive action,
without a matrix-invertibility premise. -/
def primitiveGL (g : Matrix.symplecticGroup (Fin 3) K) :
    Matrix.GeneralLinearGroup (Fin 14) K :=
  (matrix14_isUnit K K (RingHom.id K) (transposeSymplectic K g)).unit

@[simp] theorem primitiveGL_val (g : Matrix.symplecticGroup (Fin 3) K) :
    (primitiveGL K g).val = matrix14 K K (RingHom.id K) (transposeSymplectic K g) :=
  (matrix14_isUnit K K (RingHom.id K) (transposeSymplectic K g)).unit_spec

/-- The literal native pullback sends each original homogeneous
coordinate to the corresponding row of the raw transpose-action matrix. -/
theorem substitution_X_primitiveGL (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    NativeProjectiveLinear.substitution K 13 (primitiveGL K g).val (MvPolynomial.X j) =
      ∑ a : Fin 14, MvPolynomial.C
          (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) * MvPolynomial.X a := by
  rw [NativeProjectiveLinear.substitution_X,primitiveGL_val]

omit [CharZero K] in
/-- The actual base map is unchanged by the actual LG action. -/
theorem coefficientMap_action {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    baseRingHom ((f ≫ action K g) ≫ projection K) = baseRingHom (f ≫ projection K) := by
  rw [Category.assoc,action_projection]

/-- The true determinant action transports the true acted section tuple
to the raw matrix times the original tuple, in the same actual frame. -/
theorem framed_action_coordinates {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅ UnitLine T)
    (v : Fin 14 → Γ(T,⊤))
    (he : ∀ j, e.hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) = v j)
    (j : Fin 14) :
    ((LagrangianDeterminantAction.determinantActionIso K f g) ≪≫ e).hom.app ⊤
      (pullbackGlobalSections (f ≫ action K g) (determinantLine K) (primitiveSections K j)) =
      ((primitiveGL K g).val.map (baseRingHom (f ≫ projection K)) *ᵥ v) j := by
  change e.hom.app ⊤
    ((LagrangianDeterminantAction.determinantActionIso K f g).hom.app ⊤
      (pullbackGlobalSections (f ≫ action K g) (determinantLine K) (primitiveSections K j))) = _
  rw [determinantActionIso_primitive_covariance,map_sum,primitiveGL_val]
  change (∑ a : Fin 14, e.hom.app ⊤
      (LagrangianPlucker.coefficientMap K f
        (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) •
        pullbackGlobalSections f (determinantLine K) (primitiveSections K a))) = _
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Scheme.Modules.Hom.app_smul,he]
  rfl

/-- The actual raw invertible matrix preserves the unit-ideal condition
on every test-scheme coordinate ring, including nonreduced rings. -/
theorem span_primitiveGL_mulVec {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) (v : Fin 14 → Γ(T,⊤))
    (hv : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range ((primitiveGL K g).val.map (baseRingHom (f ≫ projection K)) *ᵥ v)) = ⊤ := by
  have hNM : ((primitiveGL K g)⁻¹).val.map (baseRingHom (f ≫ projection K)) *
      (primitiveGL K g).val.map (baseRingHom (f ≫ projection K)) = 1 := by
    rw [← Matrix.map_mul,Units.inv_mul]
    exact Matrix.map_one (baseRingHom (f ≫ projection K)) (map_zero _) (map_one _)
  exact (NativeProjectiveVector.span_mulVec_eq _ _ hNM v).trans hv

/-- The original LG embedding into polynomial P13 is equivariant for
the actual LG action and the actual raw transpose primitive matrix.
There is no equivariance triangle, scalar, or coordinate-change premise. -/
theorem action_polynomialPlucker (g : Matrix.symplecticGroup (Fin 3) K) :
    action K g ≫ polynomialPlucker K =
      polynomialPlucker K ≫ (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom := by
  apply (LagrangianPlucker.matrixCover K).hom_ext
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  let f := (LagrangianPlucker.matrixCover K).f ι
  let h := LagrangianPlucker.matrixChartIntegral K ι
  let hfg := LagrangianPlucker.matrixChartIntegral_diagram K ι
  let := matrixCover_chart_isAffine K ι
  let e := chartLineIso K f ι h hfg
  let v := LagrangianPlucker.chartCoordinates K f ι h
  have hv : Ideal.span (Set.range v) = ⊤ := LagrangianPlucker.chartCoordinates_span K f ι h hfg
  have he : ∀ j, e.hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) = v j :=
    chartLineIso_primitive K f ι h hfg
  let κ := baseRingHom (f ≫ projection K)
  let B := primitiveGL K g
  let w := B.val.map κ *ᵥ v
  have hw : Ideal.span (Set.range w) = ⊤ := span_primitiveGL_mulVec K f g v hv
  have hf := comp_polynomialPlucker_in_frame K f e v hv he
  have hfA := comp_polynomialPlucker_in_frame K (f ≫ action K g)
    ((LagrangianDeterminantAction.determinantActionIso K f g) ≪≫ e) w hw
    (framed_action_coordinates K f g e v he)
  rw [coefficientMap_action] at hfA
  change f ≫ (action K g ≫ polynomialPlucker K) =
    f ≫ (polynomialPlucker K ≫ (NativeProjectiveLinear.projectiveLinear K 13 B).hom)
  calc
    _ = (f ≫ action K g) ≫ polynomialPlucker K := (Category.assoc _ _ _).symm
    _ = NativeProjectiveVector.onScheme _ κ w hw := hfA
    _ = NativeProjectiveVector.onScheme _ κ v hv ≫
        (NativeProjectiveLinear.projectiveLinear K 13 B).hom :=
      NativeProjectiveVector.onScheme_linear _ κ v hv B hw
    _ = (f ≫ polynomialPlucker K) ≫ (NativeProjectiveLinear.projectiveLinear K 13 B).hom :=
      congrArg (fun a => a ≫ (NativeProjectiveLinear.projectiveLinear K 13 B).hom) hf.symm
    _ = _ := Category.assoc _ _ _

/-- Transposing the actual symplectic input recovers the untransposed
raw primitive matrix, without any basis conjugation. -/
theorem primitiveGL_transpose_val (g : Matrix.symplecticGroup (Fin 3) K) :
    (primitiveGL K (transposeSymplectic K g)).val = matrix14 K K (RingHom.id K) g := by
  rw [primitiveGL_val]
  congr 1

end M9Native.LagrangianPolynomialPluckerEquivariance
