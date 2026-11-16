module

public import M9StacksIntegration.PrimitiveRhoOrbit
public import M9StacksIntegration.NativeProjectiveVectorChart

/-! Dominance of the genuine symplectic fixed-rho orbit morphism.
The actual thirteen-parameter family factors through it as scheme morphisms. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory Matrix

namespace M9Native.PrimitiveRhoOrbitDominance

open PrimitiveGaussCoordinates PrimitiveGaussNativeOrbit PrimitiveGaussOrbitVector
open NativeProjectiveVector PrimitiveRhoOrbit

abbrev R := sourceRing ℂ

def normalVector : Fin 14 → R := Fin.cons 1 (sourceCoordinate ℂ)

theorem normalVector_span : Ideal.span (Set.range normalVector) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one

def changedVector : Fin 14 → R :=
  coordinateMatrix.val.map (algebraMap ℂ R) *ᵥ normalVector

theorem changedVector_span : Ideal.span (Set.range changedVector) = ⊤ := by
  rw [changedVector, span_mulVec_eq _ ((coordinateMatrix⁻¹).val.map (algebraMap ℂ R))]
  · exact normalVector_span
  · rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem polynomialTuple_scaled :
    (algebraMap (polynomial ℂ) R ∘ polynomialTuple) =
      algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) • normalVector := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) =
      algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) * 1
    exact (mul_one _).symm
  · change algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalTarget ℂ j) =
      algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) *
        (inverseA ℂ * algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalTarget ℂ j))
    rw [← mul_assoc, mul_comm _ (inverseA ℂ), inverseA_mul, one_mul]

theorem polynomialVector_scaled :
    (algebraMap (polynomial ℂ) R ∘ polynomialVector) =
      algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) • changedVector := by
  have hm : (coordinateMatrix.val.map MvPolynomial.C).map (algebraMap (polynomial ℂ) R) =
      coordinateMatrix.val.map (algebraMap ℂ R) := by
    ext i j
    exact (IsScalarTower.algebraMap_apply ℂ (polynomial ℂ) R _).symm
  funext i
  change algebraMap (polynomial ℂ) R ((coordinateMatrix.val.map MvPolynomial.C *ᵥ polynomialTuple) i) = _
  rw [RingHom.map_mulVec, hm, polynomialTuple_scaled, Matrix.mulVec_smul]
  rfl

theorem polynomialVector_span :
    Ideal.span (Set.range (algebraMap (polynomial ℂ) R ∘ polynomialVector)) = ⊤ := by
  rw [polynomialVector_scaled]
  change Ideal.span (Set.range fun i =>
    algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ) * changedVector i) = ⊤
  rw [← (formalA_unit ℂ).unit_spec, span_unit_mul_eq]
  exact changedVector_span

theorem nativeMap_eq_changed_point : orbitMap =
    point (algebraMap ℂ R) changedVector changedVector_span := by
  have hn := NativeProjectiveVectorChart.normalized_point (sourceCoordinate ℂ) normalVector_span
  have hl := point_linear (algebraMap ℂ R) normalVector normalVector_span
    coordinateMatrix changedVector_span
  change (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (sourceCoordinate ℂ)).toRingHom) ≫
    naturalChart) ≫ (NativeProjectiveLinear.projectiveLinear ℂ 13 coordinateMatrix).hom = _
  rw [← hn]
  exact hl.symm

theorem polynomialPoint_eq_nativeMap :
    point (algebraMap ℂ R) (algebraMap (polynomial ℂ) R ∘ polynomialVector)
      polynomialVector_span = orbitMap := by
  let u : Rˣ := (formalA_unit ℂ).unit
  have hv : (algebraMap (polynomial ℂ) R ∘ polynomialVector) =
      fun i => (u : R) * changedVector i := by
    rw [polynomialVector_scaled]
    funext i
    rw [show (u : R) = algebraMap (polynomial ℂ) R (M9.PrimitiveOpenOrbit.formalA ℂ)
      from (formalA_unit ℂ).unit_spec]
    rfl
  have hu : Ideal.span (Set.range fun i => (u : R)*changedVector i) = ⊤ := by
    rw [span_unit_mul_eq]
    exact changedVector_span
  rw [point_congr (algebraMap ℂ R) hv polynomialVector_span hu,
    point_scale _ _ changedVector_span u hu, nativeMap_eq_changed_point]

theorem polynomialPoint_eq_orbit_point :
    point (algebraMap ℂ R) (algebraMap (polynomial ℂ) R ∘ polynomialVector)
      polynomialVector_span = point (algebraMap ℂ R) orbitVector orbitVector_span := by
  let u : Rˣ := PrimitiveGaussFamily.parameter ℂ ^ 3
  have hv : (algebraMap (polynomial ℂ) R ∘ polynomialVector) =
      fun i => (u : R) * orbitVector i := by
    change (fun i => algebraMap (polynomial ℂ) R (polynomialVector i)) = _
    rw [polynomialVector_eq_scaled_orbitVector]
    funext i
    simp only [u, Units.val_pow_eq_pow_val, PrimitiveGaussFamily.parameter_val,
      Pi.smul_apply, smul_eq_mul]
  have hu : Ideal.span (Set.range fun i => (u : R)*orbitVector i) = ⊤ := by
    rw [span_unit_mul_eq]
    exact orbitVector_span
  rw [point_congr (algebraMap ℂ R) hv polynomialVector_span hu,
    point_scale _ _ orbitVector_span u hu]

/-- Genuine factorization through the universal fixed-rho group-scheme orbit morphism. -/
theorem gaussFamily_factorization :
    PrimitiveGaussNativeOrbit.orbitMap =
      PrimitiveGaussGroupScheme.gaussFamily.left ≫ PrimitiveRhoOrbit.orbitMorphism := by
  rw [gauss_pullback, ← polynomialPoint_eq_orbit_point, polynomialPoint_eq_nativeMap]

/-- The actual native symplectic orbit of rho is dominant in native P13. -/
instance orbitMorphism_isDominant : IsDominant PrimitiveRhoOrbit.orbitMorphism := by
  constructor
  have hr : Set.range PrimitiveGaussNativeOrbit.orbitMap ⊆
      Set.range PrimitiveRhoOrbit.orbitMorphism := by
    rw [gaussFamily_factorization]
    change Set.range (PrimitiveRhoOrbit.orbitMorphism ∘
      PrimitiveGaussGroupScheme.gaussFamily.left) ⊆ Set.range PrimitiveRhoOrbit.orbitMorphism
    exact Set.range_comp_subset_range _ _
  intro x
  exact closure_mono hr (PrimitiveGaussNativeOrbit.orbitMap_dense x)

theorem orbitMorphism_dense : DenseRange PrimitiveRhoOrbit.orbitMorphism :=
  PrimitiveRhoOrbit.orbitMorphism.denseRange

/-- The orbit morphism has the original complex structure map. -/
@[reassoc] theorem orbitMorphism_over :
    PrimitiveRhoOrbit.orbitMorphism ≫ M9.ProjectiveFunctionField.projection 13 =
      PrimitiveRhoOrbit.groupObject.hom := by
  change Proj.fromOfGlobalSections
      (M9.ProjectiveGeometry.ProjectiveSpace.projectiveGrading 13)
      (vectorMap (coefficient groupObject) (vector groupObject (𝟙 groupObject))) _ ≫
    (Proj.toSpecZero (M9.ProjectiveGeometry.ProjectiveSpace.projectiveGrading 13) ≫
      Spec.map (CommRingCat.ofHom
        (M9.ProjectiveGeometry.ProjectiveSpace.degreeZeroConstants 13).toRingHom)) = _
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp]
  have hc : CommRingCat.ofHom
        (M9.ProjectiveGeometry.ProjectiveSpace.degreeZeroConstants 13).toRingHom ≫
      CommRingCat.ofHom ((vectorMap (coefficient groupObject) (vector groupObject (𝟙 groupObject))).comp
        (algebraMap
          ((M9.ProjectiveGeometry.ProjectiveSpace.projectiveGrading 13) 0)
          (M9.ProjectiveGeometry.ProjectiveSpace.homogeneousCoordinateRing 13))) =
      CommRingCat.ofHom (coefficient groupObject) := by
    apply CommRingCat.hom_ext
    ext c
    change vectorMap (coefficient groupObject) (vector groupObject (𝟙 groupObject))
      (MvPolynomial.C c) = coefficient groupObject c
    simp [vectorMap]
  rw [hc, coefficient, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  change (groupObject.left.toSpecΓ ≫ Spec.map groupObject.hom.appTop) ≫
    Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv = _
  rw [← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end M9Native.PrimitiveRhoOrbitDominance
