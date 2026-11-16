module

public import M9StacksIntegration.LagrangianSectionCoefficientCovariance
public import M9StacksIntegration.LagrangianStandardSectionZeroModel
public import M9StacksIntegration.LagrangianTranslatedDeterminantCoordinates

/-!
# Actual constant symplectic transport of the original five-cut scheme

The new five-row matrix and its surjectivity are constructed from the
literal positive primitive matrix. The all-native-test equation
covariance constructs the actual curve isomorphism and retains the
original LG and structural maps. No action or fibre-isomorphism premise
is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
universe u

namespace M9Native.LagrangianFiveCutTransport

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianSigmaInvariance
open LagrangianSectionCoefficientCovariance LagrangianStandardSectionZeroModel
open IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]

/-- The actual transpose-convention LG automorphism and its actual inverse. -/
def actionIso (g : Matrix.symplecticGroup (Fin 3) K) : space K ≅ space K where
  hom := LagrangianSymplecticAction.action K (transposeSymplectic K g)
  inv := LagrangianSymplecticAction.action K (transposeSymplectic K g⁻¹)
  hom_inv_id := by
    rw [LagrangianSymplecticAction.action_mul,
      ← LagrangianTranslatedDeterminantCoordinates.transpose_mul,
      inv_mul_cancel, LagrangianTranslatedDeterminantCoordinates.transpose_one,
      LagrangianSymplecticAction.action_one]
  inv_hom_id := by
    rw [LagrangianSymplecticAction.action_mul,
      ← LagrangianTranslatedDeterminantCoordinates.transpose_mul,
      mul_inv_cancel, LagrangianTranslatedDeterminantCoordinates.transpose_one,
      LagrangianSymplecticAction.action_one]

@[reassoc] theorem actionIso_projection (g : Matrix.symplecticGroup (Fin 3) K) :
    (actionIso K g).hom ≫ projection K = projection K :=
  LagrangianSymplecticAction.action_projection K (transposeSymplectic K g)

theorem coefficientMatrix_inv_mul (g : Matrix.symplecticGroup (Fin 3) K) :
    coefficientMatrix K g⁻¹ * coefficientMatrix K g = 1 := by
  rw [← PrimitiveRingMatrices.matrix14_mul, inv_mul_cancel,
    PrimitiveRingMatrices.matrix14_one]

/-- The actual transformed original coefficient matrix. -/
def transformedMatrix (M : Matrix (Fin 5) (Fin 14) K)
    (g : Matrix.symplecticGroup (Fin 3) K) : Matrix (Fin 5) (Fin 14) K :=
  M * coefficientMatrix K g⁻¹

/-- Surjectivity follows from the proved genuine inverse primitive matrix. -/
theorem transformed_surjective (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (g : Matrix.symplecticGroup (Fin 3) K) :
    Function.Surjective (transformedMatrix K M g).mulVec := by
  intro y
  obtain ⟨x,hx⟩ := hM y
  refine ⟨coefficientMatrix K g *ᵥ x, ?_⟩
  change (M * coefficientMatrix K g⁻¹) *ᵥ (coefficientMatrix K g *ᵥ x) = y
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, coefficientMatrix_inv_mul, Matrix.mul_one, hx]

theorem transformed_row (M : Matrix (Fin 5) (Fin 14) K)
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 5) :
    coefficientRow K g⁻¹ (M j) = transformedMatrix K M g j := rfl

private theorem factors_comp_iso_iff {A B T : Scheme.{u}}
    (i : A ⟶ B) (e : B ≅ B) (t : T ⟶ B) :
    (∃ z : T ⟶ A, z ≫ (i ≫ e.hom) = t) ↔
      ∃ z : T ⟶ A, z ≫ i = t ≫ e.inv := by
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun a => a ≫ e.inv) hz
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun a => a ≫ e.hom) hz

private theorem factors_iff_detRows (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) {T : Scheme.{u}} (t : T ⟶ space K) :
    (∃ z : T ⟶ curve K M hM, z ≫ toLG K M hM = t) ↔
      ∀ j : Fin 5, pullbackGlobalSections t (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (M j)) = 0 := by
  simpa only [← LagrangianHyperplaneRows.determinantSection_row] using
    LagrangianGeometricFibre.geometricFibre_factorsThrough_iff_rows K M hM t

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (g : Matrix.symplecticGroup (Fin 3) K)

/-- The original source curve with its genuinely acted original LG immersion. -/
abbrev actedMap : curve K M hM ⟶ space K := toLG K M hM ≫ (actionIso K g).hom

instance actedMap_closed : IsClosedImmersion (actedMap K M hM g) := by
  dsimp only [actedMap]
  infer_instance

instance actedMapOver_mono : Mono (Over.mk (actedMap K M hM g)).hom := by
  change Mono (actedMap K M hM g)
  infer_instance

instance transformedMapOver_mono : Mono
    (Over.mk (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))).hom := by
  change Mono (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))
  infer_instance

/-- The acted original curve has precisely the actual transformed five
equations on every native test scheme. -/
theorem actedMap_factors_iff {T : Scheme.{u}} (t : T ⟶ space K) :
    (∃ z : T ⟶ curve K M hM, z ≫ actedMap K M hM g = t) ↔
      ∃ z : T ⟶ curve K (transformedMatrix K M g) (transformed_surjective K M hM g),
        z ≫ toLG K (transformedMatrix K M g) (transformed_surjective K M hM g) = t := by
  calc
    _ ↔ ∃ z : T ⟶ curve K M hM, z ≫ toLG K M hM = t ≫ (actionIso K g).inv :=
      factors_comp_iso_iff (toLG K M hM) (actionIso K g) t
    _ ↔ ∀ j : Fin 5, pullbackGlobalSections (t ≫ (actionIso K g).inv) (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (M j)) = 0 :=
      factors_iff_detRows K M hM _
    _ ↔ ∀ j : Fin 5, pullbackGlobalSections t (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (transformedMatrix K M g j)) = 0 := by
      apply forall_congr'
      intro j
      simpa only [actionIso, transformed_row] using
        pullback_action_zero_iff K t g⁻¹ (M j)
    _ ↔ _ := (factors_iff_detRows K (transformedMatrix K M g)
      (transformed_surjective K M hM g) t).symm

/-- The actual original five-cut transport isomorphism. -/
def cutIso : curve K M hM ≅
    curve K (transformedMatrix K M g) (transformed_surjective K M hM g) := by
  letI := transformedMapOver_mono K M hM g
  exact comparisonIso (Over.mk (actedMap K M hM g))
    (Over.mk (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))
      (fun _ t => actedMap_factors_iff K M hM g t)

@[reassoc] theorem cutIso_hom_toLG : (cutIso K M hM g).hom ≫
    toLG K (transformedMatrix K M g) (transformed_surjective K M hM g) =
      toLG K M hM ≫ (actionIso K g).hom := by
  letI := transformedMapOver_mono K M hM g
  exact comparisonIso_hom_comp (Over.mk (actedMap K M hM g))
    (Over.mk (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g)))
      (fun _ t => actedMap_factors_iff K M hM g t)

private theorem triangle_over {A B C S : Scheme.{u}}
    (e : A ⟶ B) (i : B ⟶ C) (j : A ⟶ C) (p : C ⟶ S)
    (b : B ⟶ S) (a : A ⟶ S) (h : e ≫ i = j) (hi : i ≫ p = b) (hj : j ≫ p = a) :
    e ≫ b = a := by rw [← hi, ← Category.assoc, h, hj]

/-- The transport retains the actual original structural field map. -/
theorem cutIso_hom_projection : (cutIso K M hM g).hom ≫
    curveProjection K (transformedMatrix K M g) (transformed_surjective K M hM g) =
      curveProjection K M hM := by
  have hj : (toLG K M hM ≫ (actionIso K g).hom) ≫ projection K = curveProjection K M hM :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun a => toLG K M hM ≫ a) (actionIso_projection K g)).trans
        (LagrangianOrderedFibre.geometricFibre_over K M hM))
  exact triangle_over (cutIso K M hM g).hom
    (toLG K (transformedMatrix K M g) (transformed_surjective K M hM g))
    (toLG K M hM ≫ (actionIso K g).hom) (projection K)
    (curveProjection K (transformedMatrix K M g) (transformed_surjective K M hM g))
    (curveProjection K M hM) (cutIso_hom_toLG K M hM g)
    (LagrangianOrderedFibre.geometricFibre_over K _ _) hj

end M9Native.LagrangianFiveCutTransport
