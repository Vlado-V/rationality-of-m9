module

public import M9StacksIntegration.LagrangianIncidencePlaneIso
public import M9StacksIntegration.LagrangianParameterMatrix

/-! Original geometric incidence fibres in the conventional pullback
order, and every original rational parameter point, are actual LG/P8
scheme intersections. The maps to the original LG are retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixPointRows
open M9Native.LagrangianIncidencePlaneIso M9Native.LagrangianProjectiveSectionScheme
open M9Native.LagrangianProjectiveLinearForms M9Native.LagrangianSymmetricPlucker

universe u

namespace M9Native.LagrangianGeometricFibre

variable (K : Type u) [Field K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev geometricFibre : Scheme.{u} := pullback (familyProjection K) (matrixPoint K M hM)

abbrev geometricFibreToLG : geometricFibre K M hM ⟶ LagrangianGrassmannian.space K :=
  pullback.fst (familyProjection K) (matrixPoint K M hM) ≫ familyToLG K

def geometricFibreIsoSection : geometricFibre K M hM ≅ sectionScheme K M.mulVecLin :=
  pullbackSymmetry (familyProjection K) (matrixPoint K M hM) ≪≫ fibreIsoSection K M hM

@[reassoc]
theorem geometricFibreIsoSection_hom_toLG :
    (geometricFibreIsoSection K M hM).hom ≫ sectionToLG K M.mulVecLin =
      geometricFibreToLG K M hM := by
  simp only [geometricFibreIsoSection, Iso.trans_hom, Category.assoc,
    fibreIsoSection_hom_toLG, originalFibreToLG, LagrangianFibreFactorization.fibreToLG,
    pullbackSymmetry_hom_comp_snd_assoc]

theorem geometricFibre_factorsThrough_iff_rows {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    (∃ z : T ⟶ geometricFibre K M hM, z ≫ geometricFibreToLG K M hM = l) ↔
      ∀ j : Fin 5, pullbackGlobalSections l (LagrangianPluckerQuotient.determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) = 0 := by
  rw [← originalFibre_factorsThrough_iff_rows K M hM l]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ (pullbackSymmetry (familyProjection K) (matrixPoint K M hM)).hom, ?_⟩
    simpa only [originalFibreToLG, LagrangianFibreFactorization.fibreToLG,
      geometricFibreToLG, Category.assoc, pullbackSymmetry_hom_comp_snd_assoc] using hz
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ (pullbackSymmetry (familyProjection K) (matrixPoint K M hM)).inv, ?_⟩
    simpa only [originalFibreToLG, LagrangianFibreFactorization.fibreToLG,
      geometricFibreToLG, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc] using hz

/-- No matrix-class hypothesis is needed for an actual original rational
parameter point: its surjective matrix and true scheme isomorphism exist. -/
theorem every_parameter_fibre (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _) :
    ∃ (M : Matrix (Fin 5) (Fin 14) K) (_hM : Function.Surjective M.mulVec)
      (e : pullback (familyProjection K) p ≅ sectionScheme K M.mulVecLin),
      e.hom ≫ sectionToLG K M.mulVecLin = pullback.fst (familyProjection K) p ≫ familyToLG K := by
  obtain ⟨M, hM, rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact ⟨M, hM, geometricFibreIsoSection K M hM, geometricFibreIsoSection_hom_toLG K M hM⟩

end M9Native.LagrangianGeometricFibre
