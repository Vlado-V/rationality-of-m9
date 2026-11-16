module

public import M9StacksIntegration.LagrangianMatrixPointRows
public import M9StacksIntegration.LagrangianFibreFactorization

/-! The original incidence fibre is the actual scheme intersection of
the original Lagrangian Grassmannian with its genuine quotient P8.
The comparison follows from proved factorization properties on every
test scheme and retains the original LG and base maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixPointRows
open M9Native.LagrangianFibreFactorization M9Native.LagrangianProjectiveSectionScheme
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianSymmetricPlucker M9Native.IteratedLineSectionCuts

universe u

namespace M9Native.LagrangianIncidencePlaneIso

variable (K : Type u) [Field K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev originalFibre : Scheme.{u} := fibre K (matrixPoint K M hM)

abbrev originalFibreToLG : originalFibre K M hM ⟶ LagrangianGrassmannian.space K :=
  fibreToLG K (matrixPoint K M hM)

instance originalFibreToLG_mono : Mono (originalFibreToLG K M hM) :=
  fibreToLG_mono K (matrixPoint K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM)

theorem originalFibre_factorsThrough_iff_rows {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    (∃ z : T ⟶ originalFibre K M hM, z ≫ originalFibreToLG K M hM = l) ↔
      ∀ j : Fin 5, pullbackGlobalSections l (LagrangianPluckerQuotient.determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) = 0 := by
  let p := matrixPoint K M hM
  have hp : p ≫ parameterProjection K = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM
  rw [fibre_factorsThrough_iff K p hp l]
  have hf : fixedAmbient K p hp l ≫ toParameter K =
      ((fixedAmbient K p hp l ≫ toLG K) ≫ LagrangianGrassmannian.projection K) ≫
        matrixPoint K M hM := by
    rw [LagrangianFibreFactorization.fixedAmbient_toParameter K p hp l,
      LagrangianFibreFactorization.fixedAmbient_toLG K p hp l]
  have h := LagrangianMatrixPointRows.factorsThrough_iff_original_rows K
    (fixedAmbient K p hp l) M hM hf
  rw [LagrangianFibreFactorization.fixedAmbient_toLG K p hp l] at h
  exact h

theorem originalFibre_section_factorizations {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    (∃ z : T ⟶ originalFibre K M hM, z ≫ originalFibreToLG K M hM = l) ↔
      (∃ z : T ⟶ sectionScheme K M.mulVecLin, z ≫ sectionToLG K M.mulVecLin = l) := by
  rw [originalFibre_factorsThrough_iff_rows, section_factorsThrough_iff,
    LagrangianSymmetricSectionsPullback.originalPlucker_factorsThrough_iff]

/-- The actual original fibre is isomorphic to the actual native closed
projective-plane intersection, including its nilpotent scheme structure. -/
def fibreIsoSection : originalFibre K M hM ≅ sectionScheme K M.mulVecLin := by
  let A : Over (LagrangianGrassmannian.space K) := Over.mk (originalFibreToLG K M hM)
  let B : Over (LagrangianGrassmannian.space K) := Over.mk (sectionToLG K M.mulVecLin)
  have hp : matrixPoint K M hM ≫ parameterProjection K = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM
  let : Mono A.hom := fibreToLG_mono K (matrixPoint K M hM) hp
  let : Mono B.hom := by
    change Mono (sectionToLG K M.mulVecLin)
    infer_instance
  exact comparisonIso A B (fun T l => originalFibre_section_factorizations K M hM l)

@[reassoc]
theorem fibreIsoSection_hom_toLG :
    (fibreIsoSection K M hM).hom ≫ sectionToLG K M.mulVecLin = originalFibreToLG K M hM := by
  exact comparisonHom_comp (Over.mk (originalFibreToLG K M hM))
    (Over.mk (sectionToLG K M.mulVecLin))
    (fun T l => originalFibre_section_factorizations K M hM l)

@[reassoc]
theorem fibreIsoSection_inv_toLG :
    (fibreIsoSection K M hM).inv ≫ originalFibreToLG K M hM = sectionToLG K M.mulVecLin := by
  exact comparisonHom_comp (Over.mk (sectionToLG K M.mulVecLin))
    (Over.mk (originalFibreToLG K M hM))
    (fun T l => (originalFibre_section_factorizations K M hM l).symm)

theorem originalFibreToLG_isClosedImmersion : IsClosedImmersion (originalFibreToLG K M hM) := by
  rw [← fibreIsoSection_hom_toLG K M hM]
  infer_instance

theorem fibreIsoSection_hom_base :
    (fibreIsoSection K M hM).hom ≫ sectionToLG K M.mulVecLin ≫
      LagrangianGrassmannian.projection K =
        pullback.fst (matrixPoint K M hM) (familyProjection K) := by
  rw [fibreIsoSection_hom_toLG_assoc]
  exact (fibre_base K (matrixPoint K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM)).symm

/-- The quotient plane is genuinely native P8, by its derived rank. -/
def planeEightIso : projectiveSpaceOverRing 8 (.of K) ≅ plane K M.mulVecLin :=
  planeIsoProjectiveEight K M.mulVecLin hM

theorem originalFibre_dimension_ge_one :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim (originalFibre K M hM) := by
  have he := (fibreIsoSection K M hM).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq _
  exact (sectionScheme_dimension_ge_one K M.mulVecLin hM).trans_eq he.symm

end M9Native.LagrangianIncidencePlaneIso
