module

public import M9StacksIntegration.LagrangianFibreFiveSection
public import M9StacksIntegration.LagrangianRowDifferential
public import M9StacksIntegration.LagrangianHyperplaneCoordinates

/-!
# The original five-section retains the original five defining rows

The original fixedEquationIso and fixedLineIso are evaluated on the
actual original incidence section, not on a supplied row presentation.
This identifies the actual fiveSection(M) with the actual tensor of its
original primitive14 sections and original five-by-fourteen matrix.
These are the defining five equations, distinct from the common-kernel
five-minors system.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianFixedEquationRows

/-- Original global section pullback is the actual adjunction unit on the terminal open. -/
theorem pullbackGlobalSections_eq_unit {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (s : Γ(L,⊤)) :
    pullbackGlobalSections f L s =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op ⊤)) s := by
  change ((Scheme.Modules.pullback f).obj L).presheaf.map
    (eqToHom (show f ⁻¹ᵁ (⊤ : X.Opens) = ⊤ from rfl)).op _ = _
  exact CategoryTheory.Functor.map_id_apply _ _ _

/-- The actual canonical identity pullback comparison retains the original section.
The unit-conjugation argument is the pinned native proof of
SeparatingPointsTangentVectors.Basic.pullbackSectionTop_id. -/
theorem pullbackGlobalSections_id {X : Scheme.{u}} (L : X.Modules) (s : Γ(L,⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app L).app ⊤
      (pullbackGlobalSections (𝟙 X) L s) = s := by
  rw [pullbackGlobalSections_eq_unit]
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom L
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact congr($(h).val.app (op ⊤) s).symm

open LagrangianFibreFiveSection LagrangianMatrixChart LagrangianGrassmannian
open LagrangianLinearSections LagrangianPluckerQuotient LagrangianParameterRowComparison
open LinearIncidenceTensorCoordinates

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- The actual fixed line comparison retains each original primitive section. -/
theorem fixedLineIso_section (j : Fin 14) :
    (fixedLineIso K M hM).hom.app ⊤
      (pullbackGlobalSections (fixedMap K M hM) (lineBundle K) (lineSection K j)) =
        primitiveSections K j := by
  have hc := lineComparison_section K (fixedMap K M hM) j
  have hn := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr
    (fixedMap_toLG K M hM) (determinantLine K) (primitiveSections K j)
  have h := (congrArg (fun z =>
    (((Scheme.Modules.pullbackId (space K)).app (determinantLine K)).hom.app ⊤)
      ((((Scheme.Modules.pullbackCongr (fixedMap_toLG K M hM)).app
        (determinantLine K)).hom.app ⊤) z)) hc).trans
    ((congrArg (((Scheme.Modules.pullbackId (space K)).app (determinantLine K)).hom.app ⊤)
      hn).trans (pullbackGlobalSections_id _ _))
  simpa only [fixedLineIso, Iso.trans_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, CategoryTheory.Functor.id_obj] using h

/-- The chosen actual quotient frame has the original literal matrix map, by its genuine producer. -/
theorem fixedQuotientIso_map :
    (Grassmannian.pullbackPresentation (fixedMap K M hM) (ambientQuotient K)).map ≫
      (fixedQuotientIso K M hM).hom =
      Stacks.FreeSheafMatrix.ofMatrix (M.map (scalarMap K (projection K))) := by
  have h := (LagrangianMatrixPointRows.quotientFrame K (fixedMap K M hM) M hM
    (fixedMap_parameter_condition K M hM)).choose_spec
  simpa only [fixedQuotientIso, fixedMap_toLG, Category.id_comp] using h

/-- Both actual fixed tensor comparisons act on actual decomposable sections by their original maps. -/
theorem fixedEquationIso_tensorTop (s : Γ(lineBundle K,⊤)) (t : Γ(quotientFive K,⊤)) :
    (fixedEquationIso K M hM).hom.app ⊤
      (pullbackGlobalSections (fixedMap K M hM) (LagrangianLinearSections.equationBundle K)
        (tensorTop (ambient K) (lineBundle K) (quotientFive K) s t)) =
      tensorTop (space K) (determinantLine K) (freeOn (space K) 5)
        ((fixedLineIso K M hM).hom.app ⊤
          (pullbackGlobalSections (fixedMap K M hM) (lineBundle K) s))
        ((fixedQuotientIso K M hM).hom.app ⊤
          (pullbackGlobalSections (fixedMap K M hM) (quotientFive K) t)) := by
  refine (congrArg (fun z =>
    (Stacks.SheafOfModules.Invertible.tensorProductIso (space K).sheaf.obj
      (space K).ringCatSheaf.2 (fixedLineIso K M hM) (fixedQuotientIso K M hM)).hom.val.app
        (op ⊤) z)
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt
      (fixedMap K M hM) (lineBundle K) (quotientFive K) s t)).trans ?_
  exact Stacks.SheafOfModules.tensorSections_tensorProductIsoAt (space K).sheaf.obj
    (space K).ringCatSheaf.2 (op ⊤) _ _ _ _ (fixedLineIso K M hM) (fixedQuotientIso K M hM)
      (pullbackGlobalSections (fixedMap K M hM) (lineBundle K) s)
      (pullbackGlobalSections (fixedMap K M hM) (quotientFive K) t)

/-- The actual original fixed five-section is the original tensor of its original fourteen sections and rows. -/
theorem fiveSection_eq_rowTensor :
    fiveSection K M hM =
      TensorFreeCoordinates.rowTensor (space K) (determinantLine K) 5
        (Stacks.FreeSheafMatrix.ofMatrix (M.map (scalarMap K (projection K))))
        (primitiveSections K) := by
  simp only [fiveSection, LagrangianLinearSections.equationSection, map_sum, TensorFreeCoordinates.rowTensor]
  apply Finset.sum_congr rfl
  intro j _
  rw [LagrangianLinearSectionEquations.tensorSection_eq_tensorTop, fixedEquationIso_tensorTop,
    fixedLineIso_section]
  exact congrArg (tensorTop (space K) (determinantLine K) (freeOn (space K) 5)
    (primitiveSections K j))
      (LagrangianLinearSectionEquations.quotientSection_pullback K (fixedMap K M hM)
        (fixedQuotientIso K M hM) _ (fixedQuotientIso_map K M hM) j)


/-- Original field scalars on the terminal open retain the literal original structural ring map. -/
theorem baseRingToSections_top_eq_scalarMap {T : Scheme.{u}}
    (f : T ⟶ Spec (.of K)) (a : K) :
    (show Γ(T,⊤) from baseRingToSections K (Over.mk f) (op ⊤) a) = scalarMap K f a := by
  change ((T.ringCatSheaf.obj.map (𝟙 (op (⊤ : T.Opens)))).hom
    (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom a)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The original universal coefficient convention is the original structural field map. -/
theorem scalarMap_projection_eq_coefficientMap :
    scalarMap K (projection K) = LagrangianHyperplaneCoordinates.coefficientMap K := by
  change _ = ((Scheme.ΓSpecIso (.of K)).inv ≫ (𝟙 (space K) ≫ projection K).appTop).hom
  rw [Category.id_comp]
  rfl

/-- The actual original five-section row value is precisely the original hyperplane with row coefficients a*M. -/
theorem rowProjection_fiveSection (a : Fin 5 → K) :
    (LagrangianRowDifferential.rowProjection K a).app ⊤ (fiveSection K M hM) =
      LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M) := by
  rw [fiveSection_eq_rowTensor, LagrangianRowDifferential.rowProjection,
    TensorFreeRowProjection.row_rowTensor]
  simp only [Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Matrix.map_apply,
    baseRingToSections_top_eq_scalarMap, scalarMap_projection_eq_coefficientMap]
  simp only [LagrangianHyperplaneCoordinates.determinantSection, Matrix.vecMul, dotProduct,
    map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

end M9Native.LagrangianFixedEquationRows
