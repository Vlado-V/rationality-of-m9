module

public import M9StacksIntegration.LagrangianParameterCoordinates
public import M9StacksIntegration.LagrangianDeterminantAction
public import M9StacksIntegration.LagrangianTranslatedDeterminantCoordinates
public import M9StacksIntegration.FiniteFreeBasisPullback
public import M9StacksIntegration.LinearIncidenceTensorCovariance
public import M9StacksIntegration.LagrangianLinearSectionEquations
public import M9StacksIntegration.LagrangianPrimitiveSectionCovariance

@[expose] public section

/-! The original universal LG linear-section family, with simultaneous
raw-parameter and LG changes in their literal original coordinate conventions.
The scheme action is derived from the actual equations and quotient triangles.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Opposite
open scoped BigOperators
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianRawFamilyAction

open AlgebraicGeometry.Grassmannian
open LagrangianLinearSections LagrangianParameterCoordinates
open LagrangianSigmaInvariance LagrangianMatrixChart

/-- The actual raw exterior units retain the multiplication of Sp6. -/
theorem rawUnit_mul (g h : Sp6) : rawUnit (g * h) = rawUnit g * rawUnit h := by
  apply Units.ext
  exact PrimitiveRingMatrices.matrix14_mul ℂ ℂ (RingHom.id ℂ) g h

theorem rawUnit_one : rawUnit (1 : Sp6) = 1 := by
  apply Units.ext
  exact PrimitiveRingMatrices.matrix14_one ℂ ℂ (RingHom.id ℂ)

theorem rawAction_one : rawAction (1 : Sp6) = 𝟙 (parameter ℂ) := by
  rw [rawAction, inv_one, rawUnit_one, LagrangianParameterLinearAction.action_one]

/-- The raw parameter action has the same order as the frozen original left
kernel action, established on the actual scheme morphisms. -/
theorem rawAction_mul (g h : Sp6) : rawAction g ≫ rawAction h = rawAction (h * g) := by
  rw [rawAction, rawAction, LagrangianParameterLinearAction.action_mul, rawAction,
    _root_.mul_inv_rev, rawUnit_mul]

/-- The actual simultaneous morphism on the original product. Its LG factor
is the transpose action forced by the determinant-section coordinates. -/
def ambientAction (g : Sp6) : ambient ℂ ⟶ ambient ℂ :=
  pullback.lift
    (toLG ℂ ≫ LagrangianSymplecticAction.action ℂ (transposeSymplectic ℂ g))
    (toParameter ℂ ≫ rawAction g)
    (by rw [Category.assoc, LagrangianSymplecticAction.action_projection,
      Category.assoc, rawAction_projection]; exact ambient_over ℂ)

@[reassoc] theorem ambientAction_toLG (g : Sp6) :
    ambientAction g ≫ toLG ℂ =
      toLG ℂ ≫ LagrangianSymplecticAction.action ℂ (transposeSymplectic ℂ g) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem ambientAction_toParameter (g : Sp6) :
    ambientAction g ≫ toParameter ℂ = toParameter ℂ ≫ rawAction g :=
  pullback.lift_snd _ _ _

theorem ambientAction_one : ambientAction (1 : Sp6) = 𝟙 (ambient ℂ) := by
  apply pullback.hom_ext
  · rw [ambientAction_toLG, LagrangianTranslatedDeterminantCoordinates.transpose_one,
      LagrangianSymplecticAction.action_one, Category.comp_id, Category.id_comp]
  · rw [ambientAction_toParameter, rawAction_one, Category.comp_id, Category.id_comp]

theorem ambientAction_mul (g h : Sp6) :
    ambientAction g ≫ ambientAction h = ambientAction (h * g) := by
  apply pullback.hom_ext
  · rw [Category.assoc, ambientAction_toLG, ← Category.assoc, ambientAction_toLG,
      Category.assoc, LagrangianSymplecticAction.action_mul, ambientAction_toLG,
      LagrangianTranslatedDeterminantCoordinates.transpose_mul]
  · rw [Category.assoc, ambientAction_toParameter, ← Category.assoc,
      ambientAction_toParameter, Category.assoc, rawAction_mul, ambientAction_toParameter]

/-- The simultaneous change on the actual ambient product is an honest scheme
isomorphism; its inverse is the actual inverse group element. -/
def ambientIso (g : Sp6) : ambient ℂ ≅ ambient ℂ where
  hom := ambientAction g
  inv := ambientAction g⁻¹
  hom_inv_id := by rw [ambientAction_mul, inv_mul_cancel, ambientAction_one]
  inv_hom_id := by rw [ambientAction_mul, mul_inv_cancel, ambientAction_one]

/-- The raw acted quotient is literally isomorphic to inverse coefficient
precomposition of the original universal parameter quotient on every test. -/
theorem raw_pullback_isomorphic {T : Scheme}
    (p : T ⟶ parameter ℂ) (g : Sp6) :
    (pullbackPresentation (p ≫ rawAction g) (parameterQuotient ℂ)).Isomorphic
      (LagrangianParameterLinearAction.transform ℂ
        (p ≫ parameterProjection ℂ) (rawUnit g⁻¹)
        (pullbackPresentation p (parameterQuotient ℂ))) := by
  apply LagrangianGrassmannian.presentation_isomorphic_of_class_eq
  change (⟦pullbackPresentation (p ≫ rawAction g) (parameterQuotient ℂ)⟧ : Points T 9 14) =
    LagrangianParameterLinearAction.transformPoints ℂ
      (p ≫ parameterProjection ℂ) (rawUnit g⁻¹)
      (⟦pullbackPresentation p (parameterQuotient ℂ)⟧ : Points T 9 14)
  rw [LagrangianLinearSectionQuotientCharts.pullback_parameter_class,
    LagrangianLinearSectionQuotientCharts.pullback_parameter_class]
  exact LagrangianParameterLinearAction.pointClass_action ℂ p (rawUnit g⁻¹)

/-- The actual determinant line on the product is transported through the
actual composite maps and the original determinant action. -/
def lineActionIso (g : Sp6) :
    (Scheme.Modules.pullback (ambientAction g)).obj (lineBundle ℂ) ≅ lineBundle ℂ :=
  (Scheme.Modules.pullbackComp (ambientAction g) (toLG ℂ)).app
      (LagrangianPluckerQuotient.determinantLine ℂ) ≪≫
    (Scheme.Modules.pullbackCongr (ambientAction_toLG g)).app
      (LagrangianPluckerQuotient.determinantLine ℂ) ≪≫
    LagrangianDeterminantAction.determinantActionIso ℂ (toLG ℂ) (transposeSymplectic ℂ g)

/-- The actual ambient universal quotient, not an abstract replacement,
is inverse coefficient precomposition with its actual target triangle. -/
theorem ambientQuotient_acted_isomorphic (g : Sp6) :
    (pullbackPresentation (ambientAction g) (ambientQuotient ℂ)).Isomorphic
      (LagrangianParameterLinearAction.transform ℂ
        (toParameter ℂ ≫ parameterProjection ℂ) (rawUnit g⁻¹) (ambientQuotient ℂ)) := by
  have hc : (pullbackPresentation (ambientAction g) (ambientQuotient ℂ)).Isomorphic
      (pullbackPresentation (toParameter ℂ ≫ rawAction g) (parameterQuotient ℂ)) := by
    simpa only [ambientAction_toParameter] using
      (LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
        (toParameter ℂ) (ambientAction g) (parameterQuotient ℂ))
  obtain ⟨e₀, h₀⟩ := hc
  obtain ⟨e₁, h₁⟩ := raw_pullback_isomorphic (toParameter ℂ) g
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, h₀, h₁]

/-- The native quotient comparison supplied by the actual representing functor. -/
def quotientActionIso (g : Sp6) :
    (Scheme.Modules.pullback (ambientAction g)).obj (quotientFive ℂ) ≅ quotientFive ℂ :=
  Classical.choose (ambientQuotient_acted_isomorphic g)

theorem quotientActionIso_triangle (g : Sp6) :
    (pullbackPresentation (ambientAction g) (ambientQuotient ℂ)).map ≫
        (quotientActionIso g).hom =
      (LagrangianParameterLinearAction.constantFreeIso ℂ
        (toParameter ℂ ≫ parameterProjection ℂ) (rawUnit g⁻¹)).hom ≫
          (ambientQuotient ℂ).map :=
  Classical.choose_spec (ambientQuotient_acted_isomorphic g)

/-- The original ambient structural coefficient map. -/
def ambientScalarMap : ℂ →+* Γ(ambient ℂ, ⊤) :=
  LagrangianParameterLinearAction.scalarMap ℂ (toParameter ℂ ≫ parameterProjection ℂ)

theorem ambientScalarMap_eq_coefficientMap :
    ambientScalarMap = LagrangianPlucker.coefficientMap ℂ (toLG ℂ) := by
  change LagrangianParameterLinearAction.scalarMap ℂ
      (toParameter ℂ ≫ parameterProjection ℂ) =
    LagrangianParameterLinearAction.scalarMap ℂ
      (toLG ℂ ≫ LagrangianGrassmannian.projection ℂ)
  rw [ambient_over]

/-- The raw primitive matrix extended along the actual ambient structure map. -/
def coefficientMatrix (g : Sp6) : Matrix (Fin 14) (Fin 14) Γ(ambient ℂ, ⊤) :=
  (rawUnit g).val.map ambientScalarMap

attribute [local implicit_reducible] coefficientMatrix

theorem coefficientMatrix_inv_mul (g : Sp6) : coefficientMatrix g⁻¹ * coefficientMatrix g = 1 := by
  change (PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g⁻¹).map ambientScalarMap *
    (PrimitiveRingMatrices.matrix14 ℂ ℂ (RingHom.id ℂ) g).map ambientScalarMap = 1
  rw [← Matrix.map_mul, ← PrimitiveRingMatrices.matrix14_mul, inv_mul_cancel,
    PrimitiveRingMatrices.matrix14_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Genuine all-test determinant covariance, specialized to the exact original
ambient product and the actual transpose LG action. -/
theorem lineActionIso_section (g : Sp6) (i : Fin 14) :
    (lineActionIso g).hom.app ⊤
      (pullbackGlobalSections (ambientAction g) (lineBundle ℂ) (lineSection ℂ i)) =
    ∑ j : Fin 14, coefficientMatrix g i j • lineSection ℂ j := by
  let L := LagrangianPluckerQuotient.determinantLine ℂ
  let σ := LagrangianPluckerQuotient.primitiveSections ℂ i
  have hc := SectionsEqualizer.pullbackGlobalSections_comp (ambientAction g) (toLG ℂ) L σ
  have hn := SectionsEqualizer.pullbackGlobalSections_congr (ambientAction_toLG g) L σ
  have hcov := LagrangianPrimitiveSectionCovariance.determinantActionIso_transpose_primitive_covariance
    ℂ (toLG ℂ) g i
  rw [← ambientScalarMap_eq_coefficientMap] at hcov
  change (LagrangianDeterminantAction.determinantActionIso ℂ (toLG ℂ)
      (transposeSymplectic ℂ g)).hom.app ⊤
      (pullbackGlobalSections (toLG ℂ ≫ LagrangianSymplecticAction.action ℂ
        (transposeSymplectic ℂ g)) L σ) =
    ∑ j : Fin 14, coefficientMatrix g i j • lineSection ℂ j at hcov
  have hc' := congrArg (fun s =>
    (LagrangianDeterminantAction.determinantActionIso ℂ (toLG ℂ)
      (transposeSymplectic ℂ g)).hom.app ⊤
      (((Scheme.Modules.pullbackCongr (ambientAction_toLG g)).app L).hom.app ⊤ s)) hc
  have hn' := congrArg (fun s =>
    (LagrangianDeterminantAction.determinantActionIso ℂ (toLG ℂ)
      (transposeSymplectic ℂ g)).hom.app ⊤ s) hn
  exact hc'.trans (hn'.trans hcov)

/-- The genuine quotient triangle yields the inverse coefficient matrix on
its literal fourteen basis values, without any quotient-frame premise. -/
theorem quotientActionIso_section (g : Sp6) (i : Fin 14) :
    (quotientActionIso g).hom.app ⊤
      (pullbackGlobalSections (ambientAction g) (quotientFive ℂ) (quotientSection ℂ i)) =
    ∑ k : Fin 14, coefficientMatrix g⁻¹ k i • quotientSection ℂ k := by
  have hb := FiniteFreeBasisPullback.pullbackPresentation_basis
    (ambientAction g) (ambientQuotient ℂ) i
  change Scheme.Modules.Hom.app (X := ambient ℂ)
    (pullbackPresentation (ambientAction g) (ambientQuotient ℂ)).map ⊤
      (freeBasisSection (ambient ℂ) 14 i) =
    pullbackGlobalSections (ambientAction g) (quotientFive ℂ) (quotientSection ℂ i) at hb
  rw [← hb]
  have ht := congrArg (fun φ => Scheme.Modules.Hom.app (X := ambient ℂ) φ ⊤
    (freeBasisSection (ambient ℂ) 14 i))
    (quotientActionIso_triangle g)
  change (quotientActionIso g).hom.app ⊤
      (Scheme.Modules.Hom.app (X := ambient ℂ)
    (pullbackPresentation (ambientAction g) (ambientQuotient ℂ)).map ⊤
        (freeBasisSection (ambient ℂ) 14 i)) = _ at ht
  refine ht.trans ?_
  rw [LinearIncidenceTensorCovariance.freeMap_basis_expansion]
  simp only [LagrangianParameterLinearAction.constantFreeIso_matrix,
    LagrangianParameterLinearAction.constantMatrix, coefficientMatrix,
    ambientScalarMap, Matrix.map_apply]
  rfl

/-- Actual pullback and tensor isomorphisms transport the original equation
bundle under the simultaneous original scheme transformation. -/
def equationActionIso (g : Sp6) :
    (Scheme.Modules.pullback (ambientAction g)).obj (equationBundle ℂ) ≅ equationBundle ℂ :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (ambientAction g)
      (lineBundle ℂ) (quotientFive ℂ) ≪≫
    LinearIncidenceTensorCovariance.tensorTransport (lineActionIso g) (quotientActionIso g)

/-- The original universal equation, including all fourteen actual tensor
summands, is carried to itself. Both covariance laws are proved above. -/
theorem equationActionIso_section (g : Sp6) :
    (equationActionIso g).hom.app ⊤
      (pullbackGlobalSections (ambientAction g) (equationBundle ℂ) (equationSection ℂ)) =
    equationSection ℂ := by
  have he : equationSection ℂ = ∑ i : Fin 14,
      LinearIncidenceTensorCoordinates.tensorTop (ambient ℂ) (lineBundle ℂ)
        (quotientFive ℂ) (lineSection ℂ i) (quotientSection ℂ i) := by
    simp only [equationSection, LagrangianLinearSectionEquations.tensorSection_eq_tensorTop]
  change (LinearIncidenceTensorCovariance.tensorTransport
      (lineActionIso g) (quotientActionIso g)).hom.app ⊤
      ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (ambientAction g)
        (lineBundle ℂ) (quotientFive ℂ)).hom.app ⊤
        (pullbackGlobalSections (ambientAction g) (equationBundle ℂ) (equationSection ℂ))) = _
  rw [he, LinearIncidenceTensorCovariance.pullbackTensor_sum]
  exact LinearIncidenceTensorCovariance.tensorTransport_sum
    (lineActionIso g) (quotientActionIso g)
    (coefficientMatrix g) (coefficientMatrix g⁻¹) (coefficientMatrix_inv_mul g)
    (fun i => pullbackGlobalSections (ambientAction g) (lineBundle ℂ) (lineSection ℂ i))
    (fun i => pullbackGlobalSections (ambientAction g) (quotientFive ℂ) (quotientSection ℂ i))
    (lineSection ℂ) (quotientSection ℂ) (lineActionIso_section g) (quotientActionIso_section g)

/-- The actual universal equation still vanishes after applying the actual
simultaneous transformation to the original closed incidence family. -/
theorem equation_zero_on_acted_family (g : Sp6) :
    pullbackGlobalSections (inclusion ℂ ≫ ambientAction g)
      (equationBundle ℂ) (equationSection ℂ) = 0 := by
  have hz : (((Scheme.Modules.pullback (inclusion ℂ)).map
      (equationActionIso g).hom).app ⊤)
      (pullbackGlobalSections (inclusion ℂ)
        ((Scheme.Modules.pullback (ambientAction g)).obj (equationBundle ℂ))
        (pullbackGlobalSections (ambientAction g) (equationBundle ℂ) (equationSection ℂ))) = 0 := by
    rw [SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
      equationActionIso_section, equation_zero_on_family]
  have hinj := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback (inclusion ℂ)).map (equationActionIso g).hom).app ⊤)).injective
  have hs := (map_eq_zero_iff _ hinj).mp hz
  rw [← SectionsEqualizer.pullbackGlobalSections_comp (inclusion ℂ) (ambientAction g)
    (equationBundle ℂ) (equationSection ℂ), hs, map_zero]

/-- The actual closed-family morphism is obtained from the genuine equation
zero scheme universal property, with no factorization premise. -/
def familyAction (g : Sp6) : family ℂ ⟶ family ℂ :=
  Classical.choose ((factorsThrough_iff_equation_zero ℂ (inclusion ℂ ≫ ambientAction g)).mpr
    (equation_zero_on_acted_family g))

@[reassoc] theorem familyAction_inclusion (g : Sp6) :
    familyAction g ≫ inclusion ℂ = inclusion ℂ ≫ ambientAction g :=
  Classical.choose_spec ((factorsThrough_iff_equation_zero ℂ
    (inclusion ℂ ≫ ambientAction g)).mpr (equation_zero_on_acted_family g))

@[reassoc] theorem familyAction_projection (g : Sp6) :
    familyAction g ≫ familyProjection ℂ = familyProjection ℂ ≫ rawAction g := by
  change familyAction g ≫ (inclusion ℂ ≫ toParameter ℂ) =
    (inclusion ℂ ≫ toParameter ℂ) ≫ rawAction g
  rw [← Category.assoc, familyAction_inclusion, Category.assoc,
    ambientAction_toParameter, Category.assoc]

theorem familyAction_one : familyAction (1 : Sp6) = 𝟙 (family ℂ) := by
  apply (cancel_mono (inclusion ℂ)).mp
  rw [familyAction_inclusion, ambientAction_one, Category.comp_id, Category.id_comp]

theorem familyAction_mul (g h : Sp6) :
    familyAction g ≫ familyAction h = familyAction (h * g) := by
  apply (cancel_mono (inclusion ℂ)).mp
  rw [Category.assoc, familyAction_inclusion, ← Category.assoc,
    familyAction_inclusion, Category.assoc, ambientAction_mul, familyAction_inclusion]

/-- A genuine isomorphism of the original universal five-cut family covering
the actual raw parameter automorphism, derived from the actual equations. -/
def familyIso (g : Sp6) : family ℂ ≅ family ℂ where
  hom := familyAction g
  inv := familyAction g⁻¹
  hom_inv_id := by rw [familyAction_mul, inv_mul_cancel, familyAction_one]
  inv_hom_id := by rw [familyAction_mul, mul_inv_cancel, familyAction_one]

end M9Native.LagrangianRawFamilyAction
