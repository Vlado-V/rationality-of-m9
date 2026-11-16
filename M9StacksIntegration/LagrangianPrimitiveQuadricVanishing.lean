module

public import M9StacksIntegration.HomogeneousEquationIdeal
public import M9StacksIntegration.LagrangianPrimitiveQuadrics
public import M9StacksIntegration.LagrangianPolynomialPluckerFrame
public import M9StacksIntegration.LagrangianPluckerClosed

/-! The actual twenty-one original-basis degree-two sections vanish on
the actual LG closed immersion. The proof descends actual polynomial
vanishing along the genuine affine matrix cover, retaining nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianPrimitiveQuadricVanishing

open LagrangianGrassmannian LagrangianPolynomialPluckerFrame
open LagrangianPluckerGeneration LagrangianPluckerEpimorphism

variable (K : Type u) [Field K] [CharZero K]

def originalQuadricIdeal (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    (AlgebraicGeometry.Proj (polyGrading K 13)).IdealSheafData :=
  HomogeneousEquationIdeal.equationIdeal K 13 2 (LagrangianPrimitiveQuadrics.form K) i

theorem polynomialPlucker_isClosedImmersion : IsClosedImmersion (polynomialPlucker K) := by
  dsimp only [polynomialPlucker]
  infer_instance

/-- Genuine ideal containment is proved globally on the original
closed immersion, not just on field-valued points. -/
theorem originalQuadrics_le_kernel :
    (⨆ i, originalQuadricIdeal K i) ≤ (polynomialPlucker K).ker := by
  letI := polynomialPlucker_isClosedImmersion K
  rw [← Scheme.Hom.iInf_ker_openCover_map_comp (polynomialPlucker K)
    (LagrangianPlucker.matrixCover K)]
  apply le_iInf
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  let T := (LagrangianPlucker.matrixCover K).X ι
  let f := (LagrangianPlucker.matrixCover K).f ι
  let g := LagrangianPlucker.matrixChartIntegral K ι
  have hfg := LagrangianPlucker.matrixChartIntegral_diagram K ι
  letI := matrixCover_chart_isAffine K ι
  let e := chartLineIso K f ι g hfg
  let v := LagrangianPlucker.chartCoordinates K f ι g
  have hv : Ideal.span (Set.range v) = ⊤ := LagrangianPlucker.chartCoordinates_span K f ι g hfg
  have hmap := comp_polynomialPlucker_in_frame K f e v hv
    (chartLineIso_primitive K f ι g hfg)
  have hvan (j : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
      NativeProjectiveVector.vectorMap (Stacks.ProjectiveSpaceChartRatio.baseRingHom
        (f ≫ projection K)) v (LagrangianPrimitiveQuadrics.form K j) = 0 := by
    exact LagrangianPrimitiveQuadrics.eval₂_quadric_eq_zero
      (LagrangianPlucker.coefficientMap K f)
      (Stacks.FreeSheafMatrix.toMatrix (AlgebraicGeometry.Grassmannian.chartQuotientMap 3 6 ι g))
      (LagrangianPlucker.chart_rows_isotropic K f ι g hfg) j
  change (⨆ i, HomogeneousEquationIdeal.equationIdeal K 13 2
      (LagrangianPrimitiveQuadrics.form K) i) ≤ (f ≫ polynomialPlucker K).ker
  rw [hmap]
  exact HomogeneousEquationIdeal.iSup_equationIdeal_le_ker_fromOfGlobalSections
    (NativeProjectiveVector.vectorMap _ v)
    (NativeProjectiveVector.vectorMap_irrelevant _ v hv) hvan

theorem originalQuadric_le_kernel (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    originalQuadricIdeal K i ≤ (polynomialPlucker K).ker :=
  (le_iSup (originalQuadricIdeal K) i).trans (originalQuadrics_le_kernel K)

/-- Every original quadratic pulls to the zero section after every
actual LG-valued test-scheme morphism, including nonreduced schemes. -/
theorem pullback_originalQuadric_eq_zero {T : Scheme.{u}} (f : T ⟶ space K)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    pullbackGlobalSections (f ≫ polynomialPlucker K)
      (twistingSheafModule (polyGrading K 13) (2 : ℤ))
      (degreeSection (polyGrading K 13) 2 (LagrangianPrimitiveQuadrics.form K i)) = 0 := by
  apply (pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker _ _ _).mpr
  exact (originalQuadric_le_kernel K i).trans (f.le_ker_comp (polynomialPlucker K))

end M9Native.LagrangianPrimitiveQuadricVanishing
