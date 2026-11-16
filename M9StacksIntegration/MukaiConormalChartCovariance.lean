module

public import M9StacksIntegration.MukaiConormalChartJets
public import M9StacksIntegration.LagrangianFieldJetCoefficients
public import M9StacksIntegration.LagrangianTranslatedDeterminantCoordinates
public import M9StacksIntegration.PrimitiveCoefficientKernel

/-! Inverse-dual covariance of the actual chart first-jet kernels. The
sections are the original fourteen determinant sections in the actual
translated quotient frame; their derivatives take values in the literal
native pulled cotangent sheaf. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiConormalChartCovariance

open MukaiConormalChartJets LagrangianTranslatedDeterminantSections
open LagrangianTranslatedDeterminantCoordinates LagrangianPluckerQuotient
open LagrangianTranslatedCharts LagrangianFieldJetCoefficients

variable (K : Type u) [Field K] [CharZero K]

def sectionTuple (g : Matrix.symplecticGroup (Fin 3) K) : Fin 14 → Γ(chart K,⊤) :=
  fun j => show Γ(chart K,⊤) from (translatedDeterminantIso K g).hom.app ⊤
    (pullbackGlobalSections (translatedBigCell K g) (determinantLine K) (primitiveSections K j))

theorem scalarMap_spec {R : Type u} [CommRing R] (φ : K →+* R) :
    LagrangianSymplecticAction.scalarMap K (Spec.map (CommRingCat.ofHom φ)) =
      (Scheme.ΓSpecIso (.of R)).inv.hom.comp φ := by
  unfold LagrangianSymplecticAction.scalarMap
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem chart_scalar (a : K) :
    LagrangianSymplecticAction.scalarMap K (chartProjection K) a =
      MukaiConormalBigCellSections.scalarEquiv K (MvPolynomial.C a) :=
  RingHom.congr_fun (scalarMap_spec K (MvPolynomial.C : K →+* MvPolynomial (Fin 6) K)) a

theorem sectionTuple_mul (g h : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    sectionTuple K (g*h) j =
      ∑ k, LagrangianSymplecticAction.scalarMap K (chartProjection K)
        (positiveMatrix K h j k) * sectionTuple K g k := by
  calc
    _ = ∑ k, MukaiConormalBigCellSections.scalarEquiv K
        (MvPolynomial.C (positiveMatrix K h j k)) * sectionTuple K g k :=
      translatedSections_mul K g h j
    _ = _ := by simp only [chart_scalar]

theorem value_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K)
    (j : Fin 14) :
    value K z (sectionTuple K (g*h) j) =
      ∑ k, positiveMatrix K h j k * value K z (sectionTuple K g k) := by
  rw [sectionTuple_mul]
  exact pointValue_sum_constants K (chartProjection K) z hz _ _

theorem derivative_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K)
    (j : Fin 14) :
    derivative K z (sectionTuple K (g*h) j) =
      ∑ k, positiveMatrix K h j k • derivative K z (sectionTuple K g k) := by
  rw [sectionTuple_mul]
  exact pointDerivative_sum_constants K (chartProjection K) z hz _ _

def jetTuple (z : Spec (.of K) ⟶ chart K) (g : Matrix.symplecticGroup (Fin 3) K) :
    Fin 14 → K × PointCotangent K z :=
  fun j => (value K z (sectionTuple K g j), derivative K z (sectionTuple K g j))

theorem jetTuple_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K)
    (j : Fin 14) :
    jetTuple K z (g*h) j = ∑ k, positiveMatrix K h j k • jetTuple K z g k := by
  apply Prod.ext
  · simp only [jetTuple,Prod.fst_sum,Prod.smul_fst,smul_eq_mul]
    exact value_mul K z hz g h j
  · simp only [jetTuple,Prod.snd_sum,Prod.smul_snd]
    exact derivative_mul K z hz g h j

theorem firstJetMap_coefficientMap (z : Spec (.of K) ⟶ chart K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    firstJetMap K z (sectionTuple K g) =
      PrimitiveCoefficientKernel.coefficientMap (LagrangianPluckerLinear.primitiveBasis14 K)
        (jetTuple K z g) := by
  apply LinearMap.ext
  intro ell
  apply Prod.ext <;>
    simp only [firstJetMap_apply,PrimitiveCoefficientKernel.coefficientMap_apply,
      jetTuple,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

/-- The original first-jet kernel transforms by the required actual
inverse-dual form action. No image/covariance/scalar premise is supplied. -/
theorem firstJet_kernel_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K) :
    LinearMap.ker (firstJetMap K z (sectionTuple K (g*h))) =
      (LinearMap.ker (firstJetMap K z (sectionTuple K g))).map
        (MukaiPrimitiveQuartic.quotientMap K (LagrangianTransitivity.matrixSix K h⁻¹).mulVecLin) := by
  rw [firstJetMap_coefficientMap,firstJetMap_coefficientMap]
  have ht : jetTuple K z (g*h) = fun j =>
      ∑ k, LinearMap.toMatrix (LagrangianPluckerLinear.primitiveBasis14 K)
        (LagrangianPluckerLinear.primitiveBasis14 K)
        (PrimitiveCoefficientAction.primitiveAction K
          (LagrangianSigmaInvariance.transposeSymplectic K h)).toLinearMap j k • jetTuple K z g k := by
    funext j
    rw [jetTuple_mul K z hz g h j]
    simp only [positiveMatrix,PrimitiveCoefficientMatrices.matrix14_native_toMatrix]
  rw [ht,PrimitiveCoefficientKernel.ker_coefficientMap_matrix,inverseDual_eq_quotientMap]

end M9Native.MukaiConormalChartCovariance
