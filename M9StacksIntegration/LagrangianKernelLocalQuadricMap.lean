module

public import M9StacksIntegration.LagrangianKernelAffineFiveSections
public import M9StacksIntegration.SplitQuadricChartCoordinates
public import M9StacksIntegration.NativeProjectiveChartEvaluation

/-!
# The actual local common-kernel and quadric maps agree

Both sides are actual native scheme maps into the original polynomial P4.
The original five minors, their genuine determinant frames, and the
actual quadric chart presentations discharge every coordinate condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjBaseChange
open Stacks.ProjectiveSpaceChartRatio

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianKernelLocalQuadricMap

open LagrangianKernelTailMatrix LagrangianKernelAffineFiveSections
open SplitQuadricAffineAlgebra SplitQuadricLinearSection SplitQuadricChartCoordinates
open LagrangianProjectiveSections LagrangianKernelFiveSections

variable (K : Type u) [Field K] [CharZero K]

theorem fiveFormula_dehom_variables (c : Fin 4) (j : Fin 4) :
    fiveFormula K c ((pivot c).succAbove j) = chartVariables K c j := by
  fin_cases c <;> fin_cases j <;> rfl

theorem chartMap_eq_dehomEvaluation (c : Fin 4) :
    (chartMap K c).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* ThreeRing K)
        (fun j : Fin 4 => fiveFormula K c ((pivot c).succAbove j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [chartMap]
  · intro j
    change chartMap K c (X j) = MvPolynomial.eval₂Hom
      (MvPolynomial.C : K →+* ThreeRing K)
      (fun a : Fin 4 => fiveFormula K c ((pivot c).succAbove a)) (X j)
    rw [chartMap, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X',
      fiveFormula_dehom_variables]

/-- Exact original native Q-chart morphism, identified by its derived coordinate effects. -/
theorem quadricChart_eq_fromEvaluation (c : Fin 4) :
    SplitQuadricStandardCharts.affineThreeMap K c ≫ quadricInclusion K =
      Proj.fromOfGlobalSections (polyGrading K 4)
        (NativeProjectiveChartEvaluation.globalEvaluation
          (MvPolynomial.C : K →+* ThreeRing K) (fiveFormula K c))
        (NativeProjectiveChartEvaluation.globalEvaluation_irrelevant
          (MvPolynomial.C : K →+* ThreeRing K) (pivot c) (fiveFormula K c) (fiveFormula_pivot K c)) := by
  have h := NativeProjectiveChartEvaluation.coordinates_eq_fromOfGlobalSections
    (MvPolynomial.C : K →+* ThreeRing K) (pivot c) (fiveFormula K c) (fiveFormula_pivot K c)
    (ambientChartMap K c) (by
      intro F
      rw [ambientChartMap_presentation]
      exact congrArg (fun p => (Scheme.ΓSpecIso (.of (ThreeRing K))).inv p)
        (RingHom.congr_fun (chartMap_eq_dehomEvaluation K c) F))
  exact (ambientChartMap_inclusion K c).symm.trans h

def scalarBase : Spec (.of (ThreeRing K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K))

theorem scalarBase_coeff : baseRingHom (scalarBase K) =
    (Scheme.ΓSpecIso (.of (ThreeRing K))).inv.hom.comp (MvPolynomial.C : K →+* ThreeRing K) := by
  change (((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K))).appTop).hom) = _
  exact congrArg (fun f => f.hom)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K))).symm

theorem globalEvaluation_eq (c : Fin 4) :
    NativeProjectiveChartEvaluation.globalEvaluation
        (MvPolynomial.C : K →+* ThreeRing K) (fiveFormula K c) =
      MvPolynomial.eval₂Hom (baseRingHom (scalarBase K)) (normalizedFunctions K c) := by
  rw [scalarBase_coeff]
  rfl

theorem quadricChart_eq_polynomialFunctions (c : Fin 4) :
    (SplitQuadricStandardCharts.affineThreeMap K c ≫ quadricInclusion K) ≫
        (polynomialComparison K 4).iso.inv =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver (normalizedFunctions K c)
        (normalizedFunctions_span K c) (scalarBase K) := by
  rw [quadricChart_eq_fromEvaluation]
  simpa only [globalEvaluation_eq] using fromEvaluation_comp_comparison_inv (scalarBase K)
    (normalizedFunctions K c) (normalizedFunctions_span K c)

/-- The actual two affine charts give the identical original P4 morphism.
No map equality or quadric-model isomorphism is supplied as a hypothesis. -/
theorem local_ambient_equal (c : Fin 4) :
    zeroChartMap K c ≫ zeroProjectiveMap K ≫ (polynomialComparison K 4).iso.hom =
      SplitQuadricStandardCharts.affineThreeMap K c ≫ quadricInclusion K := by
  apply (cancel_mono (polynomialComparison K 4).iso.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [Category.assoc, scalarBase] using
    (zeroChartMap_projectiveMap K c).trans (quadricChart_eq_polynomialFunctions K c).symm

end M9Native.LagrangianKernelLocalQuadricMap
