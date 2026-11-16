module
public import M9StacksIntegration.LagrangianSymmetricPlucker
public import M9StacksIntegration.PolynomialProjectiveSectionPins
public import M9StacksIntegration.LagrangianPolynomialPluckerFrame
public import M9StacksIntegration.MixedQuadraticTrisecant

/-! The ORIGINAL five row equations in polynomial P13. The native
generated symmetric-algebra classifier is proved equal to the original
polynomial Plucker map. Its genuine O(1) isomorphism recovers every
original row section, and therefore its full zero ideal. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory Module
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjBaseChange
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianPolynomialLinearRows
open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianProjectiveIntersection LagrangianProjectiveLinearForms
open LagrangianSymmetricPlucker LagrangianPolynomialPluckerFrame
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule

variable (K : Type u) [Field K] [CharZero K]

abbrev formsBasis : Basis (Fin 14) K (Forms K) := (Pi.basisFun K (Fin 14)).dualBasis

/-- Actual equality of the generated classifier and the ORIGINAL map. -/
theorem polynomialMap_eq_original :
    PolynomialProjectiveSections.polynomialMap K (formsBasis K) (determinantLine K)
      (sectionLinear K) (sectionLinear_generates K) = polynomialPlucker K := by
  change canonicalPlucker K ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial (formsBasis K)).hom = _
  rw [canonicalPlucker_eq]
  change (LagrangianPlucker.primitivePlucker K ≫
      ((polynomialComparison K 13).iso.hom ≫
        (projectiveSpaceOfModuleIsoProjMvPolynomial (formsBasis K)).inv)) ≫
      (projectiveSpaceOfModuleIsoProjMvPolynomial (formsBasis K)).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, polynomialPlucker]

/-- A genuine global comparison, with the original determinant line. -/
def polynomialDeterminantIso :
    (Scheme.Modules.pullback (polynomialPlucker K)).obj
      (twistingSheafModule (polyGrading K 13) (1 : ℤ)) ≅ determinantLine K :=
  (Scheme.Modules.pullbackCongr (polynomialMap_eq_original K).symm).app
      (twistingSheafModule (polyGrading K 13) (1 : ℤ)) ≪≫
    PolynomialProjectiveSections.polynomialTwistIso K (formsBasis K) (determinantLine K)
      (sectionLinear K) (sectionLinear_generates K)

/-- Exact section pinning; no scalar or vanishing compatibility premise. -/
theorem polynomialDeterminantIso_degreeSection (F : polyGrading K 13 1) (v : Forms K)
    (hv : SymPow.gradedMvPolynomialInv (formsBasis K) F = SymmetricAlgebra.ι K (Forms K) v) :
    (polynomialDeterminantIso K).hom.app ⊤
      (pullbackGlobalSections (polynomialPlucker K)
        (twistingSheafModule (polyGrading K 13) (1 : ℤ))
        (degreeSection (polyGrading K 13) 1 F)) = sectionLinear K v := by
  change (PolynomialProjectiveSections.polynomialTwistIso K (formsBasis K)
      (determinantLine K) (sectionLinear K) (sectionLinear_generates K)).hom.app ⊤
    ((((Scheme.Modules.pullbackCongr (polynomialMap_eq_original K).symm).app
      (twistingSheafModule (polyGrading K 13) (1 : ℤ))).hom).app ⊤
      (pullbackGlobalSections (polynomialPlucker K)
        (twistingSheafModule (polyGrading K 13) (1 : ℤ))
        (degreeSection (polyGrading K 13) 1 F))) = _
  exact (congrArg (fun s =>
    (PolynomialProjectiveSections.polynomialTwistIso K (formsBasis K) (determinantLine K)
      (sectionLinear K) (sectionLinear_generates K)).hom.app ⊤ s)
      (SectionsEqualizer.pullbackGlobalSections_congr (polynomialMap_eq_original K).symm
        (twistingSheafModule (polyGrading K 13) (1 : ℤ))
        (degreeSection (polyGrading K 13) 1 F))).trans
    (PolynomialProjectiveSectionPins.polynomialTwistIso_degreeSection K (formsBasis K)
      (determinantLine K) (sectionLinear K) (sectionLinear_generates K) F v hv)

def rowPolynomial (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) : polyGrading K 13 1 :=
  ⟨SymPow.gradedMvPolynomialHom (formsBasis K) (fiveForms K M.mulVecLin j),
    (SymPow.gradedMvPolynomialHom (formsBasis K)).map_mem
      (fiveForms_homogeneous_one K M.mulVecLin j)⟩

theorem rowPolynomial_inverse (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    SymPow.gradedMvPolynomialInv (formsBasis K) (rowPolynomial K M j) =
      SymmetricAlgebra.ι K (Forms K) (rowForms K M.mulVecLin j) := by
  change (SymmetricAlgebra.equivMvPolynomial (formsBasis K)).symm
    (SymmetricAlgebra.equivMvPolynomial (formsBasis K)
      (SymmetricAlgebra.ι K (Forms K) (rowForms K M.mulVecLin j))) = _
  exact AlgEquiv.symm_apply_apply _ _

/-- Original matrix row sections, with no new coefficient convention. -/
theorem rowPolynomial_section (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    (polynomialDeterminantIso K).hom.app ⊤
      (pullbackGlobalSections (polynomialPlucker K)
        (twistingSheafModule (polyGrading K 13) (1 : ℤ))
        (degreeSection (polyGrading K 13) 1 (rowPolynomial K M j))) =
      sectionLinear K (rowForms K M.mulVecLin j) :=
  polynomialDeterminantIso_degreeSection K (rowPolynomial K M j)
    (rowForms K M.mulVecLin j) (rowPolynomial_inverse K M j)

/-- Equality of original full ideal sheaves, including nilpotents. -/
theorem rowIdeal_comap (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    (MixedQuadraticTrisecant.degreeIdeal K 13 1 (rowPolynomial K M j)).comap (polynomialPlucker K) =
      zeroScheme (space K) (determinantLine K) (sectionLinear K (rowForms K M.mulVecLin j)) := by
  rw [MixedQuadraticTrisecant.degreeIdeal, ← Stacks.Divisors.zeroScheme_pullback]
  exact zeroScheme_eq_of_iso (polynomialDeterminantIso K) (rowPolynomial_section K M j)

end M9Native.LagrangianPolynomialLinearRows
