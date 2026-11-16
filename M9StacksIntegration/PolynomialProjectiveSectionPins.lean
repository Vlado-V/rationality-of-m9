module

public import M9StacksIntegration.PolynomialProjectiveSections

/-! Exact homogeneous-section pinning for the original generated system.
Injectivity of that original linear system then excludes every nonzero
linear equation on its actual polynomial-model image. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory Module
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open M9Native.PolynomialProjectiveSections
universe u
attribute [local instance] MvPolynomial.gradedAlgebra globalSectionsModule
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.PolynomialProjectiveSectionPins

private theorem pullbackGlobal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : pullbackGlobalSections f M s =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s) = _
  exact Functor.map_id_apply _ _ _

variable (K : Type u) [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {n : ℕ} (b : Basis (Fin (n+1)) K V)

theorem basisTwistIso_degreeSection (F : polyGrading K n 1) :
    (basisTwistIso K b).hom.app ⊤
      (pullbackGlobalSections (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom
        (twistingSheafModule (polyGrading K n) (1 : ℤ))
        (degreeSection (polyGrading K n) 1 F)) =
      degreeSection (grading K V) 1
        ⟨SymPow.gradedMvPolynomialInv b F, (SymPow.gradedMvPolynomialInv b).map_mem F.property⟩ := by
  rw [pullbackGlobal_eq]
  exact pullbackTwistIso_degreeSection (SymPow.gradedMvPolynomialInv b)
    (irrelevant_le_map_gradedMvPolynomialInv b)
    (SymmetricAlgebra.equivMvPolynomial b).symm.surjective
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) 1 F

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (ψ : V →ₗ[K] Γ(L, ⊤))
  (hψ : ⨆ v : V, Stacks.NonvanishingOpen.nonvanishingOpen X L (ψ v) = ⊤)

/-- The actual positive-twist isomorphism sends the pulled homogeneous
linear section to the original section of its genuine basis image. -/
theorem polynomialTwistIso_degreeSection (F : polyGrading K n 1) (v : V)
    (hv : SymPow.gradedMvPolynomialInv b F = SymmetricAlgebra.ι K V v) :
    (polynomialTwistIso K b L ψ hψ).hom.app ⊤
      (pullbackGlobalSections (polynomialMap K b L ψ hψ)
        (twistingSheafModule (polyGrading K n) (1 : ℤ))
        (degreeSection (polyGrading K n) 1 F)) = ψ v := by
  change (twistIsoOfGeneratingSections K V L ψ hψ).hom.app ⊤
    (((Scheme.Modules.pullback (morphismOfGeneratingSections K V L ψ hψ)).map
      (basisTwistIso K b).hom).app ⊤
      (((Scheme.Modules.pullbackComp (morphismOfGeneratingSections K V L ψ hψ)
        (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom).inv.app
          (twistingSheafModule (polyGrading K n) (1 : ℤ))).app ⊤
        (pullbackGlobalSections (polynomialMap K b L ψ hψ)
          (twistingSheafModule (polyGrading K n) (1 : ℤ))
          (degreeSection (polyGrading K n) 1 F)))) = _
  dsimp only [polynomialMap]
  rw [LineFramePullback.pullbackComp_inv_apply,
    M9Native.SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    basisTwistIso_degreeSection]
  have hs : degreeSection (grading K V) 1
      ⟨SymPow.gradedMvPolynomialInv b F, (SymPow.gradedMvPolynomialInv b).map_mem F.property⟩ =
      degreeSection (grading K V) 1 (degreeOneElement K V v) := by
    congr 1
    exact Subtype.ext hv
  rw [hs]
  exact twistIso_pullbackSectionOne K V L ψ hψ v

/-- A genuinely independent generated linear system cannot have its
actual scheme image contained in a nonzero degree-one equation. -/
theorem pullback_linearSection_ne_zero (hψinj : Function.Injective ψ)
    (F : polyGrading K n 1) (hF : (F : MvPolynomial (Fin (n+1)) K) ≠ 0) :
    pullbackGlobalSections (polynomialMap K b L ψ hψ)
      (twistingSheafModule (polyGrading K n) (1 : ℤ))
      (degreeSection (polyGrading K n) 1 F) ≠ 0 := by
  have hmem := (SymPow.gradedMvPolynomialInv b).map_mem F.property
  change SymPow.gradedMvPolynomialInv b F ∈ SymPow.symmetricPower 1 K V at hmem
  rw [SymPow.symmetricPower, pow_one] at hmem
  obtain ⟨v,hv⟩ := hmem
  have hvne : v ≠ 0 := by
    intro hzero
    apply hF
    apply (SymmetricAlgebra.equivMvPolynomial b).symm.injective
    change SymPow.gradedMvPolynomialInv b F = SymPow.gradedMvPolynomialInv b 0
    rw [← hv, hzero, map_zero, map_zero]
  intro hzero
  have h := polynomialTwistIso_degreeSection K b L ψ hψ F v hv.symm
  rw [hzero, map_zero] at h
  apply hvne
  apply hψinj
  simpa only [map_zero] using h.symm

end M9Native.PolynomialProjectiveSectionPins
