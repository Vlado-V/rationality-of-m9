module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import M9StacksIntegration.LineFramePullback
public import M9StacksIntegration.ProjectiveQuadraticCohomology

/-!
# A generated original-field section system in the polynomial projective model

The native symmetric-algebra classifier constructs the morphism and its
actual O(1) pullback isomorphism. The original basis then transports both
through the genuine graded algebra isomorphism to polynomial projective
space. The original structure morphism is retained by the coordinate square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory Module
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection
universe u
attribute [local instance] MvPolynomial.gradedAlgebra globalSectionsModule

namespace M9Native.PolynomialProjectiveSections
variable (K : Type u) [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {n : ℕ} (b : Basis (Fin (n+1)) K V)

/-- The actual basis comparison preserves the original coefficient map. -/
theorem basisIso_over :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫ projToSpecCoeff K n =
      projectiveSpaceOfModuleToSpec K V := by
  rw [projToSpecCoeff, Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap]
  exact projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero b

/-- The named graded-basis twist comparison, including the degree-one
section law supplied by the genuine native comparison. -/
def basisTwistIso :
    (Scheme.Modules.pullback (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom).obj
      (twistingSheafModule (polyGrading K n) (1 : ℤ)) ≅
        twistingSheafModule (grading K V) (1 : ℤ) := by
  exact pullbackTwistIso (SymPow.gradedMvPolynomialInv b)
    (irrelevant_le_map_gradedMvPolynomialInv b)
    (SymmetricAlgebra.equivMvPolynomial b).symm.surjective
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) 1

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (ψ : V →ₗ[K] Γ(L, ⊤))
  (hψ : ⨆ v : V, Stacks.NonvanishingOpen.nonvanishingOpen X L (ψ v) = ⊤)

def polynomialMap : X ⟶ Proj (polyGrading K n) :=
  morphismOfGeneratingSections K V L ψ hψ ≫
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom

theorem polynomialMap_over : polynomialMap K b L ψ hψ ≫ projToSpecCoeff K n =
    X ↘ Spec (.of K) := by
  rw [polynomialMap, Category.assoc, basisIso_over]
  exact morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec ψ hψ

def polynomialTwistIso :
    (Scheme.Modules.pullback (polynomialMap K b L ψ hψ)).obj
      (twistingSheafModule (polyGrading K n) (1 : ℤ)) ≅ L :=
  ((Scheme.Modules.pullbackComp (morphismOfGeneratingSections K V L ψ hψ)
      (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom).app
        (twistingSheafModule (polyGrading K n) (1 : ℤ))).symm ≪≫
    (Scheme.Modules.pullback (morphismOfGeneratingSections K V L ψ hψ)).mapIso
      (basisTwistIso K b) ≪≫ twistIsoOfGeneratingSections K V L ψ hψ

end M9Native.PolynomialProjectiveSections
