module

public import M9StacksIntegration.ProjectiveQuadraticCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The literal split quadric and its scheme-theoretic linear sections

The ordered five coordinates are (q11,q12,q22,p00,b). The quadric is
X0*X2-X1^2-X3*X4=0 in the native polynomial P4. A linear section is the
actual inverse-image ideal on the projective space of the quotient by
its genuine space of linear equations. No radical or reduced replacement
is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open M9Native.ProjectiveQuadraticCohomology
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.SplitQuadricLinearSection
variable (K : Type u) [Field K]

abbrev ambient : Scheme.{u} := projective K 4
abbrev coordinates := Fin 5 → K

def equation : MvPolynomial (Fin 5) K := X 0 * X 2 - X 1 ^ 2 - X 3 * X 4

theorem equation_homogeneous : (equation K).IsHomogeneous 2 := by
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.sub ?_ ?_) ?_
  · exact (MvPolynomial.isHomogeneous_X K (0 : Fin 5)).mul (MvPolynomial.isHomogeneous_X K 2)
  · simpa using (MvPolynomial.isHomogeneous_X K (1 : Fin 5)).pow 2
  · exact (MvPolynomial.isHomogeneous_X K (3 : Fin 5)).mul (MvPolynomial.isHomogeneous_X K 4)

theorem equation_ne_zero : equation K ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval ![(1 : K),0,1,0,0]) h
  simp [equation] at he

def form : polyGrading K 4 2 :=
  ⟨equation K, (MvPolynomial.mem_homogeneousSubmodule 2 _).mpr (equation_homogeneous K)⟩

def quadricSection : (twist K 4 2).sections :=
  Stacks.PresheafOfModules.sectionOfTop (twist K 4 2).val
    (degreeSection (polyGrading K 4) 2 (form K))

theorem section_eval : (quadricSection K).eval (Opposite.op ⊤) =
    degreeSection (polyGrading K 4) 2 (form K) :=
  Stacks.PresheafOfModules.sectionOfTop_val_top (twist K 4 2).val _

abbrev quadricIdeal : (ambient K).IdealSheafData := quadraticIdeal K 4 (quadricSection K)
abbrev quadric : Scheme.{u} := (quadricIdeal K).subscheme
abbrev quadricInclusion : quadric K ⟶ ambient K := (quadricIdeal K).subschemeι
abbrev quadricProjection : quadric K ⟶ Spec (.of K) := quadricInclusion K ≫ projToSpecCoeff K 4

theorem quadricIdeal_eq : quadricIdeal K = zeroScheme (ambient K) (twist K 4 2)
    (degreeSection (polyGrading K 4) 2 (form K)) := by
  dsimp only [quadricIdeal, quadraticIdeal]
  rw [section_eval]

def coordinateIso : projectiveSpaceOfModule K (coordinates K) ≅ ambient K :=
  projectiveSpaceOfModuleIsoProjMvPolynomial (Pi.basisFun K (Fin 5))

abbrev linearProjective (W : Submodule K (coordinates K)) : Scheme.{u} :=
  projectiveSpaceOfModule K (coordinates K ⧸ W)

def linearInclusion (W : Submodule K (coordinates K)) : linearProjective K W ⟶ ambient K :=
  quotientMap K (coordinates K) W ≫ (coordinateIso K).hom

instance linearInclusion_closed (W : Submodule K (coordinates K)) :
    IsClosedImmersion (linearInclusion K W) := by
  dsimp only [linearInclusion]
  infer_instance

abbrev linearSectionIdeal (W : Submodule K (coordinates K)) :=
  (quadricIdeal K).comap (linearInclusion K W)
abbrev linearSection (W : Submodule K (coordinates K)) : Scheme.{u} :=
  (linearSectionIdeal K W).subscheme
abbrev toLinear (W : Submodule K (coordinates K)) : linearSection K W ⟶ linearProjective K W :=
  (linearSectionIdeal K W).subschemeι

def toAmbient (W : Submodule K (coordinates K)) : linearSection K W ⟶ ambient K :=
  toLinear K W ≫ linearInclusion K W

def sectionProjection (W : Submodule K (coordinates K)) : linearSection K W ⟶ Spec (.of K) :=
  toAmbient K W ≫ projToSpecCoeff K 4

def sectionIsoPullback (W : Submodule K (coordinates K)) :
    linearSection K W ≅ pullback (linearInclusion K W) (quadricInclusion K) :=
  (quadricIdeal K).comapIso (linearInclusion K W)

@[reassoc] theorem sectionIsoPullback_hom_fst (W : Submodule K (coordinates K)) :
    (sectionIsoPullback K W).hom ≫ pullback.fst _ _ = toLinear K W :=
  (quadricIdeal K).comapIso_hom_fst (linearInclusion K W)

@[reassoc] theorem sectionIsoPullback_hom_toAmbient (W : Submodule K (coordinates K)) :
    (sectionIsoPullback K W).hom ≫ pullback.fst _ _ ≫ linearInclusion K W = toAmbient K W :=
  (quadricIdeal K).comapIso_hom_fst_assoc (linearInclusion K W) (linearInclusion K W)

end M9Native.SplitQuadricLinearSection
