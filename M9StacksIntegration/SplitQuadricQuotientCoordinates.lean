module

public import M9StacksIntegration.ProjectiveQuadricLinearPullback

/-!
# Actual quotient coordinates for scheme-theoretic quadric linear sections

A basis is used only in this coordinate adapter. The graded map is built
from the actual quotient and the actual symmetric-algebra basis maps;
its surjectivity and coefficient triangle are proved. The original
inverse-image scheme is isomorphic over the original field to the
polynomial linear-section scheme, retaining its structural map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open M9Native.SplitQuadricLinearSection M9Native.ProjectiveQuadraticCohomology
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.SplitQuadricQuotientCoordinates
variable (K : Type u) [Field K] (W : Submodule K (coordinates K))
variable (n : ℕ) (b : Basis (Fin (n+1)) K (coordinates K ⧸ W))

def gradedMap : polyGrading K 4 →+*ᵍ polyGrading K n :=
  (SymPow.gradedMvPolynomialHom b).comp
    ((quotientGradedHom K (coordinates K) W).comp
      (SymPow.gradedMvPolynomialInv (Pi.basisFun K (Fin 5))))

def coordinateAlgebraMap : MvPolynomial (Fin 5) K →ₐ[K] MvPolynomial (Fin (n+1)) K :=
  (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.comp
    ((SymPow.symAlgMap W.mkQ).comp
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun K (Fin 5))).symm.toAlgHom)

theorem gradedMap_apply (x : MvPolynomial (Fin 5) K) :
    gradedMap K W n b x = coordinateAlgebraMap K W n b x := rfl

theorem gradedMap_surjective : Function.Surjective (gradedMap K W n b) := by
  change Function.Surjective
    ((SymmetricAlgebra.equivMvPolynomial b) ∘ (SymPow.symAlgMap W.mkQ) ∘
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun K (Fin 5))).symm)
  exact (SymmetricAlgebra.equivMvPolynomial b).surjective.comp
    ((SymPow.symAlgMap_surjective W.mkQ W.mkQ_surjective).comp
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun K (Fin 5))).symm.surjective)

theorem gradedMap_C (c : K) : gradedMap K W n b (MvPolynomial.C c) = MvPolynomial.C c :=
  (coordinateAlgebraMap K W n b).commutes c

def coordinateIso : linearProjective K W ≅ projective K n :=
  projectiveSpaceOfModuleIsoProjMvPolynomial b

private theorem gradedMap_cancel :
    (SymPow.gradedMvPolynomialInv b).comp (gradedMap K W n b) =
      (quotientGradedHom K (coordinates K) W).comp
        (SymPow.gradedMvPolynomialInv (Pi.basisFun K (Fin 5))) := by
  apply GradedRingHom.ext
  intro x
  change (SymmetricAlgebra.equivMvPolynomial b).symm
      ((SymmetricAlgebra.equivMvPolynomial b)
        (SymPow.symAlgMap W.mkQ
          ((SymmetricAlgebra.equivMvPolynomial (Pi.basisFun K (Fin 5))).symm x))) = _
  exact (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply _

/-- Actual original linear embedding, with no projective-map equality supplied. -/
@[reassoc] theorem coordinate_triangle :
    (coordinateIso K W n b).hom ≫
        ProjectiveQuadricLinearPullback.linearMap K n (gradedMap K W n b)
          (gradedMap_surjective K W n b) = linearInclusion K W := by
  dsimp only [coordinateIso, ProjectiveQuadricLinearPullback.linearMap,
    linearInclusion, SplitQuadricLinearSection.coordinateIso, quotientMap]
  rw [projectiveSpaceOfModuleIsoProjMvPolynomial_hom,
    projectiveSpaceOfModuleIsoProjMvPolynomial_hom, ← Proj.map_comp, ← Proj.map_comp]
  exact Proj.map_congr (gradedMap_cancel K W n b) _ _

abbrev polynomialIdeal := ProjectiveQuadricLinearPullback.sectionIdeal K n (gradedMap K W n b)
  (gradedMap_surjective K W n b)

theorem ideal_factorization : linearSectionIdeal K W =
    (polynomialIdeal K W n b).comap (coordinateIso K W n b).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, coordinate_triangle]

def idealEqIso {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    I.subscheme ≅ J.subscheme := eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

@[reassoc] theorem idealEqIso_hom {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (idealEqIso h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp only [idealEqIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

def sectionIso : linearSection K W ≅ ProjectiveQuadricLinearPullback.sectionScheme K n
    (gradedMap K W n b) (gradedMap_surjective K W n b) :=
  idealEqIso (ideal_factorization K W n b) ≪≫
    (polynomialIdeal K W n b).comapIso (coordinateIso K W n b).hom ≪≫
      asIso (pullback.snd (coordinateIso K W n b).hom (polynomialIdeal K W n b).subschemeι)

/-- The actual scheme isomorphism preserves the original structural field map. -/
theorem sectionIso_over :
    (sectionIso K W n b).hom ≫ ProjectiveQuadricLinearPullback.sectionProjection K n
      (gradedMap K W n b) (gradedMap_surjective K W n b) = sectionProjection K W := by
  dsimp only [sectionIso, Iso.trans_hom, asIso_hom,
    ProjectiveQuadricLinearPullback.sectionProjection]
  simp only [Category.assoc]
  rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    idealEqIso_hom_assoc, coordinate_triangle_assoc]
  simp only [SplitQuadricLinearSection.sectionProjection,
    SplitQuadricLinearSection.toAmbient, Category.assoc]

/-- True field-linear transport of structure-sheaf cohomology under an actual over-field iso. -/
def structureCohomologyIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K)) (h : e.hom ≫ pY = pX) (q : ℕ) :
    structureSheafCohomology pX q ≅ structureSheafCohomology pY q :=
  structureSheafCohomologyIsoCohomologyOverField K pX q ≪≫
    eqToIso (congrArg (fun f => cohomologyOverField K f (SheafOfModules.unit X.ringCatSheaf) q) h.symm) ≪≫
    cohomologyOverFieldPushforwardIso K e.hom pY (SheafOfModules.unit X.ringCatSheaf) q ≪≫
    cohomologyOverFieldIso K pY (Stacks.Morphisms.pushforwardStructureSheafIsoUnit e) q ≪≫
    (structureSheafCohomologyIsoCohomologyOverField K pY q).symm

theorem finite_target_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K)) (h : e.hom ≫ pY = pX)
    [IsFinite pX] : IsFinite pY := by
  have ht : IsFinite (e.inv ≫ pX) := inferInstance
  have he : e.inv ≫ pX = pY := by
    rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact he ▸ ht

end M9Native.SplitQuadricQuotientCoordinates
