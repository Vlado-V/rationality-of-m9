module

public import M9StacksIntegration.Sp6GroupScheme
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual base-field affine coordinate ring of the frozen Sp6 group

The algebra is K tensor the original integral symplectic coordinate
ring over ULift Z. The affine scheme isomorphism is the actual
pullback-of-spectra isomorphism, with the factors ordered so that K
acts on the left. The original coordinate ring and group are unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace M9Native.Sp6AffineBaseChange

abbrev IntegerRing := ULift.{u} ℤ

@[instance_reducible]
def integerAlgebra (K : Type u) [CommRing K] : Algebra IntegerRing.{u} K :=
  ((algebraMap ℤ K).comp ULift.ringEquiv.toRingHom).toAlgebra

/-- The actual spectrum map of the algebra homomorphism, constructed
while both commutative-ring instances are abstract. -/
def specAlgebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

def tensorRightSpecMap (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    Spec (.of (S ⊗[R] T)) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- Bundle the tensor ring while its ring and algebra instances are
abstract, retaining their actual native tensor-product structures. -/
def tensorObject (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : CommRingCat.{u} :=
  .of (S ⊗[R] T)

@[instance_reducible]
def tensorObjectLeftAlgebra (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Algebra S (tensorObject R S T) := by
  dsimp [tensorObject]
  infer_instance

variable (K : Type u) [CommRing K]

local instance targetIntegerAlgebra : Algebra IntegerRing.{u} K := integerAlgebra K

abbrev CoordinateRing : Type u :=
  tensorObject IntegerRing.{u} K Sp6CoordinateRing.CoordinateRing.{u}

instance coordinateCommRing : CommRing (CoordinateRing K) := by
  change CommRing (tensorObject IntegerRing K Sp6CoordinateRing.CoordinateRing)
  infer_instance

instance coordinateAlgebra :
    Algebra K (CoordinateRing K) := by
  exact tensorObjectLeftAlgebra IntegerRing K Sp6CoordinateRing.CoordinateRing

def projection : Spec (.of (CoordinateRing K)) ⟶ Spec (.of K) :=
  specAlgebraMap K (CoordinateRing K)

def pullbackCanonicalIso :
    (Sp6GroupScheme.obj (Spec (.of K))).left ≅
      pullback
        (specAlgebraMap IntegerRing Sp6CoordinateRing.CoordinateRing)
        (specAlgebraMap IntegerRing K) :=
  pullback.congrHom (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)

theorem pullbackCanonicalIso_inv_fst :
    (pullbackCanonicalIso K).inv ≫
        pullback.fst Sp6GroupScheme.integralProjection
          (specULiftZIsTerminal.from (Spec (.of K))) =
      pullback.fst
        (specAlgebraMap IntegerRing Sp6CoordinateRing.CoordinateRing)
        (specAlgebraMap IntegerRing K) := by
  simp only [pullbackCanonicalIso, pullback.congrHom_inv, pullback.map,
    pullback.lift_fst, Category.comp_id]

theorem pullbackCanonicalIso_inv_snd :
    (pullbackCanonicalIso K).inv ≫ (Sp6GroupScheme.obj (Spec (.of K))).hom =
      pullback.snd
        (specAlgebraMap IntegerRing Sp6CoordinateRing.CoordinateRing)
        (specAlgebraMap IntegerRing K) := by
  change (pullbackCanonicalIso K).inv ≫
      pullback.snd Sp6GroupScheme.integralProjection
        (specULiftZIsTerminal.from (Spec (.of K))) = _
  simp only [pullbackCanonicalIso, pullback.congrHom_inv, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The actual affine presentation of the original base-changed
symplectic group, not a new scheme with the same closed points. -/
def affineIso :
    Spec (.of (CoordinateRing K)) ≅ (Sp6GroupScheme.obj (Spec (.of K))).left :=
  (pullbackSpecIso IntegerRing K Sp6CoordinateRing.CoordinateRing).symm ≪≫
    (pullbackSymmetry
      (specAlgebraMap IntegerRing Sp6CoordinateRing.CoordinateRing)
      (specAlgebraMap IntegerRing K)).symm ≪≫
    (pullbackCanonicalIso K).symm

@[reassoc]
theorem affineIso_hom_projection :
    (affineIso K).hom ≫ (Sp6GroupScheme.obj (Spec (.of K))).hom = projection K := by
  simp only [affineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackCanonicalIso_inv_snd, pullbackSymmetry_inv_comp_snd, projection, specAlgebraMap]
  exact pullbackSpecIso_inv_fst' IntegerRing K Sp6CoordinateRing.CoordinateRing

@[reassoc]
theorem affineIso_hom_integral :
    (affineIso K).hom ≫
        pullback.fst Sp6GroupScheme.integralProjection
          (specULiftZIsTerminal.from (Spec (.of K))) =
      tensorRightSpecMap IntegerRing K Sp6CoordinateRing.CoordinateRing := by
  simp only [affineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackCanonicalIso_inv_fst, pullbackSymmetry_inv_comp_fst,
    tensorRightSpecMap, specAlgebraMap]
  exact pullbackSpecIso_inv_snd IntegerRing K Sp6CoordinateRing.CoordinateRing

def overIso :
    Over.mk (projection K) ≅ Sp6GroupScheme.obj (Spec (.of K)) :=
  Over.isoMk (affineIso K) (affineIso_hom_projection K)

end M9Native.Sp6AffineBaseChange

