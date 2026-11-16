module

public import M9StacksIntegration.GrassmannianFunctionField
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# The actual function field of the original affine-space scheme

The scheme is Mathlib's original affine space, with its original projection
to Spec K. Its algebra structure on the genuine generic stalk comes from
that projection. The actual Spec isomorphism, generic-stalk restriction,
fraction-ring universal property and explicit ULift variable reindexing
construct the algebra equivalence to the literal rational-function field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.GrassmannianCharts

universe u

namespace M9Native.AffineSpaceFunctionField

variable (K : Type u) [Field K] (n : ℕ)

/-- The original affine-space scheme, retaining the original base. -/
abbrev space : Scheme.{u} := AffineSpace (ULift.{u} (Fin n)) (Spec (.of K))

/-- The original affine-space projection, literally the defining pullback projection. -/
abbrev projection : space K n ⟶ Spec (.of K) := pullback.fst _ _

/-- The literal polynomial coordinate ring of the original Spec chart. -/
abbrev polynomial := MvPolynomial (ULift.{u} (Fin n)) K

/-- The genuine original Mathlib Spec isomorphism. -/
def specIso : space K n ≅ Spec (.of (polynomial K n)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of K)

/-- The actual Spec isomorphism retains the original coefficient projection. -/
@[reassoc] theorem specIso_inv_projection :
    (specIso K n).inv ≫ projection K n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* polynomial K n)) :=
  AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin n)) (.of K)

/-- The forward Spec isomorphism gives the same original projection square. -/
@[reassoc] theorem specIso_hom_projection :
    (specIso K n).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* polynomial K n)) =
        projection K n := by
  rw [← specIso_inv_projection, Iso.hom_inv_id_assoc]

/-- Scalars on the actual generic stalk are the actual structural scalar map. -/
@[instance_reducible, instance] def functionFieldAlgebra :
    Algebra K (space K n).functionField :=
  (structureScalarMap K (projection K n)).toAlgebra

theorem functionField_algebraMap :
    algebraMap K (space K n).functionField = structureScalarMap K (projection K n) := rfl

/-- Restriction along the original Spec isomorphism and the genuine
fraction-ring comparison, before the explicit variable reindexing. -/
def liftedFunctionFieldEquiv :
    (space K n).functionField ≃ₐ[K] FractionRing (polynomial K n) := by
  let e₁ := (openImmersionFunctionFieldIso (specIso K n).inv).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (polynomial K n)
    (Spec (.of (polynomial K n))).functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := openImmersionFunctionFieldIso_scalar K (specIso K n).inv (projection K n)
  rw [specIso_inv_projection] at h
  have hs := affine_structureScalarMap K (polynomial K n)
  change structureScalarMap K (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : K →+* polynomial K n))) =
      (algebraMap (polynomial K n) (Spec (.of (polynomial K n))).functionField).comp
        MvPolynomial.C at hs
  rw [hs] at h
  have hc : e₁ (algebraMap K (space K n).functionField c) =
      algebraMap (polynomial K n) (Spec (.of (polynomial K n))).functionField
        (MvPolynomial.C c) := DFunLike.congr_fun h c
  change e₂ (e₁ (algebraMap K (space K n).functionField c)) = _
  rw [hc, e₂.commutes]
  exact (IsScalarTower.algebraMap_apply K (polynomial K n)
    (FractionRing (polynomial K n)) c).symm

/-- Reindexing the actual ULift variables, using the fraction-ring universal property. -/
def reindexFractionFieldEquiv :
    FractionRing (polynomial K n) ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K) :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K
    (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n))

/-- The function field of the original affine-space scheme is the literal
rational-function field in n variables over the original field K. -/
def rationalFunctionFieldEquiv :
    (space K n).functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K) :=
  (liftedFunctionFieldEquiv K n).trans (reindexFractionFieldEquiv K n)

/-- The coefficient formula refers to the original projection's actual scalar map. -/
theorem rationalFunctionFieldEquiv_scalar (c : K) :
    rationalFunctionFieldEquiv K n (structureScalarMap K (projection K n) c) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.C c) := by
  change rationalFunctionFieldEquiv K n (algebraMap K (space K n).functionField c) = _
  rw [(rationalFunctionFieldEquiv K n).commutes]
  exact IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
    (FractionRing (MvPolynomial (Fin n) K)) c

/-- The Spec-chart restriction sends the actual original coordinate germ
to the actual polynomial variable in the actual generic stalk of Spec. -/
local instance top_nonempty : Nonempty (⊤ : (space K n).Opens) :=
  ⟨⟨genericPoint (space K n), by trivial⟩⟩

theorem specRestriction_coordinate (i : Fin n) :
    (openImmersionFunctionFieldIso (specIso K n).inv).hom
        ((space K n).germToFunctionField ⊤
          (AffineSpace.coord (Spec (.of K)) (ULift.up i))) =
      algebraMap (polynomial K n) (Spec (.of (polynomial K n))).functionField
        (MvPolynomial.X (ULift.up i)) := by
  have h := congrArg
    (fun f : Γ(space K n, ⊤) ⟶ (Spec (.of (polynomial K n))).functionField =>
      f (AffineSpace.coord (Spec (.of K)) (ULift.up i)))
    (openImmersionFunctionFieldIso_germ (specIso K n).inv)
  have hcoord : (specIso K n).inv.appTop
      (AffineSpace.coord (Spec (.of K)) (ULift.up i)) =
        (Scheme.ΓSpecIso (.of (polynomial K n))).inv (MvPolynomial.X (ULift.up i)) :=
    AffineSpace.SpecIso_inv_appTop_coord (n := ULift.{u} (Fin n)) (.of K) (ULift.up i)
  simp only [CommRingCat.comp_apply] at h
  rw [hcoord] at h
  exact h

/-- The actual original affine coordinate germs become the corresponding
literal rational-function variables after the explicit ULift reindexing. -/
theorem rationalFunctionFieldEquiv_coordinate (i : Fin n) :
    rationalFunctionFieldEquiv K n
        ((space K n).germToFunctionField ⊤
          (AffineSpace.coord (Spec (.of K)) (ULift.up i))) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.X i) := by
  change reindexFractionFieldEquiv K n
    ((FractionRing.algEquiv (polynomial K n)
      (Spec (.of (polynomial K n))).functionField).symm
      ((openImmersionFunctionFieldIso (specIso K n).inv).hom
        ((space K n).germToFunctionField ⊤
          (AffineSpace.coord (Spec (.of K)) (ULift.up i))))) = _
  rw [specRestriction_coordinate K n i, AlgEquiv.commutes]
  simp [reindexFractionFieldEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    MvPolynomial.renameEquiv_apply]

/-- The original finite-dimensional affine space with its original
projection is an actual variety over K. -/
theorem isVariety : IsVariety K (projection K n) where
  toIsIntegral := inferInstance
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := inferInstanceAs
    (LocallyOfFiniteType ((space K n) ↘ Spec (.of K)))
  toQuasiCompact := inferInstance

end M9Native.AffineSpaceFunctionField
