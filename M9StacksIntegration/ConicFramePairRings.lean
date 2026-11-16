module

public import M9StacksIntegration.ConicFrameSourceAlgebra
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs

/-! Actual independent chart rings for the product of two conic-frame covers. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open scoped TensorProduct
open TensorProduct Algebra

universe u

namespace M9Native.ConicFramePairRings

open ConicFrameProjective ConicFrameSourceAlgebra

variable (K : Type u) [Field K]

abbrev polynomialPair := polynomial K ⊗[K] polynomial K
abbrev targetPair := targetRing K ⊗[K] targetRing K
abbrev middlePair := sourceRing K ⊗[K] polynomial K
abbrev sourcePair := sourceRing K ⊗[K] sourceRing K

def polynomialPairEquiv : polynomialPair K ≃ₐ[K] MvPolynomial (Fin 8 ⊕ Fin 8) K :=
  MvPolynomial.tensorEquivSum K (Fin 8) (Fin 8) K

def targetPairEquiv : targetPair K ≃ₐ[K]
    MvPolynomial
      (AlgebraicGeometry.Grassmannian.ChartIndex.{u}
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding ⊕
        AlgebraicGeometry.Grassmannian.ChartIndex.{u}
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding) K :=
  MvPolynomial.tensorEquivSum K _ _ K

instance polynomialPair_isDomain : IsDomain (polynomialPair K) :=
  (polynomialPairEquiv K).toRingEquiv.isDomain_iff.mpr inferInstance

instance targetPair_isDomain : IsDomain (targetPair K) :=
  (targetPairEquiv K).toRingEquiv.isDomain_iff.mpr inferInstance

def polynomialToSource : polynomial K →ₐ[K] sourceRing K :=
  IsScalarTower.toAlgHom K (polynomial K) (sourceRing K)

def polynomialPairToMiddle : polynomialPair K →ₐ[K] middlePair K :=
  Algebra.TensorProduct.map (polynomialToSource K) (AlgHom.id K (polynomial K))

def middleToSourcePair : middlePair K →ₐ[K] sourcePair K :=
  Algebra.TensorProduct.map (AlgHom.id K (sourceRing K)) (polynomialToSource K)

def polynomialPairToSourcePair : polynomialPair K →ₐ[K] sourcePair K :=
  Algebra.TensorProduct.map (polynomialToSource K) (polynomialToSource K)

instance polynomialPairMiddle_algebra : Algebra (polynomialPair K) (middlePair K) :=
  (polynomialPairToMiddle K).toRingHom.toAlgebra

instance middleSourcePair_algebra : Algebra (middlePair K) (sourcePair K) :=
  (middleToSourcePair K).toRingHom.toAlgebra

instance polynomialPairSourcePair_algebra : Algebra (polynomialPair K) (sourcePair K) :=
  (polynomialPairToSourcePair K).toRingHom.toAlgebra

instance polynomialPolynomialPairMiddle_tower :
    IsScalarTower (polynomial K) (polynomialPair K) (middlePair K) := by
  exact IsScalarTower.of_algHom (Algebra.TensorProduct.map
    (Algebra.ofId (polynomial K) (sourceRing K)) (AlgHom.id K (polynomial K)))

instance sourceMiddleSourcePair_tower :
    IsScalarTower (sourceRing K) (middlePair K) (sourcePair K) := by
  exact IsScalarTower.of_algHom (Algebra.TensorProduct.map
    (AlgHom.id (sourceRing K) (sourceRing K)) (polynomialToSource K))

instance polynomialPairMiddleSourcePair_tower :
    IsScalarTower (polynomialPair K) (middlePair K) (sourcePair K) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro z
  change polynomialPairToSourcePair K z = middleToSourcePair K (polynomialPairToMiddle K z)
  induction z using TensorProduct.inductionOn with
  | tmul p q => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

instance polynomialPairMiddle_localization :
    IsLocalization.Away ((localizer K) ⊗ₜ[K] (1 : polynomial K)) (middlePair K) := by
  have h := IsLocalization.tensorProduct_tensorProduct K (polynomial K)
    (Submonoid.powers (localizer K)) (sourceRing K) (by
      apply RingHom.ext
      intro p
      change polynomialPairToMiddle K ((1 : polynomial K) ⊗ₜ[K] p) = 1 ⊗ₜ[K] p
      simp only [polynomialPairToMiddle, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply])
  simpa only [Algebra.algebraMapSubmonoid_powers, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply] using h

instance middleSourcePair_localization :
    IsLocalization.Away ((1 : sourceRing K) ⊗ₜ[K] localizer K) (sourcePair K) := by
  have h := IsLocalization.tensorProduct_tensorProduct_right K (sourceRing K)
    (Submonoid.powers (localizer K)) (sourceRing K) (by
      apply RingHom.ext
      intro p
      change middleToSourcePair K ((1 : sourceRing K) ⊗ₜ[K] p) =
        1 ⊗ₜ[K] polynomialToSource K p
      simp only [middleToSourcePair, Algebra.TensorProduct.map_tmul, map_one,
        ])
  simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using h

def pairLocalizer : polynomialPair K := localizer K ⊗ₜ[K] localizer K

theorem pairLocalizer_ne_zero : pairLocalizer K ≠ 0 := by
  intro h
  have hh := congrArg (Algebra.TensorProduct.lmul' K (S := polynomial K)) h
  simp only [pairLocalizer, Algebra.TensorProduct.lmul'_apply_tmul, map_zero] at hh
  exact mul_ne_zero (localizer_ne_zero K) (localizer_ne_zero K) hh

instance sourcePair_localization : IsLocalization.Away (pairLocalizer K) (sourcePair K) := by
  have hright : IsLocalization.Away
      (algebraMap (polynomialPair K) (middlePair K)
        ((1 : polynomial K) ⊗ₜ[K] localizer K)) (sourcePair K) := by
    change IsLocalization.Away
      (polynomialPairToMiddle K ((1 : polynomial K) ⊗ₜ[K] localizer K)) (sourcePair K)
    simpa only [polynomialPairToMiddle, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.id_apply] using middleSourcePair_localization K
  have h := IsLocalization.Away.mul' (middlePair K) (sourcePair K)
    ((localizer K) ⊗ₜ[K] (1 : polynomial K)) ((1 : polynomial K) ⊗ₜ[K] localizer K)
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, pairLocalizer] using h

instance sourcePair_isDomain : IsDomain (sourcePair K) :=
  IsLocalization.Away.isDomain (sourcePair K) (pairLocalizer_ne_zero K)

instance coefficientPolynomialPairSourcePair_tower :
    IsScalarTower K (polynomialPair K) (sourcePair K) :=
  IsScalarTower.of_algHom (polynomialPairToSourcePair K)

abbrev polynomialPairField := FractionRing (polynomialPair K)
abbrev sourcePairField := FractionRing (sourcePair K)
abbrev targetPairField := FractionRing (targetPair K)

theorem pairLocalizer_fraction_unit :
    IsUnit (algebraMap (polynomialPair K) (polynomialPairField K) (pairLocalizer K)) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (polynomialPair K) (polynomialPairField K)).ne
    (pairLocalizer_ne_zero K)

/-- The genuine localization map retains both independent original polynomial blocks. -/
def sourcePairToPolynomialFraction : sourcePair K →ₐ[K] polynomialPairField K :=
  IsLocalization.Away.liftAlgHom (pairLocalizer K)
    (f := IsScalarTower.toAlgHom K (polynomialPair K) (polynomialPairField K))
    (pairLocalizer_fraction_unit K)

@[simp] theorem sourcePairToPolynomialFraction_algebraMap (p : polynomialPair K) :
    sourcePairToPolynomialFraction K (algebraMap (polynomialPair K) (sourcePair K) p) =
      algebraMap (polynomialPair K) (polynomialPairField K) p :=
  IsLocalization.Away.lift_eq (pairLocalizer K) (pairLocalizer_fraction_unit K) p

instance sourcePairPolynomialFraction_algebra : Algebra (sourcePair K) (polynomialPairField K) :=
  (sourcePairToPolynomialFraction K).toRingHom.toAlgebra

instance coefficientSourcePairPolynomialFraction_tower :
    IsScalarTower K (sourcePair K) (polynomialPairField K) :=
  IsScalarTower.of_algHom (sourcePairToPolynomialFraction K)

instance polynomialPairSourcePairPolynomialFraction_tower :
    IsScalarTower (polynomialPair K) (sourcePair K) (polynomialPairField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  exact (sourcePairToPolynomialFraction_algebraMap K p).symm

instance polynomialFraction_isSourceFraction :
    IsFractionRing (sourcePair K) (polynomialPairField K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (pairLocalizer K)) (sourcePair K) (polynomialPairField K)

/-- Fraction fields are compared by the actual localization maps, not by
an arbitrary rationality isomorphism. -/
def sourcePairFractionEquiv : sourcePairField K ≃ₐ[K] polynomialPairField K :=
  (FractionRing.algEquiv (sourcePair K) (polynomialPairField K)).restrictScalars K

@[simp] theorem sourcePairFractionEquiv_algebraMap (b : sourcePair K) :
    sourcePairFractionEquiv K (algebraMap (sourcePair K) (sourcePairField K) b) =
      sourcePairToPolynomialFraction K b :=
  (FractionRing.algEquiv (sourcePair K) (polynomialPairField K)).commutes b

def sourcePairRationalEquiv : sourcePairField K ≃ₐ[K]
    FractionRing (MvPolynomial (Fin 8 ⊕ Fin 8) K) :=
  (sourcePairFractionEquiv K).trans
    (IsFractionRing.algEquivOfAlgEquiv (polynomialPairEquiv K))

def targetPairRationalEquiv : targetPairField K ≃ₐ[K]
    FractionRing (MvPolynomial
      (AlgebraicGeometry.Grassmannian.ChartIndex.{u}
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding ⊕
        AlgebraicGeometry.Grassmannian.ChartIndex.{u}
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding) K) :=
  IsFractionRing.algEquivOfAlgEquiv (targetPairEquiv K)

def coordinatePairMap : targetPair K →ₐ[K] sourcePair K :=
  Algebra.TensorProduct.map (coordinateMap K) (coordinateMap K)

variable [CharZero K]

theorem coordinatePairMap_injective : Function.Injective (coordinatePairMap K) := by
  change Function.Injective
    (TensorProduct.map (coordinateMap K).toLinearMap (coordinateMap K).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _
    (coordinateMap_injective K) (coordinateMap_injective K)

theorem coordinatePairFraction_injective : Function.Injective
    ((IsScalarTower.toAlgHom K (sourcePair K) (sourcePairField K)).comp
      (coordinatePairMap K)) :=
  (IsFractionRing.injective (sourcePair K) (sourcePairField K)).comp
    (coordinatePairMap_injective K)

def pairFieldEmbedding : targetPairField K →ₐ[K] sourcePairField K :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom K (sourcePair K) (sourcePairField K)).comp
      (coordinatePairMap K))
    (coordinatePairFraction_injective K)

@[simp] theorem pairFieldEmbedding_algebraMap (a : targetPair K) :
    pairFieldEmbedding K (algebraMap (targetPair K) (targetPairField K) a) =
      algebraMap (sourcePair K) (sourcePairField K) (coordinatePairMap K a) :=
  IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom K (sourcePair K) (sourcePairField K)).comp
      (coordinatePairMap K)).toRingHom)
    (coordinatePairFraction_injective K) a

end M9Native.ConicFramePairRings
